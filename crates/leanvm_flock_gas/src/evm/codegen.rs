// Adapted from this repository's crates/evm/src/codegen.rs (itself adapted from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6): the same compilation of
// a recorded graph to straight-line code, a value used once left on the stack and a shared one kept in a memory slot
// reused after its last read; here for leanVM's verifier: the transcript absorbs runs of calldata, a check is of zero
// or of nonzero, commitments come from calldata or storage, every byte of code carries the phase it computes, and a
// measuring build that never reverts. MIT OR Apache-2.0; see NOTICE.md.
//! A recorded graph as EVM bytecode.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::evm::machine::{FIELD_MUL, PCS_OPEN};
use crate::evm::record::{Graph, Node};

const KECCAK256: u8 = 0x20;
const ISZERO: u8 = 0x15;
const AND: u8 = 0x16;
const OR: u8 = 0x17;
const XOR: u8 = 0x18;
const SHR: u8 = 0x1c;
const CALLVALUE: u8 = 0x34;
const CALLDATALOAD: u8 = 0x35;
const CALLDATASIZE: u8 = 0x36;
const CALLDATACOPY: u8 = 0x37;
const CODECOPY: u8 = 0x39;
const RETURNDATASIZE: u8 = 0x3d;
const MLOAD: u8 = 0x51;
const MSTORE: u8 = 0x52;
const SLOAD: u8 = 0x54;
const JUMPI: u8 = 0x57;
const GAS: u8 = 0x5a;
const JUMPDEST: u8 = 0x5b;
const PUSH0: u8 = 0x5f;
const DUP1: u8 = 0x80;
const RETURN: u8 = 0xf3;
const STATICCALL: u8 = 0xfa;
const REVERT: u8 = 0xfd;

/// The selector of `verify(bytes32,bytes)`: calldata starting with it is a proof to verify.
pub const VERIFY: [u8; 4] = [0x8e, 0x76, 0x0a, 0xfe];
/// Calldata: the selector, the public input's four 64-bit words (big-endian each, word 0 first), then the stream.
pub const PUBLIC_INPUT: usize = VERIFY.len();
pub const STREAM: usize = PUBLIC_INPUT + 32;

/// The phases of what is not the verifier's arithmetic.
pub const ENTRY: &str = "entry: selector, length, no value";
pub const CALLS: &str = "PCS_OPEN: claims written, calls, replies checked";
pub const ROOTS: &str = "PCS_OPEN: fixed commitments read (cold SLOAD)";
pub const MEASURE: &str = "measurement only (JUMPDEST after each check, subtracted)";

/// How the contract is entered and seeded.
#[derive(Clone, Copy, Debug)]
pub struct Entry {
    /// The transcript's seed hashes this name, the program's IV and the public input.
    pub name: [u8; 16],
    pub iv: [u8; 32],
    /// Bytes of the stream.
    pub stream_len: usize,
    /// A check that fails jumps to the instruction after it instead of the revert, so that any calldata runs the whole
    /// code: the gas of a valid proof plus one (a `JUMPDEST`) per check.
    pub measure: bool,
}

/// `PUSH` of a big-endian number, in as few bytes as it takes.
fn push(bytes: &[u8]) -> Vec<u8> {
    let trimmed = &bytes[bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len())..];
    if trimmed.is_empty() {
        return vec![PUSH0];
    }
    let mut code = vec![PUSH0 + trimmed.len() as u8];
    code.extend_from_slice(trimmed);
    code
}

fn push_usize(value: usize) -> Vec<u8> {
    push(&value.to_be_bytes())
}

/// `PUSH3` of an address in the code: one length whatever the address, so code can be laid out in two passes.
fn push3(at: usize) -> [u8; 4] {
    assert!(at < 1 << 24, "an address of three bytes");
    [0x62, (at >> 16) as u8, (at >> 8) as u8, at as u8]
}

/// A field element as a word: limb 0 lowest.
pub fn word(limbs: [u64; 3]) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (i, limb) in limbs.iter().enumerate() {
        bytes[24 - 8 * i..32 - 8 * i].copy_from_slice(&limb.to_be_bytes());
    }
    bytes
}

/// A word the contract writes to its output region.
#[derive(Clone, Copy, Debug)]
pub enum Word {
    /// A recorded value.
    Node(u32),
    Const([u8; 32]),
    /// The word of the stream at this byte offset: a root's two 16-byte halves.
    Stream(usize),
    /// The word in this storage slot: a fixed commitment.
    Stored(u8),
}

/// What the contract does with its output region, once written.
pub enum Ending {
    /// Return it.
    Return,
    /// Call `PCS_OPEN` on each of these runs of words of it, in order and back to back; revert unless every call
    /// succeeds returning the word 1, and return the word 1.
    PcsOpen(Vec<usize>),
}

enum Item {
    Code(Vec<u8>),
    /// Keep the value on top of the stack in the node's slot, too.
    Store(u32),
    Load(u32),
    /// Pop the value into output word `k`.
    Output(usize),
    /// Copy `words` constant words, from `data` on in the code's data, to output words `first` on.
    CopyConst { first: usize, words: usize, data: usize },
    /// Call `PCS_OPEN` on `words` output words from `first` on, and revert unless it attests.
    PcsOpen { first: usize, words: usize },
    /// Jump to the revert if the top of the stack is nonzero.
    FailIf,
}

struct Compiler<'a> {
    graph: &'a Graph,
    entry: &'a Entry,
    /// Kept in memory: used more than once, and not a constant.
    shared: Vec<bool>,
    done: Vec<bool>,
    /// Stack words evaluating a node takes.
    depth: Vec<u32>,
    /// Each item, and the phase its code computes.
    items: Vec<(Item, &'static str)>,
    phase: &'static str,
}

impl Compiler<'_> {
    fn code(&mut self, bytes: &[u8]) {
        self.items.push((Item::Code(bytes.to_vec()), self.phase));
    }

    fn item(&mut self, item: Item) {
        self.items.push((item, self.phase));
    }

    fn operands(node: Node) -> Vec<u32> {
        match node {
            Node::Add(a, b) | Node::Mul(a, b) if a == b => vec![a],
            Node::Add(a, b) | Node::Mul(a, b) => vec![a, b],
            Node::Hash(state, _, _) | Node::Low(state) => vec![state],
            _ => vec![],
        }
    }

    /// Leave the node's value on the stack.
    fn eval(&mut self, id: u32) {
        let at = id as usize;
        let outer = std::mem::replace(&mut self.phase, self.graph.phases[at]);
        if self.shared[at] && self.done[at] {
            self.item(Item::Load(id));
            self.phase = outer;
            return;
        }
        match self.graph.nodes[at] {
            Node::Const(limbs) => self.code(&push(&word(limbs))),
            Node::Statement(k) => {
                let load = [
                    &push_usize(PUBLIC_INPUT + 8 * k as usize)[..],
                    &[CALLDATALOAD],
                    &push_usize(192),
                    &[SHR],
                ];
                self.code(&load.concat());
            }
            Node::Input { offset, len } => {
                let load = [
                    &push_usize(STREAM + offset as usize)[..],
                    &[CALLDATALOAD],
                    &push_usize(256 - 8 * len as usize),
                    &[SHR],
                ];
                self.code(&load.concat());
            }
            Node::Add(a, b) | Node::Mul(a, b) => {
                let op = if matches!(self.graph.nodes[at], Node::Add(..)) {
                    XOR
                } else {
                    FIELD_MUL
                };
                if a == b {
                    self.eval(a);
                    self.code(&[DUP1]);
                } else {
                    // The deeper operand first, so the other is evaluated over one word, not under many.
                    let (first, second) = if self.depth[a as usize] >= self.depth[b as usize] {
                        (a, b)
                    } else {
                        (b, a)
                    };
                    self.eval(first);
                    self.eval(second);
                }
                self.code(&[op]);
            }
            // The name and the IV, as two overlapping words at 0 and 16, then the public input at 48.
            Node::Seed => {
                let head = [&self.entry.name[..], &self.entry.iv[..16]].concat();
                self.code(&[&push(&head)[..], &[PUSH0, MSTORE]].concat());
                self.code(&[&push(&self.entry.iv)[..], &push_usize(16), &[MSTORE]].concat());
                let copy = [&push_usize(32)[..], &push_usize(PUBLIC_INPUT), &push_usize(48), &[CALLDATACOPY]];
                self.code(&copy.concat());
                self.code(&[&push_usize(80)[..], &[PUSH0, KECCAK256]].concat());
            }
            Node::Hash(state, from, to) => {
                // The state's evaluation may hash too: it is done before the scratch is written.
                self.eval(state);
                self.code(&[PUSH0, MSTORE]);
                let bytes = (to - from) as usize;
                if bytes > 0 {
                    let copy = [
                        &push_usize(bytes)[..],
                        &push_usize(STREAM + from as usize),
                        &push_usize(32),
                        &[CALLDATACOPY],
                    ];
                    self.code(&copy.concat());
                }
                self.code(&[&push_usize(32 + bytes)[..], &[PUSH0, KECCAK256]].concat());
            }
            Node::Low(a) => {
                self.eval(a);
                self.code(&[&push(&[0xff; 24])[..], &[AND]].concat());
            }
        }
        if self.shared[at] {
            self.done[at] = true;
            self.item(Item::Store(id));
        }
        self.phase = outer;
    }
}

/// A contract, and what one call of it executes: its code is straight-line, so every instruction runs once.
pub struct Contract {
    pub code: Vec<u8>,
    /// The phase of each byte of code.
    pub phase_of: Vec<&'static str>,
    pub calldata_len: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    /// Bytes the transcript hashes, the states included.
    pub hashed_bytes: usize,
    pub checks: usize,
    /// Memory it touches, in words.
    pub memory_words: usize,
}

/// The contract. A call of it is calldata of the selector, the public input and `entry.stream_len` bytes of stream,
/// with no value. It reverts unless every node of `graph.zero` is zero and every one of `graph.nonzero` nonzero, else
/// writes `outputs` to a region of fresh memory, one word each, and ends as `ending` says.
pub fn compile(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry) -> Contract {
    let calldata_len = STREAM + entry.stream_len;
    let n = graph.nodes.len();
    let mut uses = vec![0u32; n];
    let output_nodes = outputs.iter().filter_map(|word| match word {
        Word::Node(id) => Some(id),
        _ => None,
    });
    let checked = graph.zero.iter().chain(&graph.nonzero).map(|(id, _)| id);
    for &root in checked.chain(output_nodes) {
        uses[root as usize] += 1;
    }
    for at in (0..n).rev() {
        if uses[at] > 0 {
            for operand in Compiler::operands(graph.nodes[at]) {
                uses[operand as usize] += 1;
            }
        }
    }
    let shared: Vec<bool> = (0..n)
        .map(|at| uses[at] > 1 && !matches!(graph.nodes[at], Node::Const(_)))
        .collect();
    let mut depth = vec![1u32; n];
    for at in 0..n {
        let of = |id: u32| if shared[id as usize] { 1 } else { depth[id as usize] };
        depth[at] = match Compiler::operands(graph.nodes[at])[..] {
            [] => 1,
            // A lone operand, and what the instruction works in above it.
            [a] => of(a).max(4),
            [a, b] => {
                if of(a) == of(b) {
                    of(a) + 1
                } else {
                    of(a).max(of(b))
                }
            }
            _ => unreachable!("at most two operands"),
        };
    }

    let mut compiler = Compiler {
        graph,
        entry,
        shared,
        done: vec![false; n],
        depth,
        items: Vec::new(),
        phase: ENTRY,
    };
    // Not a call of the verifier: calldata of another length, or of another selector, or value.
    let selector = [
        &[CALLDATASIZE][..],
        &push_usize(calldata_len),
        &[XOR, PUSH0, CALLDATALOAD],
        &push_usize(224),
        &[SHR],
        &push(&VERIFY),
        &[XOR, OR, CALLVALUE, OR],
    ];
    compiler.code(&selector.concat());
    compiler.item(Item::FailIf);
    let checks = graph.zero.len() + graph.nonzero.len();
    for &(id, _) in &graph.zero {
        compiler.eval(id);
        compiler.phase = graph.phases[id as usize];
        compiler.item(Item::FailIf);
    }
    for &(id, _) in &graph.nonzero {
        compiler.eval(id);
        compiler.phase = graph.phases[id as usize];
        compiler.code(&[ISZERO]);
        compiler.item(Item::FailIf);
    }
    // The region is fresh memory: a zero word is left as it is, and a run of constants is copied from the code
    // (`CODECOPY` and its three operands, 12 gas and 3 a word) when that is cheaper than a `PUSH` of each nonzero
    // word and of its address, and an `MSTORE` (9 gas).
    compiler.phase = CALLS;
    let mut data = Vec::new();
    let mut k = 0;
    while k < outputs.len() {
        let run = outputs[k..]
            .iter()
            .take_while(|word| matches!(word, Word::Const(_)))
            .count();
        let constants = || {
            outputs[k..k + run].iter().filter_map(|word| match word {
                Word::Const(bytes) => Some(bytes),
                _ => None,
            })
        };
        let nonzero = constants().filter(|bytes| **bytes != [0; 32]).count();
        if 12 + 3 * run < 9 * nonzero {
            compiler.item(Item::CopyConst {
                first: k,
                words: run,
                data: data.len(),
            });
            constants().for_each(|bytes| data.extend_from_slice(bytes));
            k += run;
            continue;
        }
        match outputs[k] {
            Word::Node(id) => {
                compiler.eval(id);
                compiler.phase = CALLS;
            }
            Word::Const(bytes) if bytes == [0; 32] => {
                k += 1;
                continue;
            }
            Word::Const(bytes) => compiler.code(&push(&bytes)),
            Word::Stream(offset) => compiler.code(&[&push_usize(STREAM + offset)[..], &[CALLDATALOAD]].concat()),
            Word::Stored(slot) => {
                compiler.phase = ROOTS;
                compiler.code(&[&push_usize(slot.into())[..], &[SLOAD]].concat());
                compiler.phase = CALLS;
            }
        }
        compiler.item(Item::Output(k));
        k += 1;
    }
    if let Ending::PcsOpen(runs) = ending {
        assert_eq!(runs.iter().sum::<usize>(), outputs.len(), "the calls cover the region");
        let mut first = 0;
        for &words in runs {
            compiler.item(Item::PcsOpen { first, words });
            first += words;
        }
    }
    let count = |of: &dyn Fn(Node) -> bool| (0..n).filter(|&at| uses[at] > 0 && of(graph.nodes[at])).count();
    let field_muls = count(&|node| matches!(node, Node::Mul(..)));
    let xors = count(&|node| matches!(node, Node::Add(..)));
    let hashes = count(&|node| matches!(node, Node::Hash(..) | Node::Seed));
    let hashed_bytes = (0..n)
        .filter(|&at| uses[at] > 0)
        .map(|at| match graph.nodes[at] {
            Node::Hash(_, from, to) => 32 + (to - from) as usize,
            Node::Seed => 80,
            _ => 0,
        })
        .sum();
    let items = compiler.items;

    // A slot is free again after its node's last read.
    let mut reads = vec![0u32; n];
    for (item, _) in &items {
        if let Item::Load(id) = item {
            reads[*id as usize] += 1;
        }
    }
    let mut slot = vec![0usize; n];
    let (mut free, mut n_slots) = (BinaryHeap::new(), 0);
    for (item, _) in &items {
        match item {
            Item::Store(id) => {
                slot[*id as usize] = free.pop().map_or_else(
                    || {
                        n_slots += 1;
                        n_slots - 1
                    },
                    |Reverse(s)| s,
                );
            }
            Item::Load(id) => {
                reads[*id as usize] -= 1;
                if reads[*id as usize] == 0 {
                    free.push(Reverse(slot[*id as usize]));
                }
            }
            _ => {}
        }
    }
    // Below the slots: the hashing scratch, a state and the longest run of the stream absorbed (and the seed's 80).
    let absorbed = graph.nodes.iter().map(|node| match node {
        Node::Hash(_, from, to) => (to - from) as usize,
        _ => 0,
    });
    let slots = (32 + absorbed.max().unwrap_or(0)).max(80).next_multiple_of(32);
    let address = |id: u32| push_usize(slots + 32 * slot[id as usize]);
    let returned = slots + 32 * n_slots;

    // Code, then the revert, then the constants copied: a `PUSH3` of either address has one length on both passes.
    const REVERT_CODE: [u8; 4] = [JUMPDEST, PUSH0, PUSH0, REVERT];
    let assemble = |fail: usize, data_at: usize| {
        let mut code = Vec::new();
        let mut phase_of = Vec::new();
        for (item, phase) in &items {
            let mut phase = *phase;
            match *item {
                Item::Code(ref bytes) => code.extend_from_slice(bytes),
                Item::Store(id) => code.extend([&[DUP1][..], &address(id), &[MSTORE]].concat()),
                Item::Load(id) => code.extend([&address(id)[..], &[MLOAD]].concat()),
                Item::Output(k) => code.extend([&push_usize(returned + 32 * k)[..], &[MSTORE]].concat()),
                Item::CopyConst { first, words, data } => code.extend(
                    [
                        &push_usize(32 * words)[..],
                        &push3(data_at + data),
                        &push_usize(returned + 32 * first),
                        &[CODECOPY],
                    ]
                    .concat(),
                ),
                // `STATICCALL(gas, PCS_OPEN, input, input length, 0, 32)`: the call attests iff it succeeds and
                // returns exactly one word, the word 1 (then at 0, the hashing scratch, free by now).
                Item::PcsOpen { first, words } => {
                    let call = [
                        &push_usize(32)[..],
                        &[PUSH0],
                        &push_usize(32 * words),
                        &push_usize(returned + 32 * first),
                        &push(PCS_OPEN.as_slice()),
                        &[GAS, STATICCALL, ISZERO, RETURNDATASIZE],
                        &push_usize(32),
                        &[XOR, OR, PUSH0, MLOAD],
                        &push_usize(1),
                        &[XOR, OR],
                    ];
                    code.extend(call.concat());
                    if entry.measure {
                        code.extend([&push3(code.len() + 5)[..], &[JUMPI]].concat());
                        phase_of.resize(code.len(), phase);
                        code.push(JUMPDEST);
                        phase = MEASURE;
                    } else {
                        code.extend([&push3(fail)[..], &[JUMPI]].concat());
                    }
                }
                Item::FailIf => {
                    if entry.measure {
                        // `PUSH3 next JUMPI JUMPDEST`: the check's gas, and one more.
                        code.extend([&push3(code.len() + 5)[..], &[JUMPI]].concat());
                        phase_of.resize(code.len(), phase);
                        code.push(JUMPDEST);
                        phase = MEASURE;
                    } else {
                        code.extend([&push3(fail)[..], &[JUMPI]].concat());
                    }
                }
            }
            phase_of.resize(code.len(), phase);
        }
        let tail = match ending {
            Ending::Return => [&push_usize(32 * outputs.len())[..], &push_usize(returned), &[RETURN]].concat(),
            // The word 1, which an account without code does not return.
            Ending::PcsOpen(_) => [&push_usize(1)[..], &[PUSH0, MSTORE], &push_usize(32), &[PUSH0, RETURN]].concat(),
        };
        code.extend(tail);
        phase_of.resize(code.len(), CALLS);
        (code, phase_of)
    };
    let body = assemble(0, 0).0.len();
    let (mut code, mut phase_of) = assemble(body, body + REVERT_CODE.len());
    code.extend(REVERT_CODE);
    code.extend(data);
    phase_of.resize(code.len(), ENTRY);
    Contract {
        code,
        phase_of,
        calldata_len,
        field_muls,
        xors,
        hashes,
        hashed_bytes,
        checks: checks + 1,
        memory_words: (returned + 32 * outputs.len()) / 32,
    }
}
