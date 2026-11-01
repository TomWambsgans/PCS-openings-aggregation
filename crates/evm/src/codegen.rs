// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/codegen.rs; the calls of `PCS_OPEN` are new here. MIT OR Apache-2.0; see NOTICE.md.
//! A recorded graph as EVM bytecode: straight-line code, a value used once left on the stack and a shared one
//! kept in a memory slot, which is reused after its last read.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::machine::{FIELD_MUL, PCS_OPEN};
use crate::record::{Graph, Node};

const STOP: u8 = 0x00;
const KECCAK256: u8 = 0x20;
const ISZERO: u8 = 0x15;
const AND: u8 = 0x16;
const OR: u8 = 0x17;
const XOR: u8 = 0x18;
const SHL: u8 = 0x1b;
const SHR: u8 = 0x1c;
const CALLDATALOAD: u8 = 0x35;
const CALLDATASIZE: u8 = 0x36;
const CALLDATACOPY: u8 = 0x37;
const CODECOPY: u8 = 0x39;
const RETURNDATASIZE: u8 = 0x3d;
const POP: u8 = 0x50;
const MLOAD: u8 = 0x51;
const MSTORE: u8 = 0x52;
const JUMPI: u8 = 0x57;
const GAS: u8 = 0x5a;
const JUMPDEST: u8 = 0x5b;
const PUSH0: u8 = 0x5f;
const DUP1: u8 = 0x80;
const DUP2: u8 = 0x81;
const SWAP1: u8 = 0x90;
const RETURN: u8 = 0xf3;
const STATICCALL: u8 = 0xfa;
const REVERT: u8 = 0xfd;

/// Memory below the slots is scratch for hashing: the seed's 112 bytes, or a state and the scalars it absorbs.
const SEED_SCRATCH: usize = 0x80;

/// Where calldata holds the statement's two words, then the commitments; the proof's scalars follow them.
pub const COMMITMENT: usize = 64;
pub const SCALAR_BYTES: usize = 24;

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

/// A field element as a word: limb 0 lowest.
fn word(limbs: [u64; 3]) -> [u8; 32] {
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
    /// The word of calldata at this offset.
    Calldata(usize),
}

/// What the contract does with its output region, once written.
pub enum Ending {
    /// Return it.
    Return,
    /// Call `PCS_OPEN` on each of these runs of words of it, in order and back to back; revert unless every call
    /// attests, and return nothing.
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
    CopyConst {
        first: usize,
        words: usize,
        data: usize,
    },
    /// Call `PCS_OPEN` on `words` output words from `first` on, and revert unless it attests.
    PcsOpen {
        first: usize,
        words: usize,
    },
    /// Jump to the revert if the top of the stack is nonzero.
    FailIf,
}

struct Compiler<'a> {
    graph: &'a Graph,
    /// The transcript's label before the statement: the protocol's name and the circuit's commitment.
    prefix: &'a [u8; 48],
    /// Where calldata holds the proof's scalars.
    scalars: usize,
    /// Kept in memory: used more than once, and not a constant.
    shared: Vec<bool>,
    done: Vec<bool>,
    /// Stack words evaluating a node takes.
    depth: Vec<u32>,
    items: Vec<Item>,
}

impl Compiler<'_> {
    fn code(&mut self, bytes: &[u8]) {
        self.items.push(Item::Code(bytes.to_vec()));
    }

    fn operands(node: Node) -> Vec<u32> {
        match node {
            Node::Add(a, b) | Node::Mul(a, b) if a == b => vec![a],
            Node::Add(a, b) | Node::Mul(a, b) => vec![a, b],
            Node::Hash(state, scalars, n) => [&[state][..], &scalars[..n as usize]].concat(),
            Node::Frobenius(a) | Node::Low(a) => vec![a],
            _ => vec![],
        }
    }

    /// Leave the node's value on the stack.
    fn eval(&mut self, id: u32) {
        let at = id as usize;
        if self.shared[at] && self.done[at] {
            self.items.push(Item::Load(id));
            return;
        }
        match self.graph.nodes[at] {
            Node::Const(limbs) => self.code(&push(&word(limbs))),
            Node::Statement(k) | Node::Root(k) => {
                let offset = match self.graph.nodes[at] {
                    Node::Root(_) => COMMITMENT + 32 * (k as usize / 2),
                    _ => 32 * (k as usize / 2),
                };
                self.code(&push_usize(offset));
                self.code(&[CALLDATALOAD]);
                if k % 2 == 0 {
                    self.code(&[&push_usize(128)[..], &[SHR]].concat());
                } else {
                    self.code(&[&push(&[0xff; 16])[..], &[AND]].concat());
                }
            }
            Node::Input(i) => {
                self.code(&push_usize(self.scalars + SCALAR_BYTES * i as usize));
                self.code(&[&[CALLDATALOAD][..], &push_usize(64), &[SHR]].concat());
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
            Node::Frobenius(a) => {
                // `(c0, c1, c2)` to `(c0, c2, c1 + c2)`.
                self.eval(a);
                let low = push(&[0xff; 8]);
                self.code(&[&[DUP1][..], &push_usize(128), &[SHR]].concat());
                self.code(&[&[DUP2][..], &push_usize(64), &[SHR], &low, &[AND, DUP2, XOR]].concat());
                self.code(&[&push_usize(128)[..], &[SHL, SWAP1], &push_usize(64), &[SHL, OR]].concat());
                self.code(&[&[SWAP1][..], &low, &[AND, OR]].concat());
            }
            Node::Seed => {
                self.code(&[&push(&self.prefix[..32])[..], &[PUSH0, MSTORE]].concat());
                self.code(&[&push(&self.prefix[16..])[..], &push_usize(16), &[MSTORE]].concat());
                self.code(&[&push_usize(64)[..], &[PUSH0], &push_usize(48), &[CALLDATACOPY]].concat());
                self.code(&[&push_usize(112)[..], &[PUSH0, KECCAK256]].concat());
            }
            Node::Hash(state, scalars, n) => {
                // Every operand reaches the stack before any is written to the scratch words.
                self.eval(state);
                for &scalar in &scalars[..n as usize] {
                    self.eval(scalar);
                }
                for k in (1..=n as usize).rev() {
                    self.code(&[&push_usize(32 * k)[..], &[MSTORE]].concat());
                }
                self.code(&[PUSH0, MSTORE]);
                self.code(&[&push_usize(32 * (n as usize + 1))[..], &[PUSH0, KECCAK256]].concat());
            }
            Node::Low(a) => {
                self.eval(a);
                self.code(&[&push(&[0xff; 24])[..], &[AND]].concat());
            }
        }
        if self.shared[at] {
            self.done[at] = true;
            self.items.push(Item::Store(id));
        }
    }
}

/// A contract, and what one call of it executes: its code is straight-line, so every instruction runs once.
pub struct Contract {
    pub code: Vec<u8>,
    pub field_muls: usize,
    pub hashes: usize,
    /// Memory it touches, in words.
    pub memory_words: usize,
}

/// The contract: revert unless calldata is `calldata_len` bytes and every node of `graph.nonzero` is nonzero,
/// else write `outputs` to a region of fresh memory, one word each, and end as `ending` says. The proof's
/// scalars start at byte `scalars` of calldata.
pub fn compile(
    graph: &Graph,
    outputs: &[Word],
    ending: &Ending,
    prefix: &[u8; 48],
    scalars: usize,
    calldata_len: usize,
) -> Contract {
    let n = graph.nodes.len();
    let mut uses = vec![0u32; n];
    let output_nodes = outputs.iter().filter_map(|word| match word {
        Word::Node(id) => Some(id),
        _ => None,
    });
    for &root in graph.nonzero.iter().chain(output_nodes) {
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
            [a] => of(a).max(3),
            [a, b] if matches!(graph.nodes[at], Node::Add(..) | Node::Mul(..)) => {
                if of(a) == of(b) {
                    of(a) + 1
                } else {
                    of(a).max(of(b))
                }
            }
            ref operands => {
                operands
                    .iter()
                    .zip(0..)
                    .map(|(&id, below)| of(id) + below)
                    .max()
                    .unwrap()
                    + 2
            }
        };
    }

    let mut compiler = Compiler {
        graph,
        prefix,
        scalars,
        shared,
        done: vec![false; n],
        depth,
        items: Vec::new(),
    };
    compiler.code(&[&[CALLDATASIZE][..], &push_usize(calldata_len), &[XOR]].concat());
    compiler.items.push(Item::FailIf);
    for &id in &graph.nonzero {
        compiler.eval(id);
        compiler.code(&[ISZERO]);
        compiler.items.push(Item::FailIf);
    }
    // The region is fresh memory: a zero word is left as it is, and a run of constants is copied from the code
    // (`CODECOPY` and its three operands, 12 gas and 3 a word) when that is cheaper than a `PUSH` of each nonzero
    // word and of its address, and an `MSTORE` (9 gas).
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
            compiler.items.push(Item::CopyConst {
                first: k,
                words: run,
                data: data.len(),
            });
            constants().for_each(|bytes| data.extend_from_slice(bytes));
            k += run;
            continue;
        }
        match outputs[k] {
            Word::Node(id) => compiler.eval(id),
            Word::Const(bytes) if bytes == [0; 32] => {
                k += 1;
                continue;
            }
            Word::Const(bytes) => compiler.code(&push(&bytes)),
            Word::Calldata(offset) => compiler.code(&[&push_usize(offset)[..], &[CALLDATALOAD]].concat()),
        }
        compiler.items.push(Item::Output(k));
        k += 1;
    }
    if let Ending::PcsOpen(runs) = ending {
        assert_eq!(runs.iter().sum::<usize>(), outputs.len(), "the calls cover the region");
        let mut first = 0;
        for &words in runs {
            compiler.items.push(Item::PcsOpen { first, words });
            first += words;
        }
    }
    let count = |of: &dyn Fn(Node) -> bool| (0..n).filter(|&at| uses[at] > 0 && of(graph.nodes[at])).count();
    let field_muls = count(&|node| matches!(node, Node::Mul(..)));
    let hashes = count(&|node| matches!(node, Node::Hash(..) | Node::Seed));
    let items = compiler.items;

    // A slot is free again after its node's last read.
    let mut reads = vec![0u32; n];
    for item in &items {
        if let Item::Load(id) = item {
            reads[*id as usize] += 1;
        }
    }
    let mut slot = vec![0usize; n];
    let (mut free, mut n_slots) = (BinaryHeap::new(), 0);
    for item in &items {
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
    let absorbed = graph.nodes.iter().map(|node| match node {
        Node::Hash(_, _, n) => *n as usize,
        _ => 0,
    });
    let slots = SEED_SCRATCH.max(32 * (1 + absorbed.max().unwrap_or(0)));
    let address = |id: u32| push_usize(slots + 32 * slot[id as usize]);
    let returned = slots + 32 * n_slots;

    // Code, then the revert, then the constants copied: a `PUSH2` of either address has one length on both passes.
    let push2 = |at: usize| [0x61, (at >> 8) as u8, at as u8];
    let assemble = |fail: usize, data_at: usize| {
        let mut code = Vec::new();
        for item in &items {
            match *item {
                Item::Code(ref bytes) => code.extend_from_slice(bytes),
                Item::Store(id) => code.extend([&[DUP1][..], &address(id), &[MSTORE]].concat()),
                Item::Load(id) => code.extend([&address(id)[..], &[MLOAD]].concat()),
                Item::Output(k) => code.extend([&push_usize(returned + 32 * k)[..], &[MSTORE]].concat()),
                Item::CopyConst { first, words, data } => code.extend(
                    [
                        &push_usize(32 * words)[..],
                        &push2(data_at + data),
                        &push_usize(returned + 32 * first),
                        &[CODECOPY],
                    ]
                    .concat(),
                ),
                // `STATICCALL(gas, PCS_OPEN, input, input length, 0, 0)`: the call attests iff it returns data, which
                // no failing call and no absent precompile does. Its success flag says no more, and is dropped.
                Item::PcsOpen { first, words } => code.extend(
                    [
                        &[PUSH0, PUSH0][..],
                        &push_usize(32 * words),
                        &push_usize(returned + 32 * first),
                        &push(PCS_OPEN.as_slice()),
                        &[GAS, STATICCALL, POP, RETURNDATASIZE, ISZERO],
                        &push2(fail),
                        &[JUMPI],
                    ]
                    .concat(),
                ),
                Item::FailIf => code.extend([&push2(fail)[..], &[JUMPI]].concat()),
            }
        }
        match ending {
            Ending::Return => {
                code.extend([&push_usize(32 * outputs.len())[..], &push_usize(returned), &[RETURN]].concat())
            }
            Ending::PcsOpen(_) => code.push(STOP),
        }
        code
    };
    const REVERT_CODE: [u8; 4] = [JUMPDEST, PUSH0, PUSH0, REVERT];
    let mut code = assemble(0, 0);
    code = assemble(code.len(), code.len() + REVERT_CODE.len());
    code.extend(REVERT_CODE);
    code.extend(data);
    Contract {
        code,
        field_muls,
        hashes,
        memory_words: (returned + 32 * outputs.len()) / 32,
    }
}
