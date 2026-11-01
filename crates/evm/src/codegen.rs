// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/codegen.rs; new here: the calls of `PCS_OPEN`, the selector, the index root in storage
// (`Entry`), `setIndexRoot` and the creation code. MIT OR Apache-2.0; see NOTICE.md.
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
const CALLER: u8 = 0x33;
const CALLVALUE: u8 = 0x34;
const CALLDATALOAD: u8 = 0x35;
const CALLDATASIZE: u8 = 0x36;
const CALLDATACOPY: u8 = 0x37;
const CODESIZE: u8 = 0x38;
const CODECOPY: u8 = 0x39;
const RETURNDATASIZE: u8 = 0x3d;
const MLOAD: u8 = 0x51;
const MSTORE: u8 = 0x52;
const SLOAD: u8 = 0x54;
const SSTORE: u8 = 0x55;
const JUMPI: u8 = 0x57;
const GAS: u8 = 0x5a;
const JUMPDEST: u8 = 0x5b;
const PUSH0: u8 = 0x5f;
const PUSH32: u8 = 0x7f;
const DUP1: u8 = 0x80;
const DUP2: u8 = 0x81;
const SWAP1: u8 = 0x90;
const SWAP2: u8 = 0x91;
const RETURN: u8 = 0xf3;
const STATICCALL: u8 = 0xfa;
const REVERT: u8 = 0xfd;

/// Memory below the slots is scratch for hashing: the seed's 112 bytes (at 0, or at 16 when the circuit's
/// commitment is in storage), or a state and the scalars it absorbs.
const SEED_SCRATCH: usize = 0x80;

/// The selector of `verify(bytes32,bytes32,bytes)`, the first 4 bytes of the `keccak256` of that signature: calldata
/// starting with it is a proof to verify.
pub const VERIFY: [u8; 4] = [0xde, 0x12, 0xc6, 0x40];
/// The selector of `setIndexRoot(bytes32)`.
pub const SET_INDEX_ROOT: [u8; 4] = [0xcd, 0xaf, 0x73, 0x6c];
/// The storage slot holding the circuit's commitment, when the code does not.
pub const INDEX_ROOT_SLOT: u8 = 0;

/// Where the arguments (calldata after the selector, if any) hold the statement's two words, then the commitments;
/// the proof's scalars follow them.
pub const COMMITMENT: usize = 64;
pub const SCALARS: usize = COMMITMENT + 64;
pub const SCALAR_BYTES: usize = 24;

/// How calls enter the contract, and where it finds the circuit's commitment.
#[derive(Clone, Copy, Debug)]
pub struct Entry {
    /// Calldata starts with [`VERIFY`], and a call of the verifier carries no value; otherwise calldata is the
    /// arguments alone.
    pub selector: bool,
    /// The transcript's label is the protocol's 16-byte name, the circuit's commitment, then the statement.
    pub name: [u8; 16],
    /// The circuit's commitment: in the code, or (`None`) in storage slot [`INDEX_ROOT_SLOT`], which the creation
    /// code writes and the owner may change ([`SET_INDEX_ROOT`]).
    pub index_root: Option<[u8; 32]>,
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

/// `PUSH2` of an address in the code: one length whatever the address, so code can be laid out in two passes.
fn push2(at: usize) -> [u8; 3] {
    assert!(at < 1 << 16, "an address of two bytes");
    [0x61, (at >> 8) as u8, at as u8]
}

/// Reverse the bytes of each 16-byte half of the word on top of the stack, which makes a root's bytes the word
/// `PCS_OPEN` reads ([`crate::machine::root_word`]): `x = ((x >> s) & m) | ((x & m) << s)` for `s` of 8, 4, 2
/// and 1 bytes, `m` the low `s` bytes of every `2s`-byte lane (33 gas each).
fn reverse_halves() -> Vec<u8> {
    let mut code = Vec::new();
    for bytes in [8, 4, 2, 1] {
        let mask: [u8; 32] = std::array::from_fn(|i| if i % (2 * bytes) >= bytes { 0xff } else { 0 });
        let shift = push_usize(8 * bytes);
        code.extend(
            [
                &push(&mask)[..],
                &[DUP2, DUP2, AND],
                &shift,
                &[SHL, SWAP2],
                &shift,
                &[SHR, AND, OR],
            ]
            .concat(),
        );
    }
    code
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
    /// The word of the arguments at this offset.
    Calldata(usize),
    /// The circuit's commitment, in storage, as `PCS_OPEN` reads a root: the seed writes it, having read it.
    StoredRoot,
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
    /// Jump to the contract's other entry ([`SET_INDEX_ROOT`]'s, or else the revert) if the top of the stack is
    /// nonzero.
    NotVerify,
}

struct Compiler<'a> {
    graph: &'a Graph,
    entry: &'a Entry,
    /// Where calldata holds the arguments: after the selector, if any.
    base: usize,
    /// The output word of [`Word::StoredRoot`], if any.
    stored_root: Option<usize>,
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
                    Node::Root(_) => self.base + COMMITMENT + 32 * (k as usize / 2),
                    _ => self.base + 32 * (k as usize / 2),
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
                self.code(&push_usize(self.base + SCALARS + SCALAR_BYTES * i as usize));
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
            // The label, the name and the circuit's commitment then the statement copied from calldata.
            Node::Seed => match self.entry.index_root {
                Some(root) => {
                    // At 0: the 48 bytes before the statement as two overlapping words.
                    let prefix = [&self.entry.name[..], &root].concat();
                    self.code(&[&push(&prefix[..32])[..], &[PUSH0, MSTORE]].concat());
                    self.code(&[&push(&prefix[16..])[..], &push_usize(16), &[MSTORE]].concat());
                    let copy = [
                        &push_usize(64)[..],
                        &push_usize(self.base),
                        &push_usize(48),
                        &[CALLDATACOPY],
                    ];
                    self.code(&copy.concat());
                    self.code(&[&push_usize(112)[..], &[PUSH0, KECCAK256]].concat());
                }
                None => {
                    // At 16: the name as the low half of the word at 0, so the root, read from storage (a cold
                    // `SLOAD`, 2,100 gas), is the word at 32. The wiring table's call of `PCS_OPEN` takes it too,
                    // its halves reversed, written to its output word now.
                    let slot = push_usize(INDEX_ROOT_SLOT.into());
                    self.code(&[&push(&self.entry.name)[..], &[PUSH0, MSTORE], &slot, &[SLOAD]].concat());
                    if let Some(k) = self.stored_root {
                        self.code(&[[DUP1].as_slice(), &reverse_halves()].concat());
                        self.items.push(Item::Output(k));
                    }
                    self.code(&[&push_usize(32)[..], &[MSTORE]].concat());
                    let copy = [
                        &push_usize(64)[..],
                        &push_usize(self.base),
                        &push_usize(64),
                        &[CALLDATACOPY],
                    ];
                    self.code(&copy.concat());
                    self.code(&[&push_usize(112)[..], &push_usize(16), &[KECCAK256]].concat());
                }
            },
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
    /// The code, with no owner ([`creation_code`] writes one at `owner_at`).
    pub code: Vec<u8>,
    /// Where the code holds its owner, the word a `PUSH32` pushes, if it reads the circuit's commitment from
    /// storage.
    pub owner_at: Option<usize>,
    pub field_muls: usize,
    pub hashes: usize,
    /// Memory it touches, in words.
    pub memory_words: usize,
}

/// The contract. A call of the verifier is calldata of the selector ([`VERIFY`], if `entry` has one) and the
/// arguments: the statement, the commitments and `inputs` scalars of the proof, of `SCALAR_BYTES` each. On
/// such a call, with no value, it reverts unless every node of `graph.nonzero` is nonzero, else writes `outputs`
/// to a region of fresh memory, one word each, and ends as `ending` says. Any other call is one of
/// `setIndexRoot(bytes32 root)`, if the circuit's commitment is in storage, or reverts: from the owner, with no
/// value, it stores `root` in slot [`INDEX_ROOT_SLOT`] and returns nothing.
pub fn compile(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry, inputs: usize) -> Contract {
    assert!(
        entry.selector || entry.index_root.is_some(),
        "setIndexRoot needs a selector"
    );
    let base = if entry.selector { VERIFY.len() } else { 0 };
    let calldata_len = base + SCALARS + SCALAR_BYTES * inputs;
    let stored_root = outputs.iter().position(|word| matches!(word, Word::StoredRoot));
    assert!(
        stored_root.is_none() || entry.index_root.is_none(),
        "a stored root is in storage"
    );
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
        entry,
        base,
        stored_root,
        shared,
        done: vec![false; n],
        depth,
        items: Vec::new(),
    };
    // Not a call of the verifier: calldata of another length, or of another selector, or value.
    compiler.code(&[&[CALLDATASIZE][..], &push_usize(calldata_len), &[XOR]].concat());
    if entry.selector {
        let selector = [
            &[PUSH0, CALLDATALOAD][..],
            &push_usize(224),
            &[SHR],
            &push(&VERIFY),
            &[XOR],
        ];
        compiler.code(&[&selector.concat()[..], &[OR, CALLVALUE, OR]].concat());
    }
    compiler.items.push(Item::NotVerify);
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
            Word::Calldata(offset) => compiler.code(&[&push_usize(base + offset)[..], &[CALLDATALOAD]].concat()),
            Word::StoredRoot => {
                k += 1;
                continue;
            }
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
    if let Some(k) = stored_root {
        let written = compiler
            .items
            .iter()
            .any(|item| matches!(item, Item::Output(at) if *at == k));
        assert!(written, "the seed writes the stored root");
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

    // `setIndexRoot(bytes32 root)`: revert unless calldata is its selector and `root`, with no value, from the
    // owner; else store `root`. The owner is the word of a `PUSH32`, which the creation code writes.
    let set_index_root = |fail: usize| {
        let mut code = [
            &[JUMPDEST, PUSH0, CALLDATALOAD][..],
            &push_usize(224),
            &[SHR],
            &push(&SET_INDEX_ROOT),
        ]
        .concat();
        code.extend(
            [
                &[XOR, CALLDATASIZE][..],
                &push_usize(4 + 32),
                &[XOR, OR, CALLVALUE, OR, CALLER, PUSH32],
            ]
            .concat(),
        );
        let owner = code.len();
        code.extend([0; 32]);
        code.extend([&[XOR, OR][..], &push2(fail), &[JUMPI], &push_usize(4), &[CALLDATALOAD]].concat());
        code.extend([&push_usize(INDEX_ROOT_SLOT.into())[..], &[SSTORE, STOP]].concat());
        (code, owner)
    };

    // Code, then `setIndexRoot` if the root is in storage, then the revert, then the constants copied: a `PUSH2` of
    // any of these addresses has one length on both passes.
    let assemble = |other: usize, fail: usize, data_at: usize| {
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
                // `STATICCALL(gas, PCS_OPEN, input, input length, 0, 32)`: the call attests iff it succeeds and
                // returns exactly one word, the word 1 (then at 0, the hashing scratch, free by now). A failed or
                // reverted call, an absent precompile, the word 0, or more or fewer bytes, revert.
                Item::PcsOpen { first, words } => code.extend(
                    [
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
                        &push2(fail),
                        &[JUMPI],
                    ]
                    .concat(),
                ),
                Item::FailIf => code.extend([&push2(fail)[..], &[JUMPI]].concat()),
                Item::NotVerify => code.extend([&push2(other)[..], &[JUMPI]].concat()),
            }
        }
        match ending {
            Ending::Return => {
                code.extend([&push_usize(32 * outputs.len())[..], &push_usize(returned), &[RETURN]].concat())
            }
            // The word 1, which an account without code does not return.
            Ending::PcsOpen(_) => {
                code.extend([&push_usize(1)[..], &[PUSH0, MSTORE], &push_usize(32), &[PUSH0, RETURN]].concat())
            }
        }
        code
    };
    const REVERT_CODE: [u8; 4] = [JUMPDEST, PUSH0, PUSH0, REVERT];
    let body = assemble(0, 0, 0).len();
    let stored = entry.index_root.is_none();
    let fail = body + if stored { set_index_root(0).0.len() } else { 0 };
    let mut code = assemble(if stored { body } else { fail }, fail, fail + REVERT_CODE.len());
    let mut owner_at = None;
    if stored {
        let (tail, owner) = set_index_root(fail);
        owner_at = Some(code.len() + owner);
        code.extend(tail);
    }
    code.extend(REVERT_CODE);
    code.extend(data);
    Contract {
        code,
        owner_at,
        field_muls,
        hashes,
        memory_words: (returned + 32 * outputs.len()) / 32,
    }
}

/// The creation code of `contract`, which its constructor's arguments follow in the init code: for a contract
/// reading the circuit's commitment from storage, those of `constructor(bytes32 indexRoot, address owner)`,
/// ABI-encoded (64 bytes), and none otherwise. It reverts on value, or on arguments of another length; else it
/// stores `indexRoot` in slot [`INDEX_ROOT_SLOT`], writes the `owner` word into the code, and returns the code.
pub fn creation_code(contract: &Contract) -> Vec<u8> {
    let runtime = contract.code.len();
    let arguments = if contract.owner_at.is_some() { 64 } else { 0 };
    // The revert is the last 4 bytes of the `prefix` bytes before the code.
    let build = |prefix: usize| {
        let length = [
            &[CODESIZE][..],
            &push2(prefix + runtime + arguments),
            &[XOR, CALLVALUE, OR],
        ]
        .concat();
        let mut code = [&length[..], &push2(prefix - 4), &[JUMPI]].concat();
        // The code and the arguments, to memory at 0.
        code.extend([&push2(runtime + arguments)[..], &push2(prefix), &[PUSH0, CODECOPY]].concat());
        if let Some(owner_at) = contract.owner_at {
            code.extend(
                [
                    &push2(runtime)[..],
                    &[MLOAD],
                    &push_usize(INDEX_ROOT_SLOT.into()),
                    &[SSTORE],
                ]
                .concat(),
            );
            code.extend([&push2(runtime + 32)[..], &[MLOAD], &push2(owner_at), &[MSTORE]].concat());
        }
        code.extend([&push2(runtime)[..], &[PUSH0, RETURN, JUMPDEST, PUSH0, PUSH0, REVERT]].concat());
        code
    };
    let prefix = build(4).len();
    [build(prefix), contract.code.clone()].concat()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::{Chain, PcsOpen, root_word};

    /// The root's bytes, their halves reversed, are the word `PCS_OPEN` reads.
    #[test]
    fn reversed_halves_are_the_root_word() {
        let root: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(37) ^ 0xc5);
        let code = [
            &[PUSH32][..],
            &root,
            &reverse_halves(),
            &[PUSH0, MSTORE],
            &push_usize(32),
            &[PUSH0, RETURN],
        ];
        let contract = Contract {
            code: code.concat(),
            owner_at: None,
            field_muls: 0,
            hashes: 0,
            memory_words: 1,
        };
        let mut chain = Chain::default();
        let address = chain.deploy(&creation_code(&contract)).0.expect("a deployment");
        let output = chain.call(address, &[], &PcsOpen::default()).output;
        assert_eq!(output, Some(root_word(&root).to_vec()));
    }
}
