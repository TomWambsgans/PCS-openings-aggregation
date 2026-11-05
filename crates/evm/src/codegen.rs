// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/codegen.rs; new here: the calls of `PCS_OPEN`, the selector, the index root in storage
// (`Entry`), `setIndexRoot` and the creation code; the assembly is now `crates/evm_link`'s, which also links the
// program into contracts that each fit EIP-170's limit ([`compile_linked`]). MIT OR Apache-2.0; see NOTICE.md.
//! A recorded graph as EVM bytecode: straight-line code, a value used once left on the stack and a shared one
//! kept in a memory slot, which is reused after its last read.

use evm_link::op::{
    AND, CALLDATACOPY, CALLDATALOAD, CALLDATASIZE, CALLER, CALLVALUE, CODECOPY, CODESIZE, DUP1, DUP2, FIELD_MUL,
    ISZERO, JUMPDEST, JUMPI, KECCAK256, MLOAD, MSTORE, OR, POP, PUSH0, PUSH32, RETURN, REVERT, SHL, SHR, SLOAD, SSTORE,
    STOP, SWAP1, SWAP2, XOR, push, push_usize,
};
use evm_link::{Item, Options, Program};

use crate::record::{Graph, Node};

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
    evm_link::op::word(limbs)
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

/// No tags: this contract's gas is not broken down by phase.
const UNTAGGED: &str = "";

struct Compiler<'a> {
    graph: &'a Graph,
    entry: &'a Entry,
    /// Where calldata holds the arguments: after the selector, if any.
    base: usize,
    /// The output word of [`Word::StoredRoot`], if the seed writes it.
    stored_root: Option<usize>,
    /// Kept in memory: used more than once, and not a constant.
    shared: Vec<bool>,
    done: Vec<bool>,
    /// Stack words evaluating a node takes.
    depth: Vec<u32>,
    items: Vec<(Item, &'static str)>,
    /// For [`evm_link::link`]: a seam after every node.
    seams: bool,
}

impl Compiler<'_> {
    fn code(&mut self, bytes: &[u8]) {
        self.items.push((Item::Code(bytes.to_vec()), UNTAGGED));
    }

    fn item(&mut self, item: Item) {
        self.items.push((item, UNTAGGED));
    }

    /// Push the offset of calldata bytes `offset..offset + len`, which the code then reads.
    fn calldata(&mut self, offset: usize, len: usize) {
        self.item(Item::Calldata { offset, len });
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
            self.item(Item::Load(id));
            return;
        }
        match self.graph.nodes[at] {
            Node::Const(limbs) => self.code(&push(&word(limbs))),
            Node::Statement(k) | Node::Root(k) => {
                let offset = match self.graph.nodes[at] {
                    Node::Root(_) => self.base + COMMITMENT + 32 * (k as usize / 2),
                    _ => self.base + 32 * (k as usize / 2),
                };
                self.calldata(offset, 32);
                self.code(&[CALLDATALOAD]);
                if k % 2 == 0 {
                    self.code(&[&push_usize(128)[..], &[SHR]].concat());
                } else {
                    self.code(&[&push(&[0xff; 16])[..], &[AND]].concat());
                }
            }
            Node::Input(i) => {
                self.calldata(self.base + SCALARS + SCALAR_BYTES * i as usize, 32);
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
                    self.code(&push_usize(64));
                    self.calldata(self.base, 64);
                    self.code(&[&push_usize(48)[..], &[CALLDATACOPY]].concat());
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
                        self.item(Item::Output(k));
                    }
                    self.code(&[&push_usize(32)[..], &[MSTORE]].concat());
                    self.code(&push_usize(64));
                    self.calldata(self.base, 64);
                    self.code(&[&push_usize(64)[..], &[CALLDATACOPY]].concat());
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
            self.item(Item::Store(id));
        }
        if self.seams && !matches!(self.graph.nodes[at], Node::Const(_)) {
            self.item(Item::Seam);
        }
    }
}

/// A contract, and what one call of it executes: its code is straight-line, so every instruction runs once.
#[derive(Clone)]
pub struct Contract {
    /// The code, with no owner ([`creation_code`] writes one at `owner_at`); a driver's, with no parts' addresses.
    pub code: Vec<u8>,
    /// Where the code holds its owner, the word a `PUSH32` pushes, if it reads the circuit's commitment from
    /// storage.
    pub owner_at: Option<usize>,
    pub field_muls: usize,
    pub hashes: usize,
    /// Memory it touches, in words (a driver's: its own).
    pub memory_words: usize,
    /// The parts it `DELEGATECALL`s in order, if it is a driver ([`compile_linked`]), and where its code holds each
    /// one's address (the 20 bytes of a `PUSH20`).
    pub parts: Vec<Vec<u8>>,
    pub part_at: Vec<usize>,
}

impl Contract {
    /// The driver calling its parts at `addresses`: a contract with no parts left to place.
    pub fn calling(&self, addresses: &[[u8; 20]]) -> Contract {
        assert_eq!(addresses.len(), self.parts.len(), "an address a part");
        let mut code = self.code.clone();
        for (&at, address) in self.part_at.iter().zip(addresses) {
            code[at..at + 20].copy_from_slice(address);
        }
        Contract {
            code,
            parts: Vec::new(),
            part_at: Vec::new(),
            ..self.clone()
        }
    }
}

/// The program, and the setIndexRoot tail's maker.
struct Compiled {
    program: Program,
    field_muls: usize,
    hashes: usize,
}

fn program(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry, inputs: usize, linkable: bool) -> Compiled {
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
    let output_nodes = || {
        outputs.iter().filter_map(|word| match word {
            Word::Node(id) => Some(*id),
            _ => None,
        })
    };
    for root in graph.nonzero.iter().chain(&graph.zero).copied().chain(output_nodes()) {
        uses[root as usize] += 1;
    }
    for at in (0..n).rev() {
        if uses[at] > 0 {
            for operand in Compiler::operands(graph.nodes[at]) {
                uses[operand as usize] += 1;
            }
        }
    }
    let mut kept = uses.clone();
    if linkable {
        // An output's node is kept, so that every output is written in the last part, after the last seam.
        output_nodes().for_each(|id| kept[id as usize] += 1);
    }
    let shared: Vec<bool> = (0..n)
        .map(|at| kept[at] > 1 && !matches!(graph.nodes[at], Node::Const(_)))
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
        // Linked, the seed's part is not the outputs': the last part reads the root again (a warm `SLOAD`).
        stored_root: if linkable { None } else { stored_root },
        shared,
        done: vec![false; n],
        depth,
        items: Vec::new(),
        seams: linkable,
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
    compiler.item(Item::OtherIf);
    for &id in &graph.nonzero {
        compiler.eval(id);
        compiler.code(&[ISZERO]);
        compiler.item(Item::FailIf);
    }
    for &id in &graph.zero {
        compiler.eval(id);
        compiler.item(Item::FailIf);
    }
    if linkable {
        for id in output_nodes() {
            if !matches!(graph.nodes[id as usize], Node::Const(_)) && !compiler.done[id as usize] {
                compiler.eval(id);
                compiler.code(&[POP]);
            }
        }
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
            Word::Node(id) => compiler.eval(id),
            Word::Const(bytes) if bytes == [0; 32] => {
                k += 1;
                continue;
            }
            Word::Const(bytes) => compiler.code(&push(&bytes)),
            Word::Calldata(offset) => {
                compiler.calldata(base + offset, 32);
                compiler.code(&[CALLDATALOAD]);
            }
            Word::StoredRoot if compiler.stored_root.is_some() => {
                k += 1;
                continue;
            }
            Word::StoredRoot => {
                let slot = push_usize(INDEX_ROOT_SLOT.into());
                compiler.code(&[&slot[..], &[SLOAD], &reverse_halves()].concat());
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
    if let Some(k) = compiler.stored_root {
        let written = compiler
            .items
            .iter()
            .any(|(item, _)| matches!(item, Item::Output(at) if *at == k));
        assert!(written, "the seed writes the stored root");
    }
    let count = |of: &dyn Fn(Node) -> bool| (0..n).filter(|&at| uses[at] > 0 && of(graph.nodes[at])).count();
    let absorbed = graph.nodes.iter().map(|node| match node {
        Node::Hash(_, _, n) => *n as usize,
        _ => 0,
    });
    Compiled {
        program: Program {
            items: compiler.items,
            data,
            scratch: SEED_SCRATCH.max(32 * (1 + absorbed.max().unwrap_or(0))),
            outputs: outputs.len(),
            ending: match ending {
                Ending::Return => evm_link::Ending::Return,
                Ending::PcsOpen(_) => evm_link::Ending::Attest,
            },
            calldata_len,
        },
        field_muls: count(&|node| matches!(node, Node::Mul(..))),
        hashes: count(&|node| matches!(node, Node::Hash(..) | Node::Seed)),
    }
}

/// `setIndexRoot(bytes32 root)`: revert unless calldata is its selector and `root`, with no value, from the owner;
/// else store `root`. The owner is the word of a `PUSH32`, which the creation code writes.
fn set_index_root(fail: usize) -> (Vec<u8>, Option<usize>) {
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
    (code, Some(owner))
}

fn options(entry: &Entry) -> Options<'static> {
    let other: evm_link::Other<'static> = &set_index_root;
    Options {
        jump_width: 2,
        other: entry.index_root.is_none().then_some(other),
        ..Options::default()
    }
}

/// The contract. A call of the verifier is calldata of the selector ([`VERIFY`], if `entry` has one) and the
/// arguments: the statement, the commitments and `inputs` scalars of the proof, of `SCALAR_BYTES` each. On
/// such a call, with no value, it reverts unless every node of `graph.nonzero` is nonzero and every node of
/// `graph.zero` zero (checked in that order, after the entry's checks), else writes `outputs`
/// to a region of fresh memory, one word each, and ends as `ending` says. Any other call is one of
/// `setIndexRoot(bytes32 root)`, if the circuit's commitment is in storage, or reverts: from the owner, with no
/// value, it stores `root` in slot [`INDEX_ROOT_SLOT`] and returns nothing.
pub fn compile(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry, inputs: usize) -> Contract {
    let compiled = program(graph, outputs, ending, entry, inputs, false);
    let assembled = evm_link::assemble(&compiled.program, &options(entry));
    Contract {
        code: assembled.code,
        owner_at: assembled.other_patch,
        field_muls: compiled.field_muls,
        hashes: compiled.hashes,
        memory_words: assembled.memory_words,
        parts: Vec::new(),
        part_at: Vec::new(),
    }
}

/// The same contract as contracts of at most `limit` bytes of code each ([`evm_link::link`]): the one [`compile`]
/// makes if it fits, else a driver (the entry, `setIndexRoot`, and the program's start) and the parts it calls.
pub fn compile_linked(
    graph: &Graph,
    outputs: &[Word],
    ending: &Ending,
    entry: &Entry,
    inputs: usize,
    limit: usize,
) -> Contract {
    let one = compile(graph, outputs, ending, entry, inputs);
    if one.code.len() <= limit {
        return one;
    }
    let compiled = program(graph, outputs, ending, entry, inputs, true);
    let linked = evm_link::link(&compiled.program, &options(entry), limit);
    Contract {
        code: linked.driver.code.code.clone(),
        owner_at: linked.driver.code.other_patch,
        field_muls: compiled.field_muls,
        hashes: compiled.hashes,
        memory_words: linked.driver.code.memory_words,
        parts: linked.parts.iter().map(|part| part.code.code.clone()).collect(),
        part_at: linked.driver.code.chunk_patches.clone(),
    }
}

/// The creation code of `contract`, which its constructor's arguments follow in the init code: for a contract
/// reading the circuit's commitment from storage, those of `constructor(bytes32 indexRoot, address owner)`,
/// ABI-encoded (64 bytes), and none otherwise. It reverts on value, or on arguments of another length; else it
/// stores `indexRoot` in slot [`INDEX_ROOT_SLOT`], writes the `owner` word into the code, and returns the code.
pub fn creation_code(contract: &Contract) -> Vec<u8> {
    assert!(
        contract.parts.is_empty(),
        "a driver calling its parts at their addresses"
    );
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
            parts: Vec::new(),
            part_at: Vec::new(),
        };
        let mut chain = Chain::default();
        let address = chain.deploy(&creation_code(&contract)).0.expect("a deployment");
        let output = chain.call(address, &[], &PcsOpen::default()).output;
        assert_eq!(output, Some(root_word(&root).to_vec()));
    }

    /// The opcodes and `PCS_OPEN`'s address are the machine's.
    #[test]
    fn opcodes_are_the_machines() {
        assert_eq!(FIELD_MUL, crate::machine::FIELD_MUL);
        assert_eq!(evm_link::op::PCS_OPEN, crate::machine::PCS_OPEN.into_array());
    }
}
