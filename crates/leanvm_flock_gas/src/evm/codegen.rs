// Adapted from this repository's crates/evm/src/codegen.rs (itself adapted from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6): the same compilation of
// a recorded graph to straight-line code, a value used once left on the stack and a shared one kept in a memory slot
// reused after its last read; here for leanVM's verifier: the transcript absorbs runs of calldata, a check is of zero
// or of nonzero, commitments come from calldata or storage, every byte of code carries the phase it computes, and a
// measuring build that never reverts. The compilation and the assembly are now `crates/evm_link`'s (`front`, and
// `assemble` or `link`), this file the code of each node, the entry and the outputs. MIT OR Apache-2.0; see NOTICE.md.
//! A recorded graph as EVM bytecode: one contract ([`compile`]), or contracts that each fit EIP-170's limit
//! ([`compile_deployable`]).

use evm_link::front::{self, Check, Dag, Piece, Source};
pub use evm_link::op::word;
use evm_link::op::{
    AND, CALLDATACOPY, CALLDATALOAD, CALLDATASIZE, CALLVALUE, FIELD_MUL, KECCAK256, MSTORE, OR, PUSH0, SHR, SLOAD, XOR,
    push, push_usize,
};
use evm_link::{Linked, Options, Program, Tags};

use crate::evm::record::{Graph, Node};

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
pub use evm_link::{LINK_CALL, LINK_PASS};

/// EIP-170's limit on a contract's code.
pub const MAX_CODE: usize = 24_576;

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
    /// As [`Ending::PcsOpen`], each call's input written at the region's start just before the call, and only where
    /// the call before left another word (`evm_link::front::Source::reuse`): calls sharing a point write it once.
    PcsOpenReusing(Vec<usize>),
}

/// The graph, with how the contract is seeded: the code of each node.
struct Nodes<'a> {
    graph: &'a Graph,
    entry: &'a Entry,
}

impl Dag for Nodes<'_> {
    fn len(&self) -> usize {
        self.graph.nodes.len()
    }

    fn operands(&self, id: u32) -> Vec<u32> {
        match self.graph.nodes[id as usize] {
            Node::Add(a, b) | Node::Mul(a, b) => vec![a, b],
            Node::Hash(state, _, _) | Node::Low(state) | Node::Narrow(state) | Node::Bits(state, _, _) => vec![state],
            Node::RingWeight(kernel, _) => self.graph.kernels[kernel as usize].clone(),
            _ => vec![],
        }
    }

    fn commutative(&self, id: u32) -> bool {
        matches!(self.graph.nodes[id as usize], Node::Add(..) | Node::Mul(..))
    }

    fn is_const(&self, id: u32) -> bool {
        matches!(self.graph.nodes[id as usize], Node::Const(_))
    }

    fn code(&self, id: u32) -> Vec<Piece> {
        let bytes = |bytes: &[&[u8]]| Piece::Code(bytes.concat());
        let read = |offset: usize, len: usize| Piece::Calldata { offset, len };
        match self.graph.nodes[id as usize] {
            Node::Const(limbs) => front::code(push(&word(limbs))),
            Node::Statement(k) => vec![
                read(PUBLIC_INPUT + 8 * k as usize, 32),
                bytes(&[&[CALLDATALOAD], &push_usize(192), &[SHR]]),
            ],
            Node::Input { offset, len } => vec![
                read(STREAM + offset as usize, 32),
                bytes(&[&[CALLDATALOAD], &push_usize(256 - 8 * len as usize), &[SHR]]),
            ],
            Node::Add(..) => front::code(vec![XOR]),
            Node::Mul(..) => front::code(vec![FIELD_MUL]),
            // The name and the IV, as two overlapping words at 0 and 16, then the public input at 48.
            Node::Seed => {
                let head = [&self.entry.name[..], &self.entry.iv[..16]].concat();
                vec![
                    bytes(&[
                        &push(&head),
                        &[PUSH0, MSTORE],
                        &push(&self.entry.iv),
                        &push_usize(16),
                        &[MSTORE],
                        &push_usize(32),
                    ]),
                    read(PUBLIC_INPUT, 32),
                    bytes(&[&push_usize(48), &[CALLDATACOPY], &push_usize(80), &[PUSH0, KECCAK256]]),
                ]
            }
            // The state (evaluated first: its evaluation may hash too) at 0, then the stream's bytes.
            Node::Hash(_, from, to) => {
                let len = (to - from) as usize;
                let mut code = vec![bytes(&[&[PUSH0, MSTORE]])];
                if len > 0 {
                    code.extend([
                        bytes(&[&push_usize(len)]),
                        read(STREAM + from as usize, len),
                        bytes(&[&push_usize(32), &[CALLDATACOPY]]),
                    ]);
                }
                code.push(bytes(&[&push_usize(32 + len), &[PUSH0, KECCAK256]]));
                code
            }
            Node::Low(_) => front::code([&push(&[0xff; 24])[..], &[AND]].concat()),
            Node::Narrow(_) => front::code([&push(&[0xff; 20])[..], &[AND]].concat()),
            Node::RingWeight(_, n) => front::code(crate::evm::kernel::ring_weight_code(n as usize)),
            Node::Bits(_, shift, width) => {
                let mut code = Vec::new();
                if shift > 0 {
                    code.extend(push_usize(shift as usize));
                    code.push(SHR);
                }
                if width < 64 {
                    code.extend(push_usize((1usize << width) - 1));
                    code.push(AND);
                }
                front::code(code)
            }
        }
    }

    fn tag(&self, id: u32) -> Option<&'static str> {
        (!self.is_const(id)).then(|| self.graph.phases[id as usize])
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

/// The same program as contracts that each fit ([`evm_link::link`]): a driver, which a verifying call is sent to,
/// and the parts it `DELEGATECALL`s.
pub struct Deployable {
    pub linked: Linked,
    pub calldata_len: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    pub hashed_bytes: usize,
    /// The program's checks, its entry's included: one `JUMPDEST` each in a measuring build, and one a part's call.
    pub checks: usize,
}

/// The program, and what it computes.
fn program(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry, linkable: bool) -> (Program, Stats) {
    let calldata_len = STREAM + entry.stream_len;
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
    let words = outputs
        .iter()
        .map(|word| match *word {
            Word::Node(id) => front::Word::Node(id),
            Word::Const(bytes) => front::Word::Const(bytes),
            Word::Stream(offset) => front::Word::Code(
                vec![
                    Piece::Calldata {
                        offset: STREAM + offset,
                        len: 32,
                    },
                    Piece::Code(vec![CALLDATALOAD]),
                ],
                CALLS,
            ),
            Word::Stored(slot) => {
                front::Word::Code(front::code([&push_usize(slot.into())[..], &[SLOAD]].concat()), ROOTS)
            }
        })
        .collect();
    // Below the slots: the hashing scratch, a state and the longest run of the stream absorbed (and the seed's 80).
    let absorbed = graph.nodes.iter().map(|node| match node {
        Node::Hash(_, from, to) => (to - from) as usize,
        _ => 0,
    });
    let scratch = (32 + absorbed.max().unwrap_or(0)).max(80).next_multiple_of(32);
    // A ring-weight kernel's words, from 0 (the hashing's scratch is free between nodes).
    let kernels = graph.nodes.iter().map(|node| match node {
        Node::RingWeight(_, n) => 32 * crate::evm::kernel::scratch_words(*n as usize),
        _ => 0,
    });
    let scratch = scratch.max(kernels.max().unwrap_or(0));
    let checks = graph.zero.iter().map(|&(id, _)| (id, Check::Zero));
    let source = Source {
        dag: &Nodes { graph, entry },
        entry: selector.concat(),
        entry_tag: ENTRY,
        checks: checks
            .chain(graph.nonzero.iter().map(|&(id, _)| (id, Check::Nonzero)))
            .collect(),
        outputs: words,
        calls: match ending {
            Ending::Return => None,
            Ending::PcsOpen(runs) | Ending::PcsOpenReusing(runs) => Some(runs.clone()),
        },
        reuse: matches!(ending, Ending::PcsOpenReusing(_)),
        calls_tag: CALLS,
        scratch,
        calldata_len,
        linkable,
    };
    let compiled = front::compile(&source);
    let n = graph.nodes.len();
    let used = |at: usize| compiled.uses[at] > 0;
    let count = |of: &dyn Fn(Node) -> bool| (0..n).filter(|&at| used(at) && of(graph.nodes[at])).count();
    let stats = Stats {
        calldata_len,
        field_muls: count(&|node| matches!(node, Node::Mul(..))),
        xors: count(&|node| matches!(node, Node::Add(..))),
        hashes: count(&|node| matches!(node, Node::Hash(..) | Node::Seed)),
        hashed_bytes: (0..n)
            .filter(|&at| used(at))
            .map(|at| match graph.nodes[at] {
                Node::Hash(_, from, to) => 32 + (to - from) as usize,
                Node::Seed => 80,
                _ => 0,
            })
            .sum(),
        checks: graph.zero.len() + graph.nonzero.len() + 1,
    };
    (compiled.program, stats)
}

struct Stats {
    calldata_len: usize,
    field_muls: usize,
    xors: usize,
    hashes: usize,
    hashed_bytes: usize,
    checks: usize,
}

fn options(measure: bool, jump_width: usize) -> Options<'static> {
    Options {
        jump_width,
        measure,
        other: None,
        tags: Tags {
            measure: MEASURE,
            ending: CALLS,
            tail: ENTRY,
            call: LINK_CALL,
            pass: LINK_PASS,
        },
    }
}

/// The contract. A call of it is calldata of the selector, the public input and `entry.stream_len` bytes of stream,
/// with no value. It reverts unless every node of `graph.zero` is zero and every one of `graph.nonzero` nonzero, else
/// writes `outputs` to a region of fresh memory, one word each, and ends as `ending` says.
pub fn compile(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry) -> Contract {
    let (program, stats) = program(graph, outputs, ending, entry, false);
    let assembled = evm_link::assemble(&program, &options(entry.measure, 3));
    Contract {
        code: assembled.code,
        phase_of: assembled.tags,
        calldata_len: stats.calldata_len,
        field_muls: stats.field_muls,
        xors: stats.xors,
        hashes: stats.hashes,
        hashed_bytes: stats.hashed_bytes,
        checks: stats.checks,
        memory_words: assembled.memory_words,
    }
}

/// The same contract, as contracts of at most `limit` bytes of code each: the one contract [`compile`] makes if it
/// fits, else a driver and parts.
pub fn compile_deployable(graph: &Graph, outputs: &[Word], ending: &Ending, entry: &Entry, limit: usize) -> Deployable {
    let (plain, stats) = program(graph, outputs, ending, entry, false);
    let one = evm_link::assemble(&plain, &options(entry.measure, 3));
    let linked = if one.code.len() <= limit {
        evm_link::link(&plain, &options(entry.measure, 3), limit)
    } else {
        // Every part is under 64 KB: two bytes a jump.
        let (program, _) = program(graph, outputs, ending, entry, true);
        evm_link::link(&program, &options(entry.measure, 2), limit)
    };
    deployable(linked, stats)
}

/// The same contracts cut where `like`'s are (the same program, built as `entry` says): a measuring build of `like`,
/// whose gas is `like`'s and one a check.
pub fn compile_deployable_like(
    graph: &Graph,
    outputs: &[Word],
    ending: &Ending,
    entry: &Entry,
    like: &Deployable,
) -> Deployable {
    let starts = like.linked.starts();
    let (plain, stats) = program(graph, outputs, ending, entry, false);
    let linked = if starts.is_empty() {
        evm_link::link_at(&plain, &options(entry.measure, 3), &[])
    } else {
        let (program, _) = program(graph, outputs, ending, entry, true);
        evm_link::link_at(&program, &options(entry.measure, 2), &starts)
    };
    deployable(linked, stats)
}

fn deployable(linked: Linked, stats: Stats) -> Deployable {
    Deployable {
        linked,
        calldata_len: stats.calldata_len,
        field_muls: stats.field_muls,
        xors: stats.xors,
        hashes: stats.hashes,
        hashed_bytes: stats.hashed_bytes,
        checks: stats.checks,
    }
}
