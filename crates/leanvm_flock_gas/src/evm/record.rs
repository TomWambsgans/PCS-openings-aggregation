// Adapted from this repository's crates/evm/src/record.rs and crates/evm/src/contract.rs (themselves adapted from
// leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6): the recording
// scalar and the recording channel, here for leanVM's verifier: inputs at byte offsets of the stream, a hash of a
// run of the stream's bytes, checks of zero and of nonzero, and a phase for every node. MIT OR Apache-2.0; see NOTICE.md.
//! A scalar that records the operations done on it, as a graph with shared subterms, and the channel that records
//! the proof's reads and the transcript's challenges.

use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::{Add, AddAssign, Mul, MulAssign};

use crate::VerifierError;
use crate::field::{E, ONE, ZERO};
use crate::scalar::{Scalar, phase};
use crate::transcript::Channel;

/// One recorded value. Operands are indices of earlier nodes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Node {
    Const([u64; 3]),
    /// Word `k` of the public input, a 64-bit number.
    Statement(u8),
    /// The scalar at byte `offset` of the stream, `len` bytes big-endian (24, or 16 for a root's half).
    Input {
        offset: u32,
        len: u8,
    },
    Add(u32, u32),
    Mul(u32, u32),
    /// The transcript's seed: the hash of the name, the program's IV and the public input.
    Seed,
    /// The transcript's step: the hash of a state and of the stream's bytes `from..to`.
    Hash(u32, u32, u32),
    /// The low 192 bits of a state: a challenge.
    Low(u32),
    /// `(v >> shift) mod 2^width` of an integer `v` (an [`Node::Input`] of at most 8 bytes, or bits of one).
    Bits(u32, u8, u8),
}

#[derive(Default)]
pub struct Graph {
    pub nodes: Vec<Node>,
    /// The phase each node was created in.
    pub phases: Vec<&'static str>,
    index: HashMap<Node, u32>,
    /// The values the verifier requires to be zero, then to be nonzero, with what it reports if one is not.
    pub zero: Vec<(u32, VerifierError)>,
    pub nonzero: Vec<(u32, VerifierError)>,
}

thread_local! {
    static GRAPH: RefCell<Graph> = RefCell::default();
}

/// Record what `f` computes.
pub fn record<R>(f: impl FnOnce() -> R) -> (R, Graph) {
    GRAPH.take();
    let result = f();
    (result, GRAPH.take())
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sym(pub u32);

fn constant_of(node: Node) -> Option<E> {
    match node {
        Node::Const([c0, c1, c2]) => Some(E::new(c0, c1, c2)),
        _ => None,
    }
}

impl Sym {
    pub fn new(node: Node) -> Self {
        GRAPH.with_borrow_mut(|graph| {
            let next = graph.nodes.len() as u32;
            let id = *graph.index.entry(node).or_insert(next);
            if id == next {
                graph.nodes.push(node);
                graph.phases.push(phase());
            }
            Self(id)
        })
    }

    fn node(self) -> Node {
        GRAPH.with_borrow(|graph| graph.nodes[self.0 as usize])
    }

    fn value(self) -> Option<E> {
        constant_of(self.node())
    }
}

impl Add for Sym {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        match (self.value(), rhs.value()) {
            (Some(a), Some(b)) => Self::constant(a + b),
            (Some(ZERO), _) => rhs,
            (_, Some(ZERO)) => self,
            _ if self == rhs => Self::constant(ZERO),
            _ => Self::new(Node::Add(self.0.min(rhs.0), self.0.max(rhs.0))),
        }
    }
}

impl Mul for Sym {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        match (self.value(), rhs.value()) {
            (Some(a), Some(b)) => Self::constant(a * b),
            (Some(ZERO), _) | (_, Some(ZERO)) => Self::constant(ZERO),
            (Some(ONE), _) => rhs,
            (_, Some(ONE)) => self,
            _ => Self::new(Node::Mul(self.0.min(rhs.0), self.0.max(rhs.0))),
        }
    }
}

impl AddAssign for Sym {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl MulAssign for Sym {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Scalar for Sym {
    fn constant(value: E) -> Self {
        Self::new(Node::Const([value.c0, value.c1, value.c2]))
    }

    fn bits(self, shift: usize, width: usize) -> Self {
        match self.value() {
            Some(v) => Self::constant(v.bits(shift, width)),
            None => Self::new(Node::Bits(self.0, shift as u8, width.min(255) as u8)),
        }
    }
}

/// The proof as the recorder reads it: every read and every challenge is a node of the graph the contract is
/// compiled from. Its stream is the contract's: 24 bytes a scalar, 16 a root's half.
pub struct Recorder {
    state: Sym,
    /// Bytes of the stream read, and absorbed by a challenge.
    pub cursor: u32,
    absorbed: u32,
    /// Where each root starts in the stream.
    pub roots: Vec<u32>,
    /// The stream's bytes, by the phase that reads them.
    pub reads: Vec<(&'static str, u32)>,
}

impl Recorder {
    pub fn new() -> Self {
        let _phase = crate::scalar::enter(TRANSCRIPT);
        Self {
            state: Sym::new(Node::Seed),
            cursor: 0,
            absorbed: 0,
            roots: Vec::new(),
            reads: Vec::new(),
        }
    }

    pub fn statement() -> [Sym; 4] {
        let _phase = crate::scalar::enter(CALLDATA);
        std::array::from_fn(|k| Sym::new(Node::Statement(k as u8)))
    }

    fn input(&mut self, len: u8) -> Sym {
        let reader = crate::scalar::phase();
        match self.reads.iter_mut().find(|(phase, _)| *phase == reader) {
            Some((_, bytes)) => *bytes += len as u32,
            None => self.reads.push((reader, len as u32)),
        }
        let _phase = crate::scalar::enter(CALLDATA);
        let scalar = Sym::new(Node::Input {
            offset: self.cursor,
            len,
        });
        self.cursor += len as u32;
        scalar
    }
}

impl Default for Recorder {
    fn default() -> Self {
        Self::new()
    }
}

/// The phase of the transcript's nodes, and of the proof's reads.
pub const TRANSCRIPT: &str = "transcript (Keccak-256 chain)";
pub const CALLDATA: &str = "calldata reads";

impl Channel<Sym> for Recorder {
    fn next_scalar(&mut self) -> Result<Sym, VerifierError> {
        Ok(self.input(24))
    }

    fn next_root(&mut self) -> Result<[Sym; 2], VerifierError> {
        self.roots.push(self.cursor);
        Ok([self.input(16), self.input(16)])
    }

    fn sample(&mut self) -> Sym {
        let _phase = crate::scalar::enter(TRANSCRIPT);
        self.state = Sym::new(Node::Hash(self.state.0, self.absorbed, self.cursor));
        self.absorbed = self.cursor;
        Sym::new(Node::Low(self.state.0))
    }

    fn require_zero(&mut self, value: Sym, error: VerifierError) -> Result<(), VerifierError> {
        GRAPH.with_borrow_mut(|graph| graph.zero.push((value.0, error)));
        Ok(())
    }

    fn require_nonzero(&mut self, value: Sym, error: VerifierError) -> Result<(), VerifierError> {
        GRAPH.with_borrow_mut(|graph| graph.nonzero.push((value.0, error)));
        Ok(())
    }

    fn next_integer(&mut self, bytes: usize) -> Result<Sym, VerifierError> {
        assert!((1..=8).contains(&bytes));
        Ok(self.input(bytes as u8))
    }
}
