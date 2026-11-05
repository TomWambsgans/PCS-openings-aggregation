// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/record.rs. MIT OR Apache-2.0; see NOTICE.md.
//! A scalar that records the operations done on it, as a graph with shared subterms.

use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::{Add, Mul};

use primitives::field::F192;
use quotient::protocol::Scalar;

/// The most scalars a transcript step absorbs: the five values and the hint (`quotient::protocol::Inverse::Hint`).
/// Only the first `n` of a [`Node::Hash`]'s slots are its operands (the rest zero), so the bound changes no graph.
pub const MAX_ABSORBED: usize = 6;

/// One recorded value. Operands are indices of earlier nodes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Node {
    Const([u64; 3]),
    /// A half of `y` (0, 1) or of `root` (2, 3).
    Statement(u8),
    /// A scalar of a commitment: two a commitment, in the order they are sent.
    Root(u8),
    /// A scalar of the proof.
    Input(u16),
    Add(u32, u32),
    Mul(u32, u32),
    Frobenius(u32),
    /// The transcript's seed: the hash of the label.
    Seed,
    /// The transcript's step: the hash of a state and of the first `n` of these scalars.
    Hash(u32, [u32; MAX_ABSORBED], u8),
    /// The low 192 bits of a state: a challenge.
    Low(u32),
}

#[derive(Default)]
pub struct Graph {
    pub nodes: Vec<Node>,
    index: HashMap<Node, u32>,
    /// The values the verifier requires to be nonzero.
    pub nonzero: Vec<u32>,
    /// The values the verifier requires to be zero: none in the membership protocol, the hint's check in
    /// `quotient::protocol::Inverse::Hint`.
    pub zero: Vec<u32>,
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

fn constant_of(node: Node) -> Option<F192> {
    match node {
        Node::Const([c0, c1, c2]) => Some(F192::new(c0, c1, c2)),
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
            }
            Self(id)
        })
    }

    fn node(self) -> Node {
        GRAPH.with_borrow(|graph| graph.nodes[self.0 as usize])
    }

    fn value(self) -> Option<F192> {
        constant_of(self.node())
    }
}

impl Add for Sym {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        match (self.value(), rhs.value()) {
            (Some(a), Some(b)) => Self::constant(a + b),
            (Some(F192::ZERO), _) => rhs,
            (_, Some(F192::ZERO)) => self,
            _ if self == rhs => Self::constant(F192::ZERO),
            _ => Self::new(Node::Add(self.0.min(rhs.0), self.0.max(rhs.0))),
        }
    }
}

impl Mul for Sym {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        match (self.value(), rhs.value()) {
            (Some(a), Some(b)) => Self::constant(a * b),
            (Some(F192::ZERO), _) | (_, Some(F192::ZERO)) => Self::constant(F192::ZERO),
            (Some(F192::ONE), _) => rhs,
            (_, Some(F192::ONE)) => self,
            _ => Self::new(Node::Mul(self.0.min(rhs.0), self.0.max(rhs.0))),
        }
    }
}

impl Scalar for Sym {
    fn constant(value: F192) -> Self {
        Self::new(Node::Const([value.c0, value.c1, value.c2]))
    }

    fn frobenius(self) -> Self {
        match self.value() {
            Some(value) => Self::constant(value.frobenius()),
            None => Self::new(Node::Frobenius(self.0)),
        }
    }

    fn is_nonzero(self) -> bool {
        GRAPH.with_borrow_mut(|graph| graph.nonzero.push(self.0));
        true
    }

    fn is_zero(self) -> bool {
        assert!(
            self.value().is_none_or(|value| value == F192::ZERO),
            "a constant required zero is zero"
        );
        GRAPH.with_borrow_mut(|graph| graph.zero.push(self.0));
        true
    }
}
