// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The inner verifier's graph, counted: what `π2`'s circuit must hold (SPEC-REC.md §1).
//!
//! Only **live** nodes count: those the `PCS_OPEN` calls' words or the checks read, through their operands (a hash
//! reads the state before it, a challenge its hash, the ring switch's kernel its operands). The recorder shares equal
//! subterms (one node per distinct operation), so the counts are of distinct operations, as a circuit computes them.

use std::collections::{BTreeMap, BTreeSet};

use leanvm_flock_gas::evm::codegen::Word;
use leanvm_flock_gas::evm::record::{Graph, Node, Sym, record};
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::ring_tower;
use leanvm_univariate::Opening;
use leanvm_univariate::contract::{Recorded, calls};

/// The operations of a graph, by kind.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ops {
    pub adds: usize,
    /// Additions of a constant.
    pub add_const: usize,
    /// Products of two distinct non-constant values.
    pub muls: usize,
    /// `x · x`.
    pub squares: usize,
    /// Products by a constant.
    pub mul_const: usize,
}

impl Ops {
    pub fn products(&self) -> usize {
        self.muls + self.squares
    }

    pub fn linear(&self) -> usize {
        self.adds + self.add_const + self.mul_const
    }

    fn add(&mut self, other: &Ops, times: usize) {
        self.adds += times * other.adds;
        self.add_const += times * other.add_const;
        self.muls += times * other.muls;
        self.squares += times * other.squares;
        self.mul_const += times * other.mul_const;
    }
}

/// One claim the inner verifier hands `PCS_OPEN`: its commitment, its point's nodes and its value's node.
#[derive(Clone, Debug)]
pub struct ClaimShape {
    pub name: String,
    pub point: Vec<u32>,
    pub value: u32,
}

#[derive(Clone, Debug, Default)]
pub struct Counts {
    pub nodes: usize,
    pub live: usize,
    /// Live constants (distinct values).
    pub consts: usize,
    /// The public input's words read.
    pub statement: usize,
    /// Live reads of the stream: scalars (24 bytes), root halves (16), integers (at most 8).
    pub scalars: usize,
    pub halves: usize,
    pub integers: usize,
    /// Bytes of the stream, and those of them some challenge's hash absorbs.
    pub stream_bytes: usize,
    pub hashed_stream_bytes: usize,
    /// The stream's reads that are live (read by arithmetic), and those of them past the last hash (never hashed).
    pub unhashed_live_reads: usize,
    pub ops: Ops,
    /// The ring switch's kernels, and the operations of all of them (expanded, `ring_tower::weight_at`).
    pub kernels: usize,
    pub kernel_ops: Ops,
    /// `ops` with every kernel expanded.
    pub total_ops: Ops,
    /// Bit fields of the row counts (`Node::Bits`).
    pub bits: usize,
    /// Keccak-256 calls (the seed's included), each call's input length, and Keccak-f\[1600\] permutations.
    pub hash_lengths: Vec<usize>,
    pub permutations: usize,
    /// Challenges (`Node::Low`).
    pub challenges: usize,
    pub zero_checks: usize,
    pub nonzero_checks: usize,
    pub claims: Vec<ClaimShape>,
}

impl Counts {
    /// Distinct points, by their coordinates' nodes; and the distinct non-constant coordinates over all claims.
    pub fn distinct_points(&self) -> usize {
        self.claims
            .iter()
            .map(|c| c.point.clone())
            .collect::<BTreeSet<_>>()
            .len()
    }

    pub fn coordinates(&self) -> usize {
        self.claims.iter().map(|c| c.point.len()).sum()
    }

    pub fn distinct_coordinates(&self, graph: &Graph) -> usize {
        self.claims
            .iter()
            .flat_map(|c| c.point.iter().copied())
            .filter(|&id| !matches!(graph.nodes[id as usize], Node::Const(_)))
            .collect::<BTreeSet<_>>()
            .len()
    }

    /// Hash calls by their permutations.
    pub fn hashes_by_permutations(&self) -> BTreeMap<usize, usize> {
        let mut out = BTreeMap::new();
        for &len in &self.hash_lengths {
            *out.entry(crate::permutations(len)).or_insert(0) += 1;
        }
        out
    }
}

fn operands(graph: &Graph, node: Node) -> Vec<u32> {
    match node {
        Node::Add(a, b) | Node::Mul(a, b) => vec![a, b],
        Node::Hash(s, _, _) => vec![s],
        Node::Low(h) | Node::Bits(h, _, _) => vec![h],
        Node::RingWeight(k, _) => graph.kernels[k as usize].clone(),
        Node::Const(_) | Node::Statement(_) | Node::Input { .. } | Node::Seed => vec![],
    }
}

/// The nodes `outputs` read, through their operands.
pub fn live(graph: &Graph, outputs: impl IntoIterator<Item = u32>) -> Vec<bool> {
    let mut live = vec![false; graph.nodes.len()];
    let mut stack: Vec<u32> = outputs.into_iter().collect();
    while let Some(id) = stack.pop() {
        if std::mem::replace(&mut live[id as usize], true) {
            continue;
        }
        stack.extend(operands(graph, graph.nodes[id as usize]));
    }
    live
}

/// The graph's outputs: every node a call of `PCS_OPEN` writes, and every checked value.
pub fn outputs(recorded: &Recorded) -> Vec<u32> {
    let graph = &recorded.graph;
    let words = calls(recorded).concat();
    words
        .iter()
        .filter_map(|w| match w {
            Word::Node(id) => Some(*id),
            _ => None,
        })
        .chain(graph.zero.iter().chain(&graph.nonzero).map(|&(id, _)| id))
        .collect()
}

fn ops_of(graph: &Graph, live: &[bool]) -> Ops {
    let is_const = |id: u32| matches!(graph.nodes[id as usize], Node::Const(_));
    let mut ops = Ops::default();
    for (id, node) in graph.nodes.iter().enumerate() {
        if !live[id] {
            continue;
        }
        match *node {
            Node::Add(a, b) if is_const(a) || is_const(b) => ops.add_const += 1,
            Node::Add(..) => ops.adds += 1,
            Node::Mul(a, b) if a == b => ops.squares += 1,
            Node::Mul(a, b) if is_const(a) || is_const(b) => ops.mul_const += 1,
            Node::Mul(..) => ops.muls += 1,
            _ => {}
        }
    }
    ops
}

/// The operations of one ring-switch kernel of `n` coordinates, expanded: `ring_tower::weight_at` recorded on fresh
/// inputs (its point, `1 + r`, the map's six stages).
pub fn kernel_ops(n: usize) -> Ops {
    let (out, graph) = record(|| {
        let fresh = |k: usize| {
            Sym::new(Node::Input {
                offset: k as u32,
                len: 24,
            })
        };
        let point: Vec<Sym> = (0..n).map(fresh).collect();
        let one_plus_r: Vec<Sym> = (n..2 * n).map(fresh).collect();
        let map: Vec<Sym> = (2 * n..2 * n + ring_tower::STAGES).map(fresh).collect();
        ring_tower::weight_at(&point, &one_plus_r, &map)
    });
    let live = live(&graph, [out.0]);
    ops_of(&graph, &live)
}

/// Count `recorded`'s live graph.
pub fn count(recorded: &Recorded) -> Counts {
    let graph = &recorded.graph;
    let live = live(graph, outputs(recorded));
    let mut c = Counts {
        nodes: graph.nodes.len(),
        live: live.iter().filter(|&&l| l).count(),
        stream_bytes: recorded.stream_len,
        ..Counts::default()
    };
    let mut hashed_to = 0u32;
    let mut reads: Vec<u32> = Vec::new();
    for (id, node) in graph.nodes.iter().enumerate() {
        if let Node::Hash(_, _, to) = *node {
            hashed_to = hashed_to.max(to);
        }
        if !live[id] {
            continue;
        }
        match *node {
            Node::Const(_) => c.consts += 1,
            Node::Statement(_) => c.statement += 1,
            Node::Input { offset, len } => {
                match len {
                    24 => c.scalars += 1,
                    16 => c.halves += 1,
                    _ => c.integers += 1,
                }
                reads.push(offset);
            }
            Node::Seed => c.hash_lengths.push(16 + 32 + 32),
            Node::Hash(_, from, to) => c.hash_lengths.push(32 + (to - from) as usize),
            Node::Low(_) => c.challenges += 1,
            Node::Bits(..) => c.bits += 1,
            Node::RingWeight(_, n) => {
                c.kernels += 1;
                c.kernel_ops.add(&kernel_ops(n as usize), 1);
            }
            _ => {}
        }
    }
    c.hashed_stream_bytes = hashed_to as usize;
    c.unhashed_live_reads = reads.iter().filter(|&&offset| offset >= hashed_to).count();
    c.permutations = c.hash_lengths.iter().map(|&len| crate::permutations(len)).sum();
    c.ops = ops_of(graph, &live);
    c.total_ops = c.ops.clone();
    let kernel = c.kernel_ops.clone();
    c.total_ops.add(&kernel, 1);
    c.zero_checks = graph.zero.len();
    c.nonzero_checks = graph.nonzero.len();
    for (commitment, opening) in &recorded.reduced.openings {
        if let Opening::Point { point, value, .. } = opening {
            c.claims.push(ClaimShape {
                name: format!("{commitment:?}"),
                point: point.iter().map(|s| s.0).collect(),
                value: value.0,
            });
        }
    }
    if let Some(m) = &recorded.reduced.matrices {
        for (name, value) in [("A0", m.a), ("B0", m.b)] {
            c.claims.push(ClaimShape {
                name: name.to_string(),
                point: m.point.iter().map(|s| s.0).collect(),
                value: value.0,
            });
        }
    }
    c
}

/// The coordinates two points share, position by position, and the coordinates of `b` found anywhere in `a`.
pub fn shared(a: &[u32], b: &[u32]) -> (usize, usize) {
    let same = a.iter().zip(b).take_while(|(x, y)| x == y).count();
    let anywhere = b.iter().filter(|y| a.contains(y)).count();
    (same, anywhere)
}

/// A constant node's value, if it is one.
pub fn constant(graph: &Graph, id: u32) -> Option<E> {
    match graph.nodes[id as usize] {
        Node::Const([c0, c1, c2]) => Some(E::new(c0, c1, c2)),
        _ => None,
    }
}
