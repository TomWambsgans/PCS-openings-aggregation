// Part of this repository. The node semantics are those of `leanvm_flock_gas::evm::record` and of the Keccak-256
// chain `leanvm_flock_gas::transcript::KeccakChannel` (adapted there from leanVM 42422001's transcript). MIT OR
// Apache-2.0; see NOTICE.md.
//! The inner verifier's graph evaluated on a real proof: every node's value, as `π2`'s witness generator needs it
//! (SPEC-REC.md §6, R2). A challenge's hash node holds the 32-byte Keccak state, every other node an element of `E`.

use leanvm_flock_gas::evm::codegen::Word;
use leanvm_flock_gas::evm::machine::element_word;
use leanvm_flock_gas::evm::record::{Graph, Node};
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::ring_tower;
use leanvm_flock_gas::scalar::Scalar;
use leanvm_flock_gas::transcript::{challenge_of, keccak256};
use leanvm_univariate::contract::{Recorded, calls};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value {
    E(E),
    State([u8; 32]),
}

impl Value {
    pub fn e(self) -> E {
        match self {
            Value::E(x) => x,
            Value::State(_) => panic!("a Keccak state, not an element"),
        }
    }

    fn state(self) -> [u8; 32] {
        match self {
            Value::State(s) => s,
            Value::E(_) => panic!("an element, not a Keccak state"),
        }
    }
}

fn be(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0u64, |acc, &b| acc << 8 | b as u64)
}

/// Every node's value, for the transcript seeded by `seed`, the public input's 32 bytes and the stream. Nodes are in
/// creation order, so every operand comes before its node.
pub fn evaluate(graph: &Graph, seed: [u8; 32], public: &[u8; 32], stream: &[u8]) -> Vec<Value> {
    let mut values: Vec<Value> = Vec::with_capacity(graph.nodes.len());
    for node in &graph.nodes {
        let e = |id: u32| values[id as usize].e();
        let value = match *node {
            Node::Const([c0, c1, c2]) => Value::E(E::new(c0, c1, c2)),
            Node::Statement(k) => Value::E(E::new(be(&public[8 * k as usize..8 * k as usize + 8]), 0, 0)),
            Node::Input { offset, len } => {
                let bytes = &stream[offset as usize..offset as usize + len as usize];
                Value::E(match len {
                    24 => E::new(be(&bytes[16..24]), be(&bytes[8..16]), be(&bytes[0..8])),
                    16 => E::new(be(&bytes[8..16]), be(&bytes[0..8]), 0),
                    _ => E::new(be(bytes), 0, 0),
                })
            }
            Node::Add(a, b) => Value::E(e(a) + e(b)),
            Node::Mul(a, b) => Value::E(e(a) * e(b)),
            Node::Seed => Value::State(seed),
            Node::Hash(s, from, to) => {
                let input = [&values[s as usize].state()[..], &stream[from as usize..to as usize]].concat();
                Value::State(keccak256(&input))
            }
            Node::Low(h) => Value::E(challenge_of(&values[h as usize].state())),
            Node::Bits(v, shift, width) => Value::E(<E as Scalar>::bits(e(v), shift as usize, width as usize)),
            Node::RingWeight(k, n) => {
                let ops: Vec<E> = graph.kernels[k as usize].iter().map(|&id| e(id)).collect();
                let n = n as usize;
                Value::E(ring_tower::weight_at(&ops[..n], &ops[n..2 * n], &ops[2 * n..]))
            }
        };
        values.push(value);
    }
    values
}

/// The `PCS_OPEN` calls' input bytes, as the contract writes them, from the evaluated graph.
pub fn call_inputs(recorded: &Recorded, values: &[Value], stream: &[u8]) -> Vec<Vec<u8>> {
    calls(recorded)
        .iter()
        .map(|words| {
            words
                .iter()
                .flat_map(|w| match w {
                    Word::Node(id) => element_word(values[*id as usize].e()),
                    Word::Const(bytes) => *bytes,
                    Word::Stream(at) => stream[*at..*at + 32].try_into().expect("a root"),
                    Word::Stored(_) => panic!("no stored words: the setup roots are code constants"),
                })
                .collect()
        })
        .collect()
}

/// The checks' values: those required zero, then those required nonzero.
pub fn checks(graph: &Graph, values: &[Value]) -> (Vec<E>, Vec<E>) {
    let of =
        |list: &[(u32, leanvm_flock_gas::VerifierError)]| list.iter().map(|&(id, _)| values[id as usize].e()).collect();
    (of(&graph.zero), of(&graph.nonzero))
}
