// Part of this repository. The node semantics are those of `leanvm_flock_gas::evm::record` and of
// `leanvm_flock_gas::transcript::KeccakChannel` (as in `crate::eval`). MIT OR Apache-2.0; see NOTICE.md.
//! The compiler from `π1`'s recorded verifier ([`Recorded`]) to `π2`'s circuit, and its witness (SPEC-REC.md §7 R2,
//! steps 4–5):
//!
//! - the graph is first **expanded**: replayed on the recorder's symbol with the ring switch's kernel computed
//!   (`ring_tower::weight_at`), so every node is a read, a hash, a challenge, a bit field, a constant, a sum or a
//!   product;
//! - `Seed` and `Hash` → Keccak-256 calls ([`super::keccak::Sponge`]): the seed hashes the name, the contract's IV
//!   (constants) and the public input's bits; a hash, the state's 256 digest bits and the stream's bits `from..to`;
//! - the stream's hashed bytes and the public input are **free bits**; a bit in a first block (it ends at the
//!   permutation's input slot) has a copy;
//! - `Input` (24-byte scalars, 4-byte integers), `Low`, `Statement`, `Bits` → **packings** of their bits into `K`
//!   limbs; reads never hashed are free limbs;
//! - `Add`, `Mul` → `E` units on limbs (a product, a square, a sum), constants → `κ` slots;
//! - the calls' elements, `π1`'s roots, the statement, and the zero checks → **ports** (`spec::Source`).
//!
//! The witness is the framework's: the free bits and limbs given, everything else computed by the formulas.

use std::collections::BTreeMap;

use leanvm_flock_gas::evm::codegen::Word;
use leanvm_flock_gas::evm::record::{Graph, Node, Sym, record};
use leanvm_flock_gas::field::{E, K};
use leanvm_flock_gas::ring_tower;
use leanvm_flock_gas::scalar::Scalar;
use leanvm_univariate::contract::{NAME, Recorded, calls};

use super::keccak::{Bit, Constants, Permutation, Sponge};
use super::layout::{Builder, Finished, Value};
use super::spec::{CallWord, PublicInputs, Source};
use super::units::{Arith, Bools, Limbs, Op, Packer, Ports};

/// The graph replayed with every ring-switch kernel expanded, and each original node's image.
pub fn expand(graph: &Graph) -> (Graph, Vec<u32>) {
    let (map, expanded) = record(|| {
        let mut map: Vec<Sym> = Vec::with_capacity(graph.nodes.len());
        for node in &graph.nodes {
            let m = |id: u32| map[id as usize];
            let s = match *node {
                Node::Const([a, b, c]) => Sym::constant(E::new(a, b, c)),
                Node::Statement(_) | Node::Input { .. } | Node::Seed => Sym::new(*node),
                Node::Add(a, b) => m(a) + m(b),
                Node::Mul(a, b) => m(a) * m(b),
                Node::Hash(s, from, to) => Sym::new(Node::Hash(m(s).0, from, to)),
                Node::Low(h) => Sym::new(Node::Low(m(h).0)),
                Node::Bits(v, shift, width) => m(v).bits(shift as usize, width as usize),
                Node::RingWeight(k, n) => {
                    let ops: Vec<Sym> = graph.kernels[k as usize].iter().map(|&id| m(id)).collect();
                    let n = n as usize;
                    ring_tower::weight_at(&ops[..n], &ops[n..2 * n], &ops[2 * n..])
                }
            };
            map.push(s);
        }
        map.iter().map(|s| s.0).collect::<Vec<u32>>()
    });
    (expanded, map)
}

/// What the compiler needs besides the graph: the transcript's IV (the contract's), the public input and the stream.
pub struct Inputs<'a> {
    pub iv: [u8; 32],
    pub public: [u8; 32],
    pub stream: &'a [u8],
}

/// The compiled circuit with its witness, and what the tests compare.
pub struct Compiled {
    pub finished: Finished,
    pub public: PublicInputs,
    /// The expanded graph, the original nodes' images in it, and each live element node's limbs.
    pub expanded: Graph,
    pub map: Vec<u32>,
    pub limbs: BTreeMap<u32, Limbs>,
    /// Each Keccak-256 call's digest values, by its (expanded) node.
    pub digests: BTreeMap<u32, Vec<Value>>,
    pub keccak_calls: usize,
    pub permutations: usize,
    /// `E` units: by op (mul, add, square), slot operand ended / both forwarded.
    pub arith: [[usize; 2]; 3],
    pub packings: usize,
    pub free_bits: [usize; 2],
}

/// The values of a big-endian integer of `nbytes` bytes starting at byte `first`, as `(exponent, bit)`.
fn be_bits(bit: &dyn Fn(usize) -> Value, first: usize, nbytes: usize) -> Vec<(usize, Value)> {
    (0..8 * nbytes)
        .map(|e| (e, bit(8 * (first + nbytes - 1 - e / 8) + e % 8)))
        .collect()
}

/// Compile `recorded` with the permutation template `make` (rows of `2^log_width`), on a real proof's inputs.
pub fn compile<P: Permutation>(
    recorded: &Recorded,
    log_width: u8,
    make: impl FnOnce(&mut Builder) -> P,
    inputs: &Inputs,
) -> Compiled {
    let (g, map) = expand(&recorded.graph);
    let stream = inputs.stream;
    assert_eq!(stream.len(), recorded.stream_len);
    let call_words: Vec<Vec<Word>> = calls(recorded);
    let mapped = |w: &Word| match *w {
        Word::Node(id) => Word::Node(map[id as usize]),
        other => other,
    };
    let call_words: Vec<Vec<Word>> = call_words.iter().map(|c| c.iter().map(mapped).collect()).collect();
    let zero: Vec<u32> = recorded.graph.zero.iter().map(|&(id, _)| map[id as usize]).collect();
    assert!(recorded.graph.nonzero.is_empty(), "π1's verifier checks nothing nonzero");
    let outputs = call_words
        .iter()
        .flatten()
        .filter_map(|w| match w {
            Word::Node(id) => Some(*id),
            _ => None,
        })
        .chain(zero.iter().copied());
    let live = crate::count::live(&g, outputs);

    let mut b = Builder::new(log_width);
    let permutation = make(&mut b);
    let mut sponge = Sponge::new(&mut b, permutation);
    let mut bools = Bools::new(&mut b);
    let mut packer = Packer::new(&mut b);
    let mut arith = Arith::new(&mut b);
    let mut ports = Ports::new(&mut b);

    // The stream's hashed bytes, and those in a call's first block.
    let mut hashed = vec![false; stream.len()];
    let mut first_block = vec![false; stream.len()];
    for (id, node) in g.nodes.iter().enumerate() {
        if let Node::Hash(_, from, to) = *node
            && live[id]
        {
            let (from, to) = (from as usize, to as usize);
            hashed[from..to].fill(true);
            // The message is the 32-byte state, then the bytes: the first block holds 136 − 32 of them.
            first_block[from..to.min(from + crate::KECCAK_RATE - 32)].fill(true);
        }
    }
    // Free bits: the stream's hashed bytes', then the public input's (both in byte order, low bit first).
    let mut bit_self: Vec<Option<Value>> = vec![None; 8 * stream.len()];
    let mut bit_copy: Vec<Option<Value>> = vec![None; 8 * stream.len()];
    let mut free_bits = [0usize; 2];
    for (i, &byte) in stream.iter().enumerate() {
        if !hashed[i] {
            continue;
        }
        for j in 0..8 {
            let bit = byte >> j & 1 == 1;
            if first_block[i] {
                let (v, c) = bools.bit_and_copy(&mut b, bit);
                (bit_self[8 * i + j], bit_copy[8 * i + j]) = (Some(v), Some(c));
                free_bits[1] += 1;
            } else {
                bit_self[8 * i + j] = Some(bools.bit(&mut b, bit));
                free_bits[0] += 1;
            }
        }
    }
    let mut public_self = Vec::with_capacity(256);
    let mut public_copy = Vec::with_capacity(256);
    for i in 0..256 {
        let (v, c) = bools.bit_and_copy(&mut b, inputs.public[i / 8] >> (i % 8) & 1 == 1);
        public_self.push(v);
        public_copy.push(c);
        free_bits[1] += 1;
    }
    let stream_bit = |i: usize| bit_self[i].expect("a hashed bit");

    // Keccak-256 calls, in the chain's order.
    let mut digests: BTreeMap<u32, Vec<Value>> = BTreeMap::new();
    let constant_bits = |bytes: &[u8]| -> Vec<Bit> {
        bytes
            .iter()
            .flat_map(|byte| (0..8).map(move |j| if byte >> j & 1 == 1 { Bit::One } else { Bit::Zero }))
            .collect()
    };
    for (id, node) in g.nodes.iter().enumerate() {
        match *node {
            Node::Seed if live[id] => {
                let mut message = constant_bits(&NAME);
                message.extend(constant_bits(&inputs.iv));
                message.extend(public_copy.iter().map(|&c| Bit::V(c)));
                digests.insert(id as u32, sponge.keccak256(&mut b, &message));
            }
            Node::Hash(s, from, to) if live[id] => {
                let state = &digests[&s];
                let mut message: Vec<Bit> = state.iter().map(|&v| Bit::V(v)).collect();
                for i in from as usize..to as usize {
                    for j in 0..8 {
                        let k = 8 * i + j;
                        message.push(Bit::V(match bit_copy[k] {
                            Some(c) => c,
                            None => stream_bit(k),
                        }));
                    }
                }
                digests.insert(id as u32, sponge.keccak256(&mut b, &message));
            }
            _ => {}
        }
    }
    let keccak_calls = digests.len();

    // The statement's limbs (its four big-endian words), packed once.
    let statement_limb: Vec<Value> = (0..4)
        .map(|k| packer.pack(&mut b, &mut sponge.constants, &be_bits(&|i| public_self[i], 8 * k, 8)))
        .collect();
    let mut packings = 4;

    // Uses left of each node, for choosing which operand ends at a unit.
    let mut uses = vec![0usize; g.nodes.len()];
    for (id, node) in g.nodes.iter().enumerate() {
        if !live[id] {
            continue;
        }
        if let Node::Add(a, c) | Node::Mul(a, c) = *node {
            uses[a as usize] += 1;
            if a != c {
                uses[c as usize] += 1;
            }
        }
    }

    // Element nodes' limbs, in node order; `endable`: its limbs may still end at a unit's slots.
    let mut limbs: BTreeMap<u32, Limbs> = BTreeMap::new();
    let mut endable: BTreeMap<u32, bool> = BTreeMap::new();
    for (id, node) in g.nodes.iter().enumerate() {
        if !live[id] {
            continue;
        }
        let id = id as u32;
        let zero_pair = |b: &mut Builder, consts: &mut Constants| [consts.fresh(b, K(0)), consts.fresh(b, K(0))];
        let (l, can_end): (Limbs, bool) = match *node {
            Node::Const([c0, c1, c2]) => (
                [c0, c1, c2].map(|c| sponge.constants.fresh(&mut b, K(c))),
                true,
            ),
            Node::Statement(k) => {
                let [z1, z2] = zero_pair(&mut b, &mut sponge.constants);
                ([statement_limb[k as usize], z1, z2], true)
            }
            Node::Input { offset, len } => {
                let (offset, len) = (offset as usize, len as usize);
                let all_hashed = hashed[offset..offset + len].iter().all(|&h| h);
                assert!(
                    all_hashed || hashed[offset..offset + len].iter().all(|&h| !h),
                    "a read partly hashed"
                );
                if !all_hashed {
                    // Never hashed: free limbs.
                    let bytes = &stream[offset..offset + len];
                    let be = |r: &[u8]| r.iter().fold(0u64, |acc, &x| acc << 8 | x as u64);
                    let words = match len {
                        24 => [be(&bytes[16..24]), be(&bytes[8..16]), be(&bytes[0..8])],
                        16 => [be(&bytes[8..16]), be(&bytes[0..8]), 0],
                        _ => [be(bytes), 0, 0],
                    };
                    (words.map(|w| b.free(K(w))), false)
                } else {
                    packings += 1;
                    let mut pack = |first: usize, n: usize| {
                        packer.pack(&mut b, &mut sponge.constants, &be_bits(&stream_bit, first, n))
                    };
                    match len {
                        24 => ([pack(offset + 16, 8), pack(offset + 8, 8), pack(offset, 8)], true),
                        16 => {
                            let (c0, c1) = (pack(offset + 8, 8), pack(offset, 8));
                            ([c0, c1, sponge.constants.fresh(&mut b, K(0))], true)
                        }
                        _ => {
                            let c0 = pack(offset, len);
                            let [z1, z2] = zero_pair(&mut b, &mut sponge.constants);
                            ([c0, z1, z2], true)
                        }
                    }
                }
            }
            Node::Low(h) => {
                packings += 1;
                let d = &digests[&h];
                let digest_bit = |i: usize| d[i];
                let mut limb = |i: usize, b: &mut Builder, consts: &mut Constants| {
                    packer.pack(b, consts, &be_bits(&digest_bit, 24 - 8 * i, 8))
                };
                let l0 = limb(0, &mut b, &mut sponge.constants);
                let l1 = limb(1, &mut b, &mut sponge.constants);
                let l2 = limb(2, &mut b, &mut sponge.constants);
                ([l0, l1, l2], true)
            }
            Node::Bits(v, shift, width) => {
                let Node::Input { offset, len } = g.nodes[v as usize] else {
                    panic!("a bit field of a read integer")
                };
                let (offset, len) = (offset as usize, len as usize);
                let field: Vec<(usize, Value)> = be_bits(&stream_bit, offset, len)
                    .into_iter()
                    .filter(|&(e, _)| e >= shift as usize && e < shift as usize + width as usize)
                    .map(|(e, v)| (e - shift as usize, v))
                    .collect();
                let [z1, z2] = zero_pair(&mut b, &mut sponge.constants);
                match field.len() {
                    0 => ([sponge.constants.fresh(&mut b, K(0)), z1, z2], true),
                    // One bit: the bit itself, which ends at its own self-loop.
                    1 if field[0].0 == 0 => ([field[0].1, z1, z2], false),
                    _ => {
                        packings += 1;
                        ([packer.pack(&mut b, &mut sponge.constants, &field), z1, z2], true)
                    }
                }
            }
            Node::Add(x, y) | Node::Mul(x, y) => {
                let op = match *node {
                    Node::Add(..) => Op::Add,
                    _ if x == y => Op::Square,
                    _ => Op::Mul,
                };
                let (lx, ly) = (limbs[&x], limbs[&y]);
                let (ex, ey) = (endable[&x], endable[&y]);
                // End the operand with fewer uses left (it has fewer chances), if either can end.
                let end_x = ex && (!ey || uses[x as usize] <= uses[y as usize]);
                let (a, c, end, ended) = if op == Op::Square {
                    (lx, lx, ex, x)
                } else if end_x {
                    (lx, ly, true, x)
                } else if ey {
                    (ly, lx, true, y)
                } else {
                    (lx, ly, false, x)
                };
                if end {
                    endable.insert(ended, false);
                }
                uses[x as usize] -= 1;
                if x != y {
                    uses[y as usize] -= 1;
                }
                (arith.op(&mut b, op, a, c, end), true)
            }
            Node::Seed | Node::Hash(..) => continue,
            Node::RingWeight(..) => unreachable!("expanded"),
        };
        limbs.insert(id, l);
        endable.insert(id, can_end);
    }

    // Ports: the statement, the roots, the calls' elements, the zero checks.
    ports.port(&mut b, &statement_limb, Source::Statement);
    let mut roots: Vec<[u8; 32]> = Vec::new();
    let mut root_of: BTreeMap<usize, u32> = BTreeMap::new();
    for &at in &recorded.roots_at {
        assert!(hashed[at..at + 32].iter().all(|&h| h), "a root is hashed");
        let root_limbs: Vec<Value> = (0..4)
            .map(|l| packer.pack(&mut b, &mut sponge.constants, &be_bits(&stream_bit, at + 24 - 8 * l, 8)))
            .collect();
        packings += 1;
        root_of.insert(at, roots.len() as u32);
        ports.port(&mut b, &root_limbs, Source::Root(roots.len() as u32));
        roots.push(stream[at..at + 32].try_into().expect("32 bytes"));
    }
    let mut element_of: BTreeMap<u32, u32> = BTreeMap::new();
    let mut element_nodes: Vec<u32> = Vec::new();
    let mut circuit_calls: Vec<Vec<CallWord>> = Vec::new();
    for call in &call_words {
        let mut words = Vec::new();
        for w in call {
            words.push(match *w {
                Word::Const(bytes) => CallWord::Const(bytes),
                Word::Stream(at) => CallWord::Root(root_of[&at]),
                Word::Node(id) => match g.nodes[id as usize] {
                    Node::Const([c0, c1, c2]) => CallWord::Const(super::spec::element_word(E::new(c0, c1, c2))),
                    _ => {
                        let next = element_nodes.len() as u32;
                        let e = *element_of.entry(id).or_insert_with(|| {
                            element_nodes.push(id);
                            next
                        });
                        CallWord::Element(e)
                    }
                },
                Word::Stored(_) => panic!("no stored words"),
            });
        }
        circuit_calls.push(words);
    }
    for (e, &id) in element_nodes.iter().enumerate() {
        ports.port(&mut b, &limbs[&id], Source::Element(e as u32));
    }
    for &id in &zero {
        match g.nodes[id as usize] {
            Node::Const(c) => assert_eq!(c, [0; 3], "a zero check on a nonzero constant"),
            _ => ports.port(&mut b, &limbs[&id], Source::Zero),
        }
    }
    b.calls = circuit_calls;
    let keccak_permutations = sponge.permutations;
    let finished = b.finish();
    let elements: Vec<E> = element_nodes
        .iter()
        .map(|id| {
            let w = limbs[id].map(|v| finished.words[v as usize].0);
            E::new(w[0], w[1], w[2])
        })
        .collect();
    Compiled {
        public: PublicInputs {
            statement: inputs.public,
            roots,
            elements,
        },
        finished,
        expanded: g,
        map,
        limbs,
        digests,
        keccak_calls,
        permutations: keccak_permutations,
        arith: arith.counts,
        packings,
        free_bits,
    }
}
