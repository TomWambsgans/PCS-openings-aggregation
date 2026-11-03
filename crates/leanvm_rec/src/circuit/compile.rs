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
//! - rejected (a panic, as the Lean compiler `formal/RecCircuit` refuses them; π1's graphs have none): a graph not
//!   well typed (`assert_typed`: node 0 not the seed, a hash or a challenge of an element, a sum, a product, a bit
//!   field or a ring weight of a state, a ring weight's map not of 6 stages), a read never hashed that is not a
//!   24-byte scalar, a bit field of a read of more than 8 bytes, an empty hashed read;
//! - `Add`, `Mul` → `E` units on limbs (a product, a square, a sum), constants → `κ` slots;
//! - the calls' elements, `π1`'s roots, the statement, and the zero checks → **ports** (`spec::Source`).
//!
//! The witness is the framework's: the free bits and limbs given, everything else computed by the formulas.

use std::collections::BTreeMap;

use leanvm_flock_gas::evm::codegen::Word;
use leanvm_flock_gas::evm::machine::root_word;
use leanvm_flock_gas::evm::record::{Graph, Node, Sym, record};
use leanvm_flock_gas::field::{E, K};
use leanvm_flock_gas::ring_tower;
use leanvm_flock_gas::scalar::Scalar;
use leanvm_univariate::contract::{NAME, Recorded, calls};

use super::keccak::{Bit, Constants, Permutation, Sponge};
use super::layout::{Builder, Finished, Value};
use super::spec::{CallWord, PublicInputs, Source};
use super::units::{Arith, Bools, Limbs, Op, Packer, Ports};

/// What the Lean compiler checks before the expansion (`formal/RecCircuit/RecCircuit/Expand.lean`, `Graph.typed`):
/// node 0 is the seed (π1's recorder makes it first, `Recorder::new`, and the expansion replays the graph from it);
/// every node reads earlier nodes; a hash and a challenge read a state (the seed, a hash), a sum, a product, a bit
/// field and a ring weight read elements; a ring weight's kernel is its point's `n` coordinates, `1 + r`'s `n` and the
/// map's `ring_tower::STAGES`; the checks name nodes. π1's graphs are all such; a panic otherwise.
fn assert_typed(graph: &Graph) {
    let is_state = |id: u32| matches!(graph.nodes[id as usize], Node::Seed | Node::Hash(..));
    assert_eq!(graph.nodes.first(), Some(&Node::Seed), "node 0 is the seed");
    for (i, node) in graph.nodes.iter().enumerate() {
        let earlier = |id: u32| {
            assert!((id as usize) < i, "a node reads earlier nodes");
            id
        };
        match *node {
            Node::Add(a, b) | Node::Mul(a, b) => {
                assert!(!is_state(earlier(a)) && !is_state(earlier(b)), "a sum or a product reads elements")
            }
            Node::Bits(v, ..) => assert!(!is_state(earlier(v)), "a bit field reads an element"),
            Node::Hash(s, ..) | Node::Low(s) | Node::Narrow(s) => {
                assert!(is_state(earlier(s)), "a hash or a challenge reads a state")
            }
            Node::RingWeight(k, n) => {
                let ops = &graph.kernels[k as usize];
                assert_eq!(ops.len(), 2 * n as usize + ring_tower::STAGES, "a ring weight's map has 6 stages");
                for &a in ops {
                    assert!(!is_state(earlier(a)), "a ring weight reads elements");
                }
            }
            _ => {}
        }
    }
    for &(id, _) in graph.zero.iter().chain(&graph.nonzero) {
        assert!((id as usize) < graph.nodes.len(), "a check names a node");
    }
}

/// The graph replayed with every ring-switch kernel expanded, and each original node's image.
pub fn expand(graph: &Graph) -> (Graph, Vec<u32>) {
    assert_typed(graph);
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
                Node::Narrow(h) => Sym::new(Node::Narrow(m(h).0)),
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

/// What the compiler needs besides the graph: the program's IV (leanVM's digest of the bytecode and the R1CS), from
/// which the contract's transcript IV is derived with `recorded` (`Recorded::iv`: its shape, setup roots and
/// variant; REVIEW-REC.md L2), the public input and the stream.
pub struct Inputs<'a> {
    pub program_iv: [u8; 32],
    pub public: [u8; 32],
    pub stream: &'a [u8],
}

/// The compiled circuit with its witness, and what the tests compare.
pub struct Compiled {
    pub finished: Finished,
    /// π1's contract IV, which the circuit's seed hashes (κ constants): `recorded.iv(program_iv)`.
    pub pi1_iv: [u8; 32],
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

/// The values of a little-endian integer of `nbytes` bytes starting at byte `first`, as `(exponent, bit)`.
fn le_bits(bit: &dyn Fn(usize) -> Value, first: usize, nbytes: usize) -> Vec<(usize, Value)> {
    (0..8 * nbytes).map(|e| (e, bit(8 * (first + e / 8) + e % 8))).collect()
}

/// A call word's node as π1-rec3's paired batch makes it (`transcript::pair_point`): `y_1(z) = z·z + z` or
/// `y_0(z) = z + β_1 · y_1(z)` of a challenge `z`: `(z, the coordinate)`. Then `z` is the port, not the coordinate.
fn pair_coordinate(g: &Graph, id: u32) -> Option<(u32, u8)> {
    let node = |id: u32| g.nodes[id as usize];
    let is_challenge = |z: u32| matches!(node(z), Node::Narrow(_) | Node::Low(_));
    let y1_of = |id: u32| -> Option<u32> {
        let Node::Add(a, b) = node(id) else { return None };
        [(a, b), (b, a)].into_iter().find_map(|(square, z)| match node(square) {
            Node::Mul(x, y) if x == z && y == z && is_challenge(z) => Some(z),
            _ => None,
        })
    };
    if let Some(z) = y1_of(id) {
        return Some((z, 1));
    }
    let beta1 = leanvm_flock_gas::transcript::cantor_beta1();
    let Node::Add(a, b) = node(id) else { return None };
    [(a, b), (b, a)].into_iter().find_map(|(z, product)| {
        let Node::Mul(c, y) = node(product) else { return None };
        [(c, y), (y, c)].into_iter().find_map(|(c, y)| match node(c) {
            Node::Const(limbs) if E::new(limbs[0], limbs[1], limbs[2]) == beta1 && y1_of(y) == Some(z) => Some((z, 0)),
            _ => None,
        })
    })
}

/// `π2`'s two layouts (SPEC-REC.md §2.4, §2.6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layout {
    /// Rows of 16, Keccak-f in 130,944 positions ([`super::keccak16::D16`]).
    D16v,
    /// Rows of 32, Keccak-f in 51,200 positions ([`super::keccak::D32`]).
    D32v,
}

impl Layout {
    pub fn log_width(self) -> u8 {
        match self {
            Layout::D16v => 4,
            Layout::D32v => 5,
        }
    }
}

/// `π2`'s circuit for `recorded` in `layout`, with the witness of a real proof's inputs. The circuit (`σ`, `κ`, the
/// regions and blocks, the ports and calls) depends on `recorded` only.
pub fn pi2(recorded: &Recorded, layout: Layout, inputs: &Inputs) -> Compiled {
    match layout {
        Layout::D16v => compile(recorded, 4, super::keccak16::D16::new, inputs),
        Layout::D32v => compile(recorded, 5, super::keccak::D32::new, inputs),
    }
}

/// Compile `recorded` with the permutation template `make` (rows of `2^log_width`), on a real proof's inputs.
pub fn compile<P: Permutation>(
    recorded: &Recorded,
    log_width: u8,
    make: impl FnOnce(&mut Builder) -> P,
    inputs: &Inputs,
) -> Compiled {
    let (g, map) = expand(&recorded.graph);
    let pi1_iv = recorded.iv(&inputs.program_iv);
    let stream = inputs.stream;
    assert_eq!(stream.len(), recorded.stream_len);
    let call_words: Vec<Vec<Word>> = calls(recorded);
    let mapped = |w: &Word| match *w {
        Word::Node(id) => Word::Node(map[id as usize]),
        other => other,
    };
    let call_words: Vec<Vec<Word>> = call_words.iter().map(|c| c.iter().map(mapped).collect()).collect();
    let zero: Vec<u32> = recorded.graph.zero.iter().map(|&(id, _)| map[id as usize]).collect();
    assert!(
        recorded.graph.nonzero.is_empty(),
        "π1's verifier checks nothing nonzero"
    );
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
                message.extend(constant_bits(&pi1_iv));
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
            Node::Const([c0, c1, c2]) => ([c0, c1, c2].map(|c| sponge.constants.fresh(&mut b, K(c))), true),
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
                    // Never hashed: free limbs, so a 24-byte scalar only (a shorter read's high limbs are zero in
                    // the graph, which free limbs would not constrain; the Lean compiler rejects it alike).
                    assert_eq!(len, 24, "a read never hashed is a 24-byte scalar");
                    let bytes = &stream[offset..offset + len];
                    let be = |r: &[u8]| r.iter().fold(0u64, |acc, &x| acc << 8 | x as u64);
                    let words = [be(&bytes[16..24]), be(&bytes[8..16]), be(&bytes[0..8])];
                    (words.map(|w| b.free(K(w))), false)
                } else {
                    assert!(len >= 1, "a hashed read is not empty");
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
            // A narrow challenge: limb 2 is the low 32 bits of the digest's bytes 8..16, its bytes 12..16.
            Node::Narrow(h) => {
                packings += 1;
                let d = &digests[&h];
                let digest_bit = |i: usize| d[i];
                let l0 = packer.pack(&mut b, &mut sponge.constants, &be_bits(&digest_bit, 24, 8));
                let l1 = packer.pack(&mut b, &mut sponge.constants, &be_bits(&digest_bit, 16, 8));
                let l2 = packer.pack(&mut b, &mut sponge.constants, &be_bits(&digest_bit, 12, 4));
                ([l0, l1, l2], true)
            }
            Node::Bits(v, shift, width) => {
                let Node::Input { offset, len } = g.nodes[v as usize] else {
                    panic!("a bit field of a read integer")
                };
                let (offset, len) = (offset as usize, len as usize);
                // `E::bits` takes the low limb's bits only: a wider read's field could reach past it (the Lean
                // compiler rejects every `len > 8` alike).
                assert!(len <= 8, "a bit field of an integer of at most 8 bytes");
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

    // Ports: the zero checks first, padded with constant zeros to a power of two, so that their outside tags
    // `N … N + 2^k` are an aligned coset (PI2.md §9, lever 3c: the verifier sums them in closed form); then the
    // statement, the roots, the calls' elements.
    let mut zero_ports = 0usize;
    for &id in &zero {
        match g.nodes[id as usize] {
            Node::Const(c) => assert_eq!(c, [0; 3], "a zero check on a nonzero constant"),
            _ => {
                ports.port(&mut b, &limbs[&id], Source::Zero);
                zero_ports += 1;
            }
        }
    }
    if zero_ports > 1 {
        for _ in zero_ports..zero_ports.next_power_of_two() {
            let pad = [(); 3].map(|_| sponge.constants.fresh(&mut b, K(0)));
            ports.port(&mut b, &pad, Source::Pad);
        }
    }
    ports.port(&mut b, &statement_limb, Source::Statement);
    let mut roots: Vec<[u8; 32]> = Vec::new();
    let mut root_of: BTreeMap<usize, u32> = BTreeMap::new();
    // A root is public as `PCS_OPEN`'s root word (REVIEW-REC.md M1: one ABI for the eight calls), each 16-byte half
    // of the stream's bytes reversed: its limbs `L_l` (the word's big-endian 8-byte words, the lowest first) are the
    // little-endian words of the stream's bytes 16..24, 24..32, 0..8, 8..16.
    for &at in &recorded.roots_at {
        assert!(hashed[at..at + 32].iter().all(|&h| h), "a root is hashed");
        let root_limbs: Vec<Value> = [16, 24, 0, 8]
            .into_iter()
            .map(|first| packer.pack(&mut b, &mut sponge.constants, &le_bits(&stream_bit, at + first, 8)))
            .collect();
        packings += 1;
        root_of.insert(at, roots.len() as u32);
        ports.port(&mut b, &root_limbs, Source::Root(roots.len() as u32));
        roots.push(root_word(&stream[at..at + 32].try_into().expect("32 bytes")));
    }
    let mut element_of: BTreeMap<u32, u32> = BTreeMap::new();
    let mut element_nodes: Vec<u32> = Vec::new();
    let mut circuit_calls: Vec<Vec<CallWord>> = Vec::new();
    for call in &call_words {
        let mut words = Vec::new();
        for (k, w) in call.iter().enumerate() {
            words.push(match *w {
                // A setup root (word 0): `PCS_OPEN`'s root word (M1).
                Word::Const(bytes) if k == 0 => CallWord::Const(root_word(&bytes)),
                Word::Const(bytes) => CallWord::Const(bytes),
                Word::Stream(at) => CallWord::Root(root_of[&at]),
                Word::Node(id) => match (g.nodes[id as usize], pair_coordinate(&g, id)) {
                    (Node::Const([c0, c1, c2]), _) => CallWord::Const(super::spec::element_word(E::new(c0, c1, c2))),
                    // π1-rec3: a pair's coordinate, its challenge the port (SPEC-POINTS.md).
                    (_, Some((z, coordinate))) => {
                        let next = element_nodes.len() as u32;
                        let element = *element_of.entry(z).or_insert_with(|| {
                            element_nodes.push(z);
                            next
                        });
                        CallWord::Pair { element, coordinate }
                    }
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
        pi1_iv,
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
