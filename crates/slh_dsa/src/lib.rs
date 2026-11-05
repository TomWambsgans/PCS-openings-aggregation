// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! SLH-DSA-SHAKE signature verification (FIPS 205, pure, empty context) as a circuit of [`quotient::circuit`]'s
//! one gate, `V = X + C + Y·C` on bits.
//!
//! **The statement.** Public: the public key `PK.seed ‖ PK.root` (32 bytes at `n = 16`) and a 32-byte message `M`,
//! as the quotient statement's `y` and `root` ([`statement`]). Secret: the signature. The circuit computes
//! `slh_verify_internal(M', SIG, PK)` with `M' = 0x00 ‖ 0x00 ‖ M` (FIPS 205, Algorithm 24 with `ctx` empty).
//!
//! **The free inputs**, in order ([`inputs`]): `PK.seed`, `PK.root`, `M`, then the signature, every byte low bit
//! first. `H_msg` reads `PK.root` before the hypertree computes the root it must equal. So `PK.root` is an
//! input, bound by the public words, and the computed root's XOR with it is public word 6, which the verifier
//! takes to be zero ([`quotient::circuit::Builder::finish_with_zeros`]).
//!
//! **Worst case, fixed wiring.** Every WOTS+ chain has its `w − 1 = 15` hashes. Hash `j` of chain `i` is applied
//! when `j ≥ msg[i]` and passed by otherwise, by a mux (two rows a bit). Its address is the constant `j`. The
//! FORS and XMSS authentication paths are ordered by the index bits (three rows a bit). The digest's indices, the
//! tree addresses and the checksum's digits are wiring; the checksum's sum is a 12-bit adder.

use quotient::circuit::{Builder, Circuit, Src, WORD_BITS, public_words};
use quotient::statement::Statement;

/// `lg_w`: every SLH-DSA parameter set has `w = 16`.
pub const LG_W: usize = 4;
/// `len2` at `w = 16`, for every `n` of FIPS 205.
pub const LEN2: usize = 3;
/// SHAKE256's rate in bytes.
pub const RATE: usize = 136;

/// A parameter set of FIPS 205, Table 2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    pub name: &'static str,
    pub n: usize,
    pub h: usize,
    pub d: usize,
    pub hp: usize,
    pub a: usize,
    pub k: usize,
    pub m: usize,
}

pub const SHAKE_128S: Params = Params { name: "SLH-DSA-SHAKE-128s", n: 16, h: 63, d: 7, hp: 9, a: 12, k: 14, m: 30 };
pub const SHAKE_128F: Params = Params { name: "SLH-DSA-SHAKE-128f", n: 16, h: 66, d: 22, hp: 3, a: 6, k: 33, m: 34 };
pub const SHAKE_192S: Params = Params { name: "SLH-DSA-SHAKE-192s", n: 24, h: 63, d: 7, hp: 9, a: 14, k: 17, m: 39 };
pub const SHAKE_192F: Params = Params { name: "SLH-DSA-SHAKE-192f", n: 24, h: 66, d: 22, hp: 3, a: 8, k: 33, m: 42 };
pub const SHAKE_256S: Params = Params { name: "SLH-DSA-SHAKE-256s", n: 32, h: 64, d: 8, hp: 8, a: 14, k: 22, m: 47 };
pub const SHAKE_256F: Params = Params { name: "SLH-DSA-SHAKE-256f", n: 32, h: 68, d: 17, hp: 4, a: 9, k: 35, m: 49 };
pub const ALL: [Params; 6] = [SHAKE_128S, SHAKE_128F, SHAKE_192S, SHAKE_192F, SHAKE_256S, SHAKE_256F];

/// The rows of the SLH-DSA-SHAKE-128s circuit, `2^29` (447,137,304 used; `tests/real.rs` builds it).
pub const SHAKE_128S_LOG_ROWS: usize = 29;

/// The message's bytes: a digest of what is signed.
pub const MSG_BYTES: usize = 32;

impl Params {
    pub fn len1(&self) -> usize {
        8 * self.n / LG_W
    }

    pub fn len(&self) -> usize {
        self.len1() + LEN2
    }

    /// The signature's bytes: `R`, the FORS signature, the hypertree signature.
    pub fn sig_bytes(&self) -> usize {
        self.n * (1 + self.k * (1 + self.a) + self.d * self.len() + self.h)
    }

    /// Keccak-f calls of a verification with every chain at its 15 hashes: `H_msg`; the FORS leaves, paths and
    /// `T_k`; per layer the chains, `T_len` and the path.
    pub fn keccak_f(&self) -> usize {
        let blocks = |bytes: usize| bytes / RATE + 1;
        let n = self.n;
        let h_msg = blocks(3 * n + 2 + MSG_BYTES);
        let fors = self.k * (1 + self.a) + blocks(n + 32 + self.k * n);
        let layer = 15 * self.len() * blocks(2 * n + 32) + blocks(n + 32 + self.len() * n) + self.hp * blocks(3 * n + 32);
        h_msg + fors + self.d * layer
    }
}

/// Wires of bytes, each byte low bit first: bit `i` of byte `j` at `8 j + i`.
type Bits = Vec<Src>;

fn konst(value: u64, bits: usize) -> Bits {
    (0..bits).map(|i| if (value >> i) & 1 == 1 { Src::One } else { Src::Zero }).collect()
}

fn const_bytes(bytes: &[u8]) -> Bits {
    bytes.iter().flat_map(|&byte| konst(byte as u64, 8)).collect()
}

/// A value's wires (low bit first) as `bytes` big-endian bytes.
fn be(value: &[Src], bytes: usize) -> Bits {
    let mut out = vec![Src::Zero; 8 * bytes];
    for (v, &bit) in value.iter().enumerate() {
        assert!(v < 8 * bytes, "a value of {} bits in {bytes} bytes", value.len());
        out[8 * (bytes - 1 - v / 8) + v % 8] = bit;
    }
    out
}

/// `toInt(X, bytes)`: big-endian bytes to a value's wires, low bit first.
fn to_int(x: &[Src]) -> Bits {
    let bytes = x.len() / 8;
    (0..8 * bytes).map(|v| x[8 * (bytes - 1 - v / 8) + v % 8]).collect()
}

/// `base_2b(X, b, out_len)` (FIPS 205, Algorithm 4): the bit string read most significant bit first, cut into
/// `b`-bit digits, each returned low bit first.
fn base_2b(x: &[Src], b: usize, out_len: usize) -> Vec<Bits> {
    assert!(b * out_len <= x.len());
    (0..out_len)
        .map(|o| {
            (0..b)
                .map(|t| {
                    let p = o * b + (b - 1 - t);
                    x[8 * (p / 8) + 7 - p % 8]
                })
                .collect()
        })
        .collect()
}

/// The address types of FIPS 205, Section 4.2.
const WOTS_HASH: u64 = 0;
const WOTS_PK: u64 = 1;
const TREE: u64 = 2;
const FORS_TREE: u64 = 3;
const FORS_ROOTS: u64 = 4;

/// An address: each field's value wires, low bit first.
#[derive(Clone)]
struct Adrs {
    layer: Bits,
    tree: Bits,
    kind: u64,
    key_pair: Bits,
    word2: Bits,
    word3: Bits,
}

impl Adrs {
    fn new(layer: usize, tree: &[Src], kind: u64) -> Self {
        Self {
            layer: konst(layer as u64, 8),
            tree: tree.to_vec(),
            kind,
            key_pair: vec![],
            word2: vec![],
            word3: vec![],
        }
    }

    /// The 32 bytes: layer (4), tree (12), type (4), key pair (4), chain or height (4), hash or index (4).
    fn bits(&self) -> Bits {
        [
            be(&self.layer, 4),
            be(&self.tree, 12),
            be(&konst(self.kind, 32), 4),
            be(&self.key_pair, 4),
            be(&self.word2, 4),
            be(&self.word3, 4),
        ]
        .concat()
    }
}

/// SHAKE256 of `msg` (whole bytes), its first `out_bytes` bytes: the sponge over [`Builder::keccak_f`].
pub fn shake256(b: &mut Builder, msg: &[Src], out_bytes: usize) -> Bits {
    assert!(msg.len().is_multiple_of(8) && out_bytes <= RATE);
    let len = msg.len() / 8;
    let blocks = len / RATE + 1;
    let mut padded = msg.to_vec();
    padded.resize(8 * RATE * blocks, Src::Zero);
    // The domain and the first padding bit, 0x1F, then the last bit, 0x80, of the last block.
    for i in 0..5 {
        padded[8 * len + i] = Src::One;
    }
    padded[8 * (RATE * blocks - 1) + 7] = Src::One;
    let mut state = [[Src::Zero; 64]; 25];
    for block in padded.chunks(8 * RATE) {
        for (i, &bit) in block.iter().enumerate() {
            state[i / 64][i % 64] = b.xor(state[i / 64][i % 64], bit);
        }
        state = b.keccak_f(state);
    }
    (0..8 * out_bytes).map(|i| state[i / 64][i % 64]).collect()
}

/// `if0` where `bit` is 0, `if1` where it is 1: `if0 ⊕ (bit ∧ (if0 ⊕ if1))`, two rows a wire.
fn select(b: &mut Builder, bit: Src, if0: &[Src], if1: &[Src]) -> Bits {
    match bit {
        Src::Zero => if0.to_vec(),
        Src::One => if1.to_vec(),
        _ => {
            let not = b.not(bit);
            (0..if0.len())
                .map(|i| {
                    let differ = b.xor(if0[i], if1[i]);
                    b.chi(if0[i], not, differ)
                })
                .collect()
        }
    }
}

/// `(node, auth)` where `bit` is 0, `(auth, node)` where it is 1: three rows a wire.
fn ordered(b: &mut Builder, bit: Src, node: &[Src], auth: &[Src]) -> (Bits, Bits) {
    let not = b.not(bit);
    let (mut left, mut right) = (Vec::with_capacity(node.len()), Vec::with_capacity(node.len()));
    for i in 0..node.len() {
        let differ = b.xor(node[i], auth[i]);
        let l = b.chi(node[i], not, differ);
        right.push(b.xor(l, differ));
        left.push(l);
    }
    (left, right)
}

/// Whether the value of `bits` (low bit first) is at most the constant `j`.
fn at_most(b: &mut Builder, bits: &[Src], j: usize) -> Src {
    bits.iter().enumerate().fold(Src::One, |below, (t, &bit)| {
        if (j >> t) & 1 == 1 {
            // `¬bit ∨ below`.
            b.chi(Src::One, below, bit)
        } else {
            // `¬bit ∧ below`.
            b.chi(Src::Zero, bit, below)
        }
    })
}

/// `x + y` on `x.len()` bits.
fn add(b: &mut Builder, x: &[Src], y: &[Src]) -> Bits {
    let mut carry = Src::Zero;
    (0..x.len())
        .map(|t| {
            let (p, q) = (x[t], y.get(t).copied().unwrap_or(Src::Zero));
            let differ = b.xor(p, q);
            let sum = b.xor(differ, carry);
            // The majority: `p` where `p = q`, else `carry`.
            let same = b.not(differ);
            let other = b.xor(p, carry);
            carry = b.chi(p, same, other);
            sum
        })
        .collect()
}

/// The hashes of FIPS 205's SHAKE instantiation, counting their Keccak-f calls.
struct Hashes<'a> {
    b: &'a mut Builder,
    seed: Bits,
    n: usize,
    calls: usize,
}

impl Hashes<'_> {
    fn shake(&mut self, input: &[Src], out: usize) -> Bits {
        self.calls += input.len() / 8 / RATE + 1;
        shake256(self.b, input, out)
    }

    /// `F`, `H` and `T_l`: `SHAKE256(PK.seed ‖ ADRS ‖ M, 8n)`.
    fn t(&mut self, adrs: &Adrs, parts: &[&[Src]]) -> Bits {
        let input = [&self.seed[..], &adrs.bits()[..], &parts.concat()[..]].concat();
        self.shake(&input, self.n)
    }

    /// WOTS+ (FIPS 205, Algorithm 8): the public key from a signature of `msg`, at `adrs`'s layer, tree and key
    /// pair.
    fn wots_pk(&mut self, p: &Params, sig: &[Src], msg: &[Src], adrs: &Adrs) -> Bits {
        let bits = 8 * self.n;
        let mut digits = base_2b(msg, LG_W, p.len1());
        // `csum = Σ (w − 1 − msg[i])`, each term the digit's complement; its three digits are its nibbles, high
        // first (`csum << 4` as two bytes, read four bits at a time).
        let mut csum = konst(0, 12);
        for digit in &digits {
            let complement: Bits = digit.iter().map(|&bit| self.b.not(bit)).collect();
            csum = add(self.b, &csum, &complement);
        }
        digits.extend([8, 4, 0].map(|low| csum[low..low + 4].to_vec()));
        let mut tops = Vec::with_capacity(p.len());
        for (i, digit) in digits.iter().enumerate() {
            let mut at = adrs.clone();
            at.word2 = konst(i as u64, 32);
            let mut tmp = sig[bits * i..bits * (i + 1)].to_vec();
            for j in 0..(1 << LG_W) - 1 {
                at.word3 = konst(j as u64, 32);
                let next = self.t(&at, &[&tmp]);
                let applied = at_most(self.b, digit, j);
                tmp = select(self.b, applied, &tmp, &next);
            }
            tops.push(tmp);
        }
        let mut pk = adrs.clone();
        pk.kind = WOTS_PK;
        let parts: Vec<&[Src]> = tops.iter().map(|top| &top[..]).collect();
        self.t(&pk, &parts)
    }

    /// An XMSS root from a signature of `msg` at leaf `leaf` (FIPS 205, Algorithm 11).
    fn xmss_root(&mut self, p: &Params, layer: usize, tree: &[Src], leaf: &[Src], sig: &[Src], msg: &[Src]) -> Bits {
        let bits = 8 * self.n;
        let (wots_sig, auth) = sig.split_at(bits * p.len());
        let mut adrs = Adrs::new(layer, tree, WOTS_HASH);
        adrs.key_pair = leaf.to_vec();
        let mut node = self.wots_pk(p, wots_sig, msg, &adrs);
        for k in 0..p.hp {
            let mut at = Adrs::new(layer, tree, TREE);
            at.word2 = konst(k as u64 + 1, 32);
            at.word3 = leaf[k + 1..].to_vec();
            let (left, right) = ordered(self.b, leaf[k], &node, &auth[bits * k..bits * (k + 1)]);
            node = self.t(&at, &[&left, &right]);
        }
        node
    }

    /// The FORS public key from a signature of `md` (FIPS 205, Algorithm 17).
    fn fors_pk(&mut self, p: &Params, sig: &[Src], md: &[Src], tree: &[Src], leaf: &[Src]) -> Bits {
        let bits = 8 * self.n;
        let indices = base_2b(md, p.a, p.k);
        let mut roots = Vec::with_capacity(p.k);
        for (i, index) in indices.iter().enumerate() {
            let part = &sig[bits * (1 + p.a) * i..bits * (1 + p.a) * (i + 1)];
            // The tree index at height `t`: `(i 2^a + index) >> t`.
            let at = |t: usize| {
                let mut adrs = Adrs::new(0, tree, FORS_TREE);
                adrs.key_pair = leaf.to_vec();
                adrs.word2 = konst(t as u64, 32);
                adrs.word3 = [&index[t..], &konst(i as u64, 8)[..]].concat();
                adrs
            };
            let mut node = self.t(&at(0), &[&part[..bits]]);
            for j in 0..p.a {
                let auth = &part[bits * (1 + j)..bits * (2 + j)];
                let (left, right) = ordered(self.b, index[j], &node, auth);
                node = self.t(&at(j + 1), &[&left, &right]);
            }
            roots.push(node);
        }
        let mut adrs = Adrs::new(0, tree, FORS_ROOTS);
        adrs.key_pair = leaf.to_vec();
        let parts: Vec<&[Src]> = roots.iter().map(|root| &root[..]).collect();
        self.t(&adrs, &parts)
    }
}

/// The circuit's parts before it is closed.
pub struct Built {
    pub builder: Builder,
    pub public: [Vec<Src>; 4],
    /// `computed root ⊕ PK.root`: public word 6, zero exactly when the signature verifies.
    pub zero: Vec<Src>,
    pub keccak_f: usize,
}

/// The verification of `p` (`n = 16`: the public key is 32 bytes, two public words), its rows unclosed.
pub fn build(p: &Params) -> Built {
    assert_eq!(p.n, 16, "the public key must fit two public words");
    let bits = 8 * p.n;
    // About 113,000 rows a Keccak-f, the inputs and the muxes.
    let mut b = Builder::with_capacity(p.keccak_f() * 113_500 + 8 * p.sig_bytes() + (1 << 20));
    let seed: Bits = (0..bits).map(|_| b.input()).collect();
    let root: Bits = (0..bits).map(|_| b.input()).collect();
    let msg: Bits = (0..8 * MSG_BYTES).map(|_| b.input()).collect();
    let sig: Bits = (0..8 * p.sig_bytes()).map(|_| b.input()).collect();

    let mut hashes = Hashes { b: &mut b, seed: seed.clone(), n: p.n, calls: 0 };
    // `H_msg(R, PK.seed, PK.root, M')`, `M' = 0x00 ‖ 0x00 ‖ M`.
    let randomizer = &sig[..bits];
    let digest = hashes.shake(&[randomizer, &seed, &root, &const_bytes(&[0, 0]), &msg].concat(), p.m);
    let md_bytes = (p.k * p.a).div_ceil(8);
    let tree_bytes = (p.h - p.hp).div_ceil(8);
    let leaf_bytes = p.hp.div_ceil(8);
    let md = &digest[..8 * md_bytes];
    let idx_tree = to_int(&digest[8 * md_bytes..8 * (md_bytes + tree_bytes)])[..p.h - p.hp].to_vec();
    let idx_leaf = to_int(&digest[8 * (md_bytes + tree_bytes)..8 * (md_bytes + tree_bytes + leaf_bytes)])[..p.hp].to_vec();

    let fors_len = bits * p.k * (1 + p.a);
    let mut node = hashes.fors_pk(p, &sig[bits..bits + fors_len], md, &idx_tree, &idx_leaf);
    let xmss_len = bits * (p.len() + p.hp);
    let (mut tree, mut leaf) = (idx_tree, idx_leaf);
    for layer in 0..p.d {
        if layer > 0 {
            leaf = tree[..p.hp].to_vec();
            tree = tree[p.hp..].to_vec();
        }
        let at = bits + fors_len + xmss_len * layer;
        node = hashes.xmss_root(p, layer, &tree, &leaf, &sig[at..at + xmss_len], &node);
    }
    let keccak_f = hashes.calls;
    assert_eq!(bits + fors_len + xmss_len * p.d, sig.len());

    let zero: Bits = (0..bits).map(|i| b.xor(node[i], root[i])).collect();
    assert_eq!(zero.len(), WORD_BITS);
    let public = public_words(&[&seed[..], &root[..]].concat(), &msg);
    Built { builder: b, public, zero, keccak_f }
}

/// The circuit on the fewest rows that hold it, and its Keccak-f calls.
pub fn circuit(p: &Params) -> (Circuit, usize) {
    let Built { builder, public, zero, keccak_f } = build(p);
    let log_rows = builder.len().next_power_of_two().trailing_zeros() as usize;
    (builder.finish_with_zeros(log_rows, &public, &[zero]), keccak_f)
}

/// The quotient statement of a verification: `y` the public key, `root` the message.
pub fn statement(pk: &[u8; 32], msg: &[u8; MSG_BYTES]) -> Statement {
    Statement { y: *pk, root: *msg }
}

/// The free inputs: `PK.seed`, `PK.root`, `M`, then the signature, each byte low bit first.
pub fn inputs(p: &Params, pk: &[u8; 32], msg: &[u8; MSG_BYTES], sig: &[u8]) -> Vec<bool> {
    assert_eq!(sig.len(), p.sig_bytes());
    [&pk[..], &msg[..], sig].concat().iter().flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1 == 1)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;
    use quotient::circuit::read;
    use sha3::digest::{ExtendableOutput, Update, XofReader};

    fn reference(bytes: &[u8], out: usize) -> Vec<u8> {
        let mut h = sha3::Shake256::default();
        h.update(bytes);
        let mut reader = h.finalize_xof();
        let mut digest = vec![0; out];
        reader.read(&mut digest);
        digest
    }

    /// The circuit's SHAKE256 is the standard one, across block boundaries and paddings.
    #[test]
    fn shake256_matches() {
        let mut rng = Rng::new(0x5A);
        for len in [0, 1, 34, 64, 80, 135, 136, 137, 271, 272, 300] {
            let mut b = Builder::new();
            let msg: Bits = (0..8 * len).map(|_| b.input()).collect();
            let out = shake256(&mut b, &msg, 30);
            let log_rows = b.len().next_power_of_two().trailing_zeros() as usize;
            let circuit = b.finish(log_rows, &std::array::from_fn(|_| vec![Src::Zero; WORD_BITS]));
            let bytes: Vec<u8> = (0..len).map(|_| rng.next_u64() as u8).collect();
            let v = circuit.outputs(&bytes.iter().flat_map(|&x| (0..8).map(move |i| (x >> i) & 1 == 1)).collect::<Vec<_>>());
            let got: Vec<u8> = (0..30).map(|j| (0..8).fold(0u8, |acc, i| acc | read(&v, out[8 * j + i]) << i)).collect();
            assert_eq!(got, reference(&bytes, 30), "length {len}");
        }
    }

    /// The digit helpers: `base_2b`, `toInt`, the comparison and the adder, on constants.
    #[test]
    fn helpers() {
        let value = |bits: &[Src]| bits.iter().enumerate().fold(0u64, |acc, (i, &s)| acc | ((s == Src::One) as u64) << i);
        let bytes = [0b1011_0010u8, 0x5C, 0xF1];
        let x = const_bytes(&bytes);
        let digits: Vec<u64> = base_2b(&x, 4, 6).iter().map(|d| value(d)).collect();
        assert_eq!(digits, [0xB, 0x2, 0x5, 0xC, 0xF, 0x1]);
        let digits: Vec<u64> = base_2b(&x, 6, 4).iter().map(|d| value(d)).collect();
        let all = u32::from_be_bytes([0, bytes[0], bytes[1], bytes[2]]);
        assert_eq!(digits, (0..4).rev().map(|i| ((all >> (6 * i)) & 63) as u64).collect::<Vec<_>>());
        assert_eq!(value(&to_int(&x)), all as u64);
        assert_eq!(value(&be(&konst(0x0102, 16), 4)), u32::from_le_bytes([0, 0, 1, 2]) as u64);

        let mut b = Builder::new();
        let ins: Bits = (0..4).map(|_| b.input()).collect();
        let les: Vec<Src> = (0..16).map(|j| at_most(&mut b, &ins, j)).collect();
        let acc: Bits = (0..12).map(|_| b.input()).collect();
        let sum = add(&mut b, &acc, &ins);
        let circuit = b.finish(17, &std::array::from_fn(|_| vec![Src::Zero; WORD_BITS]));
        for digit in 0..16u64 {
            for a in [0u64, 1, 7, 15, 255, 465, 4000] {
                let inputs: Vec<bool> = (0..4).map(|i| (digit >> i) & 1 == 1).chain((0..12).map(|i| (a >> i) & 1 == 1)).collect();
                let v = circuit.outputs(&inputs);
                for (j, &le) in les.iter().enumerate() {
                    assert_eq!(read(&v, le) == 1, digit <= j as u64, "{digit} <= {j}");
                }
                let got = sum.iter().enumerate().fold(0u64, |acc, (i, &s)| acc | (read(&v, s) as u64) << i);
                assert_eq!(got, (a + digit) % 4096);
            }
        }
    }

    #[test]
    fn sizes() {
        assert_eq!(SHAKE_128S.sig_bytes(), 7_856);
        assert_eq!(SHAKE_128F.sig_bytes(), 17_088);
        assert_eq!(SHAKE_192S.sig_bytes(), 16_224);
        assert_eq!(SHAKE_256S.sig_bytes(), 29_792);
        assert_eq!(SHAKE_256F.sig_bytes(), 49_856);
        let calls: Vec<usize> = ALL.iter().map(Params::keccak_f).collect();
        assert_eq!(calls, [3_959, 11_963, 5_748, 17_421, 8_577, 17_802]);
    }
}
