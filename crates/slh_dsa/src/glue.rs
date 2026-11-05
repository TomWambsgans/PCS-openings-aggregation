// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! SLH-DSA-SHAKE verification at lane granularity: the glue circuit of `SPEC-FAST.md` (design C\*, §4.3–4.5).
//!
//! The statement is [`crate::build`]'s, on `K = GF(2^64)` lanes instead of bits. A lane holds 64 bits of a
//! Keccak state, bit `z` as the coefficient of `x^z` (Flock's packing; a lane is the little-endian `u64` of its 8
//! bytes). The same gate `V = X + C + Y·C` is then an XOR (`Y = 0`), a copy (`Y = 1`) and, with `Y` a bit, a lane
//! mux; bits are cells only where SLH-DSA reads bits: the digest, the layer messages (their digits and checksum),
//! the index bits, and the final root.
//!
//! **Keccak-f is not computed here.** Every call is a block of the port region ([`port_index`]): its 25 input lanes
//! are the `C` cells of its port rows, wired to their sources, and its 25 output lanes their `X = V` cells, free
//! values the prover supplies (Flock proves them, and the link ties the region to Flock's words). An output the
//! circuit reads as bits is *unpacked*: its port's `X` reads `Σ b_i x^i` of 64 free bits instead of itself, so
//! the port's value is the packing of those bits.
//!
//! **The gadgets** (rows): a packing `Σ b_i x^i` of `k` variable bits is `k` rows from a cached constant start
//! ([`G::pack`]); an unpacking is 64 free bits and their packing; the WOTS+ step is `F`, `at_most(digit, j)` and
//! [`crate::select`] on the two lanes; an authentication-path level is [`crate::ordered`] on two lanes; a sponge
//! block after the first XORs the next message lanes into the rate. `ADRS` is [`crate::Adrs`]'s 32 bytes, packed
//! lane by lane (identical packings are shared).

use std::collections::HashMap;

use primitives::field::F64;
use primitives::hash::{STATE_LANES, keccak_f};
use quotient::circuit::{Builder, Circuit, PUBLIC_ROWS, Src, WORD_BITS, public_words, read_k};

use super::{
    Adrs, Bits, FORS_ROOTS, FORS_TREE, LG_W, MSG_BYTES, Params, RATE, TREE, WOTS_HASH, WOTS_PK, add, at_most,
    base_2b, const_bytes, konst, ordered, select, to_int,
};

/// The glue's rows: `2^18`, the port region the upper half.
pub const LOG_ROWS: usize = 18;
/// Port quads a block (a Keccak-f call): 25 lanes, the constant `x` (quad 25), six zero quads.
pub const QUADS: usize = 32;
/// Keccak-f blocks: 4,096 (3,959 calls of SLH-DSA-SHAKE-128s, the rest Keccak-f(0)).
pub const BLOCKS: usize = 4096;
/// The port region's first row: `2^17`, so the region is the aligned half `[2^17, 2^18)`.
pub const PORT_START: usize = 1 << 17;
/// The quad holding `x`, which the glue takes from block 0.
pub const X_QUAD: usize = 25;
/// Rate lanes of SHAKE256.
const RATE_LANES: usize = RATE / 8;

/// The port layout (`SPEC-FAST.md` §4.5): quad `q` of block `b` is port `32 b + q`, the row
/// `PORT_START + 32 b + q`. The quads of a block:
/// - `q < 25`: `(X, Y, C, V) = (O_q, 1, I_q, O_q)`, output lane `q` (free, or the packing of its unpacked bits)
///   and input lane `q`;
/// - `q = 25`: `(x, 1, 0, x)`, `x` free (Flock pins it);
/// - `26 ≤ q < 32`: `(0, 1, 0, 0)`.
///
/// Changing the layout is changing this function (and [`PORT_START`], [`QUADS`]).
pub const fn port_index(block: usize, quad: usize) -> usize {
    QUADS * block + quad
}

/// Two lanes: a value of `n = 16` bytes.
pub type Node = [Src; 2];

/// How the prover fills a free row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hint {
    /// Bit `k` of the public input `PK.seed ‖ PK.root ‖ M`, each byte low bit first.
    Public(u32),
    /// Lane `k` of the lane inputs (the signature: bytes `8k..8k + 8`, little-endian).
    Lane(u32),
    /// The constant `x` (quad 25 of every block).
    X,
    /// Output lane `lane` of Keccak-f call `call`.
    Out { call: u32, lane: u8 },
    /// Bit `bit` of output lane `lane` of call `call`.
    OutBit { call: u32, lane: u8, bit: u8 },
}

/// The gadgets a row is counted under, in report order.
pub const GADGETS: [&str; 12] = [
    "public rows",
    "inputs (PK, M bits; signature lanes)",
    "x powers and constant lanes",
    "public bits -> seed, root, M lanes",
    "ADRS packing",
    "unpacking (digest, layer messages, final root)",
    "WOTS+ at_most(digit, j)",
    "WOTS+ step mux",
    "WOTS+ checksum",
    "auth-path swap",
    "sponge continuation XORs",
    "root comparison (word 6)",
];

/// The glue under construction: a [`Builder`] with a port region, the prover's hints, and caches.
pub struct G {
    pub b: Builder,
    hints: HashMap<u32, Hint>,
    /// `x^0 .. x^63`.
    pows: Vec<Src>,
    consts: HashMap<u64, Src>,
    packs: HashMap<Vec<Src>, Src>,
    /// Each call's input lanes, in block order.
    calls: Vec<[Src; STATE_LANES]>,
    blocks: usize,
    seed: Node,
    tally: [usize; GADGETS.len()],
    gadget: usize,
    mark: usize,
}

impl G {
    /// A glue builder whose port region of `blocks` blocks starts at row `port_start`: every block's quads 25–31
    /// placed, `x` taken from block 0.
    pub fn new(port_start: usize, blocks: usize) -> Self {
        let mut g = Self {
            b: Builder::with_ports(port_start, port_start, QUADS * blocks),
            hints: HashMap::new(),
            pows: Vec::with_capacity(64),
            consts: HashMap::new(),
            packs: HashMap::new(),
            calls: Vec::new(),
            blocks,
            seed: [Src::Zero; 2],
            tally: [0; GADGETS.len()],
            gadget: 0,
            mark: 0,
        };
        g.tally[0] = PUBLIC_ROWS;
        g.mark = g.b.len();
        for block in 0..blocks {
            let x = g.b.port(port_index(block, X_QUAD), None, Src::Zero);
            g.hint(x, Hint::X);
            for q in X_QUAD + 1..QUADS {
                g.b.port(port_index(block, q), Some(Src::Zero), Src::Zero);
            }
        }
        let x = Src::Row(g.b.port_row(port_index(0, X_QUAD)));
        g.at(2);
        g.pows.extend([Src::One, x]);
        for i in 2..64 {
            let next = g.b.mul(g.pows[i - 1], x);
            g.pows.push(next);
        }
        g
    }

    fn hint(&mut self, src: Src, hint: Hint) {
        let Src::Row(r) = src else { panic!("a constant hinted") };
        assert!(self.hints.insert(r, hint).is_none());
    }

    /// Count the rows built since the last switch, then count under `gadget`; returns the previous one.
    fn at(&mut self, gadget: usize) -> usize {
        let now = self.b.len();
        self.tally[self.gadget] += now - self.mark;
        self.mark = now;
        std::mem::replace(&mut self.gadget, gadget)
    }

    /// A free bit, filled by `hint`.
    pub fn bit(&mut self, hint: Hint) -> Src {
        let bit = self.b.input();
        self.hint(bit, hint);
        bit
    }

    /// A free lane, filled by `hint`.
    pub fn lane(&mut self, hint: Hint) -> Src {
        let lane = self.b.free_k();
        self.hint(lane, hint);
        lane
    }

    /// The constant lane `Σ_{bit i of value} x^i`: the XOR of a smaller cached constant and a power, or of the
    /// constants of its lowest bytes and its top byte, so constants that share bytes share rows.
    pub fn kconst(&mut self, value: u64) -> Src {
        if value == 0 {
            return Src::Zero;
        }
        if value.is_power_of_two() {
            return self.pows[value.trailing_zeros() as usize];
        }
        if let Some(&src) = self.consts.get(&value) {
            return src;
        }
        let before = self.at(2);
        let top_bit = 63 - value.leading_zeros() as usize;
        let below = value & ((1u64 << (top_bit & !7)) - 1);
        let (low, high) = if below != 0 {
            // Bytes below the top one: their constant ⊕ the top byte's.
            (below, value ^ below)
        } else {
            // One byte: the constant without its top bit ⊕ that bit.
            (value ^ 1 << top_bit, 1 << top_bit)
        };
        let (low, high) = (self.kconst(low), self.kconst(high));
        let src = self.b.xor(low, high);
        self.at(before);
        self.consts.insert(value, src);
        src
    }

    /// The lane `Σ b_i x^i` of 64 bits (constants or bit cells). With `k` variable bits it is `k` rows from the
    /// constant `K0 = Σ_{b_i = 1 or variable} x^i`: the row `(acc, b_i, x^i)` gives `acc + x^i + b_i x^i`.
    /// Identical packings are one.
    pub fn pack(&mut self, bits: &[Src]) -> Src {
        assert_eq!(bits.len(), 64);
        let mask = |keep: fn(Src) -> bool| (0..64).filter(|&i| keep(bits[i])).fold(0u64, |acc, i| acc | 1 << i);
        if bits.iter().all(|&s| matches!(s, Src::Zero | Src::One)) {
            return self.kconst(mask(|s| s == Src::One));
        }
        if let Some(&src) = self.packs.get(bits) {
            return src;
        }
        let mut acc = self.kconst(mask(|s| s != Src::Zero));
        for (i, &bit) in bits.iter().enumerate() {
            if let Src::Row(_) = bit {
                acc = self.b.row(acc, bit, self.pows[i]);
            }
        }
        self.packs.insert(bits.to_vec(), acc);
        acc
    }

    /// One Keccak-f call, the next block: its input lanes wired to `input`, its output lanes free, those in
    /// `unpack` the packings of 64 free bits each (returned, low bit first).
    pub fn keccak(&mut self, input: [Src; STATE_LANES], unpack: &[usize]) -> ([Src; STATE_LANES], Vec<Bits>) {
        let call = self.calls.len();
        assert!(call < self.blocks, "more than {} Keccak-f calls", self.blocks);
        let before = self.at(5);
        let mut packed = [None; STATE_LANES];
        let mut bits = Vec::with_capacity(unpack.len());
        for &lane in unpack {
            let lane_bits: Bits = (0..64)
                .map(|bit| self.bit(Hint::OutBit { call: call as u32, lane: lane as u8, bit: bit as u8 }))
                .collect();
            packed[lane] = Some(self.pack(&lane_bits));
            bits.push(lane_bits);
        }
        self.at(before);
        let out = std::array::from_fn(|q| {
            let o = self.b.port(port_index(call, q), packed[q], input[q]);
            if packed[q].is_none() {
                self.hint(o, Hint::Out { call: call as u32, lane: q as u8 });
            }
            o
        });
        self.calls.push(input);
        (out, bits)
    }

    /// SHAKE256 of whole lanes (`8 · msg.len()` bytes), absorbed block by block: a block after the first XORs its
    /// rate lanes into the previous output and copies the capacity. The last call's lanes `unpack` are unpacked.
    pub fn sponge(&mut self, msg: &[Src], unpack: &[usize]) -> ([Src; STATE_LANES], Vec<Bits>) {
        let blocks = 8 * msg.len() / RATE + 1;
        let mut padded = msg.to_vec();
        padded.resize(RATE_LANES * blocks, Src::Zero);
        let last = RATE_LANES * blocks - 1;
        // The domain and the first padding bit, 0x1F, then the last bit, 0x80, of the last block.
        let (first, end) = if msg.len() == last { (0x1F | 1 << 63, 0) } else { (0x1F, 1 << 63) };
        padded[msg.len()] = self.kconst(first);
        if end != 0 {
            padded[last] = self.kconst(end);
        }
        let mut state = [Src::Zero; STATE_LANES];
        let mut bits = vec![];
        for block in 0..blocks {
            let before = self.at(10);
            let input = std::array::from_fn(|i| {
                if i < RATE_LANES { self.b.xor(state[i], padded[RATE_LANES * block + i]) } else { state[i] }
            });
            self.at(before);
            (state, bits) = self.keccak(input, if block + 1 == blocks { unpack } else { &[] });
        }
        (state, bits)
    }

    /// `ADRS`'s four lanes.
    fn adrs(&mut self, adrs: &Adrs) -> [Src; 4] {
        let bits = adrs.bits();
        let before = self.at(4);
        let lanes = std::array::from_fn(|l| self.pack(&bits[64 * l..64 * (l + 1)]));
        self.at(before);
        lanes
    }

    /// `F`, `H` and `T_l`: `SHAKE256(PK.seed ‖ ADRS ‖ M, 8n)`, the parts whole nodes. With `unpack`, also the
    /// value's 128 bits.
    fn t(&mut self, adrs: &Adrs, parts: &[Node], unpack: bool) -> (Node, Bits) {
        let adrs = self.adrs(adrs);
        let msg: Vec<Src> = self.seed.iter().chain(&adrs).chain(parts.iter().flatten()).copied().collect();
        let (out, bits) = self.sponge(&msg, if unpack { &[0, 1] } else { &[] });
        ([out[0], out[1]], bits.concat())
    }

    /// WOTS+ (FIPS 205, Algorithm 8), as [`crate::Hashes::wots_pk`], on lanes.
    fn wots_pk(&mut self, p: &Params, sig: &[Node], msg: &[Src], adrs: &Adrs) -> Node {
        let mut digits = base_2b(msg, LG_W, p.len1());
        let before = self.at(8);
        let mut csum = konst(0, 12);
        for digit in &digits {
            let complement: Bits = digit.iter().map(|&bit| self.b.not(bit)).collect();
            csum = add(&mut self.b, &csum, &complement);
        }
        self.at(before);
        digits.extend([8, 4, 0].map(|low| csum[low..low + 4].to_vec()));
        let mut tops = Vec::with_capacity(p.len());
        for (i, digit) in digits.iter().enumerate() {
            let mut at = adrs.clone();
            at.word2 = konst(i as u64, 32);
            let mut tmp = sig[i];
            for j in 0..(1 << LG_W) - 1 {
                at.word3 = konst(j as u64, 32);
                let (next, _) = self.t(&at, &[tmp], false);
                let before = self.at(6);
                let applied = at_most(&mut self.b, digit, j);
                self.at(7);
                tmp = select(&mut self.b, applied, &tmp, &next).try_into().unwrap();
                self.at(before);
            }
            tops.push(tmp);
        }
        let mut pk = adrs.clone();
        pk.kind = WOTS_PK;
        self.t(&pk, &tops, false).0
    }

    /// An authentication-path level: `(node, auth)` ordered by `bit`, then `H`.
    fn level(&mut self, adrs: &Adrs, bit: Src, node: Node, auth: Node, unpack: bool) -> (Node, Bits) {
        let before = self.at(9);
        let (left, right) = ordered(&mut self.b, bit, &node, &auth);
        self.at(before);
        self.t(adrs, &[left.try_into().unwrap(), right.try_into().unwrap()], unpack)
    }

    /// An XMSS root from a signature of `msg` at leaf `leaf` (FIPS 205, Algorithm 11), and its bits.
    fn xmss_root(&mut self, p: &Params, layer: usize, tree: &[Src], leaf: &[Src], sig: &[Node], msg: &[Src])
    -> (Node, Bits) {
        let (wots_sig, auth) = sig.split_at(p.len());
        let mut adrs = Adrs::new(layer, tree, WOTS_HASH);
        adrs.key_pair = leaf.to_vec();
        let mut node = self.wots_pk(p, wots_sig, msg, &adrs);
        let mut bits = vec![];
        for k in 0..p.hp {
            let mut at = Adrs::new(layer, tree, TREE);
            at.word2 = konst(k as u64 + 1, 32);
            at.word3 = leaf[k + 1..].to_vec();
            (node, bits) = self.level(&at, leaf[k], node, auth[k], k + 1 == p.hp);
        }
        (node, bits)
    }

    /// The FORS public key from a signature of `md` (FIPS 205, Algorithm 17), and its bits.
    fn fors_pk(&mut self, p: &Params, sig: &[Node], md: &[Src], tree: &[Src], leaf: &[Src]) -> (Node, Bits) {
        let indices = base_2b(md, p.a, p.k);
        let mut roots = Vec::with_capacity(p.k);
        for (i, index) in indices.iter().enumerate() {
            let part = &sig[(1 + p.a) * i..(1 + p.a) * (i + 1)];
            let at = |t: usize| {
                let mut adrs = Adrs::new(0, tree, FORS_TREE);
                adrs.key_pair = leaf.to_vec();
                adrs.word2 = konst(t as u64, 32);
                adrs.word3 = [&index[t..], &konst(i as u64, 8)[..]].concat();
                adrs
            };
            let mut node = self.t(&at(0), &[part[0]], false).0;
            for j in 0..p.a {
                node = self.level(&at(j + 1), index[j], node, part[1 + j], false).0;
            }
            roots.push(node);
        }
        let mut adrs = Adrs::new(0, tree, FORS_ROOTS);
        adrs.key_pair = leaf.to_vec();
        self.t(&adrs, &roots, true)
    }

    /// The remaining blocks as Keccak-f(0) (inputs the constant 0, outputs free), then the circuit on
    /// `2^log_rows` rows.
    pub fn finish(mut self, log_rows: usize, public: &[Vec<Src>; 4], zeros: &[Vec<Src>]) -> Glue {
        let used_calls = self.calls.len();
        while self.calls.len() < self.blocks {
            self.keccak([Src::Zero; STATE_LANES], &[]);
        }
        self.at(0);
        let main_rows = self.b.len();
        let rows = GADGETS.iter().copied().zip(self.tally).collect();
        Glue {
            circuit: self.b.finish_with_zeros(log_rows, public, zeros),
            hints: self.hints,
            calls: self.calls,
            used_calls,
            main_rows,
            rows,
            digest: vec![],
            roots: vec![],
            zero: vec![],
        }
    }
}

/// The glue circuit, the prover's hints, and taps.
pub struct Glue {
    pub circuit: Circuit,
    hints: HashMap<u32, Hint>,
    /// Each block's input lanes (the padding blocks' are zero).
    pub calls: Vec<[Src; STATE_LANES]>,
    /// The blocks that are SLH-DSA's Keccak-f calls; the rest are Keccak-f(0).
    pub used_calls: usize,
    /// Rows below the port region (the public ones included).
    pub main_rows: usize,
    /// Rows below the port region by gadget, in [`GADGETS`] order.
    pub rows: Vec<(&'static str, usize)>,
    /// `H_msg`'s digest, `8 m` bits.
    pub digest: Bits,
    /// The FORS public key, then each layer's root: `d + 1` values of 128 bits.
    pub roots: Vec<Bits>,
    /// `computed root ⊕ PK.root`: public word 6.
    pub zero: Bits,
}

/// Why a witness of the glue fails.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlueError {
    /// A gate or a wire ([`Circuit::check_k`]).
    Cells(quotient::circuit::CheckError),
    /// A port quad is not of its form, or block `b`'s outputs are not Keccak-f of its inputs.
    Port(usize),
}

impl Glue {
    /// Every row's output, the prover's honest witness: `public` the bits of `PK.seed ‖ PK.root ‖ M`, `lanes` the
    /// lane inputs, every Keccak-f output computed from its call's inputs.
    pub fn outputs(&self, public: &[bool], lanes: &[u64]) -> Vec<F64> {
        let mut states: Vec<Option<[u64; STATE_LANES]>> = vec![None; self.calls.len()];
        self.circuit.outputs_k(|r, v| match self.hints[&r] {
            Hint::Public(k) => F64(public[k as usize] as u64),
            Hint::Lane(k) => F64(lanes[k as usize]),
            Hint::X => F64::G,
            Hint::Out { call, lane } => F64(self.state(&mut states, call as usize, v)[lane as usize]),
            Hint::OutBit { call, lane, bit } => {
                F64(self.state(&mut states, call as usize, v)[lane as usize] >> bit & 1)
            }
        })
    }

    fn state(&self, states: &mut [Option<[u64; STATE_LANES]>], call: usize, v: &[F64]) -> [u64; STATE_LANES] {
        *states[call].get_or_insert_with(|| {
            let mut state = self.calls[call].map(|src| read_k(v, src).0);
            keccak_f(&mut state);
            state
        })
    }

    /// The checks the rest of π1 makes of the port region, made directly: every quad of its form (`(O, 1, I, O)`,
    /// `(x, 1, 0, x)`, `(0, 1, 0, 0)`), and every block's outputs Keccak-f of its inputs.
    pub fn check_ports(&self, cells: &[F64]) -> Result<(), GlueError> {
        let (start, _) = self.circuit.port_region;
        let quad = |block: usize, q: usize| {
            let r = start + port_index(block, q);
            [0, 1, 2, 3].map(|role| cells[4 * r + role])
        };
        for block in 0..self.calls.len() {
            let mut state = [0u64; STATE_LANES];
            for (q, lane) in state.iter_mut().enumerate() {
                let [x, y, c, v] = quad(block, q);
                if x != v || y != F64::ONE {
                    return Err(GlueError::Port(block));
                }
                *lane = c.0;
            }
            keccak_f(&mut state);
            let forms = (0..STATE_LANES).all(|q| quad(block, q)[3] == F64(state[q]))
                && quad(block, X_QUAD) == [F64::G, F64::ONE, F64::ZERO, F64::G]
                && (X_QUAD + 1..QUADS).all(|q| quad(block, q) == [F64::ZERO, F64::ONE, F64::ZERO, F64::ZERO]);
            if !forms {
                return Err(GlueError::Port(block));
            }
        }
        Ok(())
    }

    /// The cells of the honest witness, checked: the gates and wires ([`Circuit::check_k`]) and the ports.
    pub fn witness(&self, public: &[bool], lanes: &[u64]) -> Result<Vec<F64>, GlueError> {
        let cells = self.circuit.cells_k(&self.outputs(public, lanes));
        self.circuit.check_k(&cells).map_err(GlueError::Cells)?;
        self.check_ports(&cells)?;
        Ok(cells)
    }

    /// Bit `j` of public word `word`, from the cells: the public rows' `X` (even `j`) and `Y` (odd `j`) cells.
    pub fn public_bit(cells: &[F64], word: usize, j: usize) -> u64 {
        cells[4 * (word * (WORD_BITS / 2) + j / 2) + (j % 2)].0
    }
}

/// The glue of `p` (`n = 16`): free bits `PK.seed ‖ PK.root ‖ M` ([`Hint::Public`]), free lanes the signature
/// ([`Hint::Lane`]), public words 0–3 the statement and word 6 `root ⊕ PK.root`.
pub fn build(p: &Params) -> Glue {
    assert_eq!(p.n, 16, "nodes of two lanes");
    assert!(p.keccak_f() <= BLOCKS && p.h - p.hp <= 64);
    let bits = 8 * p.n;
    let mut g = G::new(PORT_START, BLOCKS);

    g.at(1);
    let mut public = (0..2 * bits + 8 * MSG_BYTES).map(|k| g.bit(Hint::Public(k as u32)));
    let seed: Bits = public.by_ref().take(bits).collect();
    let root: Bits = public.by_ref().take(bits).collect();
    let msg: Bits = public.collect();
    let sig: Vec<Src> = (0..p.sig_bytes() / 8).map(|k| g.lane(Hint::Lane(k as u32))).collect();
    let sig: Vec<Node> = sig.chunks(2).map(|pair| [pair[0], pair[1]]).collect();

    // `H_msg(R, PK.seed, PK.root, M')`: lanes 0–1 `R`, 2–3 the seed, 4–5 `PK.root`, then the bytes 48..88 of
    // `0x0000 ‖ M ‖ 0x1F ‖ 0…`, the last rate lane `0x80 << 56`; one block.
    g.at(3);
    let packed: Vec<Src> = [&seed, &root].iter().flat_map(|v| v.chunks(64)).map(|lane| g.pack(lane)).collect();
    g.seed = [packed[0], packed[1]];
    let tail = [const_bytes(&[0, 0]), msg.clone(), const_bytes(&[0x1F]), const_bytes(&[0; 5])].concat();
    assert!(3 * p.n + 2 + MSG_BYTES < RATE && tail.len() == 5 * 64);
    let tail: Vec<Src> = tail.chunks(64).map(|lane| g.pack(lane)).collect();
    let mut input = [Src::Zero; STATE_LANES];
    input[..2].copy_from_slice(&sig[0]);
    input[2..6].copy_from_slice(&packed);
    input[6..11].copy_from_slice(&tail);
    input[RATE_LANES - 1] = g.kconst(1 << 63);
    let digest_lanes: Vec<usize> = (0..p.m.div_ceil(8)).collect();
    let (_, digest) = g.keccak(input, &digest_lanes);
    let digest: Bits = digest.concat()[..8 * p.m].to_vec();

    let md_bytes = (p.k * p.a).div_ceil(8);
    let tree_bytes = (p.h - p.hp).div_ceil(8);
    let leaf_bytes = p.hp.div_ceil(8);
    let md = &digest[..8 * md_bytes];
    let idx_tree = to_int(&digest[8 * md_bytes..8 * (md_bytes + tree_bytes)])[..p.h - p.hp].to_vec();
    let leaf_at = 8 * (md_bytes + tree_bytes);
    let idx_leaf = to_int(&digest[leaf_at..leaf_at + 8 * leaf_bytes])[..p.hp].to_vec();

    let fors_len = p.k * (1 + p.a);
    let (_, mut node) = g.fors_pk(p, &sig[1..1 + fors_len], md, &idx_tree, &idx_leaf);
    let mut roots = vec![node.clone()];
    let xmss_len = p.len() + p.hp;
    let (mut tree, mut leaf) = (idx_tree, idx_leaf);
    for layer in 0..p.d {
        if layer > 0 {
            leaf = tree[..p.hp].to_vec();
            tree = tree[p.hp..].to_vec();
        }
        let at = 1 + fors_len + xmss_len * layer;
        node = g.xmss_root(p, layer, &tree, &leaf, &sig[at..at + xmss_len], &node).1;
        roots.push(node.clone());
    }
    assert_eq!(1 + fors_len + xmss_len * p.d, sig.len());
    assert_eq!(g.calls.len(), p.keccak_f());

    g.at(11);
    let zero: Bits = (0..bits).map(|i| g.b.xor(node[i], root[i])).collect();
    assert_eq!(zero.len(), WORD_BITS);
    let public = public_words(&[&seed[..], &root[..]].concat(), &msg);
    let mut glue = g.finish(LOG_ROWS, &public, std::slice::from_ref(&zero));
    assert!(glue.main_rows <= PORT_START, "{} rows below the ports", glue.main_rows);
    glue.digest = digest;
    glue.roots = roots;
    glue.zero = zero;
    glue
}

/// The public bits `PK.seed ‖ PK.root ‖ M`, each byte low bit first, and the signature's lanes.
pub fn inputs(p: &Params, pk: &[u8; 32], msg: &[u8; MSG_BYTES], sig: &[u8]) -> (Vec<bool>, Vec<u64>) {
    assert_eq!(sig.len(), p.sig_bytes());
    let bytes = [&pk[..], &msg[..]].concat();
    let public = bytes.iter().flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1 == 1)).collect();
    let lanes = sig.chunks(8).map(|lane| u64::from_le_bytes(lane.try_into().unwrap())).collect();
    (public, lanes)
}

/// The value of 128 bit cells (low bit first) as 16 bytes, from the row outputs.
pub fn read_bytes(v: &[F64], bits: &[Src]) -> Vec<u8> {
    let byte = |bits: &[Src]| bits.iter().enumerate().fold(0u8, |acc, (i, &s)| acc | (read_k(v, s).0 as u8) << i);
    bits.chunks(8).map(byte).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;
    use sha3::digest::{ExtendableOutput, Update, XofReader};

    /// A small glue: the port region of `blocks` blocks at row 2^12, on 2^13 rows.
    fn small(blocks: usize) -> G {
        G::new(1 << 12, blocks)
    }

    fn close(g: G) -> Glue {
        g.finish(13, &std::array::from_fn(|_| vec![Src::Zero; WORD_BITS]), &[])
    }

    /// Free bits `Public(from..)`.
    fn bits(g: &mut G, n: usize, from: usize) -> Bits {
        (from..from + n).map(|k| g.bit(Hint::Public(k as u32))).collect()
    }

    /// Free lanes `Lane(from..)`.
    fn lanes(g: &mut G, n: usize, from: usize) -> Vec<Src> {
        (from..from + n).map(|k| g.lane(Hint::Lane(k as u32))).collect()
    }

    /// The honest outputs, checked.
    fn run(glue: &Glue, public: &[bool], lanes: &[u64]) -> Vec<F64> {
        glue.witness(public, lanes).expect("the honest witness holds");
        glue.outputs(public, lanes)
    }

    fn value(v: &[F64], src: Src) -> u64 {
        read_k(v, src).0
    }

    /// Constant lanes are their bits' sums of powers of `x`; packings of bits (some constant, some variable) are
    /// `Σ b_i x^i`; equal packings are shared.
    #[test]
    fn constants_and_packing() {
        let mut rng = Rng::new(0x61);
        let constants: Vec<u64> = [0, 1, 2, 0x1F, 1 << 63, 0x1F | 1 << 63, u64::MAX, 0x0300_0000_0100_0000]
            .into_iter()
            .chain((0..40).map(|_| rng.next_u64() >> (rng.next_u64() % 64)))
            .collect();
        let mut g = small(1);
        let k: Vec<Src> = constants.iter().map(|&c| g.kconst(c)).collect();
        assert_eq!(g.kconst(constants[7]), k[7], "cached");
        let free = bits(&mut g, 64 * 4, 0);
        // Lane `l`: bit `i` free where `(i + l) % 3 != 0`, else the constant bit of a random value.
        let fixed: Vec<u64> = (0..4).map(|_| rng.next_u64()).collect();
        let layout: Vec<Bits> = (0..4)
            .map(|l| {
                (0..64)
                    .map(|i| {
                        if (i + l) % 3 != 0 {
                            free[64 * l + i]
                        } else if fixed[l] >> i & 1 == 1 {
                            Src::One
                        } else {
                            Src::Zero
                        }
                    })
                    .collect()
            })
            .collect();
        let packed: Vec<Src> = layout.iter().map(|lane| g.pack(lane)).collect();
        let before = g.b.len();
        assert_eq!(g.pack(&layout[2]), packed[2]);
        assert_eq!(g.b.len(), before, "a repeated packing is free");
        let glue = close(g);
        for _ in 0..4 {
            let public: Vec<bool> = (0..256).map(|_| rng.next_u64() & 1 == 1).collect();
            let v = run(&glue, &public, &[]);
            for (c, &src) in constants.iter().zip(&k) {
                assert_eq!(value(&v, src), *c);
            }
            for (l, lane) in layout.iter().enumerate() {
                let expected = (0..64).fold(0u64, |acc, i| {
                    let bit = match lane[i] {
                        Src::One => 1,
                        Src::Zero => 0,
                        _ => public[64 * l + i] as u64,
                    };
                    acc | bit << i
                });
                assert_eq!(value(&v, packed[l]), expected, "lane {l}");
            }
        }
    }

    /// The lane mux ([`select`]) and the authentication-path swap ([`ordered`]) on lanes, the control a bit.
    #[test]
    fn mux_and_swap() {
        let mut g = small(1);
        let ab = lanes(&mut g, 4, 0);
        let s = bits(&mut g, 1, 0)[0];
        let muxed = select(&mut g.b, s, &ab[..2], &ab[2..]);
        let (left, right) = ordered(&mut g.b, s, &ab[..2], &ab[2..]);
        let glue = close(g);
        let mut rng = Rng::new(0x62);
        for bit in [false, true, false, true] {
            let l: Vec<u64> = (0..4).map(|_| rng.next_u64()).collect();
            let v = run(&glue, &[bit], &l);
            let got = |srcs: &[Src]| srcs.iter().map(|&s| value(&v, s)).collect::<Vec<_>>();
            let (node, auth) = (&l[..2], &l[2..]);
            assert_eq!(got(&muxed), if bit { auth } else { node });
            assert_eq!(got(&left), if bit { auth } else { node });
            assert_eq!(got(&right), if bit { node } else { auth });
        }
    }

    /// `ADRS`'s lanes are the little-endian words of its 32 bytes, for each address type's fields.
    #[test]
    fn adrs_packing() {
        let mut rng = Rng::new(0x63);
        let mut g = small(1);
        let tree = bits(&mut g, 54, 0);
        let leaf = bits(&mut g, 9, 54);
        let index = bits(&mut g, 12, 63);
        let mut wots = Adrs::new(3, &tree[9 * 3..], WOTS_HASH);
        wots.key_pair = leaf.clone();
        wots.word2 = konst(17, 32);
        wots.word3 = konst(14, 32);
        let mut node = Adrs::new(6, &tree[9 * 6..], TREE);
        node.word2 = konst(4, 32);
        node.word3 = leaf[4..].to_vec();
        let mut fors = Adrs::new(0, &tree, FORS_TREE);
        fors.key_pair = leaf.clone();
        fors.word2 = konst(5, 32);
        fors.word3 = [&index[5..], &konst(9, 8)[..]].concat();
        let mut roots = Adrs::new(0, &tree, FORS_ROOTS);
        roots.key_pair = leaf.clone();
        let cases = [wots, node, fors, roots];
        let packed: Vec<[Src; 4]> = cases.iter().map(|a| g.adrs(a)).collect();
        let glue = close(g);
        for _ in 0..4 {
            let (t, l, i) = (rng.next_u64() >> 10, rng.next_u64() & 511, rng.next_u64() & 4095);
            let public: Vec<bool> = (0..54)
                .map(|k| t >> k & 1 == 1)
                .chain((0..9).map(|k| l >> k & 1 == 1))
                .chain((0..12).map(|k| i >> k & 1 == 1))
                .collect();
            let v = run(&glue, &public, &[]);
            // (layer, key pair, word 2, word 3) of each case.
            let fields = [(3u64, l, 17, 14), (6, 0, 4, l >> 4), (0, l, 5, (9 << 12 | i) >> 5), (0, l, 0, 0)];
            for ((adrs, (layer, key_pair, word2, word3)), lanes) in cases.iter().zip(fields).zip(&packed) {
                let mut bytes = Vec::with_capacity(32);
                bytes.extend((layer as u32).to_be_bytes());
                bytes.extend([0u8; 4]);
                bytes.extend((t >> (9 * layer)).to_be_bytes());
                bytes.extend((adrs.kind as u32).to_be_bytes());
                bytes.extend((key_pair as u32).to_be_bytes());
                bytes.extend((word2 as u32).to_be_bytes());
                bytes.extend((word3 as u32).to_be_bytes());
                for (k, &lane) in lanes.iter().enumerate() {
                    let expected = u64::from_le_bytes(bytes[8 * k..8 * k + 8].try_into().unwrap());
                    assert_eq!(value(&v, lane), expected, "type {} lane {k}", adrs.kind);
                }
            }
        }
    }

    /// The lane sponge is SHAKE256 across block boundaries and paddings (the continuation XORs, the copied
    /// capacity), and an unpacked output's bits are the output's.
    #[test]
    fn sponge_continuation() {
        let mut rng = Rng::new(0x64);
        let sizes = [0usize, 1, 8, 16, 17, 18, 33, 34, 35, 76];
        let mut g = small(24);
        let mut from = 0;
        let mut outs = vec![];
        for &n in &sizes {
            let msg = lanes(&mut g, n, from);
            from += n;
            outs.push(g.sponge(&msg, &[0, 3]));
        }
        assert_eq!(g.calls.len(), sizes.iter().map(|n| 8 * n / RATE + 1).sum::<usize>());
        let glue = close(g);
        let l: Vec<u64> = (0..from).map(|_| rng.next_u64()).collect();
        let v = run(&glue, &[], &l);
        let mut at = 0;
        for (&n, (out, bits)) in sizes.iter().zip(&outs) {
            let bytes: Vec<u8> = l[at..at + n].iter().flat_map(|w| w.to_le_bytes()).collect();
            at += n;
            let mut h = sha3::Shake256::default();
            h.update(&bytes);
            let mut digest = [0u8; 32];
            h.finalize_xof().read(&mut digest);
            let expected: Vec<u64> = digest.chunks(8).map(|w| u64::from_le_bytes(w.try_into().unwrap())).collect();
            let got: Vec<u64> = out[..4].iter().map(|&s| value(&v, s)).collect();
            assert_eq!(got, expected, "{n} lanes");
            for (lane, lane_bits) in [0, 3].iter().zip(bits) {
                let unpacked = lane_bits.iter().enumerate().fold(0u64, |acc, (i, &s)| acc | value(&v, s) << i);
                assert_eq!(unpacked, expected[*lane]);
            }
        }
    }

    /// The ports bind: another value at a free output port, or an unpacked bit unlike the output's, still
    /// evaluates the rows but fails the port check (what Flock and the link check); a non-bit in a free bit fails
    /// its gate.
    #[test]
    fn ports_bind_outputs_and_bits() {
        let mut g = small(2);
        let msg = lanes(&mut g, 3, 0);
        let (out, bits) = g.sponge(&msg, &[1]);
        let glue = close(g);
        let l = [1u64, 2, 3];
        let v = glue.outputs(&[], &l);
        let cells = glue.circuit.cells_k(&v);
        assert_eq!(glue.circuit.check_k(&cells), Ok(()));
        assert_eq!(glue.check_ports(&cells), Ok(()));
        let Src::Row(free_out) = out[0] else { unreachable!() };
        let Src::Row(bit) = bits[0][5] else { unreachable!() };
        for row in [free_out, bit] {
            let bad = glue.circuit.outputs_k(|r, _| v[r as usize] + if r == row { F64::ONE } else { F64::ZERO });
            let cells = glue.circuit.cells_k(&bad);
            assert_eq!(glue.circuit.check_k(&cells), Ok(()));
            assert_eq!(glue.check_ports(&cells), Err(GlueError::Port(0)));
        }
        let two = glue.circuit.outputs_k(|r, _| if r == bit { F64(2) } else { v[r as usize] });
        let cells = glue.circuit.cells_k(&two);
        assert_eq!(glue.circuit.check_k(&cells), Err(quotient::circuit::CheckError::Gate(bit as usize)));
    }
}
