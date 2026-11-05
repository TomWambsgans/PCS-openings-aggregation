// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! **π1 of SLH-DSA-SHAKE-128s with a fast prover** (`crates/slh_dsa/SPEC-FAST.md`, design C\*, §4.1, §4.5, §4.6).
//!
//! The statement is `slh_dsa`'s: public `PK.seed ‖ PK.root ‖ M`, secret the signature. Three arguments share one
//! transcript (leanvm_flock_gas's Keccak-256 chain, `KeccakChannel`, so that π2 records it as it records π1-rec3):
//!
//! - **the glue** (`slh_dsa::glue`, `2^18` rows of `quotient::circuit`'s gate over `K = GF(2^64)`), proven by the
//!   quotient argument of `crates/quotient` (its copy and gate identities at one point `t`), restated here as linear
//!   relations on the committed columns ([`verifier`]);
//! - **Flock** on `q_flock`, the 4,096 Keccak-f blocks of `lv42_flock::keccak` (`2^29` bits, `2^23` words);
//! - **the link** (§4.5): the glue's port cells, the upper half `ω_(2^(m-1)) + V_(m-1)` of its cells, are
//!   `q_flock`'s port words, by the identity `W + ℓ_q = Q_link · Z` checked at `t`.
//!
//! The commitments are three stacks ([`layouts`]): `C1 = q_flock ‖ W ‖ Q_link`, `C2 = (h, q, q_gate)` (the quotient
//! table, non-hiding: the signature is not secret), and the setup `σ` (the glue's wiring, a constant the IV binds).
//! One batching sumcheck (π1-rec3's pairs, `FsShape::Rec3`) leaves one point claim per stack, at one point, which
//! [`prover`] opens with leanVM's WHIR as `crates/leanvm_univariate` does.
//!
//! Every column is committed as its `B` coefficients (`leanvm_univariate::stacks`: the multilinear of a column of
//! `2^v` words at `(w_0(t), …, w_(v-1)(t))` is the polynomial at `t`), but `q_flock`, which Flock reads as values.

#![forbid(unsafe_code)]

pub mod prover;
pub mod quotients;
pub mod verifier;

use fiat_shamir::merkle::Hash;
use leanvm_flock_gas::flock_min::{PACKING, Slices, Variant};
use leanvm_flock_gas::transcript::{FsShape, keccak256};
use leanvm_univariate::claims::{Column, Commitment};
use leanvm_univariate::stacks::StackLayout;
use leanvm_univariate::verifier::chunks;

/// Flock's variant: π1-rec3's (skip 3, the slices sent and the lincheck's terminal checked by the circuit, the
/// zerocheck's eq point by squares, the batching sumcheck in narrow pairs).
pub const FLOCK: Variant = Variant {
    skip: 3,
    slices: Slices::TowerWalk,
    fs: FsShape::Rec3,
};

/// The quotient argument's public region: the cells of the first `2^REGION` (`crates/quotient`'s `REGION`).
pub const REGION: usize = 11;
/// The degree the public weight adds past the cells (`crates/quotient`'s `PUBLIC_EXCESS`): `11 · 2^10 - 2^11`.
pub const PUBLIC_EXCESS: u64 = 9216;
/// Words of a Keccak-f block (`lv42_flock::keccak::WORDS`) and its port words (`PORT_WORDS`): the port word `4q +
/// role` of block `b` is `q_flock`'s word `b · 2^11 + 4q + role`.
pub const BLOCK_WORD_BITS: usize = lv42_flock::keccak::K_LOG - PACKING;
pub const PORT_WORD_BITS: usize = 7;
const _: () = assert!(1 << PORT_WORD_BITS == lv42_flock::keccak::PORT_WORDS);

/// The sizes a verifier is built for: the glue's rows, the Keccak-f blocks, Flock's variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    pub log_rows: usize,
    pub blocks_log: usize,
    pub flock: Variant,
}

impl Params {
    /// SLH-DSA-SHAKE-128s: `2^18` rows, 4,096 blocks (`slh_dsa::glue`).
    pub const SLH_128S: Self = Self {
        log_rows: 18,
        blocks_log: 12,
        flock: FLOCK,
    };

    /// A small glue for tests: `2^13` rows, 128 blocks (`log_n = 24`, the walked Flock verifier's least).
    pub const TOY: Self = Self {
        log_rows: 13,
        blocks_log: 7,
        flock: FLOCK,
    };

    /// The cells' variables: four cells a row.
    pub fn m(&self) -> usize {
        self.log_rows + 2
    }

    pub fn n(&self) -> usize {
        1 << self.m()
    }

    /// The port region's variables: the cells' upper half.
    pub fn port_vars(&self) -> usize {
        self.m() - 1
    }

    pub fn blocks(&self) -> usize {
        1 << self.blocks_log
    }

    /// The port region's first row (`slh_dsa::glue::PORT_START` at 128s).
    pub fn port_start(&self) -> usize {
        1 << (self.log_rows - 1)
    }

    /// Flock's variables: `k_log = 17` bits a block.
    pub fn flock_log_n(&self) -> usize {
        lv42_flock::keccak::K_LOG + self.blocks_log
    }

    /// `q_flock`'s word variables.
    pub fn qflock_vars(&self) -> usize {
        self.flock_log_n() - PACKING
    }

    /// The layout's constraints: the port region is the upper half of the rows, 32 rows a block; the public region
    /// fits below it; Flock's walked verifier has at least 7 more variables than its block.
    pub fn validate(&self) {
        assert_eq!(slh_dsa::glue::QUADS << self.blocks_log, self.port_start(), "the port region is the rows' upper half");
        assert!(self.m() > REGION + 2, "the public region below the port region");
        assert!(self.blocks_log >= 7, "Flock's walked verifier needs 2^24 bits");
        assert_eq!(self.port_vars(), PORT_WORD_BITS + self.blocks_log);
    }

    /// The copy quotient's coefficients: `(h + P W) d d' + d + d' = q w_m` has degree `4n + 9213`.
    pub fn copy_count(&self) -> u64 {
        3 * self.n() as u64 + PUBLIC_EXCESS - 2
    }

    /// The gate quotient's: `gate(W(x), W(x + 1), W(x + β_1), W(x + β_1 + 1)) = q_gate R` has degree `2n - 2`, `R`
    /// of degree `n/4`.
    pub fn gate_count(&self) -> u64 {
        7 * (self.n() as u64 / 4) - 1
    }

    /// The link's: `W + ℓ_q = Q_link Z`, `ℓ_q` of degree `(m - 1) 2^(m-2)` (a multilinear of `m - 1` coordinate
    /// functionals of degree `2^(m-2)`), `Z` of degree `2^(m-1)`.
    pub fn link_count(&self) -> u64 {
        let m = self.m() as u64;
        (m - 3) * (1 << (m - 2)) + 1
    }

    /// The bytes the IV binds of the parameters.
    pub fn bytes(&self) -> [u8; 4] {
        [self.log_rows as u8, self.blocks_log as u8, self.flock.skip as u8, self.flock.fs as u8]
    }
}

/// `C1`'s columns besides `q_flock`: the glue's cells `W` and the link's quotient `Q_link`, by chunk.
pub const W: Column = Column::Extra {
    commitment: Commitment::C1,
    id: 1,
};

pub fn q_link(chunk: usize) -> Column {
    Column::Extra {
        commitment: Commitment::C1,
        id: 0x10 + chunk as u16,
    }
}

/// `C2`'s columns: the copy argument's sum `h`, its quotient `q` by chunk, the gate's quotient by chunk.
pub const H: Column = Column::Extra {
    commitment: Commitment::C2,
    id: 1,
};

pub fn q_copy(chunk: usize) -> Column {
    Column::Extra {
        commitment: Commitment::C2,
        id: 0x10 + chunk as u16,
    }
}

pub fn q_gate(chunk: usize) -> Column {
    Column::Extra {
        commitment: Commitment::C2,
        id: 0x20 + chunk as u16,
    }
}

/// The setup's column: the wiring `σ`.
pub const SIGMA: Column = Column::Extra {
    commitment: Commitment::Setup,
    id: 1,
};

/// The quotients' chunks (`leanvm_univariate::verifier::chunks`: at most three powers of two): the link's, the
/// copy's, the gate's.
pub fn link_chunks(p: &Params) -> Vec<usize> {
    chunks(p.link_count())
}

pub fn copy_chunks(p: &Params) -> Vec<usize> {
    chunks(p.copy_count())
}

pub fn gate_chunks(p: &Params) -> Vec<usize> {
    chunks(p.gate_count())
}

/// The three stacks' layouts, each with an even number of variables (the batch's pairs end on a stack's end).
pub fn layouts(p: &Params) -> Vec<(Commitment, StackLayout)> {
    p.validate();
    let m = p.m();
    let mut c1 = vec![(Column::Qflock, p.qflock_vars(), false), (W, m, false)];
    c1.extend(link_chunks(p).iter().enumerate().map(|(c, &e)| (q_link(c), e, false)));
    let mut c2 = vec![(H, m, true)];
    c2.extend(copy_chunks(p).iter().enumerate().map(|(c, &e)| (q_copy(c), e, true)));
    c2.extend(gate_chunks(p).iter().enumerate().map(|(c, &e)| (q_gate(c), e, false)));
    let setup = vec![(SIGMA, m, false)];
    let even = |columns: &[(Column, usize, bool)]| {
        let mut layout = StackLayout::new(columns);
        layout.vars += layout.vars & 1;
        layout
    };
    vec![
        (Commitment::C1, even(&c1)),
        (Commitment::C2, even(&c2)),
        (Commitment::Setup, even(&setup)),
    ]
}

/// The protocol's name, the seed's first 16 bytes.
pub const NAME: [u8; 16] = *b"slh-fast-pi1-v01";

/// A stack's `PCS_OPEN` layout word: the parameters (bytes 0..4), the opening's code (22..24), the stack's
/// variables (24) and the words its blocks place (25..32), which WHIR's verifier reads
/// (`leanvm_univariate::prover::opening::verify`).
pub fn layout_word(p: &Params, commitment: Commitment, layout: &StackLayout) -> [u8; 32] {
    let code: u16 = match commitment {
        Commitment::C1 => 0x5101,
        Commitment::C2 => 0x5102,
        Commitment::Setup => 0x5103,
    };
    let placed = layout.words();
    assert!(layout.vars < 256 && placed < 1 << 56);
    let mut word = [0u8; 32];
    word[..4].copy_from_slice(&p.bytes());
    word[22..24].copy_from_slice(&code.to_be_bytes());
    word[24] = layout.vars as u8;
    word[25..].copy_from_slice(&placed.to_be_bytes()[1..]);
    word
}

/// The three layout words, in [`layouts`]' order.
pub fn layout_words(p: &Params) -> Vec<[u8; 32]> {
    layouts(p).iter().map(|(c, l)| layout_word(p, *c, l)).collect()
}

/// The IV: the hash of a tag, the setup's root (the glue's wiring), the parameters and the three layout words. A
/// constant of the verifier.
pub fn iv(p: &Params, setup_root: &Hash) -> [u8; 32] {
    let mut data = b"slh-fast-pi1-iv1".to_vec();
    data.extend_from_slice(setup_root);
    data.extend_from_slice(&p.bytes());
    for word in layout_words(p) {
        data.extend_from_slice(&word);
    }
    keccak256(&data)
}

/// The transcript's seed (§4.1, step 1): `keccak(name ‖ IV ‖ PK.seed ‖ PK.root ‖ M)`, 112 bytes, one Keccak-f.
pub fn seed(iv: &[u8; 32], pk: &[u8; 32], msg: &[u8; 32]) -> [u8; 32] {
    keccak256(&[&NAME[..], iv, pk, msg].concat())
}

/// The public input `PK ‖ M` as the verifier reads it: eight 64-bit words, big-endian, in order.
pub fn public_words(pk: &[u8; 32], msg: &[u8; 32]) -> [u64; 8] {
    let bytes = [&pk[..], &msg[..]].concat();
    std::array::from_fn(|k| u64::from_be_bytes(bytes[8 * k..8 * k + 8].try_into().unwrap()))
}

/// A WHIR opening of one stack's point claim.
pub struct OpeningProof {
    pub commitment: Commitment,
    pub root: Hash,
    pub point: Vec<primitives::field::F192>,
    pub value: primitives::field::F192,
    pub proof: fiat_shamir::transcript::Proof,
}

/// A proof: the stream the verifier reads (after the public input) and one opening per stack.
pub struct Proof {
    pub stream: Vec<u8>,
    pub openings: Vec<OpeningProof>,
}
