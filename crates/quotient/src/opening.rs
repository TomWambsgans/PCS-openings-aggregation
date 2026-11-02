// Part of this repository. The layout idea (a claim on a whole table, its weight restricted to the lanes that
// can be nonzero) is from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation,
// crates/flock/src/quotient/opening.rs; `wire_proof` is leanVM's `keccak_gkr::batch_bench::scalar_proof`
// (commit c445e3d5). The hidden layout adapts the padding of leanVM's `flock::membership` (same branch,
// crates/flock/membership-zk.md) to tables that fill their stack; see HIDING.md. MIT OR Apache-2.0; see NOTICE.md.
//! The commitments the claims are opened against, with leanVM's WHIR **unchanged**: its commitments and proofs
//! are those of its committer ([`pcs::whir::commit`]) and its prover ([`pcs::whir::recursive_prover_with_basis`]),
//! made in less memory ([`pcs::whir::commit_tree`], [`pcs::whir::recursive_prover_with_lane_tensors`]), and its
//! verifier ([`verifier::whir::verify_whir`], the one leanerVM proves sound) checks them, at a size and rate it
//! supports (a stack of `2^15` to `2^28` words, `64` lanes at its first fold).
//!
//! A protocol's claims are on a *table*: a multilinear in `vars` variables. A table is known to vanish
//! outside some blocks, so it is committed as the **stack** of those blocks, one WHIR lane each, in the order
//! the [`Layout`] lists them. A claim stays a plain multilinear claim on the whole table: its weight on the
//! stack is the claim's `eq`, read wherever the stack holds the table's entries. All the claims on one
//! commitment are opened together, as one random combination, which binds them to one table of the root's
//! level-0 Johnson list (leanVM's WHIR takes no out-of-domain sample at level 0): claims on one commitment must never
//! be opened separately.
//!
//! A **hidden** layout ([`Layout::hidden`]) makes the commitment and its opening independent of the table given
//! the claims (`HIDING.md`): every lane's first piece of `2^LOG_PIECE` entries is random, the pieces the table's
//! blocks give up sit in one *overflow* lane, and seven lanes are random. The claims weigh nothing of the
//! randomness. At the last [`GADGET`] entries of the first piece the opening adds a fixed weight, the *gadget*,
//! on random values that cancel it (a pair of lanes holding one value, or a lane holding zero): it weighs
//! nothing in any claim either, so the claims, their values and the verifier's checks are those of the table,
//! and it is what makes the lane rounds of WHIR's first fold uniform for every challenge (`HIDING.md`).

use fiat_shamir::digest_words;
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::{Proof, ProverState};
use pcs::whir::{LaneTensor, commit_tree_in, config_for_rate, recursive_prover_with_lane_tensors};
use primitives::field::{F64, F192, powers};
use primitives::hash::hash as keccak256;
use primitives::multilinear::{eq_table, mle_eval, mle_eval_par};
use rand::{RngCore, SeedableRng, rngs::StdRng};

const LABEL: &[u8] = b"pcs-quotient-opening";

/// The first fold of leanVM's WHIR: `2^6` lanes.
pub const LANE_FOLD: usize = 6;

/// A hidden lane's first piece: `2^LOG_PIECE` random entries, the coefficients of the basis polynomials of
/// degree below `2^LOG_PIECE`. Those below `2^LOG_PIECE - GADGET` must exceed the positions WHIR opens at its
/// first level (at most 225).
pub const LOG_PIECE: usize = 8;

/// The gadget's entries, the last of every lane's first piece: three patterns of three entries. Pattern `g`
/// weighs its lanes ([`gadget_lanes`]) by `β_i` at its entry `i` ([`Layout::gadget_entry`]), `β = 1, t, t²` the
/// basis of `E` over `K`; the values there cancel it.
pub const GADGET: usize = 9;

/// The hidden layouts' overflow lane: the first of the upper half, with the seven random lanes after it (the
/// cube of lanes `32..40`).
pub const OVERFLOW_LANE: usize = 32;

/// The random lanes a hidden layout takes at least: with the overflow lane, the cube of lanes `32..40`.
pub const MIN_RANDOM_LANES: usize = 7;

/// The lanes of gadget pattern `g`: `0` and `31`, `1` and `30` (pairs complementary in the lower half, each
/// holding one random value), then the overflow lane alone (holding zero).
pub fn gadget_lanes(g: usize) -> &'static [usize] {
    const LANES: [&[usize]; 3] = [&[0, 31], &[1, 30], &[OVERFLOW_LANE]];
    LANES[g]
}

/// `β_i`, the gadget's weight at a pattern's entry `i`: the basis `1, t, t²` of `E` over `K`.
pub fn gadget_beta(i: usize) -> F192 {
    let mut c = [0u64; 3];
    c[i] = 1;
    F192::new(c[0], c[1], c[2])
}

/// A claim: the table's multilinear extension at `point` is `value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub point: Vec<F192>,
    pub value: F192,
}

/// What a lane of the stack holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lane {
    /// The table's block of `2^log_lane` entries (in a hidden layout, all of it but its first piece).
    Block(usize),
    /// Pieces of the table, at its pieces `1, 2, ...`: [`Layout::pieces`].
    Overflow,
    /// Randomness.
    Random,
}

/// Where a table can be nonzero, and how it is stacked: lane `l` holds what [`Layout::lane`] says, in
/// lanes of `2^log_lane = 2^(log_n - 6)` words.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    /// The table's variables.
    pub vars: usize,
    /// The stack's variables: `64` lanes of `2^(log_n - 6)` words.
    pub log_n: usize,
    lanes: Vec<Lane>,
    /// A hidden layout's piece, `2^log_piece` entries; `None` for a public one.
    log_piece: Option<usize>,
    /// The table's pieces at the overflow lane's pieces `1, 2, ...`: the piece each block lane gives up, in lane
    /// order, then the pieces of what the chunks hold past their whole blocks.
    pieces: Vec<usize>,
}

impl Layout {
    /// Lanes for the leading `len` entries of each listed chunk of `2^log_chunk` entries, in that order.
    pub fn new(vars: usize, log_chunk: usize, log_n: usize, chunks: &[(usize, usize)]) -> Self {
        let log_lane = log_n - LANE_FOLD;
        assert!(log_lane <= log_chunk && log_chunk <= vars);
        let blocks: Vec<usize> = chunks
            .iter()
            .flat_map(|&(chunk, len)| {
                assert!(chunk >> (vars - log_chunk) == 0 && len <= 1 << log_chunk);
                (0..len.div_ceil(1 << log_lane)).map(move |j| (chunk << (log_chunk - log_lane)) | j)
            })
            .collect();
        assert!(
            !blocks.is_empty() && blocks.len() <= 1 << LANE_FOLD,
            "{} lanes",
            blocks.len()
        );
        Self {
            vars,
            log_n,
            lanes: blocks.into_iter().map(Lane::Block).collect(),
            log_piece: None,
            pieces: vec![],
        }
    }

    /// The hidden layout of the same chunks, with `random` random lanes (at least [`MIN_RANDOM_LANES`]): the
    /// first `32` whole blocks of the chunks on lanes `0..32` (random lanes there if there are fewer), the
    /// overflow lane [`OVERFLOW_LANE`] for the pieces the blocks give up and the chunks' tails, the random lanes
    /// after it, then the other blocks. A block lane holds its block but for its first piece, which is random;
    /// the block's first piece is on the overflow lane.
    pub fn hidden(vars: usize, log_chunk: usize, log_n: usize, chunks: &[(usize, usize)], random: usize) -> Self {
        Self::hidden_with(vars, log_chunk, log_n, chunks, random, LOG_PIECE)
    }

    /// [`Layout::hidden`] with pieces of `2^log_piece` entries: smaller ones scale the layout down for tests.
    pub fn hidden_with(
        vars: usize,
        log_chunk: usize,
        log_n: usize,
        chunks: &[(usize, usize)],
        random: usize,
        log_piece: usize,
    ) -> Self {
        let log_lane = log_n - LANE_FOLD;
        assert!(log_piece < log_lane && log_lane <= log_chunk && log_chunk <= vars);
        assert!(GADGET < 1 << log_piece, "a first piece of 2^{log_piece} entries has no room past the gadget");
        let (mut blocks, mut tails) = (vec![], vec![]);
        for &(chunk, len) in chunks {
            assert!(chunk >> (vars - log_chunk) == 0 && len <= 1 << log_chunk);
            let first = chunk << (log_chunk - log_lane);
            let whole = len >> log_lane;
            blocks.extend((0..whole).map(|j| first + j));
            let at = (first + whole) << (log_lane - log_piece);
            let tail = len - (whole << log_lane);
            tails.extend((0..tail.div_ceil(1 << log_piece)).map(|j| at + j));
        }
        assert!(random >= MIN_RANDOM_LANES, "{random} random lanes");
        let lower = blocks.len().min(OVERFLOW_LANE);
        let lanes: Vec<Lane> = (blocks[..lower].iter().map(|&b| Lane::Block(b)))
            .chain((lower..OVERFLOW_LANE).map(|_| Lane::Random))
            .chain([Lane::Overflow])
            .chain((0..random).map(|_| Lane::Random))
            .chain(blocks[lower..].iter().map(|&b| Lane::Block(b)))
            .collect();
        assert!(lanes.len() <= 1 << LANE_FOLD, "{} lanes", lanes.len());
        let given_up = lanes.iter().filter_map(|lane| match *lane {
            Lane::Block(b) => Some(b << (log_lane - log_piece)),
            _ => None,
        });
        let pieces: Vec<usize> = given_up.chain(tails).collect();
        assert!(
            !pieces.is_empty() && pieces.len() < 1 << (log_lane - log_piece),
            "{} pieces overflow a lane",
            pieces.len()
        );
        Self {
            vars,
            log_n,
            lanes,
            log_piece: Some(log_piece),
            pieces,
        }
    }

    pub fn log_lane(&self) -> usize {
        self.log_n - LANE_FOLD
    }

    pub fn lanes(&self) -> usize {
        self.lanes.len()
    }

    /// A hidden layout's piece, `2^log_piece` entries.
    pub fn log_piece(&self) -> Option<usize> {
        self.log_piece
    }

    /// Words the stack carries: whole lanes.
    pub fn placed(&self) -> usize {
        self.lanes.len() << self.log_lane()
    }

    /// What lane `l` holds.
    pub fn lane(&self, l: usize) -> Lane {
        self.lanes[l]
    }

    /// The block lane `l` holds.
    pub fn block(&self, l: usize) -> usize {
        match self.lanes[l] {
            Lane::Block(b) => b,
            lane => panic!("lane {l} holds {lane:?}"),
        }
    }

    /// The table's pieces at the overflow lane's pieces `1, 2, ...`.
    pub fn pieces(&self) -> &[usize] {
        &self.pieces
    }

    /// The overflow lane.
    pub fn overflow(&self) -> Option<usize> {
        self.lanes.iter().position(|&lane| lane == Lane::Overflow)
    }

    /// The entry of gadget pattern `g` at which it weighs its lanes by `β_i`, in every lane's first piece.
    pub fn gadget_entry(&self, g: usize, i: usize) -> usize {
        assert!(g < 3 && i < 3);
        (1 << self.log_piece.expect("a hidden layout")) - GADGET + 3 * g + i
    }

    /// The gadget's weight on entry `y` of lane `l` (zero in a public layout).
    pub fn gadget_at(&self, l: usize, y: usize) -> F192 {
        let Some(s) = self.log_piece else {
            return F192::ZERO;
        };
        match y.checked_sub((1 << s) - GADGET) {
            Some(k) if k < GADGET && gadget_lanes(k / 3).contains(&l) => gadget_beta(k % 3),
            _ => F192::ZERO,
        }
    }

    /// Leading entries of the table's `chunk` (of `2^log_chunk`) the stack holds.
    pub fn covered(&self, log_chunk: usize, chunk: usize) -> usize {
        let log_lane = self.log_lane();
        let blocks: Vec<usize> = self
            .lanes
            .iter()
            .filter_map(|lane| match *lane {
                Lane::Block(b) => Some(b),
                _ => None,
            })
            .collect();
        let whole = blocks.iter().filter(|&&b| b >> (log_chunk - log_lane) == chunk).count() << log_lane;
        let tails = self.log_piece.map_or(0, |s| {
            let tails = &self.pieces[blocks.len()..];
            tails.iter().filter(|&&p| p >> (log_chunk - s) == chunk).count() << s
        });
        whole + tails
    }

    /// A claim's weight's scales: `eq` of the point's high coordinates at each block lane's block (zero on the
    /// other lanes), and `eq` of the coordinates above a piece at each overflow piece.
    pub(crate) fn scales(&self, point: &[F192]) -> (Vec<F192>, Vec<F192>) {
        assert_eq!(point.len(), self.vars);
        let high = &point[self.log_lane()..];
        let lanes = self
            .lanes
            .iter()
            .map(|lane| match *lane {
                Lane::Block(b) => eq_bits(high, b),
                _ => F192::ZERO,
            })
            .collect();
        let pieces = match self.log_piece {
            Some(s) => self.pieces.iter().map(|&p| eq_bits(&point[s..], p)).collect(),
            None => vec![],
        };
        (lanes, pieces)
    }

    /// A claim's weight on the stack, scaled by `scale`, as lane tensors: in a public layout, the point's `eq` on
    /// the lane's coordinates on every lane; in a hidden one, that `eq` past the first piece on the block lanes,
    /// and the overflow pieces' on the overflow lane. The opening's weight adds the gadget once
    /// ([`Layout::weight`]).
    pub fn tensors(&self, point: &[F192], scale: F192) -> Vec<LaneTensor> {
        let log_lane = self.log_lane();
        let (lanes, pieces) = self.scales(point);
        let mut low = eq_table(&point[..log_lane]);
        let scales: Vec<F192> = lanes.iter().map(|&w| scale * w).collect();
        let Some(s) = self.log_piece else {
            return vec![LaneTensor { scales, low }];
        };
        let piece = 1 << s;
        // The block lanes: the point's `eq`, zero on the first piece.
        low[..piece].fill(F192::ZERO);
        // The overflow lane: each piece's `eq` below the piece, times the piece's scale.
        let piece_low = eq_table(&point[..s]);
        let mut overflow = vec![F192::ZERO; 1 << log_lane];
        for (k, &w) in pieces.iter().enumerate() {
            let out = &mut overflow[(k + 1) * piece..(k + 2) * piece];
            out.iter_mut().zip(&piece_low).for_each(|(o, &e)| *o = w * e);
        }
        let mut on_overflow = vec![F192::ZERO; self.lanes()];
        on_overflow[self.overflow().expect("an overflow lane")] = scale;
        // A tensor that is zero (a claim on no block, or on no overflow piece) is left out.
        let zero = |v: &[F192]| v.iter().all(|x| x.is_zero());
        [(scales, low), (on_overflow, overflow)]
            .into_iter()
            .filter(|(scales, low)| !zero(scales) && !zero(low))
            .map(|(scales, low)| LaneTensor { scales, low })
            .collect()
    }

    /// The opening's weight for claims at the given points, each scaled by its challenge, as lane tensors: the
    /// claims' [`Layout::tensors`], and in a hidden layout the gadget. The overflow lane's tensors, the claims'
    /// and the gadget's third pattern, are one (they share their lane), so a hidden layout's weight is a tensor a
    /// claim on its blocks, one on its overflow lane and one a pair of the gadget.
    pub fn weight<'a>(&self, claims: impl IntoIterator<Item = (&'a [F192], F192)>) -> Vec<LaneTensor> {
        let tensors = claims.into_iter().flat_map(|(point, scale)| self.tensors(point, scale));
        let Some(s) = self.log_piece else {
            return tensors.collect();
        };
        let (lanes, lane) = (self.lanes(), 1usize << self.log_lane());
        let overflow = self.overflow().expect("an overflow lane");
        let pattern = |g: usize| -> LaneTensor {
            let mut scales = vec![F192::ZERO; lanes];
            gadget_lanes(g).iter().for_each(|&l| scales[l] = F192::ONE);
            let mut low = vec![F192::ZERO; lane];
            (0..3).for_each(|i| low[self.gadget_entry(g, i)] = gadget_beta(i));
            LaneTensor { scales, low }
        };
        let mut on_overflow = pattern(2);
        let mut out = vec![];
        for tensor in tensors {
            let scale = tensor.scales[overflow];
            if !scale.is_zero() && tensor.scales.iter().enumerate().all(|(l, x)| l == overflow || x.is_zero()) {
                let low = &mut on_overflow.low[1 << s..];
                low.iter_mut().zip(&tensor.low[1 << s..]).for_each(|(o, &e)| *o += scale * e);
            } else {
                out.push(tensor);
            }
        }
        out.extend([on_overflow, pattern(0), pattern(1)]);
        out
    }

    /// The weight of a claim at `point` on entry `y` of lane `l`, from the claim's [`Layout::scales`]: what
    /// [`Layout::tensors`] give there.
    #[cfg(test)]
    pub(crate) fn weight_at(&self, point: &[F192], scales: &(Vec<F192>, Vec<F192>), l: usize, y: usize) -> F192 {
        let low = &point[..self.log_lane()];
        let Some(s) = self.log_piece else {
            return scales.0[l] * eq_bits(low, y);
        };
        let piece = y >> s;
        match self.lanes[l] {
            _ if piece == 0 => F192::ZERO,
            Lane::Block(_) => scales.0[l] * eq_bits(low, y),
            Lane::Random => F192::ZERO,
            Lane::Overflow => match scales.1.get(piece - 1) {
                Some(&w) => w * eq_bits(&point[..s], y & ((1 << s) - 1)),
                None => F192::ZERO,
            },
        }
    }
}

/// `eq(point, bits of index)`, low coordinate first.
pub(crate) fn eq_bits(point: &[F192], index: usize) -> F192 {
    point.iter().enumerate().fold(F192::ONE, |w, (k, &p)| {
        w * if (index >> k) & 1 == 1 { p } else { F192::ONE + p }
    })
}

/// A table, as what is committed of it: its stack.
pub struct Table {
    pub layout: Layout,
    pub stack: Vec<F64>,
}

/// Lane `l`'s generator: ChaCha (`StdRng`) keyed by Keccak-256 of the table's seed and the lane.
fn lane_rng(seed: &[u8; 32], l: usize) -> StdRng {
    StdRng::from_seed(keccak256(&[&seed[..], &(l as u64).to_le_bytes()].concat()))
}

fn fill_random(rng: &mut StdRng, out: &mut [F64]) {
    out.iter_mut().for_each(|w| *w = F64(rng.next_u64()));
}

/// In debug builds, what a reused buffer's words are set to before a table is filled in it: none may be left.
#[cfg(debug_assertions)]
const UNWRITTEN: F64 = F64(0x7E57_ED0B_AD5E_ED11);

/// `buffer` resized to `len` words, for fills that must overwrite every word they are handed. In debug builds,
/// the words it brings are first set to `UNWRITTEN`, which [`check_written`] then looks for.
fn reuse(mut buffer: Vec<F64>, len: usize) -> Vec<F64> {
    buffer.truncate(len);
    #[cfg(debug_assertions)]
    buffer.fill(UNWRITTEN);
    buffer.resize(len, F64::ZERO);
    buffer
}

/// In debug builds, that a fill wrote every word of `out`, a run of a buffer from [`reuse`] it was handed.
fn check_written(out: &[F64]) {
    #[cfg(debug_assertions)]
    assert!(
        !out.contains(&UNWRITTEN),
        "a table's fill left words of a reused buffer: it must write every word it is handed"
    );
    let _ = out;
}

impl Table {
    /// The table whose lane `l`, holding block `b`, `fill(l, b, lane)` writes whole. The layout is not hidden.
    pub fn new(layout: Layout, fill: impl Fn(usize, usize, &mut [F64]) + Sync) -> Self {
        Self::new_in(layout, Vec::new(), fill)
    }

    /// [`Self::new`], its stack in `buffer`'s allocation when that holds it: a buffer the caller is done with,
    /// whose words `fill` overwrites.
    ///
    /// `fill` must write every word of the lane it is handed: where it does not, the stack keeps the buffer's
    /// old words (where [`Self::new`] has zeros). Debug builds check it.
    pub fn new_in(layout: Layout, buffer: Vec<F64>, fill: impl Fn(usize, usize, &mut [F64]) + Sync) -> Self {
        assert!(layout.log_piece.is_none(), "a hidden layout takes `Table::hidden`");
        let lane = 1 << layout.log_lane();
        let mut buffer = reuse(buffer, layout.placed());
        parallel::chunks_mut(&mut buffer, lane, |l, out| {
            fill(l, layout.block(l), out);
            check_written(out);
        });
        Self { layout, stack: buffer }
    }

    /// A table of a hidden layout: `entries(start, out)` writes the table's entries `start..start + out.len()`
    /// (a run of whole pieces of one block, or a piece), and everything else the stack holds is uniform, drawn
    /// from `seed`, which must be 32 uniformly random bytes known to no one else, but at the gadget's entries:
    /// there each pair of a pattern holds one value, and the overflow lane zero.
    pub fn hidden(layout: Layout, seed: &[u8; 32], entries: impl Fn(usize, &mut [F64]) + Sync) -> Self {
        Self::hidden_in(layout, Vec::new(), seed, entries)
    }

    /// [`Self::hidden`], its stack in `buffer`'s allocation when that holds it.
    ///
    /// `entries` must write every word of the run it is handed: where it does not, the stack keeps the buffer's
    /// old words (where [`Self::hidden`] has zeros). Debug builds check it.
    pub fn hidden_in(
        layout: Layout,
        buffer: Vec<F64>,
        seed: &[u8; 32],
        entries: impl Fn(usize, &mut [F64]) + Sync,
    ) -> Self {
        let s = layout.log_piece.expect("a public layout takes `Table::new`");
        let log_lane = layout.log_lane();
        let piece = 1 << s;
        let held = layout.pieces.len();
        let mut buffer = reuse(buffer, layout.placed());
        let entries = |start: usize, out: &mut [F64]| {
            entries(start, out);
            check_written(out);
        };
        parallel::chunks_mut(&mut buffer, 1 << log_lane, |l, out| {
            let mut rng = lane_rng(seed, l);
            // Every lane's first piece, the gadget's entries included.
            fill_random(&mut rng, &mut out[..piece]);
            match layout.lanes[l] {
                Lane::Block(b) => entries((b << log_lane) + piece, &mut out[piece..]),
                Lane::Overflow => {
                    for (k, &p) in layout.pieces.iter().enumerate() {
                        entries(p * piece, &mut out[(k + 1) * piece..(k + 2) * piece]);
                    }
                    fill_random(&mut rng, &mut out[(held + 1) * piece..]);
                }
                Lane::Random => fill_random(&mut rng, &mut out[piece..]),
            }
        });
        // The gadget's values: a pair's second lane takes its first lane's, the overflow lane zero.
        for g in 0..3 {
            for i in 0..3 {
                let y = layout.gadget_entry(g, i);
                match gadget_lanes(g) {
                    &[a, b] => buffer[(b << log_lane) + y] = buffer[(a << log_lane) + y],
                    &[a] => buffer[(a << log_lane) + y] = F64::ZERO,
                    _ => unreachable!(),
                }
            }
        }
        Self { layout, stack: buffer }
    }

    /// The table's entries `start..start + out.len()`, a run of whole pieces, read back from a hidden stack:
    /// what [`Table::hidden`]'s `entries` wrote there (zero where the layout holds nothing).
    pub fn read(&self, start: usize, out: &mut [F64]) {
        let layout = &self.layout;
        let s = layout.log_piece.expect("a hidden layout");
        let (piece, log_lane) = (1usize << s, layout.log_lane());
        assert!(start.is_multiple_of(piece) && out.len().is_multiple_of(piece));
        let lane = |l: usize| &self.stack[l << log_lane..(l + 1) << log_lane];
        let overflow = lane(layout.overflow().expect("an overflow lane"));
        parallel::chunks_mut(out, piece, |j, out| {
            let p = (start >> s) + j;
            if let Some(k) = layout.pieces.iter().position(|&q| q == p) {
                out.copy_from_slice(&overflow[(k + 1) * piece..(k + 2) * piece]);
            } else if let Some(l) = layout.lanes.iter().position(|&x| x == Lane::Block(p >> (log_lane - s))) {
                // A block's first piece is on the overflow lane, found above.
                let k = p & ((1 << (log_lane - s)) - 1);
                out.copy_from_slice(&lane(l)[k * piece..(k + 1) * piece]);
            } else {
                out.fill(F64::ZERO);
            }
        });
    }

    /// Its multilinear extension at `point`.
    pub fn eval(&self, point: &[F192]) -> F192 {
        let layout = &self.layout;
        let log_lane = layout.log_lane();
        let (lanes, pieces) = layout.scales(point);
        let Some(s) = layout.log_piece else {
            return self
                .stack
                .chunks_exact(1 << log_lane)
                .zip(lanes)
                .fold(F192::ZERO, |acc, (lane, w)| {
                    acc + w * mle_eval_par(lane, &point[..log_lane])
                });
        };
        let piece = 1 << s;
        self.stack
            .chunks_exact(1 << log_lane)
            .enumerate()
            .fold(F192::ZERO, |acc, (l, lane)| {
                acc + match layout.lanes[l] {
                    Lane::Block(_) if lanes[l].is_zero() => F192::ZERO,
                    Lane::Block(_) => {
                        // The first piece is not the table's: its share of the lane's `eq` is taken out.
                        let low = &point[..log_lane];
                        let first_share = low[s..].iter().fold(F192::ONE, |w, &p| w * (F192::ONE + p));
                        lanes[l] * (mle_eval_par(lane, low) + first_share * mle_eval(&lane[..piece], &point[..s]))
                    }
                    Lane::Random => F192::ZERO,
                    Lane::Overflow => pieces.iter().enumerate().fold(F192::ZERO, |sum, (k, &w)| {
                        sum + w * mle_eval(&lane[(k + 1) * piece..(k + 2) * piece], &point[..s])
                    }),
                }
            })
    }
}

/// What a commitment keeps for its openings: its Merkle tree alone. The codeword is twice the stack, and an
/// opening reads a few hundred of its rows, so it encodes them again from the stack rather than keep it.
pub struct Committed {
    pub root: Hash,
    tree: Vec<Hash>,
}

/// WHIR's rate, `2^-LOG_INV_RATE`.
pub const LOG_INV_RATE: usize = 1;

/// leanVM's commitment ([`pcs::whir::commit`]'s root and tree), encoded one half of the codeword at a time.
pub fn commit(table: &Table) -> Committed {
    commit_in(table, Vec::new())
}

/// [`commit`], encoding in `scratch`'s allocation when that holds a half of the codeword (as many words as the
/// stack): a buffer the caller is done with.
pub fn commit_in(table: &Table, scratch: Vec<F64>) -> Committed {
    let (commitment, tree) = commit_tree_in(&table.stack, table.layout.log_n, LANE_FOLD, LOG_INV_RATE, scratch);
    Committed {
        root: commitment.root,
        tree,
    }
}

/// The opening's seed: its label, then the root and the claims it opens.
pub(crate) fn seed(root: &Hash, claims: &[Claim]) -> ([u8; 32], [u8; 32]) {
    let mut bytes = root.to_vec();
    for claim in claims {
        for x in claim.point.iter().chain([&claim.value]) {
            for limb in [x.c0, x.c1, x.c2] {
                bytes.extend_from_slice(&limb.to_le_bytes());
            }
        }
    }
    (keccak256(LABEL), keccak256(&bytes))
}

/// Prove every one of `claims` on one committed table, in one opening.
pub fn open(table: &Table, committed: &Committed, claims: &[Claim]) -> Proof {
    open_stack(
        &table.layout,
        &table.stack[..],
        &committed.root,
        &committed.tree[..],
        claims,
    )
}

/// [`open`], consuming the table and its commitment: the stack and the Merkle tree, read last for the rows the
/// first queries open, are freed then, before WHIR commits its deeper levels.
pub fn open_owned(table: Table, committed: Committed, claims: &[Claim]) -> Proof {
    open_stack(&table.layout, table.stack, &committed.root, committed.tree, claims)
}

fn open_stack(
    layout: &Layout,
    stack: impl AsRef<[F64]>,
    root: &Hash,
    tree: impl AsRef<[Hash]>,
    claims: &[Claim],
) -> Proof {
    let config = config_for_rate(layout.log_n, LOG_INV_RATE).expect("a WHIR shape leanVM supports");
    let (iv, statement) = seed(root, claims);
    let mut ps = ProverState::new(digest_words(&iv), digest_words(&statement));
    let lambdas = powers(ps.sample(), claims.len());
    let target = claims
        .iter()
        .zip(&lambdas)
        .fold(F192::ZERO, |acc, (c, &l)| acc + l * c.value);
    // The combined weight on the stack, as lane tensors ([`Layout::weight`]), each claim's scaled by its power of
    // the challenge, and a hidden layout's gadget. The prover never writes the weight out.
    let weight: Vec<LaneTensor> = layout.weight(claims.iter().zip(&lambdas).map(|(c, &l)| (&c.point[..], l)));
    recursive_prover_with_lane_tensors(&config, layout.log_n, stack, &weight, target, None, tree, &mut ps);
    ps.into_proof()
}

fn ext(x: F192) -> verifier::E {
    verifier::E::new(x.c0, x.c1, x.c2)
}

/// The opening proof in the `verifier` crate's types: the same limbs, digests and row words.
pub fn wire_proof(proof: &Proof) -> verifier::Proof {
    let batches = proof.merkle.iter().map(|paths| verifier::PrunedMerklePaths {
        leaf_data: paths
            .leaf_data
            .iter()
            .map(|row| row.iter().map(|word| verifier::K(word.0)).collect())
            .collect(),
        sibling_hashes: paths.sibling_hashes.clone(),
    });
    verifier::Proof {
        stream: proof.stream.iter().map(|&x| ext(x)).collect(),
        merkle_openings: verifier::MerkleOpenings::Pruned(batches.collect()),
    }
}

/// A claim's weight as the verifier evaluates it, scaled by the claim's power of the challenge.
struct ClaimWeight {
    /// The point's lane coordinates.
    low: Vec<verifier::E>,
    /// Per lane: the block lanes' scales.
    lanes: Vec<verifier::E>,
    /// Per overflow piece, from the overflow lane's piece `1` on.
    pieces: Vec<verifier::E>,
}

/// Check an opening of `claims` against `root`, with leanVM's WHIR verifier.
pub fn verify(
    layout: &Layout,
    root: &Hash,
    claims: &[Claim],
    proof: &verifier::Proof,
) -> Result<(), verifier::VerifierError> {
    use verifier::{Digest, E, Transcript};
    let one = E::new(1, 0, 0);
    let zero = E::new(0, 0, 0);
    if claims.iter().any(|claim| claim.point.len() != layout.vars) {
        return Err(verifier::VerifierError::WhirShape);
    }
    let (iv, statement) = seed(root, claims);
    let mut transcript = Transcript::new(proof, Digest(iv), Digest(statement), true);
    let lambda = transcript.sample();
    let mut lambdas = vec![one];
    while lambdas.len() < claims.len() {
        lambdas.push(*lambdas.last().unwrap() * lambda);
    }
    let target = claims
        .iter()
        .zip(&lambdas)
        .fold(zero, |acc, (c, &l)| acc + l * ext(c.value));
    let log_lane = layout.log_lane();
    let parts: Vec<ClaimWeight> = claims
        .iter()
        .zip(&lambdas)
        .map(|(claim, &l)| {
            let (lanes, pieces) = layout.scales(&claim.point);
            ClaimWeight {
                low: claim.point[..log_lane].iter().map(|&x| ext(x)).collect(),
                lanes: lanes.iter().map(|&w| l * ext(w)).collect(),
                pieces: pieces.iter().map(|&w| l * ext(w)).collect(),
            }
        })
        .collect();
    let lanes = layout.lanes.clone();
    let (piece, overflow) = (layout.log_piece, layout.overflow());
    // The gadget, in a hidden layout: per pattern, its lanes and its entries with their weights.
    let gadget: Vec<(&[usize], Vec<(usize, E)>)> = match piece {
        Some(_) => (0..3)
            .map(|g| {
                let entries = (0..3).map(|i| (layout.gadget_entry(g, i), ext(gadget_beta(i))));
                (gadget_lanes(g), entries.collect())
            })
            .collect(),
        None => vec![],
    };
    let eq1 = move |c: E, p: E| c * p + (one + c) * (one + p);
    let eq = move |a: &[E], b: &[E]| a.iter().zip(b).fold(one, |w, (&c, &p)| w * eq1(c, p));
    let eq_index = move |x: &[E], index: usize| {
        x.iter()
            .enumerate()
            .fold(one, |w, (k, &p)| w * if (index >> k) & 1 == 1 { p } else { one + p })
    };
    let weight = move |x: &[E]| -> E {
        // `x` is a stack point: the lane's coordinates first, then the lane index's six.
        let (low, high) = x.split_at(log_lane);
        let lane_eq: Vec<E> = (0..lanes.len()).map(|l| eq_index(high, l)).collect();
        let claims = parts.iter().fold(zero, |acc, part| {
            let on_blocks = lanes.iter().enumerate().fold(zero, |sum, (l, lane)| match lane {
                Lane::Block(_) => sum + part.lanes[l] * lane_eq[l],
                _ => sum,
            });
            let Some(s) = piece else {
                return acc + eq(&part.low, low) * on_blocks;
            };
            // In-lane weights. Below a piece every one shares its factors; a block lane's first piece is not the
            // table's, so its share of the lane's `eq`, `eq(·, 0)` above the piece, is taken out; the overflow
            // lane's piece `k + 1` holds the piece of scale `pieces[k]`.
            let below = eq(&part.low[..s], &low[..s]);
            let above = eq(&part.low[s..], &low[s..]);
            let first_above = part.low[s..].iter().fold(one, |w, &p| w * (one + p));
            let first_piece = low[s..].iter().fold(one, |w, &p| w * (one + p));
            let pieces = part
                .pieces
                .iter()
                .enumerate()
                .fold(zero, |sum, (k, &w)| sum + w * eq_index(&low[s..], k + 1));
            let on_overflow = lane_eq[overflow.expect("an overflow lane")];
            acc + below * ((above + first_above * first_piece) * on_blocks + pieces * on_overflow)
        });
        let gadget = gadget.iter().fold(zero, |acc, (pattern, entries)| {
            let on = pattern.iter().fold(zero, |sum, &l| sum + lane_eq[l]);
            acc + on * entries.iter().fold(zero, |sum, &(y, beta)| sum + beta * eq_index(low, y))
        });
        claims + gadget
    };
    verifier::whir::verify_whir(
        &mut transcript,
        layout.log_n,
        layout.placed() as u64,
        LOG_INV_RATE,
        target,
        Digest(*root),
        &weight,
    )?;
    transcript.finish().map(|_| ())
}

#[cfg(test)]
mod adversarial;

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Entries that look random: a hash of their place.
    fn pseudo(i: usize) -> F64 {
        F64(((i as u64) + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(17))
    }

    fn opens(table: &Table, claims: &[Claim]) -> bool {
        let committed = commit(table);
        let proof = open(table, &committed, claims);
        verify(&table.layout, &committed.root, claims, &wire_proof(&proof)).is_ok()
    }

    /// A table with lanes out of order and a gap opens two claims together; a wrong value does not open.
    #[test]
    fn claims_open_against_a_stacked_table() {
        let mut rng = Rng::new(0x0E);
        let (vars, log_chunk, log_n) = (18, 14, 16);
        let layout = Layout::new(vars, log_chunk, log_n, &[(3, 1 << 14), (0, 3000), (9, 1 << 13)]);
        let table = Table::new(layout, |l, _, lane| {
            for (i, w) in lane.iter_mut().enumerate() {
                *w = pseudo(l << 32 | i);
            }
        });
        let claims: Vec<Claim> = (0..2)
            .map(|_| {
                let point = rng.ext_vec(vars);
                let value = table.eval(&point);
                Claim { point, value }
            })
            .collect();
        assert!(opens(&table, &claims));
        let mut wrong = claims.clone();
        wrong[1].value += F192::ONE;
        assert!(!opens(&table, &wrong));
    }

    /// The same kind of table in a hidden layout: the claims, on the table, keep their values and open; the
    /// stack differs from one seed to another; a wrong value does not open.
    #[test]
    fn claims_open_against_a_hidden_table() {
        let mut rng = Rng::new(0x0F);
        let (vars, log_chunk, log_n) = (20, 15, 20);
        let chunks = [(3, 1 << 15), (0, 3000), (9, (1 << 14) + 700), (5, 1 << 15)];
        let layout = Layout::hidden(vars, log_chunk, log_n, &chunks, MIN_RANDOM_LANES);
        // Five blocks on lanes 0..5, random lanes to 32, the overflow lane and seven random lanes.
        assert_eq!((layout.lanes(), layout.pieces().len()), (32 + 1 + 7, 5 + 12 + 3));
        assert_eq!(layout.covered(log_chunk, 0), 12 << LOG_PIECE);
        assert_eq!(layout.covered(log_chunk, 9), (1 << 14) + (3 << LOG_PIECE));
        // The table: chunk entries are a hash of their index, zero past each chunk's length.
        let value = |i: usize| {
            let (chunk, at) = (i >> log_chunk, i & ((1 << log_chunk) - 1));
            match chunks.iter().find(|c| c.0 == chunk) {
                Some(&(_, len)) if at < len => pseudo(i),
                _ => F64::ZERO,
            }
        };
        let entries = |start: usize, out: &mut [F64]| {
            out.iter_mut().enumerate().for_each(|(k, o)| *o = value(start + k));
        };
        let table = Table::hidden(layout.clone(), &[1; 32], entries);
        let other = Table::hidden(layout.clone(), &[2; 32], entries);
        assert_ne!(table.stack, other.stack);
        let full: Vec<F64> = (0..1 << vars).map(value).collect();
        let claims: Vec<Claim> = (0..2)
            .map(|_| {
                let point = rng.ext_vec(vars);
                let value = mle_eval_par(&full, &point);
                assert_eq!(table.eval(&point), value);
                assert_eq!(other.eval(&point), value);
                Claim { point, value }
            })
            .collect();
        assert!(opens(&table, &claims));
        assert!(opens(&other, &claims));
        let mut wrong = claims.clone();
        wrong[0].value += F192::ONE;
        assert!(!opens(&table, &wrong));
    }
}
