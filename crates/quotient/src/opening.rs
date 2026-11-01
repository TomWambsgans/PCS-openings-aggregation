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
//! commitment are opened together, as one random combination, which is what binds them to one table.
//!
//! A **hidden** layout ([`Layout::hidden`]) makes the commitment and its opening independent of the table given
//! the claims (`HIDING.md`): every lane's first piece of `2^LOG_PIECE` entries is random, the pieces the table's
//! blocks give up sit in one *overflow* lane, and a few lanes are random. The weight is zero on the
//! randomness, or, on the overflow lane's *share*, cancels in every claim, so the claims, their values and the
//! verifier are those of the table.

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
/// degree below `2^LOG_PIECE`. It must exceed the positions WHIR opens at its first level (at most 225).
pub const LOG_PIECE: usize = 8;

/// A claim: the table's multilinear extension at `point` is `value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub point: Vec<F192>,
    pub value: F192,
}

/// What a lane of the stack holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lane {
    /// The table's block of `2^log_lane` entries (in a hidden layout, all of it but one piece, in an order of
    /// pieces that depends on the lane's parity).
    Block(usize),
    /// Pieces of the table, at its pieces `1, 2, ...`: [`Layout::pieces`].
    Overflow,
    /// Randomness: but for the share lane's pieces `1, 2, ...` (one share of the overflow lane's).
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
    /// The random lane whose pieces `1..=pieces.len()` are a share of the overflow lane's: the table's piece
    /// is the sum of the two, and both carry its weight.
    share: Option<usize>,
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
            share: None,
        }
    }

    /// The hidden layout of the same chunks, with `random` random lanes, `L` lanes in all: a lane per whole
    /// block of a chunk, the overflow lane `L - 2` for the pieces the blocks give up and the chunks' tails, the
    /// share lane `L - 1`, and the other random lanes on odd lanes, spread from lane `1` up. Block lane `l`
    /// holds its block's piece `k ⊕ (l mod 2)` at its piece `k`: its first piece is random, and the block's
    /// piece `l mod 2` is on the overflow lane.
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
        let total = blocks.len() + 1 + random;
        assert!(random >= 4 && total <= 1 << LANE_FOLD, "{total} lanes");
        let mut lanes = vec![None; total];
        lanes[total - 1] = Some(Lane::Random);
        lanes[total - 2] = Some(Lane::Overflow);
        // The other random lanes: odd, at the start of each of `random - 1` even spans of the pairs below, so
        // lane `1` (zero in every bit the rounds after the first read) is one.
        let pairs = (total - 2) / 2;
        for k in 0..random - 1 {
            lanes[2 * (k * pairs / (random - 1)) + 1] = Some(Lane::Random);
        }
        assert_eq!(lanes.iter().flatten().count(), random + 1, "distinct random lanes");
        let mut blocks = blocks.into_iter();
        let lanes: Vec<Lane> = lanes
            .into_iter()
            .map(|lane| lane.unwrap_or_else(|| Lane::Block(blocks.next().expect("a block per lane"))))
            .collect();
        let given_up = lanes.iter().enumerate().filter_map(|(l, lane)| match *lane {
            Lane::Block(b) => Some((b << (log_lane - log_piece)) | (l & 1)),
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
            share: Some(total - 1),
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

    /// The random lane holding a share of the overflow lane's pieces.
    pub fn share(&self) -> Option<usize> {
        self.share
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
    /// the lane's coordinates on every lane; in a hidden one, that `eq` past the first piece on even block lanes,
    /// the same with the pieces of each pair swapped on odd ones, and the overflow pieces' on the overflow and
    /// share lanes.
    pub fn tensors(&self, point: &[F192], scale: F192) -> Vec<LaneTensor> {
        let log_lane = self.log_lane();
        let (lanes, pieces) = self.scales(point);
        let low = eq_table(&point[..log_lane]);
        let Some(s) = self.log_piece else {
            return vec![LaneTensor {
                scales: lanes.iter().map(|&w| scale * w).collect(),
                low,
            }];
        };
        let piece = 1 << s;
        let parity = |odd: usize| -> Vec<F192> {
            lanes
                .iter()
                .enumerate()
                .map(|(l, &w)| if l & 1 == odd { scale * w } else { F192::ZERO })
                .collect()
        };
        // Even block lanes: the point's `eq`, zero on the first piece; odd ones: that of the pieces swapped.
        let mut odd = vec![F192::ZERO; 1 << log_lane];
        parallel::chunks_mut(&mut odd, 2 * piece, |pair, out| {
            let at = pair * 2 * piece;
            out[..piece].copy_from_slice(&low[at + piece..at + 2 * piece]);
            out[piece..].copy_from_slice(&low[at..at + piece]);
        });
        odd[..piece].fill(F192::ZERO);
        let mut even = low;
        even[..piece].fill(F192::ZERO);
        // The overflow lane and its share: each piece's `eq` below the piece, times the piece's scale.
        let piece_low = eq_table(&point[..s]);
        let mut overflow = vec![F192::ZERO; 1 << log_lane];
        for (k, &w) in pieces.iter().enumerate() {
            let out = &mut overflow[(k + 1) * piece..(k + 2) * piece];
            out.iter_mut().zip(&piece_low).for_each(|(o, &e)| *o = w * e);
        }
        let mut on_overflow = vec![F192::ZERO; self.lanes()];
        on_overflow[self.overflow().expect("an overflow lane")] = scale;
        on_overflow[self.share.expect("a share lane")] = scale;
        let (even_scales, odd_scales) = (parity(0), parity(1));
        // A tensor that is zero (a claim on blocks of one parity, or on no overflow piece) is left out.
        let zero = |v: &[F192]| v.iter().all(|x| x.is_zero());
        [(even_scales, even), (odd_scales, odd), (on_overflow, overflow)]
            .into_iter()
            .filter(|(scales, low)| !zero(scales) && !zero(low))
            .map(|(scales, low)| LaneTensor { scales, low })
            .collect()
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
            Lane::Block(_) => scales.0[l] * eq_bits(low, y ^ ((l & 1) << s)),
            Lane::Random if self.share != Some(l) => F192::ZERO,
            _ => match scales.1.get(piece - 1) {
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

impl Table {
    /// The table whose lane `l`, holding block `b`, `fill(l, b, lane)` writes whole. The layout is not hidden.
    pub fn new(layout: Layout, fill: impl Fn(usize, usize, &mut [F64]) + Sync) -> Self {
        Self::new_in(layout, Vec::new(), fill)
    }

    /// [`Self::new`], its stack in `buffer`'s allocation when that holds it: a buffer the caller is done with,
    /// whose words `fill` overwrites.
    pub fn new_in(layout: Layout, mut buffer: Vec<F64>, fill: impl Fn(usize, usize, &mut [F64]) + Sync) -> Self {
        assert!(layout.log_piece.is_none(), "a hidden layout takes `Table::hidden`");
        let lane = 1 << layout.log_lane();
        buffer.resize(layout.placed(), F64::ZERO);
        parallel::chunks_mut(&mut buffer, lane, |l, out| fill(l, layout.block(l), out));
        Self { layout, stack: buffer }
    }

    /// A table of a hidden layout: `entries(start, out)` writes the table's entries `start..start + out.len()`
    /// (a run of whole pieces of one block, or a piece), and everything else the stack holds is uniform, drawn
    /// from `seed`, which must be 32 uniformly random bytes known to no one else.
    pub fn hidden(layout: Layout, seed: &[u8; 32], entries: impl Fn(usize, &mut [F64]) + Sync) -> Self {
        Self::hidden_in(layout, Vec::new(), seed, entries)
    }

    /// [`Self::hidden`], its stack in `buffer`'s allocation when that holds it.
    pub fn hidden_in(
        layout: Layout,
        mut buffer: Vec<F64>,
        seed: &[u8; 32],
        entries: impl Fn(usize, &mut [F64]) + Sync,
    ) -> Self {
        let s = layout.log_piece.expect("a public layout takes `Table::new`");
        let log_lane = layout.log_lane();
        let piece = 1 << s;
        let held = layout.pieces.len();
        let share = layout.share.expect("a share lane");
        buffer.resize(layout.placed(), F64::ZERO);
        parallel::chunks_mut(&mut buffer, 1 << log_lane, |l, out| {
            let mut rng = lane_rng(seed, l);
            match layout.lanes[l] {
                Lane::Block(b) => {
                    fill_random(&mut rng, &mut out[..piece]);
                    if l & 1 == 0 {
                        entries((b << log_lane) + piece, &mut out[piece..]);
                    } else {
                        // Pieces `2i` and `2i + 1` swapped: piece `1` is the block's piece `0`.
                        for (k, at) in out.chunks_exact_mut(piece).enumerate().skip(1) {
                            entries((b << log_lane) + (k ^ 1) * piece, at);
                        }
                    }
                }
                Lane::Overflow => {
                    fill_random(&mut rng, &mut out[..piece]);
                    fill_random(&mut rng, &mut out[(held + 1) * piece..]);
                    for (k, &p) in layout.pieces.iter().enumerate() {
                        entries(p * piece, &mut out[(k + 1) * piece..(k + 2) * piece]);
                    }
                    // The share lane holds `ρ` at its pieces `1..=held` (its generator's stream there): the
                    // overflow lane holds the table's pieces plus `ρ`.
                    let mut rho = vec![F64::ZERO; (held + 1) * piece];
                    fill_random(&mut lane_rng(seed, share), &mut rho);
                    out[piece..(held + 1) * piece]
                        .iter_mut()
                        .zip(&rho[piece..])
                        .for_each(|(o, &r)| *o += r);
                }
                Lane::Random => fill_random(&mut rng, out),
            }
        });
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
        let (overflow, share) = (
            lane(layout.overflow().expect("an overflow lane")),
            lane(layout.share.expect("a share lane")),
        );
        parallel::chunks_mut(out, piece, |j, out| {
            let p = (start >> s) + j;
            if let Some(k) = layout.pieces.iter().position(|&q| q == p) {
                let at = (k + 1) * piece..(k + 2) * piece;
                out.iter_mut()
                    .zip(&overflow[at.clone()])
                    .zip(&share[at])
                    .for_each(|((o, &a), &b)| *o = a + b);
            } else if let Some(l) = layout.lanes.iter().position(|&x| x == Lane::Block(p >> (log_lane - s))) {
                let k = (p & ((1 << (log_lane - s)) - 1)) ^ (l & 1);
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
                        // An odd lane's pieces are swapped in pairs: its point's coordinate `s` is flipped.
                        let mut low = point[..log_lane].to_vec();
                        low[s] += F192::from(F64((l & 1) as u64));
                        // The first piece is not the table's: its share of the lane's `eq` is taken out.
                        let first_share = low[s..].iter().fold(F192::ONE, |w, &p| w * (F192::ONE + p));
                        lanes[l] * (mle_eval_par(lane, &low) + first_share * mle_eval(&lane[..piece], &point[..s]))
                    }
                    Lane::Random if layout.share != Some(l) => F192::ZERO,
                    _ => pieces.iter().enumerate().fold(F192::ZERO, |sum, (k, &w)| {
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
    // The combined weight on the stack, as lane tensors ([`Layout::tensors`]), each claim's scaled by its power of
    // the challenge. The prover never writes the weight out.
    let weight: Vec<LaneTensor> = claims
        .iter()
        .zip(&lambdas)
        .flat_map(|(claim, &lambda)| layout.tensors(&claim.point, lambda))
        .collect();
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
    verify_paths(layout, root, claims, proof).map(|_| ())
}

/// [`verify`], returning every query's Merkle path in the order the verifier opened them: the proof's openings in
/// their raw form, one full path per query, which is the form `formal/Statement`'s verifier reads.
pub fn verify_paths(
    layout: &Layout,
    root: &Hash,
    claims: &[Claim],
    proof: &verifier::Proof,
) -> Result<Vec<verifier::MerklePath>, verifier::VerifierError> {
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
    let (piece, share) = (layout.log_piece, layout.share);
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
        parts.iter().fold(zero, |acc, part| {
            let on = |odd: usize| {
                lanes.iter().enumerate().fold(zero, |sum, (l, lane)| match lane {
                    Lane::Block(_) if l & 1 == odd => sum + part.lanes[l] * lane_eq[l],
                    _ => sum,
                })
            };
            let Some(s) = piece else {
                return acc + eq(&part.low, low) * (on(0) + on(1));
            };
            // In-lane weights. Below a piece and above coordinate `s`, every one shares its factors; an odd block
            // lane flips coordinate `s`; a block lane's first piece is not the table's, so its share of the
            // lane's `eq`, `eq(·, 0)` above the piece, is taken out.
            let below = eq(&part.low[..s], &low[..s]);
            let above = eq(&part.low[s + 1..], &low[s + 1..]);
            let first_above = part.low[s + 1..].iter().fold(one, |w, &p| w * (one + p));
            let first_piece = low[s..].iter().fold(one, |w, &p| w * (one + p));
            let block = |c: E| above * eq1(c, low[s]) + first_above * (one + c) * first_piece;
            let (even, odd) = (block(part.low[s]), block(one + part.low[s]));
            let pieces = part
                .pieces
                .iter()
                .enumerate()
                .fold(zero, |sum, (k, &w)| sum + w * eq_index(&low[s..], k + 1));
            let on_overflow = lane_eq[layout_overflow(&lanes)] + lane_eq[share.expect("a share lane")];
            acc + below * (even * on(0) + odd * on(1) + pieces * on_overflow)
        })
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
    transcript.finish()
}

fn layout_overflow(lanes: &[Lane]) -> usize {
    lanes
        .iter()
        .position(|&lane| lane == Lane::Overflow)
        .expect("an overflow lane")
}

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
        let layout = Layout::hidden(vars, log_chunk, log_n, &chunks, 4);
        assert_eq!((layout.lanes(), layout.pieces().len()), (5 + 1 + 4, 5 + 12 + 3));
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
