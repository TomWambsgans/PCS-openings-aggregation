// Part of this repository. The layout idea (a claim on a whole table, its weight restricted to the lanes that
// can be nonzero) is from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation,
// crates/flock/src/quotient/opening.rs; `wire_proof` is leanVM's `keccak_gkr::batch_bench::scalar_proof`
// (commit c445e3d5). MIT OR Apache-2.0; see NOTICE.md.
//! The commitments the claims are opened against, with leanVM's WHIR **unchanged**: its committer
//! ([`pcs::whir::commit`]), its prover ([`pcs::whir::recursive_prover_with_basis`]) and its verifier
//! ([`verifier::whir::verify_whir`], the one leanerVM proves sound), at a size and rate it supports (a stack of
//! `2^15` to `2^28` words, `64` lanes at its first fold).
//!
//! A protocol's claims are on a *table*: a multilinear in `vars` variables. A table is known to vanish
//! outside some blocks, so it is committed as the **stack** of those blocks, one WHIR lane each, in the order
//! the [`Layout`] lists them. A claim stays a plain multilinear claim on the whole table: its weight on the
//! stack is the claim's `eq`, read at each lane's block. All the claims on one commitment are opened together,
//! as one random combination, which is what binds them to one table.

use fiat_shamir::digest_words;
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::{Proof, ProverState};
use pcs::whir::{ProverData, commit as whir_commit, config_for_rate, recursive_prover_with_basis};
use primitives::field::{F64, F192, powers};
use primitives::hash::hash as keccak256;
use primitives::multilinear::{eq_table, mle_eval_par};

const LABEL: &[u8] = b"pcs-quotient-opening";

/// The first fold of leanVM's WHIR: `2^6` lanes.
pub const LANE_FOLD: usize = 6;

/// A claim: the table's multilinear extension at `point` is `value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub point: Vec<F192>,
    pub value: F192,
}

/// Where a table can be nonzero, and how it is stacked: lane `l` of the stack holds the table's entries
/// `[blocks[l] · 2^log_lane, (blocks[l] + 1) · 2^log_lane)`, with `2^log_lane = 2^(log_n - 6)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    /// The table's variables.
    pub vars: usize,
    /// The stack's variables: `64` lanes of `2^(log_n - 6)` words.
    pub log_n: usize,
    blocks: Vec<usize>,
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
        Self { vars, log_n, blocks }
    }

    pub fn log_lane(&self) -> usize {
        self.log_n - LANE_FOLD
    }

    pub fn lanes(&self) -> usize {
        self.blocks.len()
    }

    /// Words the stack carries: whole lanes.
    pub fn placed(&self) -> usize {
        self.blocks.len() << self.log_lane()
    }

    /// The block lane `l` holds.
    pub fn block(&self, l: usize) -> usize {
        self.blocks[l]
    }

    /// Leading entries of the table's `chunk` (of `2^log_chunk`) its lanes hold.
    pub fn covered(&self, log_chunk: usize, chunk: usize) -> usize {
        let per = log_chunk - self.log_lane();
        self.blocks.iter().filter(|&&b| b >> per == chunk).count() << self.log_lane()
    }

    /// Each lane's weight in a claim at `point`: `eq` of the point's high coordinates at the lane's block.
    pub fn lane_weights(&self, point: &[F192]) -> Vec<F192> {
        assert_eq!(point.len(), self.vars);
        let high = &point[self.log_lane()..];
        self.blocks.iter().map(|&b| eq_bits(high, b)).collect()
    }
}

/// `eq(point, bits of index)`, low coordinate first.
fn eq_bits(point: &[F192], index: usize) -> F192 {
    point.iter().enumerate().fold(F192::ONE, |w, (k, &p)| {
        w * if (index >> k) & 1 == 1 { p } else { F192::ONE + p }
    })
}

/// A table, as what is committed of it: its stack.
pub struct Table {
    pub layout: Layout,
    pub stack: Vec<F64>,
}

impl Table {
    /// The table whose lane `l`, holding block `b`, `fill(l, b, lane)` writes whole.
    pub fn new(layout: Layout, fill: impl Fn(usize, usize, &mut [F64]) + Sync) -> Self {
        let lane = 1 << layout.log_lane();
        let mut stack = vec![F64::ZERO; layout.placed()];
        parallel::chunks_mut(&mut stack, lane, |l, out| fill(l, layout.block(l), out));
        Self { layout, stack }
    }

    /// Its multilinear extension at `point`.
    pub fn eval(&self, point: &[F192]) -> F192 {
        let log_lane = self.layout.log_lane();
        self.stack
            .chunks_exact(1 << log_lane)
            .zip(self.layout.lane_weights(point))
            .fold(F192::ZERO, |acc, (lane, w)| {
                acc + w * mle_eval_par(lane, &point[..log_lane])
            })
    }
}

/// What a commitment keeps for its openings.
pub struct Committed {
    pub root: Hash,
    data: ProverData,
}

/// WHIR's rate, `2^-LOG_INV_RATE`.
pub const LOG_INV_RATE: usize = 1;

pub fn commit(table: &Table) -> Committed {
    let (commitment, data) = whir_commit(&table.stack, table.layout.log_n, LANE_FOLD, LOG_INV_RATE);
    Committed {
        root: commitment.root,
        data,
    }
}

/// The opening's seed: its label, then the root and the claims it opens.
fn seed(root: &Hash, claims: &[Claim]) -> ([u8; 32], [u8; 32]) {
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
    let layout = &table.layout;
    let log_lane = layout.log_lane();
    let config = config_for_rate(layout.log_n, LOG_INV_RATE).expect("a WHIR shape leanVM supports");
    let (iv, statement) = seed(&committed.root, claims);
    let mut ps = ProverState::new(digest_words(&iv), digest_words(&statement));
    let lambdas = powers(ps.sample(), claims.len());
    let target = claims
        .iter()
        .zip(&lambdas)
        .fold(F192::ZERO, |acc, (c, &l)| acc + l * c.value);
    // The combined weight on the stack, lane by lane: each claim's `eq` on the lane's coordinates, scaled by
    // its power of the challenge and by `eq` of its high coordinates at the lane's block.
    let mut weight = vec![F192::ZERO; layout.placed()];
    for (claim, &lambda) in claims.iter().zip(&lambdas) {
        let low = eq_table(&claim.point[..log_lane]);
        let scales: Vec<F192> = layout.lane_weights(&claim.point).iter().map(|&w| lambda * w).collect();
        parallel::chunks_mut(&mut weight, 1 << log_lane, |l, out| {
            let scale = scales[l];
            if !scale.is_zero() {
                out.iter_mut().zip(&low).for_each(|(o, &e)| *o += scale * e);
            }
        });
    }
    recursive_prover_with_basis(
        &config,
        layout.log_n,
        &table.stack,
        weight,
        target,
        &committed.data.codeword,
        &committed.data.merkle_tree,
        &mut ps,
    );
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
        .fold(E::new(0, 0, 0), |acc, (c, &l)| acc + l * ext(c.value));
    let log_lane = layout.log_lane();
    // Per claim: its `eq` at the point's lane coordinates, and each lane's scale.
    let parts: Vec<(Vec<E>, Vec<E>)> = claims
        .iter()
        .zip(&lambdas)
        .map(|(claim, &l)| {
            let low = claim.point[..log_lane].iter().map(|&x| ext(x)).collect();
            let scales = layout.lane_weights(&claim.point).iter().map(|&w| l * ext(w)).collect();
            (low, scales)
        })
        .collect();
    let lanes = layout.lanes();
    let weight = move |x: &[E]| -> E {
        // `x` is a stack point: the lane's coordinates first, then the lane index's six.
        let (low, high) = x.split_at(log_lane);
        let lane_eq: Vec<E> = (0..lanes)
            .map(|l| {
                high.iter()
                    .enumerate()
                    .fold(one, |w, (k, &p)| w * if (l >> k) & 1 == 1 { p } else { one + p })
            })
            .collect();
        parts.iter().fold(E::new(0, 0, 0), |acc, (claim_low, scales)| {
            let on_lanes = scales
                .iter()
                .zip(&lane_eq)
                .fold(E::new(0, 0, 0), |s, (&w, &e)| s + w * e);
            let eq = claim_low
                .iter()
                .zip(low)
                .fold(one, |w, (&c, &p)| w * (c * p + (one + c) * (one + p)));
            acc + eq * on_lanes
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

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// A table with lanes out of order and a gap opens two claims together; a wrong value does not open.
    #[test]
    fn claims_open_against_a_stacked_table() {
        let mut rng = Rng::new(0x0E);
        let (vars, log_chunk, log_n) = (18, 14, 16);
        let layout = Layout::new(vars, log_chunk, log_n, &[(3, 1 << 14), (0, 3000), (9, 1 << 13)]);
        // Entries that look random: a hash of their place in the stack.
        let table = Table::new(layout, |l, _, lane| {
            for (i, w) in lane.iter_mut().enumerate() {
                *w = F64(((l << 32 | i) as u64 + 1)
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .rotate_left(17));
            }
        });
        let committed = commit(&table);
        let claims: Vec<Claim> = (0..2)
            .map(|_| {
                let point = rng.ext_vec(vars);
                let value = table.eval(&point);
                Claim { point, value }
            })
            .collect();
        let proof = open(&table, &committed, &claims);
        assert_eq!(
            verify(&table.layout, &committed.root, &claims, &wire_proof(&proof)),
            Ok(())
        );

        let mut wrong = claims.clone();
        wrong[1].value += F192::ONE;
        let proof = open(&table, &committed, &wrong);
        assert!(verify(&table.layout, &committed.root, &wrong, &wire_proof(&proof)).is_err());
    }
}
