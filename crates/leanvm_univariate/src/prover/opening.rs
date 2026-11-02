// Part of this repository. Follows crates/quotient/src/opening.rs (its transcript's shape: one hash of a prefix and
// the claim as the IV, a zero public digest, the root the proof's first two scalars); the commitment and the proof are
// leanVM's WHIR (`pcs`, vendored from leanVM commit c445e3d5) unchanged, and the check is its verifier (`verifier`).
// MIT OR Apache-2.0; see NOTICE.md.
//! What `PCS_OPEN` checks, for the univariate PIOP's commitments: one point claim on a whole stack (SPEC.md §8, the
//! point-claim ABI), proven and verified with leanVM's WHIR at rate `1/2`, `64` lanes at its first fold.
//!
//! The claim is the stack's multilinear (all `2^vars` words, whatever they hold) at a point. WHIR commits only the
//! stack's whole lanes that carry data and reads the others as zero, and its prover needs a weight that vanishes on
//! those absent lanes: the claim's `eq(point, ·)` restricted to the committed lanes, which is the same claim as the
//! stack is zero there.

use fiat_shamir::digest_words;
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::{Proof, ProverState};
use pcs::whir::{LaneTensor, commit_tree_in, config_for_rate, recursive_prover_with_lane_tensors};
use primitives::field::{F64, F192};
use primitives::hash::hash as keccak256;

/// WHIR's first fold: `2^6` lanes.
pub const LANE_FOLD: usize = 6;
/// WHIR's rate, `2^-LOG_INV_RATE` (the repository's: `review/whir_params.py`).
pub const LOG_INV_RATE: usize = 1;
const LABEL: &[u8; 20] = b"leanvm-univariate-op";
/// The version of this opening (its transcript, WHIR's configuration at c445e3d5): 2 since the layout word is
/// `PCS_OPEN`'s 32 bytes (SPEC.md §13, F2).
pub const VERSION: u64 = 2;

/// A commitment: its root and Merkle tree, the stack's variables and the words its blocks place.
pub struct Committed {
    pub root: Hash,
    tree: Vec<Hash>,
    pub vars: usize,
    pub placed: u64,
}

/// Commit to a stack of whole lanes (`words.len()` a multiple of `2^(vars - 6)`).
pub fn commit(words: &[F64], vars: usize, placed: u64) -> Committed {
    let (commitment, tree) = commit_tree_in(words, vars, LANE_FOLD, LOG_INV_RATE, Vec::new());
    Committed {
        root: commitment.root,
        tree,
        vars,
        placed,
    }
}

/// The opening's IV: Keccak-256 of the label, the version, `PCS_OPEN`'s layout word (32 bytes: the shape, the
/// opening's code, the stack's variables and placed words: `contract::layout_word`), the stack's variables, the
/// rate, then the point's coordinates and the value (three 8-byte little-endian limbs each).
pub fn iv(layout: &[u8; 32], vars: usize, point: &[F192], value: F192) -> [u8; 32] {
    let mut bytes = LABEL.to_vec();
    bytes.extend_from_slice(&VERSION.to_le_bytes());
    bytes.extend_from_slice(layout);
    for n in [vars as u64, LOG_INV_RATE as u64, point.len() as u64] {
        bytes.extend_from_slice(&n.to_le_bytes());
    }
    for x in point.iter().chain([&value]) {
        for limb in [x.c0, x.c1, x.c2] {
            bytes.extend_from_slice(&limb.to_le_bytes());
        }
    }
    keccak256(&bytes)
}

fn eq_bits(index: usize, point: &[F192]) -> F192 {
    point.iter().enumerate().fold(F192::ONE, |acc, (k, &p)| {
        acc * if index >> k & 1 == 1 { p } else { F192::ONE + p }
    })
}

/// Prove `stack(point) = value`.
pub fn open(words: &[F64], committed: &Committed, layout: &[u8; 32], point: &[F192], value: F192) -> Proof {
    let vars = committed.vars;
    assert_eq!(point.len(), vars);
    let config = config_for_rate(vars, LOG_INV_RATE).expect("a WHIR shape leanVM supports");
    let mut ps = ProverState::new(digest_words(&iv(layout, vars, point, value)), digest_words(&[0; 32]));
    ps.add_root(&committed.root);
    let log_lane = vars - LANE_FOLD;
    let lanes = words.len() >> log_lane;
    let tensor = LaneTensor {
        scales: (0..lanes).map(|l| eq_bits(l, &point[log_lane..])).collect(),
        low: primitives::multilinear::eq_table(&point[..log_lane]),
    };
    recursive_prover_with_lane_tensors(&config, vars, words, &[tensor], value, None, &committed.tree, &mut ps);
    ps.into_proof()
}

fn ext(x: F192) -> verifier::E {
    verifier::E::new(x.c0, x.c1, x.c2)
}

/// The proof in the `verifier` crate's types.
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

/// Check an opening of `stack(point) = value` against `root`, with leanVM's WHIR verifier: the stack's variables and
/// placed words are the layout word's (bytes 24 and 25..32).
pub fn verify(
    root: &Hash,
    layout: &[u8; 32],
    point: &[F192],
    value: F192,
    proof: &verifier::Proof,
) -> Result<(), verifier::VerifierError> {
    use verifier::{Digest, E, Transcript};
    let vars = layout[24] as usize;
    let placed = {
        let mut bytes = [0u8; 8];
        bytes[1..].copy_from_slice(&layout[25..]);
        u64::from_be_bytes(bytes)
    };
    if point.len() != vars {
        return Err(verifier::VerifierError::WhirShape);
    }
    let mut transcript = Transcript::new(proof, Digest(iv(layout, vars, point, value)), Digest([0; 32]), true);
    let halves = transcript.next_scalars(2)?;
    if Digest::from_halves(halves[0], halves[1])? != Digest(*root) {
        return Err(verifier::VerifierError::MerkleRootMismatch);
    }
    let one = E::new(1, 0, 0);
    let log_lane = vars - LANE_FOLD;
    let lane = 1u64 << log_lane;
    let lanes = placed.div_ceil(lane).max(1) as usize;
    let p: Vec<E> = point.iter().map(|&x| ext(x)).collect();
    let weight = move |x: &[E]| -> E {
        let (low, high) = x.split_at(log_lane);
        let eq_low = p[..log_lane]
            .iter()
            .zip(low)
            .fold(one, |acc, (&a, &b)| acc * (a * b + (one + a) * (one + b)));
        let bit = |l: usize, k: usize, v: E| if l >> k & 1 == 1 { v } else { one + v };
        let on_lanes = (0..lanes).fold(E::new(0, 0, 0), |acc, l| {
            let a = (0..LANE_FOLD).fold(one, |w, k| w * bit(l, k, p[log_lane + k]));
            let b = (0..LANE_FOLD).fold(one, |w, k| w * bit(l, k, high[k]));
            acc + a * b
        });
        eq_low * on_lanes
    };
    verifier::whir::verify_whir(&mut transcript, vars, placed, LOG_INV_RATE, ext(value), Digest(*root), &weight)?;
    transcript.finish().map(|_| ())
}
