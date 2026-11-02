//! Adversarial review of the lean openings (commit 411866f): `commit` / `commit_in` / `open` / `open_owned`
//! against the opening of commit d940553 (leanVM's `commit` and the dense-weight prover), rebuilt here line for
//! line, on random layouts with gaps, out-of-order and repeated blocks, partial lanes, and claims whose high
//! coordinates are boolean or not.

use super::*;
use pcs::whir::{commit as whir_commit, recursive_prover_with_basis};
use primitives::test_rng::Rng;

/// The opening of commit d940553, verbatim but for taking the codeword from a fresh `pcs::whir::commit` and for the
/// transcript's start, which now has leanVM's shape: the IV of [`iv`], a zero public digest, the root sent first.
fn old_open(table: &Table, claims: &[Claim]) -> (Hash, Proof) {
    let layout = &table.layout;
    let log_lane = layout.log_lane();
    let config = config_for_rate(layout.log_n, LOG_INV_RATE).expect("a WHIR shape leanVM supports");
    let (commitment, data) = whir_commit(&table.stack, layout.log_n, LANE_FOLD, LOG_INV_RATE);
    let mut ps = ProverState::new(digest_words(&iv(layout, claims)), digest_words(&PUBLIC_DIGEST));
    ps.add_root(&commitment.root);
    let lambdas = powers(ps.sample(), claims.len());
    let target = claims
        .iter()
        .zip(&lambdas)
        .fold(F192::ZERO, |acc, (c, &l)| acc + l * c.value);
    let mut weight = vec![F192::ZERO; layout.placed()];
    for (claim, &lambda) in claims.iter().zip(&lambdas) {
        let low = eq_table(&claim.point[..log_lane]);
        // d940553's `lane_weights`: on a public layout, the block lanes' scales.
        let scales: Vec<F192> = layout.scales(&claim.point).0.iter().map(|&w| lambda * w).collect();
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
        &data.codeword,
        &data.merkle_tree,
        &mut ps,
    );
    (commitment.root, ps.into_proof())
}

fn pick(rng: &mut Rng, n: usize) -> usize {
    rng.next_u64() as usize % n
}

/// A random layout: `log_n` in 15..=max_log_n, the table up to 4 variables wider than the stack, chunks of
/// any size the layout allows, listed out of order, some partial, some repeated, at most 64 lanes.
fn random_layout(rng: &mut Rng, max_log_n: usize) -> Layout {
    let log_n = 15 + pick(rng, max_log_n - 14);
    let log_lane = log_n - LANE_FOLD;
    let vars = log_n + pick(rng, 5);
    let log_chunk = log_lane + pick(rng, vars - log_lane + 1);
    let n_chunks = 1usize << (vars - log_chunk);
    let per_chunk = 1usize << (log_chunk - log_lane);
    let mut chunks = vec![];
    let mut lanes = 0;
    loop {
        let chunk = pick(rng, n_chunks);
        let len = match pick(rng, 4) {
            0 => 1 << log_chunk,
            1 => 1 + pick(rng, 1 << log_chunk),
            2 => 16,
            _ => (1 + pick(rng, per_chunk)) << log_lane,
        }
        .min(1 << log_chunk);
        let add = len.div_ceil(1 << log_lane);
        if lanes + add > 64 {
            break;
        }
        lanes += add;
        chunks.push((chunk, len));
        if pick(rng, 3) == 0 {
            break;
        }
    }
    if chunks.is_empty() {
        chunks.push((pick(rng, n_chunks), 1));
    }
    Layout::new(vars, log_chunk, log_n, &chunks)
}

/// A point whose high (lane-selecting) coordinates are boolean, random, or a mix.
fn random_point(rng: &mut Rng, layout: &Layout, kind: usize) -> Vec<F192> {
    let log_lane = layout.log_lane();
    (0..layout.vars)
        .map(|i| {
            if i < log_lane {
                return rng.ext();
            }
            match kind {
                0 => rng.ext(),
                1 => {
                    if rng.bit() {
                        F192::ONE
                    } else {
                        F192::ZERO
                    }
                }
                _ => {
                    if rng.bit() {
                        rng.ext()
                    } else {
                        F192::from(F64(rng.bit() as u64))
                    }
                }
            }
        })
        .collect()
}

/// The lean commitment and opening are the old ones, byte for byte, on random layouts and claims; the claims
/// that hold verify, and an owned opening is the borrowed one.
#[test]
fn lean_openings_are_the_old_openings() {
    let mut rng = Rng::new(0x0E0E);
    for case in 0..160 {
        let layout = random_layout(&mut rng, 20);
        let salt = rng.next_u64();
        let table = Table::new(layout.clone(), |l, block, lane| {
            for (i, w) in lane.iter_mut().enumerate() {
                *w = F64(word(salt ^ ((l as u64) << 48) ^ ((block as u64) << 32) ^ i as u64));
            }
        });
        let n_claims = 1 + pick(&mut rng, 4);
        let claims: Vec<Claim> = (0..n_claims)
            .map(|c| {
                let point = random_point(&mut rng, &layout, (case + c) % 3);
                // Every other case carries a false claim.
                let value = table.eval(&point) + if case % 2 == 1 && c == 0 { F192::ONE } else { F192::ZERO };
                Claim { point, value }
            })
            .collect();
        let ctx = format!("case {case}: {layout:?}, {n_claims} claims");
        let (old_root, old_proof) = old_open(&table, &claims);
        let committed = commit(&table);
        assert_eq!(committed.root, old_root, "root: {ctx}");
        let proof = open(&table, &committed, &claims);
        assert!(proof == old_proof, "open: {ctx}");
        let verdict = verify(&table.layout, &committed.root, &claims, &wire_proof(&proof));
        assert_eq!(verdict.is_ok(), case % 2 == 0, "verdict {verdict:?}: {ctx}");
        // Owned, with the commitment encoded in a dirty scratch buffer of each size.
        for scratch_len in [
            0usize,
            table.stack.len() / 3,
            table.stack.len(),
            2 * table.stack.len() + 5,
        ] {
            let scratch = vec![F64(0xA5A5_A5A5_A5A5_A5A5); scratch_len];
            let committed = commit_in(&table, scratch);
            assert_eq!(committed.root, old_root, "commit_in({scratch_len}): {ctx}");
            let owned = Table {
                layout: table.layout.clone(),
                stack: table.stack.clone(),
            };
            let proof = open_owned(owned, committed, &claims);
            assert!(proof == old_proof, "open_owned: {ctx}");
        }
    }
}

/// A word that looks random: a hash of its index.
fn word(x: u64) -> u64 {
    let x = (x ^ 0x1234_5678).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(23);
    x.wrapping_mul(0xBF58_476D_1CE4_E5B9) ^ (x >> 31)
}

/// `Table::new_in` on a buffer full of garbage, longer or shorter than the stack, is `Table::new`, as long as
/// `fill` writes whole lanes; a fill that writes part of a lane (as the witness table's mask lane did before the
/// hidden layouts) leaves the buffer's old words in the rest, which debug builds refuse.
#[test]
fn table_new_in_is_new_for_whole_lane_fills() {
    let layout = Layout::new(18, 14, 16, &[(3, 1 << 14), (0, 3000), (9, 1 << 13)]);
    let whole = |l: usize, _: usize, lane: &mut [F64]| {
        lane.iter_mut()
            .enumerate()
            .for_each(|(i, w)| *w = F64((l * 1_000_003 + i) as u64))
    };
    let fresh = Table::new(layout.clone(), whole);
    for len in [0usize, 100, layout.placed(), 3 * layout.placed()] {
        let reused = Table::new_in(layout.clone(), vec![F64(u64::MAX); len], whole);
        assert_eq!(reused.stack, fresh.stack, "buffer of {len}");
    }
    // A partial fill: what the old `Table::new` zeroed, a reused buffer keeps; debug builds refuse it.
    let partial = |_: usize, _: usize, lane: &mut [F64]| lane[..16].fill(F64(7));
    let fresh = Table::new(layout.clone(), partial);
    let reused =
        std::panic::catch_unwind(|| Table::new_in(layout.clone(), vec![F64(u64::MAX); layout.placed()], partial));
    match (reused, cfg!(debug_assertions)) {
        (Ok(reused), false) => assert_ne!(
            reused.stack, fresh.stack,
            "documents the precondition: fill must write whole lanes"
        ),
        (Err(_), true) => {}
        (Ok(_), true) => panic!("debug builds check that fill writes whole lanes"),
        (Err(_), false) => panic!("only debug builds check that fill writes whole lanes"),
    }
}

/// FINDING (fixed): an opening of no claims. The old opening proved it (a zero weight), and the verifier accepts
/// that proof; the lean one panicked in `pcs::whir::tensor_lane_rounds`, and now makes the old proof.
#[test]
fn open_no_claims() {
    let layout = Layout::new(16, 16, 16, &[(0, 1 << 16)]);
    let table = Table::new(layout, |l, _, lane| {
        lane.iter_mut().for_each(|w| *w = F64(l as u64 + 3))
    });
    let (old_root, old_proof) = old_open(&table, &[]);
    // The old opening of no claims is a proof the verifier accepts.
    assert_eq!(verify(&table.layout, &old_root, &[], &wire_proof(&old_proof)), Ok(()));
    let committed = commit(&table);
    let got = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| open(&table, &committed, &[])));
    match got {
        Ok(proof) => assert!(proof == old_proof),
        Err(_) => panic!("open(.., &[]) panics; the old opening proved it"),
    }
}
