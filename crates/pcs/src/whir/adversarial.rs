//! Adversarial review of the lean prover paths (commit 411866f): `commit_tree_in`, `encoded_rows`, the lean
//! deeper levels and `recursive_prover_with_lane_tensors`, each against the untouched `commit` /
//! `recursive_prover_with_basis` on randomized shapes.

use super::*;
use crate::whir_config::test_config_for;
use primitives::test_rng::Rng;

fn rand_words(rng: &mut Rng, n: usize) -> Vec<F64> {
    (0..n).map(|_| F64(rng.next_u64())).collect()
}

fn pick(rng: &mut Rng, n: usize) -> usize {
    rng.next_u64() as usize % n
}

/// Lane counts to try for `2^log_batch` lanes: 1, 2, all, all but one, and two at random.
fn lane_counts(rng: &mut Rng, log_batch: usize) -> Vec<usize> {
    let max = 1usize << log_batch;
    let mut v = vec![
        1,
        2.min(max),
        max,
        (max - 1).max(1),
        1 + pick(rng, max),
        1 + pick(rng, max),
    ];
    v.sort_unstable();
    v.dedup();
    v
}

/// Scratch buffers a caller could hand `commit_tree_in`: none, too small, exactly one replica, larger and
/// longer than one replica, all full of garbage.
fn scratches(len: usize) -> Vec<Vec<F64>> {
    let garbage = |len: usize, cap: usize| {
        let mut v = Vec::with_capacity(cap);
        v.resize(len, F64(0x5A5A_5A5A_5A5A_5A5A));
        v
    };
    vec![
        Vec::new(),
        garbage(len / 2, len / 2),
        garbage(len, len),
        garbage(len, 3 * len),
        garbage(3 * len + 7, 3 * len + 7),
    ]
}

/// `commit_tree_in` commits to `commit`'s root and tree, at every rate up to 2^-3, every interleaving up to
/// 2^6, any lane count, and whatever scratch it is handed.
#[test]
fn commit_tree_is_commit() {
    let mut rng = Rng::new(0xC0);
    for log_n in 2..=19usize {
        for log_batch in 1..=6usize.min(log_n - 1) {
            for log_inv_rate in 1..=3usize {
                // Keep it quick at the large sizes.
                if log_n > 14 && (log_batch != 6 || log_inv_rate == 3) {
                    continue;
                }
                for lanes in lane_counts(&mut rng, log_batch) {
                    let message = rand_words(&mut rng, lanes << (log_n - log_batch));
                    let (cm, pd) = commit(&message, log_n, log_batch, log_inv_rate);
                    for scratch in scratches(message.len()) {
                        let cap = scratch.capacity();
                        let (lean, tree) = commit_tree_in(&message, log_n, log_batch, log_inv_rate, scratch);
                        assert_eq!(
                            lean.root, cm.root,
                            "log_n={log_n} batch={log_batch} rate={log_inv_rate} lanes={lanes} scratch cap {cap}"
                        );
                        assert_eq!(tree, pd.merkle_tree);
                    }
                }
            }
        }
    }
}

/// `encoded_rows` re-encodes `commit`'s rows at any positions (unsorted, repeated, the first and last), in
/// groups of any size: one lane, a group that does not divide the lanes, all at once.
#[test]
fn encoded_rows_are_the_codeword_rows() {
    let mut rng = Rng::new(0xC1);
    for log_n in 2..=19usize {
        for log_batch in 1..=6usize.min(log_n - 1) {
            for log_inv_rate in 1..=3usize {
                if log_n > 14 && (log_batch != 6 || log_inv_rate == 3) {
                    continue;
                }
                for lanes in lane_counts(&mut rng, log_batch) {
                    let message = rand_words(&mut rng, lanes << (log_n - log_batch));
                    let (_, pd) = commit(&message, log_n, log_batch, log_inv_rate);
                    let rows_total = pd.codeword.len() / lanes;
                    let mut positions: Vec<usize> = (0..50).map(|_| pick(&mut rng, rows_total)).collect();
                    positions.extend([rows_total - 1, 0, rows_total - 1, rows_total / 2]);
                    let lane_words = rows_total;
                    for budget in [
                        0,
                        1,
                        lane_words - 1,
                        lane_words,
                        2 * lane_words,
                        3 * lane_words + 1,
                        7 * lane_words,
                        usize::MAX,
                    ] {
                        let rows = encoded_rows_within(&message, log_n, log_batch, log_inv_rate, &positions, budget);
                        assert_eq!(rows.len(), positions.len());
                        for (row, &q) in rows.iter().zip(&positions) {
                            assert_eq!(
                                row[..],
                                pd.codeword[q * lanes..(q + 1) * lanes],
                                "log_n={log_n} batch={log_batch} rate={log_inv_rate} lanes={lanes} budget={budget} row={q}"
                            );
                        }
                    }
                }
            }
        }
    }
}

/// A lean deeper level has the whole level's tree and opens its rows, for every interleaving 2^0..2^5,
/// rates 2^-1..2^-4 and message sizes from one column.
#[test]
fn lean_ligero_is_whole_ligero() {
    let mut rng = Rng::new(0xC2);
    for log_lanes in 0..=5usize {
        for log_inv_rate in 1..=4usize {
            for log_msg_cols in 0..=12usize {
                if log_msg_cols + log_lanes > 14 {
                    continue;
                }
                let poly = rng.ext_vec(1 << (log_msg_cols + log_lanes));
                let ntt = AdditiveNttF64::standard(log_msg_cols + log_inv_rate);
                let whole = ligero_commit_ext_within(&poly, log_msg_cols, log_lanes, log_inv_rate, &ntt, usize::MAX);
                let lean = ligero_commit_ext_within(&poly, log_msg_cols, log_lanes, log_inv_rate, &ntt, 0);
                assert!(matches!(lean.rows, LigeroRows::Message { .. }));
                assert_eq!(
                    lean.tree, whole.tree,
                    "lanes=2^{log_lanes} rate={log_inv_rate} cols=2^{log_msg_cols}"
                );
                let n = whole.block_len;
                let mut positions: Vec<usize> = (0..60).map(|_| pick(&mut rng, n)).collect();
                positions.extend([0, n - 1, 0]);
                assert_eq!(lean.rows(&positions), whole.rows(&positions));
                // All rows at once, in reverse.
                let all: Vec<usize> = (0..n).rev().collect();
                if n <= 1 << 12 {
                    assert_eq!(lean.rows(&all), whole.rows(&all));
                }
            }
        }
    }
}

/// How claims' scales are drawn.
#[derive(Clone, Copy, Debug)]
enum Scales {
    /// Every lane random.
    Random,
    /// Random, some lanes zero.
    SomeZero,
    /// `eq` of boolean high coordinates: one lane is one, the rest zero (a claim on one block).
    Boolean,
    /// Every lane zero.
    AllZero,
}

/// The dense weight of lane tensors over `n_lanes` lanes of `block` words.
fn dense_of(weight: &[LaneTensor], n_lanes: usize, block: usize) -> Vec<F192> {
    (0..n_lanes * block)
        .map(|i| {
            weight
                .iter()
                .fold(F192::ZERO, |acc, t| acc + t.scales[i / block] * t.low[i % block])
        })
        .collect()
}

fn tensors(rng: &mut Rng, claims: usize, n_lanes: usize, block: usize, how: Scales) -> Vec<LaneTensor> {
    (0..claims)
        .map(|c| {
            let low = if c % 2 == 0 {
                rng.ext_vec(block)
            } else {
                // An `eq` table, as the openings use.
                let point = rng.ext_vec(block.trailing_zeros() as usize);
                build_eq_table_ext(&point)
            };
            let one = pick(rng, n_lanes);
            let scales = (0..n_lanes)
                .map(|l| match how {
                    Scales::Random => rng.ext(),
                    Scales::SomeZero => {
                        if rng.bit() {
                            F192::ZERO
                        } else {
                            rng.ext()
                        }
                    }
                    Scales::Boolean => {
                        if l == one {
                            F192::ONE
                        } else {
                            F192::ZERO
                        }
                    }
                    Scales::AllZero => F192::ZERO,
                })
                .collect();
            LaneTensor { scales, low }
        })
        .collect()
}

fn run(f: impl FnOnce(&mut ProverState)) -> fiat_shamir::transcript::Proof {
    let mut ps = ProverState::from_label(b"adversarial");
    f(&mut ps);
    ps.into_proof()
}

/// One differential case: the dense prover on the written-out weight against the lane-tensor prover with the
/// codeword, without it (rows re-encoded), on an owned witness and tree, and with every deeper level lean.
fn check_case(pc: &ProverConfig, log_n: usize, n_lanes: usize, claims: usize, how: Scales, seed: u64) {
    let mut rng = Rng::new(seed);
    let block = 1usize << (log_n - pc.initial_k);
    let witness = rand_words(&mut rng, n_lanes * block);
    let weight = tensors(&mut rng, claims, n_lanes, block, how);
    let dense = dense_of(&weight, n_lanes, block);
    let target = inner_product_base_ext(&witness, &dense);
    let (_, pd) = commit(&witness, log_n, pc.initial_k, pc.log_inv_rates[0]);
    let expected = run(|ps| {
        recursive_prover_with_basis(
            pc,
            log_n,
            &witness,
            dense.clone(),
            target,
            &pd.codeword,
            &pd.merkle_tree,
            ps,
        )
    });
    let ctx = format!(
        "log_n={log_n} k0={} rates={:?} lanes={n_lanes} claims={claims} scales={how:?} seed={seed:#x}",
        pc.initial_k, pc.log_inv_rates
    );
    let with_codeword = run(|ps| {
        recursive_prover_with_lane_tensors(
            pc,
            log_n,
            &witness,
            &weight,
            target,
            Some(&pd.codeword),
            &pd.merkle_tree,
            ps,
        )
    });
    assert!(with_codeword == expected, "with codeword: {ctx}");
    let reencoded =
        run(|ps| recursive_prover_with_lane_tensors(pc, log_n, &witness, &weight, target, None, &pd.merkle_tree, ps));
    assert!(reencoded == expected, "re-encoded rows: {ctx}");
    let (_, tree) = commit_tree(&witness, log_n, pc.initial_k, pc.log_inv_rates[0]);
    let owned = run(|ps| {
        recursive_prover_with_lane_tensors(pc, log_n, witness.clone(), &weight, target, None, tree.clone(), ps)
    });
    assert!(owned == expected, "owned witness and tree: {ctx}");
    // Every deeper level lean, on this thread.
    LEAN_LIGERO_BYTES_OVERRIDE.set(Some(0));
    let lean = run(|ps| recursive_prover_with_lane_tensors(pc, log_n, &witness, &weight, target, None, &tree, ps));
    let lean_dense = run(|ps| {
        recursive_prover_with_basis(
            pc,
            log_n,
            &witness,
            dense.clone(),
            target,
            &pd.codeword,
            &pd.merkle_tree,
            ps,
        )
    });
    LEAN_LIGERO_BYTES_OVERRIDE.set(None);
    assert!(lean == expected, "lean deeper levels: {ctx}");
    assert!(lean_dense == expected, "dense prover, lean deeper levels: {ctx}");
}

/// The lane-tensor prover proves, byte for byte, what the dense prover proves on the weight written out: on the
/// production profile at log_n = 15..=20 and rates 2^-1..2^-3, on the test fallback below it, at any lane
/// count, with 1..=5 claims whose scales are random, partly zero, boolean or all zero.
#[test]
fn lane_tensor_prover_is_the_dense_prover() {
    let mut rng = Rng::new(0xC3);
    let mut cases = 0;
    for log_n in 8..=20usize {
        let mut configs = vec![];
        for rate in 1..=3usize {
            if let Ok(pc) = config_for_rate(log_n, rate) {
                configs.push(pc);
            }
        }
        if configs.is_empty() {
            configs.push(test_config_for(log_n));
        }
        for pc in &configs {
            let width = 1usize << pc.initial_k;
            let mut lanes = vec![1, 2, 3, width - 1, width, 1 + pick(&mut rng, width)];
            lanes.retain(|&l| l >= 1 && l <= width);
            lanes.sort_unstable();
            lanes.dedup();
            if log_n > 17 {
                lanes = vec![width - 5, width];
            }
            for &n_lanes in &lanes {
                for (claims, how) in [
                    (1, Scales::Random),
                    (2, Scales::SomeZero),
                    (3, Scales::Boolean),
                    (5, Scales::Random),
                    (2, Scales::AllZero),
                ] {
                    if log_n > 17 && claims > 2 {
                        continue;
                    }
                    check_case(pc, log_n, n_lanes, claims, how, rng.next_u64());
                    cases += 1;
                }
            }
        }
    }
    eprintln!("{cases} cases");
}

/// Which deeper levels the production profile keeps lean (codeword >= 1 GiB), for the sizes the openings use.
#[test]
fn print_lean_levels() {
    for log_n in 15..=28usize {
        let Ok(pc) = config_for_rate(log_n, 1) else { continue };
        let shapes = pc.level_shapes(log_n);
        let bytes: Vec<String> = (1..shapes.levels)
            .map(|i| {
                let b = shapes.block_len[i] * (1usize << shapes.ks[i]) * 24;
                format!(
                    "L{i}: {} MiB{}",
                    b >> 20,
                    if b >= LEAN_LIGERO_BYTES { " LEAN" } else { "" }
                )
            })
            .collect();
        eprintln!(
            "log_n={log_n} rates={:?} ks={:?} {}",
            pc.log_inv_rates,
            shapes.ks,
            bytes.join(", ")
        );
    }
}

/// FINDING (fixed): the lane-tensor prover with no claim at all panicked (`assert!(!weight.is_empty() && ..)` in
/// `tensor_lane_rounds`), where the dense prover proves the zero weight. With `!weight.is_empty() &&` dropped
/// from that assert, it proves what the dense prover proves.
#[test]
fn no_claims() {
    let log_n = 15;
    let pc = config_for_rate(log_n, 1).unwrap();
    let mut rng = Rng::new(0xC4);
    let block = 1usize << (log_n - pc.initial_k);
    let witness = rand_words(&mut rng, 7 * block);
    let (_, pd) = commit(&witness, log_n, pc.initial_k, 1);
    let expected = run(|ps| {
        recursive_prover_with_basis(
            &pc,
            log_n,
            &witness,
            vec![F192::ZERO; witness.len()],
            F192::ZERO,
            &pd.codeword,
            &pd.merkle_tree,
            ps,
        )
    });
    let got = std::panic::catch_unwind(|| {
        run(|ps| recursive_prover_with_lane_tensors(&pc, log_n, &witness, &[], F192::ZERO, None, &pd.merkle_tree, ps))
    });
    match got {
        Ok(p) => assert!(p == expected, "differs from the dense prover"),
        Err(_) => panic!("the lane-tensor prover panics on an empty claim list, the dense prover proves it"),
    }
}

/// Tiny shapes for Miri (`cargo +nightly miri test --target x86_64-unknown-linux-gnu -p pcs miri_`):
/// `commit_tree_in` on scratch buffers of every kind (its `set_len` over uninitialised capacity),
/// `encoded_rows` (an uninitialised group buffer), a lean level's commit and rows.
#[test]
fn miri_commit_tree_rows_and_lean_level() {
    let mut rng = Rng::new(0xC5);
    let (log_n, log_batch, log_inv_rate) = (6usize, 2usize, 1usize);
    let message = rand_words(&mut rng, 3 << (log_n - log_batch));
    let (cm, pd) = commit(&message, log_n, log_batch, log_inv_rate);
    for scratch in scratches(message.len()) {
        let (lean, tree) = commit_tree_in(&message, log_n, log_batch, log_inv_rate, scratch);
        assert_eq!((lean.root, &tree), (cm.root, &pd.merkle_tree));
    }
    let positions = [5usize, 0, 31, 5];
    for budget in [1, usize::MAX] {
        let rows = encoded_rows_within(&message, log_n, log_batch, log_inv_rate, &positions, budget);
        for (row, &q) in rows.iter().zip(&positions) {
            assert_eq!(row[..], pd.codeword[q * 3..(q + 1) * 3]);
        }
    }
    let poly = rng.ext_vec(1 << 4);
    let ntt = AdditiveNttF64::standard(3 + 2);
    let whole = ligero_commit_ext_within(&poly, 3, 1, 2, &ntt, usize::MAX);
    let lean = ligero_commit_ext_within(&poly, 3, 1, 2, &ntt, 0);
    assert_eq!(lean.tree, whole.tree);
    let positions = [0usize, 7, 31, 8, 7];
    assert_eq!(lean.rows(&positions), whole.rows(&positions));
}

/// Tiny shape for Miri: one whole lane-tensor proof against the dense one, rows re-encoded, owned witness.
#[test]
fn miri_lane_tensor_prover() {
    let log_n = 8;
    let pc = test_config_for(log_n);
    let block = 1usize << (log_n - pc.initial_k);
    let mut rng = Rng::new(0xC6);
    let n_lanes = (1usize << pc.initial_k) - 1;
    let witness = rand_words(&mut rng, n_lanes * block);
    let weight = tensors(&mut rng, 2, n_lanes, block, Scales::SomeZero);
    let dense = dense_of(&weight, n_lanes, block);
    let target = inner_product_base_ext(&witness, &dense);
    let (_, pd) = commit(&witness, log_n, pc.initial_k, pc.log_inv_rates[0]);
    let expected = run(|ps| {
        recursive_prover_with_basis(
            &pc,
            log_n,
            &witness,
            dense.clone(),
            target,
            &pd.codeword,
            &pd.merkle_tree,
            ps,
        )
    });
    let (_, tree) = commit_tree(&witness, log_n, pc.initial_k, pc.log_inv_rates[0]);
    let got =
        run(|ps| recursive_prover_with_lane_tensors(&pc, log_n, witness.clone(), &weight, target, None, tree, ps));
    assert!(got == expected);
}
