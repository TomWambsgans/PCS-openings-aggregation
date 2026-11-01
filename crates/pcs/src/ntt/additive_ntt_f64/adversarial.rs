//! Adversarial review of the replica / rows-only encodes (commit 411866f): every new transform is checked
//! against the untouched whole-codeword encode, over shapes the production callers never use as well as the
//! ones they do.

use super::*;
use primitives::test_rng::Rng;

fn rand_words(rng: &mut Rng, n: usize) -> Vec<F64> {
    (0..n).map(|_| F64(rng.next_u64())).collect()
}

/// The whole codeword of a row-major message, the untouched encoder.
fn whole(k: usize, msg: &[F64], lanes: usize, r: usize) -> Vec<F64> {
    let mut data = vec![F64::ZERO; msg.len() << r];
    data[..msg.len()].copy_from_slice(msg);
    AdditiveNttF64::standard(k).encode_interleaved_in_place(&mut data, lanes, r);
    data
}

/// Lane counts a commitment can have: every count up to 9, then a few odd and power-of-two ones up to 64 (and
/// 3x for the F192 lanes of a deeper level).
const LANES: &[usize] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 16, 17, 24, 37, 48, 59, 63, 64, 96, 192];

/// Under Miri, the sweeps below shrink to domains up to `2^MIRI_MAX_K` and these lane counts.
const MIRI_MAX_K: usize = 5;
const MIRI_LANES: &[usize] = &[1, 3, 8];

/// Whether a sweep skips `lanes` lanes on a `2^k` domain under Miri.
fn miri_skips(k: usize, lanes: usize) -> bool {
    cfg!(miri) && (k > MIRI_MAX_K || !MIRI_LANES.contains(&lanes))
}

/// A replica's transform is F_2-affine in the block index, as the whole one's is: its twiddles are the
/// whole transform's at the replica's blocks, for every layer, every block and every rate, and nested replicas
/// compose. `twiddles_radix8` (the fused kernel's) agrees with `twiddle` on replicas, offsets included.
#[test]
fn replica_twiddles_are_the_whole_transforms() {
    for k in 1..=if cfg!(miri) { MIRI_MAX_K + 1 } else { 14 } {
        let full = AdditiveNttF64::standard(k);
        for r in 0..=k.min(5) {
            for b in 0..1usize << r {
                let rep = full.replica(r, b);
                assert_eq!(rep.log_domain_size(), k - r);
                for layer in 0..k - r {
                    for block in 0..1usize << layer {
                        assert_eq!(
                            rep.twiddle(layer, block),
                            full.twiddle(layer + r, (b << layer) | block),
                            "k={k} r={r} b={b} layer={layer} block={block}"
                        );
                    }
                    if layer + 2 < k - r {
                        for block in 0..1usize << layer {
                            let t = rep.twiddles_radix8(layer, block);
                            let want = [
                                rep.twiddle(layer, block),
                                rep.twiddle(layer + 1, 2 * block),
                                rep.twiddle(layer + 1, 2 * block + 1),
                                rep.twiddle(layer + 2, 4 * block),
                                rep.twiddle(layer + 2, 4 * block + 1),
                                rep.twiddle(layer + 2, 4 * block + 2),
                                rep.twiddle(layer + 2, 4 * block + 3),
                            ];
                            assert_eq!(t, want, "radix-8 k={k} r={r} b={b} layer={layer} block={block}");
                        }
                    }
                }
                // Nested: replica b2 (of 2^r2) of replica b (of 2^r) is replica (b << r2) | b2 (of 2^(r + r2)).
                for r2 in 0..=(k - r).min(2) {
                    for b2 in 0..1usize << r2 {
                        let nested = rep.replica(r2, b2);
                        let direct = full.replica(r + r2, (b << r2) | b2);
                        for layer in 0..k - r - r2 {
                            for block in 0..1usize << layer {
                                assert_eq!(nested.twiddle(layer, block), direct.twiddle(layer, block));
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Encoding one replica at a time, in place, from a copy of the message, gives the whole codeword's rows,
/// for every rate up to 2^-4, lane counts 1..192 and domains 2^1 .. 2^20; the row sink sees each row exactly
/// once, with the codeword's value.
#[test]
fn replica_encode_is_the_whole_encode() {
    let mut rng = Rng::new(0xADE1);
    for k in 1..=20usize {
        for r in 1..=k.min(4) {
            for &lanes in LANES {
                // Keep the sweep a few seconds: big domains with few lane counts.
                if (lanes << k) > (1 << 22) || (k > 14 && !matches!(lanes, 1 | 3 | 37 | 64)) || miri_skips(k, lanes) {
                    continue;
                }
                let msg = rand_words(&mut rng, lanes << (k - r));
                let want = whole(k, &msg, lanes, r);
                let full = AdditiveNttF64::standard(k);
                for b in 0..1usize << r {
                    let rep = full.replica(r, b);
                    let mut got = msg.clone();
                    rep.encode_interleaved_in_place(&mut got, lanes, 0);
                    assert_eq!(
                        got[..],
                        want[b * msg.len()..(b + 1) * msg.len()],
                        "k={k} r={r} lanes={lanes} replica={b}"
                    );
                    // With a row sink, as `commit_tree` encodes.
                    let seen = std::sync::Mutex::new(vec![0u8; 1 << (k - r)]);
                    let mut sunk = msg.clone();
                    let expect = &want[b * msg.len()..(b + 1) * msg.len()];
                    rep.encode_interleaved_in_place_with(&mut sunk, lanes, 0, &|row, rows: &[F64]| {
                        assert_eq!(rows.len() % lanes, 0);
                        assert_eq!(
                            rows,
                            &expect[row * lanes..row * lanes + rows.len()],
                            "sunk rows at {row}"
                        );
                        let mut seen = seen.lock().unwrap();
                        for i in row..row + rows.len() / lanes {
                            seen[i] += 1;
                        }
                    });
                    assert!(seen.into_inner().unwrap().iter().all(|&c| c == 1), "each row once");
                }
            }
        }
    }
}

/// Sorted distinct rows to want: none, the first, the last, every one, a few at random, half at random, and
/// two adjacent at a block boundary.
fn wanted_sets(rng: &mut Rng, rows: usize) -> Vec<Vec<usize>> {
    let mut sets = vec![vec![], vec![0], vec![rows - 1], (0..rows).collect()];
    for count in [1usize, 3, 40, rows / 2] {
        let mut s: Vec<usize> = (0..count).map(|_| rng.next_u64() as usize % rows).collect();
        s.sort_unstable();
        s.dedup();
        sets.push(s);
    }
    if rows >= 2 {
        sets.push(vec![rows / 2 - 1, rows / 2]);
    }
    sets
}

/// The rows-only encodes (in place, and from a separate message, whole or by replica) give the wanted rows
/// of the whole encode, whatever else they leave.
#[test]
fn rows_only_encode_gives_the_wanted_rows() {
    let mut rng = Rng::new(0xADE2);
    for k in 1..=20usize {
        for r in 1..=k.min(4) {
            for &lanes in LANES {
                if (lanes << k) > (1 << 22)
                    || (k > 14 && !matches!(lanes, 1 | 5 | 59 | 64 | 192))
                    || miri_skips(k, lanes)
                {
                    continue;
                }
                let msg = rand_words(&mut rng, lanes << (k - r));
                let want = whole(k, &msg, lanes, r);
                let full = AdditiveNttF64::standard(k);
                for rows in wanted_sets(&mut rng, 1 << k) {
                    // In place, as `encoded_rows` encodes a group of lanes.
                    let mut got = vec![F64(0xDEAD); msg.len() << r];
                    got[..msg.len()].copy_from_slice(&msg);
                    full.encode_interleaved_rows_in_place(&mut got, lanes, r, &rows);
                    for &q in &rows {
                        assert_eq!(
                            got[q * lanes..(q + 1) * lanes],
                            want[q * lanes..(q + 1) * lanes],
                            "in place: k={k} r={r} lanes={lanes} row={q} of {}",
                            rows.len()
                        );
                    }
                    // From a separate message into an uninitialised-looking codeword.
                    let mut got = vec![F64(0xBEEF); msg.len() << r];
                    full.encode_interleaved_rows_with(&mut got, &msg, lanes, r, &rows);
                    for &q in &rows {
                        assert_eq!(
                            got[q * lanes..(q + 1) * lanes],
                            want[q * lanes..(q + 1) * lanes],
                            "with msg: k={k} r={r} lanes={lanes} row={q}"
                        );
                    }
                    // One replica at a time, as a lean deeper level reopens its rows.
                    let per = 1usize << (k - r);
                    for b in 0..1usize << r {
                        let local: Vec<usize> = rows.iter().filter(|&&q| q / per == b).map(|&q| q - b * per).collect();
                        let mut got = vec![F64(0xF00D); msg.len()];
                        full.replica(r, b)
                            .encode_interleaved_rows_with(&mut got, &msg, lanes, 0, &local);
                        for &q in &local {
                            assert_eq!(
                                got[q * lanes..(q + 1) * lanes],
                                want[(b * per + q) * lanes..(b * per + q + 1) * lanes],
                                "replica rows: k={k} r={r} lanes={lanes} replica={b} row={q}"
                            );
                        }
                    }
                }
            }
        }
    }
}

/// A row list that is not sorted, or repeats a row, is refused rather than encoded wrong.
#[test]
#[should_panic(expected = "sorted, distinct rows")]
fn rows_only_encode_refuses_repeats() {
    let mut data = vec![F64::ZERO; 16];
    AdditiveNttF64::standard(4).encode_interleaved_rows_in_place(&mut data, 1, 1, &[3, 3]);
}

/// Tiny shapes for Miri (`cargo +nightly miri test --target x86_64-unknown-linux-gnu -p pcs miri_`, with the
/// `bench` dev-dependency removed, as jemalloc does not cross-build, and plain copies in place of streaming
/// stores, as Miri runs no inline assembly): the replica and rows-only encodes, in place and from a separate
/// message into an uninitialised codeword. At the cache budgets of x86 they take `replicate` and the deep pass;
/// with `L2_WORDS = 16` and `L3_WORDS = 32` (a local edit), one or two gathered passes from the message first.
///
/// FINDING (fixed): under Stacked Borrows and Tree Borrows alike Miri reported UB in the in-place encodes:
/// `encode_interleaved_in_place{,_with}` (pre-existing, leanVM's) and `encode_interleaved_rows_in_place` (new)
/// took `msg = SendPtr(data.as_mut_ptr())` and then passed `data` to `transform`, whose `&mut` argument is
/// protected (LLVM `noalias`); the first pass / `replicate` then read the message through `msg`, a pointer not
/// derived from that argument, while the function wrote through it. With `-Zmiri-disable-stacked-borrows` this
/// test passed (no uninitialised read, no out-of-bounds access, no data race). The message is now
/// `Message::InPlace`, its pointer derived from the buffer by each pass that reads it; this test passes under
/// both models.
#[test]
fn miri_replica_and_rows_only_encodes() {
    let mut rng = Rng::new(0xADE3);
    for (k, r, lanes) in [(5usize, 1usize, 3usize), (6, 2, 1), (4, 1, 6), (8, 1, 3)] {
        let msg = rand_words(&mut rng, lanes << (k - r));
        let want = whole(k, &msg, lanes, r);
        let full = AdditiveNttF64::standard(k);
        for b in 0..1usize << r {
            let mut got = msg.clone();
            full.replica(r, b).encode_interleaved_in_place(&mut got, lanes, 0);
            assert_eq!(got[..], want[b * msg.len()..(b + 1) * msg.len()]);
        }
        let rows = [0usize, 3, (1 << k) - 1];
        let mut got = vec![F64::ZERO; msg.len() << r];
        got[..msg.len()].copy_from_slice(&msg);
        full.encode_interleaved_rows_in_place(&mut got, lanes, r, &rows);
        // Separate message, codeword uninitialised as the callers allocate it.
        // SAFETY: under test, the encode must write every word before reading it (Miri checks).
        let mut fresh = unsafe { primitives::uninit_vec::<F64>(msg.len() << r) };
        full.encode_interleaved_rows_with(&mut fresh, &msg, lanes, r, &rows);
        for &q in &rows {
            assert_eq!(got[q * lanes..(q + 1) * lanes], want[q * lanes..(q + 1) * lanes]);
            assert_eq!(fresh[q * lanes..(q + 1) * lanes], want[q * lanes..(q + 1) * lanes]);
        }
    }
}
