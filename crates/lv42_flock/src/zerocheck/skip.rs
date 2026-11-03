// Part of this repository. Builds on leanVM's zerocheck prover (https://github.com/leanEthereum/leanVM, commit
// 42422001): the driver, its bit and table rounds and `send_round` are crates/flock/src/zerocheck.rs's (the table
// rounds copied, the rest called), and the round-1 kernel follows crates/flock/src/zerocheck/
// univariate_skip_optimized.rs (the fixed small and medium eq coordinates, the shift-reduce, the C part on S lifted
// to Λ). New here: a univariate skip of any `k` in 3..=6, the round-1 kernel for it, and the bit passes' schedule.
// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0. MIT OR Apache-2.0; see NOTICE.md.
//! The zerocheck with a univariate skip of `k` variables, `3 ≤ k ≤ 6`: leanVM's protocol with `k` for its fixed 6
//! (`leanvm_flock_gas::flock_min`'s `zerocheck` verifies it).
//!
//! - The eq point `r` on the `m - k` variables after the skip: leanVM's seven fixed coordinates (three small, four
//!   medium), then `m - k - 7` sampled.
//! - Round 1: `P(λ) = Σ_x eq(r, x) (â(λ, x) b̂(λ, x) + ĉ(λ, x))` on the coset `Λ = φ_8(2^k + i)`, `i < 2^k`, where
//!   `â(·, x)` extends the `2^k` bits of group `x` from `S = φ_8(i)`; `P` vanishes on `S`.
//! - Then `z`, `m - k` rounds of degree 3 (the low variable first, `G(0)` left to the verifier), `â`, `b̂`.
//!
//! **Round 1** ([`round1`]). A witness bit's index is `(s, K, b, x)`: `s` the `k` skip bits, `K` the three small
//! coordinates (8 consecutive groups), `b` the four medium ones (16 runs of 8 groups), `x` the rest. Since
//! `eq(r_small, K) = C_s φ_8(X^K)` (asserted), `Σ_K eq(r_small, K) φ_8(y_K) = C_s φ_8(Σ_K X^K y_K)`: the eight groups'
//! products `â b̂ ∈ F_8` combine in `F_8` (`gf2p8mulb` on x86), and the C bits of a lane are one byte, bit `K` from
//! group `K` (an 8×8 bit transpose). The 16 medium positions are table lookups of `eq(r_med, b) C_s φ_8(v)`; one
//! product a lane per `x`. The C part is computed on `S` and extended to `Λ` (`ntt_extend_vec`), as leanVM does.
//!
//! **The other rounds** are leanVM's kernels: the bit passes fold a position's `2^(k + t)` bits at level `t` with
//! `L(z) ⊗ eq(ρ_1..ρ_t)` (`BitFold`, rows of 1 to 128 bytes), two rounds a pass, until the rows are 64 or 128 bytes;
//! that pass stores the three folded tables, and the table rounds finish.

use fiat_shamir::transcript::ProverState;
use pcs::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};
use primitives::field::{F8, F192, PHI_8_TABLE_192 as PHI_8_TABLE};
use primitives::multilinear::lagrange_weights_naive;

use super::bit_fold::BitFold;
use super::multilinear::{
    PackedWitness, bit_round_materialize, bit_round_pair, bit_round_pair_bytes, fold_and_compute_round_pair_into,
    fold_and_compute_round_single_into, fold_in_place_pair, fold_in_place_single, interpolate_at_z_combined,
    round_pair_naive, round_single_naive,
};
use super::univariate_skip::{SplitEq, build_eq, ntt_extend_vec};
use super::univariate_skip_optimized::{c_s, medium_challenges, small_challenges};
use super::{K_SKIP, N_INNER, PaddingSpec, ZerocheckClaim, send_round};

/// The smallest skip this module proves: a group is a whole byte.
pub const MIN_SKIP: usize = 3;

/// The zerocheck with a skip of `k`: leanVM's own prover ([`super::prove_packed_padded`]) at `k = 6`, this module's
/// otherwise.
pub fn prove_packed_padded_skip(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k: usize,
    padding: &PaddingSpec,
    ps: &mut ProverState,
) -> ZerocheckClaim {
    if k == K_SKIP {
        return super::prove_packed_padded(a_packed, b_packed, c_packed, m, padding, ps);
    }
    prove_skip(a_packed, b_packed, c_packed, m, k, padding, ps)
}

/// The last [`prove_skip`]'s stages and their seconds (round 1, each bit pass, the storing pass, the table rounds),
/// for profiling.
pub static STAGES: std::sync::Mutex<Vec<(String, f64)>> = std::sync::Mutex::new(Vec::new());

/// This module's zerocheck with a skip of `k` (at `k = 6` too, where it writes what leanVM's does: a test of it).
pub fn prove_skip(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k: usize,
    padding: &PaddingSpec,
    ps: &mut ProverState,
) -> ZerocheckClaim {
    assert!((MIN_SKIP..=K_SKIP).contains(&k), "a skip of 3 to 6 variables");
    assert!(m >= k + N_INNER + 1, "m ≥ k + 8");
    let bytes = (1usize << m) / 8;
    assert!(a_packed.len() == bytes && b_packed.len() == bytes && c_packed.len() == bytes);
    let n_mlv = m - k;

    // The eq point after the skip: the fixed coordinates, then the sampled ones.
    let r_rest: Vec<F192> = small_challenges()
        .into_iter()
        .chain(medium_challenges())
        .chain(ps.sample_vec(m - k - N_INNER))
        .collect();

    let mut stages: Vec<(String, f64)> = Vec::new();
    let mut clock = std::time::Instant::now();
    let mut lap = |stages: &mut Vec<(String, f64)>, name: String| {
        let now = std::time::Instant::now();
        stages.push((name, (now - clock).as_secs_f64()));
        clock = now;
    };
    let span = tracing::info_span!("Round 1").entered();
    let round1 = round1(a_packed, b_packed, c_packed, m, k, &r_rest);
    drop(span);
    lap(&mut stages, "round 1".into());
    for &x in &round1 {
        ps.add_scalar(x);
    }
    let z = ps.sample();

    let span = tracing::info_span!("Bit rounds").entered();
    let bits = PackedWitness {
        a: a_packed,
        b: b_packed,
        c: c_packed,
    };
    let lagrange = lagrange_weights_naive(k, z);
    let mut c_running = interpolate_at_z_combined(&round1, k, z);
    let mut mlv_chis: Vec<F192> = Vec::with_capacity(n_mlv);
    // Pairs of rounds from the bits while the stored tables would be larger than at leanVM's level 4 of a skip of
    // 6 (rows of 2^10 bits): passes at levels 0, 2, .., the last stored at level 2 * passes.
    let passes = (10 - k) / 2;
    for t in (0..(n_mlv - 1) & !1).step_by(2).take(passes) {
        let pair = if t == 0 && k == MIN_SKIP {
            // Positions of one byte: the products from a table of all of them.
            let weights: [F192; 8] = lagrange[..].try_into().expect("8 weights");
            bit_round_pair_bytes(bits, &weights, &r_rest[1..], padding)
        } else {
            let fold = BitFold::at_level(&lagrange, &mlv_chis);
            bit_round_pair(bits, &fold, &r_rest[t + 1..], padding)
        };
        let (g1, g_inf) = pair.first;
        c_running = send_round(ps, c_running, r_rest[t], None, g1, g_inf, &mut mlv_chis);
        let (g1, g_inf) = pair.second(mlv_chis[t]);
        c_running = send_round(ps, c_running, r_rest[t + 1], None, g1, g_inf, &mut mlv_chis);
        lap(&mut stages, format!("bit pass at level {t}"));
    }
    let materialize_level = mlv_chis.len();
    let fold = BitFold::at_level(&lagrange, &mlv_chis);
    let ((g1, g_inf), [mut a_mlv, mut b_mlv, mut c_mlv]) =
        bit_round_materialize(bits, &fold, &r_rest[materialize_level + 1..], padding);
    c_running = send_round(ps, c_running, r_rest[materialize_level], None, g1, g_inf, &mut mlv_chis);
    drop(span);
    lap(&mut stages, format!("storing pass at level {materialize_level}"));

    // The table rounds: leanVM's (crates/flock/src/zerocheck.rs), unchanged.
    let span = tracing::info_span!("Table rounds").entered();
    let n_in = a_mlv.len();
    let (mut a_nxt, mut b_nxt, mut c_nxt) = if n_in >= 1024 {
        // SAFETY (x3): the fused rounds below write every slot they read; a buffer is only ever read over the prefix
        // a round just wrote.
        unsafe {
            (
                primitives::uninit_vec::<F192>(n_in / 2),
                primitives::uninit_vec::<F192>(n_in / 2),
                primitives::uninit_vec::<F192>(n_in / 2),
            )
        }
    } else {
        (Vec::new(), Vec::new(), Vec::new())
    };
    for i in materialize_level..(n_mlv - 1) {
        let chi_prev = mlv_chis[i];
        let log_n_before = a_mlv.len().trailing_zeros() as usize;
        let r_eq = &r_rest[i + 2..];
        let (m1, mi) = if log_n_before >= 10 {
            let half = a_mlv.len() / 2;
            let (m1, mi) =
                fold_and_compute_round_pair_into(&a_mlv, &b_mlv, &mut a_nxt[..half], &mut b_nxt[..half], chi_prev, r_eq);
            let m1c = fold_and_compute_round_single_into(&c_mlv, &mut c_nxt[..half], chi_prev, r_eq);
            std::mem::swap(&mut a_mlv, &mut a_nxt);
            std::mem::swap(&mut b_mlv, &mut b_nxt);
            std::mem::swap(&mut c_mlv, &mut c_nxt);
            a_mlv.truncate(half);
            b_mlv.truncate(half);
            c_mlv.truncate(half);
            (m1 + m1c, mi)
        } else {
            fold_in_place_pair(&mut a_mlv, &mut b_mlv, chi_prev);
            fold_in_place_single(&mut c_mlv, chi_prev);
            let (m1, mi) = round_pair_naive(&a_mlv, &b_mlv, r_eq);
            (m1 + round_single_naive(&c_mlv, r_eq), mi)
        };
        let r = r_rest[i + 1];
        let g0 = (r == F192::ONE).then(|| {
            let eq = build_eq(r_eq);
            (0..eq.len()).fold(F192::ZERO, |acc, x| acc + eq[x] * (a_mlv[2 * x] * b_mlv[2 * x] + c_mlv[2 * x]))
        });
        c_running = send_round(ps, c_running, r, g0, m1, mi, &mut mlv_chis);
    }
    let chi_last = *mlv_chis.last().expect("at least one round");
    fold_in_place_pair(&mut a_mlv, &mut b_mlv, chi_last);
    let (final_a_eval, final_b_eval) = (a_mlv[0], b_mlv[0]);
    let final_c_eval = c_running + final_a_eval * final_b_eval;
    ps.add_scalar(final_a_eval);
    ps.add_scalar(final_b_eval);
    drop(span);
    lap(&mut stages, "table rounds".into());
    *STAGES.lock().expect("the stages") = stages;
    ZerocheckClaim {
        z,
        mlv_challenges: mlv_chis,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: final_c_eval,
    }
}

/// The small coordinates' eight groups and the medium coordinates' sixteen runs of them: the groups an `x` covers.
const GROUPS: usize = 8 * 16;

/// The round-1 message `P(λ) = P^AB(λ) + P^C(λ)` on `Λ`, as the verifier reads it, for a skip of `k`: at `k = 3`
/// with GFNI by [`round1_bytes`], otherwise by [`round1_generic`].
pub fn round1(a: &[u8], b: &[u8], c: &[u8], m: usize, k: usize, r_rest: &[F192]) -> Vec<F192> {
    if k == MIN_SKIP && super::bit_fold::GFNI {
        return round1_bytes(a, b, c, m, r_rest);
    }
    if (4..=5).contains(&k) && super::bit_fold::GFNI {
        return round1_words(a, b, c, m, k, r_rest);
    }
    round1_folded(a, b, c, m, k, r_rest)
}

/// Round 1 at a skip of 4 or 5 (a group of `nc = 2` or 4 bytes, `8 nc` lanes), as [`round1_bytes`] is at 3: per
/// medium position and per 8 lanes, the 8 groups' extension is `nc` affines (byte `j` of every group broadcast, against
/// lane `λ`'s matrix of bits `8 j..8 j + 8`), XORed; then the products, the powers `X^K`, the fold over `K`; the C row
/// is `nc` bit transposes; the medium positions a [`BitFold`] of 16-byte rows.
#[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
pub fn round1_words(a: &[u8], b: &[u8], c: &[u8], m: usize, k: usize, r_rest: &[F192]) -> Vec<F192> {
    use core::arch::x86_64::*;
    assert!((4..=5).contains(&k));
    assert_eq!(r_rest.len(), m - k);
    let ell = 1usize << k;
    let nc = ell / 8;
    let ntt_s = AdditiveNttGf8::new(k, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k, F8(ell as u8));
    let table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    // Column s (input bit s of a group, byte s / 8) at every lane.
    let columns: Vec<Vec<F8>> = (0..ell)
        .map(|s| {
            let mut bytes = vec![0u8; nc];
            bytes[s / 8] = 1 << (s % 8);
            let mut out = vec![F8::ZERO; ell];
            table.apply(&bytes, &mut out);
            out
        })
        .collect();
    // matrices[j][g]: the 8 qwords of lanes 8 g..8 g + 8 for the group's byte j (input bit i is bit 8 j + i).
    let matrices: Vec<Vec<[u64; 8]>> = (0..nc)
        .map(|j| {
            (0..nc)
                .map(|g| {
                    std::array::from_fn(|q| {
                        let lane = 8 * g + q;
                        (0..8).fold(0u64, |acc, bit| {
                            let row = (0..8).fold(0u64, |r, i| r | u64::from(columns[8 * j + i][lane].0 >> bit & 1) << i);
                            acc | row << (8 * (7 - bit))
                        })
                    })
                })
                .collect()
        })
        .collect();
    let eq_small = build_eq(&r_rest[..3]);
    let cs = c_s();
    for (kk, &e) in eq_small.iter().enumerate() {
        assert_eq!(e, cs * PHI_8_TABLE[1 << kk], "the small coordinates' eq is C_s X^K");
    }
    let eq_med = build_eq(&r_rest[3..N_INNER]);
    let weights: Vec<F192> = (0..128).map(|w| eq_med[w / 8] * cs * PHI_8_TABLE[1 << (w % 8)]).collect();
    let fold = BitFold::new(&weights);
    let eq = SplitEq::new(&r_rest[N_INNER..]);
    let lo_size = 1usize << eq.n_lo;
    let block = GROUPS * nc;
    assert_eq!(a.len(), (lo_size << eq.n_hi) * block);

    // Byte j of the 8 groups at `at` (group K at at + K nc), one byte a group.
    let gather = |data: &[u8], at: usize, j: usize| (0..8).fold(0u64, |w, kk| w | u64::from(data[at + kk * nc + j]) << (8 * kk));
    // SAFETY: the target features are enabled at compile time; the matrices are 8 qwords each.
    let ab_row = |x: &[u64], y: &[u64], g: usize| -> u64 {
        unsafe {
            let (mut ea, mut eb) = (_mm512_setzero_si512(), _mm512_setzero_si512());
            for j in 0..nc {
                let mj = _mm512_loadu_si512(matrices[j][g].as_ptr().cast());
                ea = _mm512_xor_si512(ea, _mm512_gf2p8affine_epi64_epi8::<0>(_mm512_set1_epi64(x[j] as i64), mj));
                eb = _mm512_xor_si512(eb, _mm512_gf2p8affine_epi64_epi8::<0>(_mm512_set1_epi64(y[j] as i64), mj));
            }
            let powers = _mm512_set1_epi64(0x8040_2010_0804_0201u64 as i64);
            let t = _mm512_gf2p8mul_epi8(_mm512_gf2p8mul_epi8(ea, eb), powers);
            let t = _mm512_xor_si512(t, _mm512_srli_epi64::<32>(t));
            let t = _mm512_xor_si512(t, _mm512_srli_epi64::<16>(t));
            let t = _mm512_xor_si512(t, _mm512_srli_epi64::<8>(t));
            _mm_cvtsi128_si64(_mm512_cvtepi64_epi8(t)) as u64
        }
    };
    let zero = || (vec![F192::ZERO; ell], vec![F192::ZERO; ell]);
    let (ab, c_s_part) = parallel::fold_reduce(
        1usize << eq.n_hi,
        zero,
        |acc, x_hi| {
            let (mut part_ab, mut part_c) = zero();
            let mut rows = vec![[0u8; 16]; 2 * ell];
            let mut folded = vec![F192::ZERO; 2 * ell];
            let mut out = [F192::ZERO; super::bit_fold::BLOCK];
            let (mut xa, mut xb) = (vec![0u64; nc], vec![0u64; nc]);
            for x_lo in 0..lo_size {
                let at = (x_hi * lo_size + x_lo) * block;
                for medium in 0..16 {
                    let o = at + 8 * nc * medium;
                    for j in 0..nc {
                        xa[j] = gather(a, o, j);
                        xb[j] = gather(b, o, j);
                    }
                    for g in 0..nc {
                        let row = ab_row(&xa, &xb, g);
                        let crow = transpose_8x8(gather(c, o, g));
                        for q in 0..8 {
                            rows[8 * g + q][medium] = (row >> (8 * q)) as u8;
                            rows[ell + 8 * g + q][medium] = (crow >> (8 * q)) as u8;
                        }
                    }
                }
                for (chunk, dst) in rows.chunks(64).zip(folded.chunks_mut(64)) {
                    fold.fold_block(chunk, &mut out);
                    dst.copy_from_slice(&out[..dst.len()]);
                }
                let e = eq.lo[x_lo];
                for l in 0..ell {
                    part_ab[l] += e * folded[l];
                    part_c[l] += e * folded[ell + l];
                }
            }
            let e = eq.hi[x_hi];
            for l in 0..ell {
                acc.0[l] += e * part_ab[l];
                acc.1[l] += e * part_c[l];
            }
        },
        |mut x, y| {
            for l in 0..ell {
                x.0[l] += y.0[l];
                x.1[l] += y.1[l];
            }
            x
        },
    );
    let c_lifted = ntt_extend_vec(&c_s_part, &table);
    ab.iter().zip(&c_lifted).map(|(&x, &y)| x + y).collect()
}

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
)))]
pub fn round1_words(a: &[u8], b: &[u8], c: &[u8], m: usize, k: usize, r_rest: &[F192]) -> Vec<F192> {
    round1_folded(a, b, c, m, k, r_rest)
}

/// [`round1_generic`] with the medium positions' conversion as one GF(2)-linear map of a lane's 16 bytes (a
/// [`BitFold`] of 16-byte rows, GFNI where the build has it) instead of 16 table lookups a lane.
pub fn round1_folded(a: &[u8], b: &[u8], c: &[u8], m: usize, k: usize, r_rest: &[F192]) -> Vec<F192> {
    assert!((MIN_SKIP..=K_SKIP).contains(&k));
    assert_eq!(r_rest.len(), m - k);
    let ell = 1usize << k;
    let nc = ell / 8;
    let ntt_s = AdditiveNttGf8::new(k, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k, F8(ell as u8));
    let table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let eq_small = build_eq(&r_rest[..3]);
    let cs = c_s();
    for (kk, &e) in eq_small.iter().enumerate() {
        assert_eq!(e, cs * PHI_8_TABLE[1 << kk], "the small coordinates' eq is C_s X^K");
    }
    let eq_med = build_eq(&r_rest[3..N_INNER]);
    let weights: Vec<F192> = (0..128).map(|w| eq_med[w / 8] * cs * PHI_8_TABLE[1 << (w % 8)]).collect();
    let fold = BitFold::new(&weights);
    let eq = SplitEq::new(&r_rest[N_INNER..]);
    let lo_size = 1usize << eq.n_lo;
    let block = GROUPS * nc;
    assert_eq!(a.len(), (lo_size << eq.n_hi) * block);

    let zero = || (vec![F192::ZERO; ell], vec![F192::ZERO; ell]);
    let (ab, c_s_part) = parallel::fold_reduce(
        1usize << eq.n_hi,
        zero,
        |acc, x_hi| {
            let (mut part_ab, mut part_c) = zero();
            let mut scratch = Rows::new(ell);
            // An x's rows: the AB lanes, then the C lanes, 16 medium bytes each.
            let mut rows = vec![[0u8; 16]; 2 * ell];
            let mut folded = vec![F192::ZERO; 2 * ell];
            let mut out = [F192::ZERO; super::bit_fold::BLOCK];
            for x_lo in 0..lo_size {
                let at = (x_hi * lo_size + x_lo) * block;
                let (a, b, c) = (&a[at..at + block], &b[at..at + block], &c[at..at + block]);
                if a.iter().chain(b).chain(c).all(|&x| x == 0) {
                    continue;
                }
                scratch.rows(a, b, c, &table, &mut rows);
                for (chunk, dst) in rows.chunks(64).zip(folded.chunks_mut(64)) {
                    fold.fold_block(chunk, &mut out);
                    dst.copy_from_slice(&out[..dst.len()]);
                }
                let e = eq.lo[x_lo];
                for l in 0..ell {
                    part_ab[l] += e * folded[l];
                    part_c[l] += e * folded[ell + l];
                }
            }
            let e = eq.hi[x_hi];
            for l in 0..ell {
                acc.0[l] += e * part_ab[l];
                acc.1[l] += e * part_c[l];
            }
        },
        |mut x, y| {
            for l in 0..ell {
                x.0[l] += y.0[l];
                x.1[l] += y.1[l];
            }
            x
        },
    );
    let c_lifted = ntt_extend_vec(&c_s_part, &table);
    ab.iter().zip(&c_lifted).map(|(&x, &y)| x + y).collect()
}

/// Round 1 at a skip of 3, a group a byte. For one `x` (16 medium positions of 8 bytes, one a small position `K`):
///
/// - a word's 8 groups extend to `Λ` in one `gf2p8affine` (qword `λ` the word broadcast, its matrix lane `λ` of the
///   extension), so byte `8 λ + K` is `â(λ, K)`; `â b̂` and `X^K` are two `gf2p8mulb`, and the sum over `K` a fold of
///   each qword's bytes: the AB row of the medium position, one byte a lane;
/// - the C row is the word's 8×8 bit transpose (lane `s`, bit `K`);
/// - the 16 medium positions' rows of a lane are a 16-byte row, `Σ_b eq(r_med, b) C_s φ_8(row_b)` one GF(2)-linear
///   map of it: [`BitFold`]'s, 64 rows (4 `x`s, 8 AB and 8 C lanes each) at a time.
#[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
pub fn round1_bytes(a: &[u8], b: &[u8], c: &[u8], m: usize, r_rest: &[F192]) -> Vec<F192> {
    use core::arch::x86_64::*;
    const ELL: usize = 8;
    let k = MIN_SKIP;
    assert_eq!(r_rest.len(), m - k);
    let ntt_s = AdditiveNttGf8::new(k, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k, F8(ELL as u8));
    let table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    // Lane λ's matrix: input bit s to the byte c_(s, λ), the extension of e_s at lane λ; the affine's result bit j
    // is the parity of the input against matrix byte 7 - j.
    let columns: Vec<[F8; ELL]> = (0..8)
        .map(|s| {
            let mut out = [F8::ZERO; ELL];
            table.apply(&[1u8 << s], &mut out);
            out
        })
        .collect();
    let matrices: [u64; ELL] = std::array::from_fn(|lane| {
        (0..8).fold(0u64, |q, j| {
            let row = (0..8).fold(0u64, |r, s| r | u64::from(columns[s][lane].0 >> j & 1) << s);
            q | row << (8 * (7 - j))
        })
    });
    let eq_small = build_eq(&r_rest[..3]);
    let cs = c_s();
    for (kk, &e) in eq_small.iter().enumerate() {
        assert_eq!(e, cs * PHI_8_TABLE[1 << kk], "the small coordinates' eq is C_s X^K");
    }
    // A lane's 16 medium bytes, bit `8 b + i`, weigh eq(r_med, b) C_s φ_8(2^i).
    let eq_med = build_eq(&r_rest[3..N_INNER]);
    let weights: Vec<F192> = (0..128).map(|w| eq_med[w / 8] * cs * PHI_8_TABLE[1 << (w % 8)]).collect();
    let fold = BitFold::new(&weights);
    let eq = SplitEq::new(&r_rest[N_INNER..]);
    let lo_size = 1usize << eq.n_lo;
    let block = GROUPS; // bytes an x covers
    assert_eq!(a.len(), (lo_size << eq.n_hi) * block);

    // SAFETY: the target features are enabled at compile time; every load is 8 in-bounds bytes.
    let ab_row = |x: u64, y: u64| -> u64 {
        unsafe {
            let m = _mm512_loadu_si512(matrices.as_ptr().cast());
            let ea = _mm512_gf2p8affine_epi64_epi8::<0>(_mm512_set1_epi64(x as i64), m);
            let eb = _mm512_gf2p8affine_epi64_epi8::<0>(_mm512_set1_epi64(y as i64), m);
            let powers = _mm512_set1_epi64(0x8040_2010_0804_0201u64 as i64);
            let t = _mm512_gf2p8mul_epi8(_mm512_gf2p8mul_epi8(ea, eb), powers);
            let t = _mm512_xor_si512(t, _mm512_srli_epi64::<32>(t));
            let t = _mm512_xor_si512(t, _mm512_srli_epi64::<16>(t));
            let t = _mm512_xor_si512(t, _mm512_srli_epi64::<8>(t));
            let bytes = _mm512_cvtepi64_epi8(t);
            _mm_cvtsi128_si64(bytes) as u64
        }
    };
    let word = |data: &[u8], at: usize| u64::from_le_bytes(data[at..at + 8].try_into().expect("8 bytes"));
    let zero = || ([F192::ZERO; ELL], [F192::ZERO; ELL]);
    let (ab, c_s_part) = parallel::fold_reduce(
        1usize << eq.n_hi,
        zero,
        |acc, x_hi| {
            let (mut part_ab, mut part_c) = zero();
            let mut rows = [[0u8; 16]; 64];
            let mut folded = [F192::ZERO; super::bit_fold::BLOCK];
            for x_first in (0..lo_size).step_by(4) {
                let subs = (lo_size - x_first).min(4);
                for sub in 0..subs {
                    let at = (x_hi * lo_size + x_first + sub) * block;
                    for medium in 0..16 {
                        let o = at + 8 * medium;
                        let row = ab_row(word(a, o), word(b, o));
                        let crow = transpose_8x8(word(c, o));
                        for lane in 0..ELL {
                            rows[16 * sub + lane][medium] = (row >> (8 * lane)) as u8;
                            rows[16 * sub + 8 + lane][medium] = (crow >> (8 * lane)) as u8;
                        }
                    }
                }
                fold.fold_block(&rows[..16 * subs], &mut folded);
                for sub in 0..subs {
                    let e = eq.lo[x_first + sub];
                    for lane in 0..ELL {
                        part_ab[lane] += e * folded[16 * sub + lane];
                        part_c[lane] += e * folded[16 * sub + 8 + lane];
                    }
                }
            }
            let e = eq.hi[x_hi];
            for lane in 0..ELL {
                acc.0[lane] += e * part_ab[lane];
                acc.1[lane] += e * part_c[lane];
            }
        },
        |mut x, y| {
            for l in 0..ELL {
                x.0[l] += y.0[l];
                x.1[l] += y.1[l];
            }
            x
        },
    );
    let c_lifted = ntt_extend_vec(&c_s_part, &table);
    ab.iter().zip(&c_lifted).map(|(&x, &y)| x + y).collect()
}

#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
)))]
pub fn round1_bytes(a: &[u8], b: &[u8], c: &[u8], m: usize, r_rest: &[F192]) -> Vec<F192> {
    round1_generic(a, b, c, m, MIN_SKIP, r_rest)
}

/// The round-1 message for any skip of 3 to 6: per `x`, its 128 groups extended by the inverse NTT's byte tables.
pub fn round1_generic(a: &[u8], b: &[u8], c: &[u8], m: usize, k: usize, r_rest: &[F192]) -> Vec<F192> {
    assert!((MIN_SKIP..=K_SKIP).contains(&k));
    assert_eq!(r_rest.len(), m - k);
    let ell = 1usize << k;
    let nc = ell / 8;
    let ntt_s = AdditiveNttGf8::new(k, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k, F8(ell as u8));
    let table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);

    // The small coordinates' eq is geometric: eq(r_small, K) = C_s φ_8(X^K), the shift-reduce's premise.
    let eq_small = build_eq(&r_rest[..3]);
    let cs = c_s();
    for (kk, &e) in eq_small.iter().enumerate() {
        assert_eq!(e, cs * PHI_8_TABLE[1 << kk], "the small coordinates' eq is C_s X^K");
    }
    // Medium position b's lookups: eq(r_med, b) C_s φ_8(v).
    let convert: Vec<[F192; 256]> = build_eq(&r_rest[3..N_INNER])
        .iter()
        .map(|&e| {
            let scale = e * cs;
            std::array::from_fn(|v| scale * PHI_8_TABLE[v])
        })
        .collect();
    let eq = SplitEq::new(&r_rest[N_INNER..]);
    let lo_size = 1usize << eq.n_lo;
    let block = GROUPS * nc;
    assert_eq!(a.len(), (lo_size << eq.n_hi) * block);

    let zero = || (vec![F192::ZERO; ell], vec![F192::ZERO; ell]);
    let (ab, c_s_part) = parallel::fold_reduce(
        1usize << eq.n_hi,
        zero,
        |acc, x_hi| {
            let (mut part_ab, mut part_c) = zero();
            let mut rows = Rows::new(ell);
            for x_lo in 0..lo_size {
                let at = (x_hi * lo_size + x_lo) * block;
                let (a, b, c) = (&a[at..at + block], &b[at..at + block], &c[at..at + block]);
                if a.iter().chain(b).chain(c).all(|&x| x == 0) {
                    continue;
                }
                let (sum_ab, sum_c) = rows.x(a, b, c, &table, &convert);
                let e = eq.lo[x_lo];
                for l in 0..ell {
                    part_ab[l] += e * sum_ab[l];
                    part_c[l] += e * sum_c[l];
                }
            }
            let e = eq.hi[x_hi];
            for l in 0..ell {
                acc.0[l] += e * part_ab[l];
                acc.1[l] += e * part_c[l];
            }
        },
        |mut x, y| {
            for l in 0..ell {
                x.0[l] += y.0[l];
                x.1[l] += y.1[l];
            }
            x
        },
    );
    let c_lifted = ntt_extend_vec(&c_s_part, &table);
    ab.iter().zip(&c_lifted).map(|(&x, &y)| x + y).collect()
}

/// One worker's scratch for an `x`: the eight groups' extensions to `Λ`, the powers `X^K`.
struct Rows {
    ell: usize,
    ea: [F8; 8 * 64],
    eb: [F8; 8 * 64],
    powers: [u8; 8 * 64],
}

impl Rows {
    fn new(ell: usize) -> Self {
        Self {
            ell,
            ea: [F8::ZERO; 8 * 64],
            eb: [F8::ZERO; 8 * 64],
            powers: std::array::from_fn(|i| 1u8 << (i / ell).min(7)),
        }
    }

    /// One `x`'s sums over its 128 groups, per lane: `Σ_(b, K) eq(r_inner, (K, b)) φ_8(â b̂)` on `Λ` and
    /// `Σ_(b, K) eq(r_inner, (K, b)) c` on `S`.
    #[inline]
    fn x(
        &mut self,
        a: &[u8],
        b: &[u8],
        c: &[u8],
        table: &InvNttTableByteSingleGf8,
        convert: &[[F192; 256]],
    ) -> ([F192; 64], [F192; 64]) {
        let ell = self.ell;
        let (mut sum_ab, mut sum_c) = ([F192::ZERO; 64], [F192::ZERO; 64]);
        for (medium, lookups) in convert.iter().enumerate() {
            let (row, crow) = self.medium(a, b, c, medium, table);
            for l in 0..ell {
                sum_ab[l] += lookups[row[l] as usize];
                sum_c[l] += lookups[crow[l] as usize];
            }
        }
        (sum_ab, sum_c)
    }

    /// One `x`'s rows: lane `l`'s 16 medium bytes, the AB lanes (`rows[l]`) then the C lanes (`rows[ell + l]`).
    #[inline]
    fn rows(&mut self, a: &[u8], b: &[u8], c: &[u8], table: &InvNttTableByteSingleGf8, rows: &mut [[u8; 16]]) {
        let ell = self.ell;
        for medium in 0..16 {
            let (row, crow) = self.medium(a, b, c, medium, table);
            for l in 0..ell {
                rows[l][medium] = row[l];
                rows[ell + l][medium] = crow[l];
            }
        }
    }

    /// Medium position `medium`'s AB row (`Σ_K X^K â b̂`, a lane a byte) and C row (lane `s`, bit `K` group `K`'s).
    #[inline]
    fn medium(
        &mut self,
        a: &[u8],
        b: &[u8],
        c: &[u8],
        medium: usize,
        table: &InvNttTableByteSingleGf8,
    ) -> ([u8; 64], [u8; 64]) {
        let ell = self.ell;
        let nc = ell / 8;
        let at = medium * 8 * nc;
        for kk in 0..8 {
            let group = at + kk * nc..at + (kk + 1) * nc;
            table.apply(&a[group.clone()], &mut self.ea[kk * ell..(kk + 1) * ell]);
            table.apply(&b[group], &mut self.eb[kk * ell..(kk + 1) * ell]);
        }
        // y_K = â b̂, then X^K y_K, summed over K: lane l of the row.
        let len = 8 * ell;
        let mut products = [0u8; 8 * 64];
        mul_bytes(bytes_of(&self.ea[..len]), bytes_of(&self.eb[..len]), &mut products[..len]);
        let mut shifted = [0u8; 8 * 64];
        mul_bytes(&products[..len], &self.powers[..len], &mut shifted[..len]);
        let mut row = [0u8; 64];
        for kk in 0..8 {
            for (r, &s) in row[..ell].iter_mut().zip(&shifted[kk * ell..(kk + 1) * ell]) {
                *r ^= s;
            }
        }
        // The C bits of lane s: bit K from group K.
        let mut crow = [0u8; 64];
        for j in 0..nc {
            let word = (0..8).fold(0u64, |w, kk| w | u64::from(c[at + kk * nc + j]) << (8 * kk));
            crow[8 * j..8 * j + 8].copy_from_slice(&transpose_8x8(word).to_le_bytes());
        }
        (row, crow)
    }
}

fn bytes_of(x: &[F8]) -> &[u8] {
    // SAFETY: `F8` is `repr(transparent)` over `u8`.
    unsafe { std::slice::from_raw_parts(x.as_ptr().cast::<u8>(), x.len()) }
}

/// The 8×8 bit matrix whose byte `r` is row `r`, transposed: bit `8 r + c` to bit `8 c + r` (Hacker's Delight 7-3).
fn transpose_8x8(mut x: u64) -> u64 {
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^= t ^ (t << 28);
    x
}

/// `out[i] = a[i] b[i]` in `F_8`, the lengths a multiple of 64.
#[inline]
fn mul_bytes(a: &[u8], b: &[u8], out: &mut [u8]) {
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
    // SAFETY: the target features are enabled at compile time; every load and store is 64 in-bounds bytes.
    unsafe {
        use core::arch::x86_64::*;
        for ((x, y), o) in a.chunks_exact(64).zip(b.chunks_exact(64)).zip(out.chunks_exact_mut(64)) {
            let p = _mm512_gf2p8mul_epi8(_mm512_loadu_si512(x.as_ptr().cast()), _mm512_loadu_si512(y.as_ptr().cast()));
            _mm512_storeu_si512(o.as_mut_ptr().cast(), p);
        }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw")))]
    for ((&x, &y), o) in a.iter().zip(b).zip(out.iter_mut()) {
        *o = (F8(x) * F8(y)).0;
    }
}
