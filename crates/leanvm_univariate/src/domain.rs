// Part of this repository. The Cantor basis is computed as in crates/quotient/src/domain.rs (adapted there from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// crates/flock/src/quotient/domain.rs), here for leanVM 42422001's `K` (crates/verifier/src/field.rs at 42422001).
// MIT OR Apache-2.0; see NOTICE.md.
//! The Cantor basis of `K`, its subspaces, and the encodings of SPEC.md §2.
//!
//! - `ω_i = Σ_k i_k β_k`, `V_r = {ω_i : i < 2^r}`, digits `w_0(x) = x`, `w_{k+1} = w_k^2 + w_k`: `w_r` is the subspace
//!   polynomial of `V_r` and `w_l(ω_i) = ω_{i >> l}`.
//! - A column of `2^r` rows is committed as its coefficients in the basis `B_k = Π_l (w_l if k_l else 1 + w_l)`, so
//!   that `f(t)` is the multilinear extension of its coefficients at `(w_0(t), …, w_{r-1}(t))`.
//! - `y_l`, the linearised polynomials with `y_l(ω_i) = i_l` on `V_r`: a column committed as values is read at `t`
//!   through them (SPEC.md §2, "composition").

use std::sync::OnceLock;

use leanvm_flock_gas::K;
use leanvm_flock_gas::field::{E, ONE};
use leanvm_flock_gas::scalar::Scalar;

/// Basis vectors computed: enough for a heap of `2^27` positions and its quotient's spill.
pub const BASIS: usize = 32;

pub fn s(x: K) -> K {
    x.square() + x
}

/// `beta[0] = 1` and `s(beta[k + 1]) = beta[k]`, each the solution with its low bit clear.
pub fn beta() -> &'static [K; BASIS] {
    static BETA: OnceLock<[K; BASIS]> = OnceLock::new();
    BETA.get_or_init(|| {
        // `s` is linear over GF(2): reduce its matrix once, keeping what each pivot was made of.
        let mut pivots = [(0u64, 0u64); 64];
        for j in 0..64 {
            let (mut image, mut source) = (s(K(1 << j)).0, 1u64 << j);
            while image != 0 {
                let top = 63 - image.leading_zeros() as usize;
                if pivots[top].0 == 0 {
                    pivots[top] = (image, source);
                    break;
                }
                image ^= pivots[top].0;
                source ^= pivots[top].1;
            }
        }
        let solve = |target: K| {
            let (mut image, mut source) = (target.0, 0u64);
            while image != 0 {
                let top = 63 - image.leading_zeros() as usize;
                assert!(pivots[top].0 != 0, "outside the image of s");
                image ^= pivots[top].0;
                source ^= pivots[top].1;
            }
            K(source & !1)
        };
        let mut beta = [K(1); BASIS];
        for k in 1..BASIS {
            beta[k] = solve(beta[k - 1]);
        }
        beta
    })
}

/// `ω_i`.
pub fn point(index: u64) -> K {
    (0..BASIS)
        .filter(|&k| index >> k & 1 == 1)
        .fold(K(0), |acc, k| acc + beta()[k])
}

/// `ω_i` as an element of `E`.
pub fn point_e(index: u64) -> E {
    E::from(point(index))
}

/// `w_0(t), …, w_{count-1}(t)`.
pub fn digits<S: Scalar>(t: S, count: usize) -> Vec<S> {
    std::iter::successors(Some(t), |&w| Some(w * w + w)).take(count).collect()
}

/// `w_l(ω_a)` for `l < count`: `ω_{a >> l}`.
pub fn digits_of_point(a: u64, count: usize) -> Vec<E> {
    (0..count).map(|l| point_e(a >> l)).collect()
}

/// `a[l][m]` with `y_l(x) = Σ_{m<r} a[l][m] x^(2^m)` and `y_l(ω_i) = i_l` for `i < 2^r`: the inverse of the
/// transposed Moore matrix `M[j][m] = β_j^(2^m)`.
pub fn coordinate_functionals(r: usize) -> Vec<Vec<K>> {
    let frob = |mut x: K, m: usize| {
        for _ in 0..m {
            x = x.square();
        }
        x
    };
    // Solve A M^T = I: row l of A satisfies Σ_m A[l][m] M[j][m] = δ_lj, i.e. M A^T = I, so A^T = M^-1.
    // Gauss-Jordan on [M | I].
    let mut rows: Vec<Vec<K>> = (0..r)
        .map(|j| {
            let mut row: Vec<K> = (0..r).map(|m| frob(beta()[j], m)).collect();
            row.extend((0..r).map(|c| K((c == j) as u64)));
            row
        })
        .collect();
    for col in 0..r {
        let pivot = (col..r).find(|&i| rows[i][col].0 != 0).expect("the Moore matrix is invertible");
        rows.swap(col, pivot);
        let inverse = rows[col][col].inv();
        rows[col].iter_mut().for_each(|x| *x = *x * inverse);
        for i in 0..r {
            let factor = rows[i][col];
            if i != col && factor.0 != 0 {
                let pivot_row = rows[col].clone();
                rows[i].iter_mut().zip(&pivot_row).for_each(|(x, &p)| *x = *x + factor * p);
            }
        }
    }
    // rows now hold [I | M^-1]; A^T = M^-1, so A[l][m] = M^-1[m][l].
    (0..r).map(|l| (0..r).map(|m| rows[m][r + l]).collect()).collect()
}

/// `y_0(t), …, y_{r-1}(t)` from the functionals: `r - 1` squarings and `r^2` products by constants.
pub fn coordinates_at<S: Scalar>(t: S, functionals: &[Vec<K>]) -> Vec<S> {
    let r = functionals.len();
    let frobenius: Vec<S> = std::iter::successors(Some(t), |&x| Some(x.square())).take(r).collect();
    functionals
        .iter()
        .map(|row| {
            S::sum(
                row.iter()
                    .zip(&frobenius)
                    .filter(|(a, _)| a.0 != 0)
                    .map(|(&a, &x)| S::constant(E::from(a)) * x),
            )
        })
        .collect()
}

/// The vanishing polynomial of the first `rows` points of `V_r` at the point whose digits are `w`: the product over
/// the aligned cosets `ω_a + V_b` of `[0, rows)`'s binary decomposition of `w_b + ω_{a >> b}`.
pub fn prefix_vanishing<S: Scalar>(w: &[S], rows: u64) -> S {
    let mut product = S::one();
    let mut start = 0u64;
    for b in (0..64).rev() {
        if rows >> b & 1 == 1 {
            product *= w[b] + S::constant(point_e(start >> b));
            start += 1 << b;
        }
    }
    product
}

/// [`prefix_vanishing`] at `t` for a count known only by its bits `bits[b]` (the scalars 0 or 1, `b ≤ r`, so up to
/// `2^r`): `Π_b (1 + bit_b · d_b)`, `d` the digits of `t + ω_rows`. A set bit `b` contributes the coset
/// `ω_start + V_b`, `start` the bits above `b`: its factor `w_b(t) + ω_(start >> b)` is `d_b + 1`, since `w_b` is
/// GF(2)-linear and `ω_(rows >> b) = ω_(start >> b) + 1` (SPEC.md §13).
pub fn prefix_vanishing_from_bits<S: Scalar>(t: S, bits: &[S]) -> S {
    let omega = bits
        .iter()
        .enumerate()
        .fold(S::zero(), |acc, (b, &bit)| acc + bit * S::constant(point_e(1 << b)));
    let mut digit = t + omega;
    let mut product = S::one();
    for (b, &bit) in bits.iter().enumerate() {
        if b > 0 {
            digit = digit * digit + digit;
        }
        product *= S::one() + bit * digit;
    }
    product
}

/// The active rows' fixed cosets (SPEC.md §13): bit `b < r` of a count owns the rows `[2^r - 2^(b+1), 2^r - 2^b)`,
/// and bit `r` (a count of `2^r`) all of `V_r`. A count's active rows are the cosets of its set bits, the highest
/// first, so a count above `2^(r-1)` starts with the prefix `[0, 2^(r-1))`; the last row `2^r - 1` is active only
/// in a full table. This coset's offset is a constant: `ω_(2^(r-b) - 2)`.
pub fn coset_offset(r: usize, b: usize) -> E {
    point_e((1 << (r - b)) - 2)
}

/// The positions of a height-`r` table's `rows` active rows, in order.
pub fn active_positions(rows: u64, r: usize) -> Vec<u64> {
    assert!(rows <= 1 << r);
    if rows == 1 << r {
        return (0..rows).collect();
    }
    let mut out = Vec::with_capacity(rows as usize);
    for b in (0..r).rev() {
        if rows >> b & 1 == 1 {
            let start = (1u64 << r) - (2u64 << b);
            out.extend(start..start + (1 << b));
        }
    }
    out
}

/// Whether row `i` of a height-`r` table with `rows` active rows is active.
pub fn is_active(i: u64, rows: u64, r: usize) -> bool {
    if rows == 1 << r {
        return true;
    }
    // Row i < 2^r - 1 lies in bit b's coset for the b with 2^r - 2^(b+1) <= i < 2^r - 2^b.
    let gap = (1u64 << r) - i; // in (2^b, 2^(b+1)]
    gap >= 2 && rows >> (63 - (gap - 1).leading_zeros()) & 1 == 1
}

/// `Z_act(t)` of the fixed cosets from the count's bits `bits[b]` (0 or 1, `b ≤ r`):
/// `Π_(b<r) (1 + c_b (w_b + K_b + 1)) · (1 + c_r (w_r + 1))`, `K_b` [`coset_offset`]. The factors `w_b + K_b + 1`
/// are shared by every table of the height.
pub fn active_vanishing_from_bits<S: Scalar>(w: &[S], bits: &[S], r: usize) -> S {
    assert_eq!(bits.len(), r + 1);
    let one = S::one();
    let mut product = one + bits[r] * (w[r] + one);
    for (b, &bit) in bits[..r].iter().enumerate() {
        product *= one + bit * (w[b] + S::constant(coset_offset(r, b) + ONE));
    }
    product
}

/// The vanishing polynomial of `[rows, 2^r)` in `V_r`, likewise.
pub fn suffix_vanishing<S: Scalar>(w: &[S], rows: u64, r: usize) -> S {
    let mut product = S::one();
    let mut start = rows;
    while start < 1 << r {
        let b = (start.trailing_zeros() as usize).min(r);
        let mut b = b;
        while start + (1 << b) > 1 << r {
            b -= 1;
        }
        product *= w[b] + S::constant(point_e(start >> b));
        start += 1 << b;
    }
    product
}

/// `w_m / w_r = Π_{j=r}^{m-1} (w_j + 1)`, for `r < m` (since `s^(k)(z) / z = Π_{j<k} (s^(j)(z) + 1)`).
pub fn vanishing_ratio<S: Scalar>(w: &[S], r: usize, m: usize) -> S {
    (r..m).fold(S::one(), |acc, j| acc * (w[j] + S::one()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rng(seed: u64) -> impl FnMut() -> u64 {
        let mut state = seed | 1;
        move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        }
    }

    /// `s(β_{k+1}) = β_k`, `w_l(ω_i) = ω_{i >> l}`, `w_r` vanishes on `V_r` and is 1 at `β_r`.
    #[test]
    fn cantor_basis() {
        for k in 1..BASIS {
            assert_eq!(s(beta()[k]), beta()[k - 1]);
        }
        let mut next = rng(3);
        for _ in 0..200 {
            let i = next() % (1 << 24);
            let w = digits(E::from(point(i)), 25);
            for (l, &wl) in w.iter().enumerate() {
                assert_eq!(wl, point_e(i >> l));
            }
            let r = (next() % 24) as usize + 1;
            let inside = i % (1 << r);
            assert_eq!(digits(point_e(inside), r + 1)[r], E::default());
        }
        assert_eq!(digits(point_e(1 << 10), 11)[10], E::new(1, 0, 0));
    }

    /// `y_l(ω_i) = i_l` on `V_r`.
    #[test]
    fn coordinate_functionals_read_bits() {
        let r = 18;
        let a = coordinate_functionals(r);
        let mut next = rng(5);
        for _ in 0..100 {
            let i = next() % (1 << r);
            let y = coordinates_at(point_e(i), &a);
            for (l, &yl) in y.iter().enumerate() {
                assert_eq!(yl, E::new(i >> l & 1, 0, 0), "bit {l} of {i}");
            }
        }
    }

    /// The prefix and suffix vanishing polynomials vanish exactly where they should and multiply to `w_r`.
    #[test]
    fn active_and_padding_vanishing() {
        let r = 12;
        let rows = 2_731;
        for i in [0u64, 1, 2_730, 2_731, 2_732, 4_095, 1_000] {
            let w = digits(point_e(i), r + 1);
            let act = prefix_vanishing(&w, rows);
            let pad = suffix_vanishing(&w, rows, r);
            assert_eq!(act == E::default(), i < rows, "active at {i}");
            assert_eq!(pad == E::default(), i >= rows, "padding at {i}");
        }
        let t = E::new(0x1234_5678_9abc, 0x42, 0x77);
        let w = digits(t, r + 1);
        assert_eq!(prefix_vanishing(&w, rows) * suffix_vanishing(&w, rows, r), w[r]);
        assert_eq!(vanishing_ratio(&digits(t, 22), 17, 21) * w_at(t, 17), w_at(t, 21));
    }

    /// The fixed cosets: the active positions are `rows` of them, `is_active` agrees, and `Z_act` from the bits
    /// vanishes exactly on them.
    #[test]
    fn fixed_cosets_from_the_bits() {
        let mut next = rng(13);
        for r in [1usize, 3, 6] {
            for rows in 0..=(1u64 << r) {
                let positions = active_positions(rows, r);
                assert_eq!(positions.len() as u64, rows);
                let bits: Vec<E> = (0..=r).map(|b| E::new(rows >> b & 1, 0, 0)).collect();
                for i in 0..1u64 << r {
                    let active = positions.contains(&i);
                    assert_eq!(is_active(i, rows, r), active, "r {r} rows {rows} row {i}");
                    let w = digits(point_e(i), r + 1);
                    let z = active_vanishing_from_bits(&w, &bits, r);
                    assert_eq!(z == E::default(), active, "r {r} rows {rows} row {i}");
                }
                let t = E::new(next(), next(), next());
                let w = digits(t, r + 1);
                let z = active_vanishing_from_bits(&w, &bits, r);
                assert_ne!(z, E::default());
            }
        }
    }

    /// From the count's bits, the prefix vanishing polynomial is the one from the count, up to `2^r` included.
    #[test]
    fn prefix_vanishing_from_the_bits() {
        let mut next = rng(11);
        for r in [2usize, 5, 12, 18] {
            for rows in [1u64, (1 << (r - 1)) + 1, (1 << r) - 1, 1 << r, next() % (1 << r) + 1] {
                let t = E::new(next(), next(), next());
                let bits: Vec<E> = (0..=r).map(|b| E::new(rows >> b & 1, 0, 0)).collect();
                let w = digits(t, r + 2);
                assert_eq!(prefix_vanishing_from_bits(t, &bits), prefix_vanishing(&w, rows), "r {r}, rows {rows}");
            }
        }
    }

    fn w_at(t: E, r: usize) -> E {
        digits(t, r + 1)[r]
    }
}
