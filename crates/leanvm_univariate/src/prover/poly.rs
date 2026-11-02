// Part of this repository. The additive transform is crates/quotient/src/domain.rs's (adapted there from leanVM's
// branch PCS-openings-aggregation, commit 651453c6). MIT OR Apache-2.0; see NOTICE.md.
//! Polynomials on the Cantor subspaces (SPEC.md §2), prover side.
//!
//! - `values` ↔ `novel`: the additive transform of `crates/quotient/src/domain.rs`, novel basis
//!   `X_k = Π_{l : k_l = 1} w_l`, values at `offset + ω_i`.
//! - `novel` ↔ `B`: `B_k = Π_l (w_l if k_l else 1 + w_l) = Σ_{j ⊇ k} X_j`, so the novel coefficients are the subset
//!   sums of the `B` coefficients (`a_j = Σ_{k ⊆ j} b_k`), and in characteristic 2 the same transform inverts it.
//! - The extension cosets `D_m = ω_{2^m} + V_m`, disjoint from `V_m` and so from every `V_r`, `r ≤ m`, where a
//!   quotient's values are its numerator's over the vanishing polynomial's.

use primitives::field::{F64, F192};
use quotient::domain::{Module, coefficients, point, values};

/// The novel coefficients of the polynomial of degree `< data.len()` whose value at `ω_i` is `data[i]`, in place.
pub fn novel_from_values<M: Module>(data: &mut [M]) {
    coefficients(data, F64::ZERO);
}

/// Novel to `B` coefficients (or back), in place: `b_k = Σ_{j ⊆ k} a_j`.
pub fn subset_sums<M: Module>(data: &mut [M]) {
    let n = data.len();
    assert!(n.is_power_of_two());
    let mut half = 1;
    while half < n {
        let block = 2 * half;
        let chunk = block.max(1 << 14).min(n);
        parallel::chunks_mut(data, chunk, |_, piece| {
            for pair in piece.chunks_exact_mut(block) {
                let (lo, hi) = pair.split_at_mut(half);
                for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                    *h = *h + l;
                }
            }
        });
        half = block;
    }
}

/// The `B` coefficients of the polynomial whose values on `V_r` are `values` (`2^r` of them).
pub fn b_from_values<M: Module>(mut data: Vec<M>) -> Vec<M> {
    novel_from_values(&mut data);
    subset_sums(&mut data);
    data
}

/// The point `ω_index`, for any index below `2^28`.
pub fn omega(index: usize) -> F64 {
    point(index)
}

/// The values of the polynomial of novel coefficients `novel` (degree `< 2^r`) on the aligned coset
/// `ω_first + V_r`, `2^r | first`.
pub fn on_coset<M: Module>(novel: &[M], first: usize) -> Vec<M> {
    let mut data = novel.to_vec();
    debug_assert_eq!(first % novel.len(), 0);
    values(&mut data, point(first));
    data
}

/// The values of the polynomial of novel coefficients `novel` (degree `< 2^r`, `r ≤ m`) on `D_m`'s sub-coset
/// `j` of `V_r`: the points `ω_{2^m + j 2^r + i}`, `i < 2^r`.
pub fn on_extension<M: Module>(novel: &[M], m: usize, j: usize) -> Vec<M> {
    on_coset(novel, (1 << m) + j * novel.len())
}

/// The novel coefficients of the polynomial of degree `< 2^m` whose values on `D_m` are `data`, in place.
pub fn novel_from_extension<M: Module>(data: &mut [M], m: usize) {
    assert_eq!(data.len(), 1 << m);
    coefficients(data, point(1 << m));
}

/// `Σ_k b_k B_k(t)` for `B` coefficients `b` of a K-column: the multilinear extension at the digits `w[..r]`.
pub fn eval_k(b: &[F64], w: &[F192]) -> F192 {
    let r = b.len().trailing_zeros() as usize;
    primitives::multilinear::mle_eval_par(b, &w[..r])
}

/// [`eval_k`] for an E-column.
pub fn eval_e(b: &[F192], w: &[F192]) -> F192 {
    let r = b.len().trailing_zeros() as usize;
    if r == 0 {
        return b[0];
    }
    let point = &w[..r];
    // One parallel pass for the low variables, then the rest in place.
    let low = r.min(12);
    let eq = primitives::multilinear::eq_table(&point[..low]);
    let rows = b.len() >> low;
    let mut folded: Vec<F192> = parallel::map_collect(rows, |row| {
        let chunk = &b[row << low..(row + 1) << low];
        chunk.iter().zip(&eq).fold(F192::ZERO, |acc, (&x, &e)| acc + x * e)
    });
    for &p in &point[low..] {
        let half = folded.len() / 2;
        for i in 0..half {
            folded[i] = folded[2 * i] + p * (folded[2 * i] + folded[2 * i + 1]);
        }
        folded.truncate(half);
    }
    folded[0]
}

/// `Π_{l<r}` of the digits' factors for a `B` basis element at a K point: `B_k(x)` from `x`'s digits, for tests.
pub fn digits_k(x: F64, count: usize) -> Vec<F64> {
    std::iter::successors(Some(x), |&w| Some(w.square() + w)).take(count).collect()
}

/// Batch inversion in parallel chunks (Montgomery's trick per chunk); every entry must be nonzero.
pub fn batch_invert(data: &mut [F192]) {
    parallel::chunks_mut(data, 1 << 12, |_, chunk| {
        let mut prefix = Vec::with_capacity(chunk.len());
        let mut acc = F192::ONE;
        for &x in chunk.iter() {
            prefix.push(acc);
            acc *= x;
        }
        let mut inv = acc.inv();
        for i in (0..chunk.len()).rev() {
            let x = chunk[i];
            chunk[i] = inv * prefix[i];
            inv *= x;
        }
    });
}

/// `E` of the verifier (`leanvm_flock_gas`) from the prover's, and back: the same limbs.
pub fn to_v(x: F192) -> leanvm_flock_gas::field::E {
    leanvm_flock_gas::field::E::new(x.c0, x.c1, x.c2)
}

pub fn from_v(x: leanvm_flock_gas::field::E) -> F192 {
    F192::new(x.c0, x.c1, x.c2)
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

    /// `B` coefficients read at the digits are the polynomial: at the points of `V_r` (its values) and off it.
    #[test]
    fn b_basis_is_the_multilinear_at_the_digits() {
        let mut next = rng(9);
        let r = 10;
        let vals: Vec<F64> = (0..1 << r).map(|_| F64(next())).collect();
        let b = b_from_values(vals.clone());
        for i in [0usize, 1, 5, 1000, 1023] {
            let w: Vec<F192> = digits_k(omega(i), r).into_iter().map(F192::from).collect();
            assert_eq!(eval_k(&b, &w), F192::from(vals[i]));
        }
        // Off the subspace: against the novel basis evaluated directly.
        let mut novel = vals.clone();
        novel_from_values(&mut novel);
        let x = omega(5000);
        let w: Vec<F192> = digits_k(x, r).into_iter().map(F192::from).collect();
        let direct = quotient::domain::evaluate(&novel, 0, 1, &w);
        assert_eq!(eval_k(&b, &w), direct);
        // And on an extension coset.
        let ext = on_extension(&novel, 12, 3);
        let x = omega((1 << 12) + 3 * (1 << r) + 77);
        let w: Vec<F192> = digits_k(x, r).into_iter().map(F192::from).collect();
        assert_eq!(F192::from(ext[77]), eval_k(&b, &w));
        let e: Vec<F192> = b.iter().map(|&k| F192::from(k) * F192::new(3, 5, 7)).collect();
        assert_eq!(eval_e(&e, &w), eval_k(&b, &w) * F192::new(3, 5, 7));
    }
}
