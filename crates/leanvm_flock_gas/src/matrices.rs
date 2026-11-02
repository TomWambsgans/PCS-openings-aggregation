// Part of this repository. `matrix_values` is adapted from leanVM (https://github.com/leanEthereum/leanVM), commit
// 42422001, file crates/verifier/src/deferred.rs; the reduction is new here, in the spirit of leanVM's deferred
// matrix claims (`crates/rec_aggregation`, "Deferred evaluation claims"). MIT OR Apache-2.0; see NOTICE.md.
//! The lincheck's terminal identity left to `PCS_OPEN`: one evaluation claim on each of flock's matrices `A0`, `B0`.
//!
//! leanVM's verifier checks the lincheck's terminal identity by walking the BLAKE2s circuit against
//! `w = eq(chi_in') ⊗ s` and `e = eq(chi_in) ⊗ L(z_skip)` (`L` the 64 Lagrange weights of the skip domain): some
//! 50,000 products, too many for a contract. Its two matrix terms are
//!
//! `M = Σ_(x, y) L_x(z_skip) s_y G(x, y)`, `G(x, y) = (Â0 + α B̂0)((x, chi_in), (y, chi_in'))`
//!
//! over `x, y ∈ {0,1}^6`, the row (column) index being its 6 low bits then its 8 high ones, LSB first. The prover
//! proves that sum by a sumcheck of 12 rounds of degree 2 (`x` then `y`, each low bit first), which leaves
//! `G(ρ, σ) L̂(ρ) ŝ(σ)` at a random `(ρ, σ)`; it sends `a = Â0(ρ, chi_in, σ, chi_in')` and `b = B̂0(...)`, and the
//! verifier checks `(a + α b) L̂(ρ) ŝ(σ)` against the sumcheck (`L̂`, `ŝ`: 64-entry tables, a few hundred products).
//! `A0` and `B0` are fixed (the BLAKE2s R1CS), so their commitments are too: two claims for `PCS_OPEN`, at one point.

use crate::field::E;
use crate::flock::{blake2s_row_values, lagrange_weights};
use crate::layout::{BLAKE2S_CONSTANT_COLUMN, BLAKE2S_R1CS_LOG_SIZE, FLOCK_K_SKIP, FLOCK_NUM_LINCHECK_ROUNDS, K_BITS};
use crate::multilinear::{dot, eq_eval, eq_kernel, multilinear_eval};
use crate::scalar::{Scalar, enter};
use crate::transcript::{Channel, sumcheck};
use crate::{VerifierError, require};

/// The variables of the sum: the low row bits, then the low column bits.
pub const MATRIX_ROUNDS: usize = 2 * FLOCK_K_SKIP;

/// What the reduction leaves: `A0` and `B0` at `point` (the row's 14 coordinates, then the column's).
#[derive(Clone, Debug)]
pub struct MatrixClaim<S> {
    pub point: Vec<S>,
    pub a: S,
    pub b: S,
}

/// The lincheck's terminal identity (`r_lc`, its running claim) as claims on `A0` and `B0`.
pub fn reduce_matrices<S: Scalar>(
    transcript: &mut impl Channel<S>,
    z_skip: S,
    chi_in: &[S],
    chi_in_prime: &[S],
    s: &[S],
    alpha: S,
    r_lc: S,
) -> Result<MatrixClaim<S>, VerifierError> {
    let _phase = enter("flock matrices: reduction to A0, B0 claims");
    assert_eq!(chi_in.len(), FLOCK_NUM_LINCHECK_ROUNDS);
    let skip_weights = lagrange_weights(K_BITS, z_skip);
    // The terminal's two known terms: the c claim (C = I) and the constant position's pin, w at column 512.
    let constant_bits: Vec<S> = (0..FLOCK_NUM_LINCHECK_ROUNDS)
        .map(|bit| S::constant(E::new((BLAKE2S_CONSTANT_COLUMN / K_BITS) as u64 >> bit & 1, 0, 0)))
        .collect();
    let pin = eq_eval(&constant_bits, chi_in_prime) * s[BLAKE2S_CONSTANT_COLUMN % K_BITS];
    let known = alpha.pow(2) * eq_eval(chi_in, chi_in_prime) * dot(&skip_weights, s) + alpha.pow(3) * pin;
    let (challenges, claim) = {
        let _rounds = enter("flock matrices: sumcheck rounds");
        sumcheck(transcript, r_lc + known, 3, &[None; MATRIX_ROUNDS])?
    };
    let (rho, sigma) = challenges.split_at(FLOCK_K_SKIP);
    let (a, b) = (transcript.next_scalar()?, transcript.next_scalar()?);
    let terminal = (a + alpha * b) * multilinear_eval(&skip_weights, rho)? * multilinear_eval(s, sigma)?;
    transcript.require_zero(terminal + claim, VerifierError::FlockMatrixTerminal)?;
    Ok(MatrixClaim {
        point: [rho, chi_in, sigma, chi_in_prime].concat(),
        a,
        b,
    })
}

/// The multilinear extensions of `A0` and `B0` at `point`: the row coordinates, then the column coordinates.
///
/// The same forward walk of the BLAKE2s circuit as the lincheck's terminal check, against eq weights on both sides.
pub fn matrix_values(point: &[E]) -> Result<(E, E), VerifierError> {
    require(point.len() == 2 * BLAKE2S_R1CS_LOG_SIZE, VerifierError::MultilinearSize)?;
    let (row, column) = point.split_at(BLAKE2S_R1CS_LOG_SIZE);
    let (left_values, right_values) = blake2s_row_values(&eq_kernel(column));
    Ok((
        multilinear_eval(&left_values, row)?,
        multilinear_eval(&right_values, row)?,
    ))
}

/// The honest prover's side of the reduction, natively: what a leanVM prover would add (tests only).
#[cfg(test)]
pub mod prover {
    use super::*;
    use crate::field::ZERO;
    use crate::transcript::KeccakWriter;

    /// `G_A(x, y)`, `G_B(x, y)` at index `x + 64 y`: one walk per column slice.
    pub fn sliced_matrices(chi_in: &[E], chi_in_prime: &[E]) -> (Vec<E>, Vec<E>) {
        let high = eq_kernel(chi_in_prime);
        let rows = eq_kernel(chi_in);
        let (mut ga, mut gb) = (vec![ZERO; K_BITS * K_BITS], vec![ZERO; K_BITS * K_BITS]);
        for y in 0..K_BITS {
            let mut w = vec![ZERO; 1 << BLAKE2S_R1CS_LOG_SIZE];
            for (h, &weight) in high.iter().enumerate() {
                w[h * K_BITS + y] = weight;
            }
            let (left, right) = blake2s_row_values(&w);
            for x in 0..K_BITS {
                for (h, &weight) in rows.iter().enumerate() {
                    ga[x + K_BITS * y] += weight * left[h * K_BITS + x];
                    gb[x + K_BITS * y] += weight * right[h * K_BITS + x];
                }
            }
        }
        (ga, gb)
    }

    /// Prove `Σ_i Π_t tables[t][i]` over `log2(len)` variables, low bit first, with degree-2 messages `(c0, c2)`.
    pub fn prove_product_sum(writer: &mut KeccakWriter, mut tables: Vec<Vec<E>>, rounds: usize) -> Vec<E> {
        let mut point = Vec::new();
        for _ in 0..rounds {
            let half = tables[0].len() / 2;
            let mut coefficients = [ZERO; 4];
            for i in 0..half {
                let mut product = vec![crate::field::ONE];
                for table in &tables {
                    let (lo, hi) = (table[2 * i], table[2 * i + 1]);
                    let linear = [lo, lo + hi];
                    let mut next = vec![ZERO; product.len() + 1];
                    for (d, &p) in product.iter().enumerate() {
                        next[d] += p * linear[0];
                        next[d + 1] += p * linear[1];
                    }
                    product = next;
                }
                for (c, p) in coefficients.iter_mut().zip(&product) {
                    *c += *p;
                }
            }
            assert_eq!(coefficients[3], ZERO, "degree 2 in every variable");
            writer.send(coefficients[0]);
            writer.send(coefficients[2]);
            let r = writer.sample();
            point.push(r);
            for table in &mut tables {
                for i in 0..half {
                    table[i] = table[2 * i] + r * (table[2 * i] + table[2 * i + 1]);
                }
                table.truncate(half);
            }
        }
        point
    }
}

#[cfg(test)]
mod tests {
    use super::prover::*;
    use super::*;
    use crate::field::ZERO;
    use crate::transcript::{Checks, KeccakChannel, KeccakWriter, keccak_seed};

    fn element(seed: &mut u64) -> E {
        let mut next = || {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        };
        E::new(next(), next(), next())
    }

    /// leanVM's walk, as `flock::verify_flock_lincheck` does it, for the terminal's matrix terms and its known terms.
    fn walked_terminal(z_skip: E, chi_in: &[E], chi_in_prime: &[E], s: &[E], alpha: E) -> E {
        let skip_weights = lagrange_weights(K_BITS, z_skip);
        let high = eq_kernel(chi_in_prime);
        let mut w_col = vec![ZERO; high.len() * K_BITS];
        for (l, &slice) in s.iter().enumerate() {
            for (h, &weight) in high.iter().enumerate() {
                w_col[h * K_BITS + l] = slice * weight;
            }
        }
        let (left_values, right_values) = blake2s_row_values(&w_col);
        let (mut left_blocks, mut right_blocks) = (vec![ZERO; high.len()], vec![ZERO; high.len()]);
        for (l, &weight) in skip_weights.iter().enumerate() {
            for (h, (left, right)) in left_blocks.iter_mut().zip(&mut right_blocks).enumerate() {
                *left += weight * left_values[h * K_BITS + l];
                *right += weight * right_values[h * K_BITS + l];
            }
        }
        multilinear_eval(&left_blocks, chi_in).unwrap()
            + alpha * multilinear_eval(&right_blocks, chi_in).unwrap()
            + alpha.pow(2) * eq_eval(chi_in, chi_in_prime) * dot(&skip_weights, s)
            + alpha.pow(3) * w_col[BLAKE2S_CONSTANT_COLUMN]
    }

    /// For any lincheck terminal leanVM's walk accepts, the honest prover's reduction is accepted, and its two claims
    /// are `A0` and `B0` at the point; a running claim the walk rejects is rejected.
    #[test]
    fn reduction_is_complete_and_its_claims_are_the_matrices() {
        let mut seed = 0x005E_ED0F_F10C;
        let z_skip = element(&mut seed);
        let chi_in: Vec<E> = (0..8).map(|_| element(&mut seed)).collect();
        let chi_in_prime: Vec<E> = (0..8).map(|_| element(&mut seed)).collect();
        let s: Vec<E> = (0..K_BITS).map(|_| element(&mut seed)).collect();
        let alpha = element(&mut seed);
        // The running claim leanVM's walk accepts.
        let r_lc = walked_terminal(z_skip, &chi_in, &chi_in_prime, &s, alpha);

        let (ga, gb) = sliced_matrices(&chi_in, &chi_in_prime);
        let skip = lagrange_weights(K_BITS, z_skip);
        let g: Vec<E> = ga.iter().zip(&gb).map(|(&a, &b)| a + alpha * b).collect();
        let skip_table: Vec<E> = (0..K_BITS * K_BITS).map(|i| skip[i % K_BITS]).collect();
        let s_table: Vec<E> = (0..K_BITS * K_BITS).map(|i| s[i / K_BITS]).collect();

        let seed_bytes = keccak_seed(b"matrix reduction", &[1; 32], &[2; 32]);
        let mut writer = KeccakWriter::new(seed_bytes);
        let point = prove_product_sum(&mut writer, vec![g, skip_table, s_table], MATRIX_ROUNDS);
        let (rho, sigma) = point.split_at(FLOCK_K_SKIP);
        let full = [rho, &chi_in, sigma, &chi_in_prime].concat();
        let (a, b) = matrix_values(&full).unwrap();
        assert_eq!(multilinear_eval(&ga, &point).unwrap(), a);
        assert_eq!(multilinear_eval(&gb, &point).unwrap(), b);
        writer.send(a);
        writer.send(b);

        let verify = |r_lc: E, b_sent: E| {
            let mut stream = writer.stream.clone();
            let at = stream.len() - 24;
            stream[at..].copy_from_slice(&crate::transcript::scalar_bytes(b_sent));
            let mut channel = KeccakChannel::new(seed_bytes, &stream, Checks::Enforce);
            reduce_matrices(&mut channel, z_skip, &chi_in, &chi_in_prime, &s, alpha, r_lc)
        };
        let claim = verify(r_lc, b).expect("the honest reduction verifies");
        assert_eq!(claim.point, full);
        assert_eq!((claim.a, claim.b), (a, b));
        assert_eq!(
            verify(r_lc + crate::field::ONE, b).err(),
            Some(VerifierError::FlockMatrixTerminal)
        );
        assert_eq!(
            verify(r_lc, b + crate::field::ONE).err(),
            Some(VerifierError::FlockMatrixTerminal)
        );
    }
}
