// Part of this repository. Builds on `crate::flock` and `crate::matrices`: the first is adapted from leanVM
// (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/flock.rs, whose zerocheck,
// lincheck and ring switch this module re-states with the univariate skip's size and the slices' fate as
// parameters. New here: the skip of any size `k ≤ 6`, the matrices' reduction over the skip's `k` row bits, and the
// lincheck's slices left to one claim of their combination. MIT OR Apache-2.0; see NOTICE.md.
//! Flock's verifier, lever by lever (`crates/leanvm_univariate/SPEC.md`, the Flock section).
//!
//! **What the verifier needs of the 64 slices.** The lincheck ends on `s_i = ẑ(i, p)`, `i < 64` the packing bits
//! of `q_flock`, `p` its 26 word coordinates. The matrices' reduction (`crate::matrices`) uses three linear forms
//! of them: `Σ e_i s_i` (the `C = I` claim), `s_0` (the constant's pin) and `ŝ(σ)` (its terminal), and each enters
//! its check linearly. So the verifier needs only one linear combination `Σ μ_i s_i`, of known weights and known
//! value: the sumcheck's running claim is affine in the unknown forms (each round multiplies the claim's part by
//! its challenge), so the terminal becomes `Σ μ_i s_i = κ`.
//!
//! **What that combination is on the commitment.** `q_flock(u) = Σ_i z(i, u) x^i` packs the bits, so
//! `Σ_i μ_i ẑ(i, p) = Σ_u eq(p, u) ℓ(q_flock(u))` with `ℓ(y) = Σ_i μ_i bit_i(y)`, `GF(2)`-linear but not
//! `E`-linear: `ℓ(y) = Σ_(k<64) ν_k y^(2^k)`. A WHIR claim is an `E`-linear form of the committed words (a weight,
//! however arbitrary, times each word), and an `E`-linear form is `y ↦ ν y` on each word: one of the 64 dimensions
//! of `ℓ`. So the combination is not one WHIR claim; it is one claim of a type that ring-switches inside the opening
//! (leanVM's `ring_switch_open`: the 64 slices, the map `Φ`, a weighted WHIR claim), what [`Slices::Claim`] leaves to
//! `PCS_OPEN`. With `E`-linear claims only, the 64 slices are sent and the contract computes the ring switch's
//! target ([`Slices::Weighted`]: its weight `Φ(eq(p, ·))` left to a weighted claim; [`Slices::InContract`], the
//! measured baseline: its coefficients and its weight at a point computed by the contract too).

use crate::VerifierError;
use crate::field::{E, GEN};
use crate::flock::{N_FIXED_CHALLENGES, fixed_challenges, lagrange_interpolate, lagrange_weights, ring_map};
use crate::layout::{BLAKE2S_CONSTANT_COLUMN, BLAKE2S_R1CS_LOG_SIZE, FLOCK_NUM_LINCHECK_ROUNDS, K_BITS};
use crate::matrices::MatrixClaim;
use crate::multilinear::{dot, eq_eval, eq_kernel, multilinear_eval, poly_eval};
use crate::scalar::{Scalar, enter};
use crate::transcript::{Channel, sumcheck};

/// The packing bits of `q_flock`: 64 bits a word.
pub const PACKING: usize = 6;

/// What becomes of the lincheck's 64 slices.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slices {
    /// leanVM's: sent; the contract computes the ring switch's map, its 64 coefficients, its target, and the
    /// weight `Φ(eq(p, ·))` at a point (as the baseline contract's stack batch does).
    InContract,
    /// Sent; the contract computes the target only, the weight left to `PCS_OPEN` as a weighted claim.
    Weighted,
    /// Not sent: one claim `Σ μ_i ẑ(i, p) = κ` of a bit-slice type, ring-switched inside `PCS_OPEN`.
    Claim,
    /// As [`Slices::Weighted`], with the ring map's stages in tower order ([`crate::ring_tower`]): the target through
    /// `K`'s subfields, the weight at a point from the inside out.
    Tower,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Variant {
    /// The univariate skip's variables, `0..=6` (leanVM: 6). `0` is no skip: every round multilinear.
    pub skip: usize,
    pub slices: Slices,
}

impl Variant {
    pub const LEANVM: Self = Self {
        skip: PACKING,
        slices: Slices::InContract,
    };

    /// The scalars Flock reads at `log_n` variables: the skip's `2^k` values, the zerocheck's rounds and its two
    /// values, the lincheck's rounds, the slices if sent, the matrices' rounds and their two values.
    pub fn scalars(&self, log_n: usize) -> usize {
        let skip = if self.skip > 0 { 1 << self.skip } else { 0 };
        let slices = if self.slices == Slices::Claim { 0 } else { K_BITS };
        skip + 2 * (log_n - self.skip) + 2 + 2 * FLOCK_NUM_LINCHECK_ROUNDS + slices + 2 * (self.skip + PACKING) + 2
    }
}

/// What the reduction leaves for `PCS_OPEN`.
#[derive(Clone, Debug)]
pub struct Reduced<S> {
    /// `q_flock`'s word coordinates of the slices: the lincheck's column bits, then the instance bits.
    pub point: Vec<S>,
    /// `A0`, `B0` at one point (fixed commitments).
    pub matrices: MatrixClaim<S>,
    pub end: End<S>,
}

#[derive(Clone, Debug)]
pub enum End<S> {
    /// The ring switch's claim `Σ_u W(u) q_flock(u) = target`, `W = Φ(eq(point, ·))`, `Φ` drawn by `map`; with
    /// [`Slices::InContract`], also `W` at a point and its coefficients. `weight` is for measuring that variant
    /// (`tests/flock_levers.rs` outputs it, so that its cost is counted); `crates/leanvm_univariate` never uses
    /// `InContract`.
    Ring { map: Vec<S>, target: S, weight: Option<S> },
    /// `Σ_i weights_i ẑ(i, point) = value`.
    Combination { weights: Vec<S>, value: S },
}

/// What the zerocheck leaves: the skip's point (none without a skip), the rounds' challenges, and the claims on
/// `Az`, `Bz`, `Cz` there.
type Zerocheck<S> = (Option<S>, Vec<S>, [S; 3]);

/// The zerocheck with a skip over `k` variables: `2^k` values on the skip's coset (none for `k = 0`), then
/// `log_n - k` rounds; seven fixed coordinates first, as leanVM's.
fn zerocheck<S: Scalar>(
    log_n: usize,
    k: usize,
    transcript: &mut impl Channel<S>,
) -> Result<Zerocheck<S>, VerifierError> {
    let _phase = enter("flock zerocheck: skip round");
    let mut r: Vec<Option<S>> = fixed_challenges().map(|c| Some(S::constant(c))).into();
    r.extend(transcript.samples(log_n - k - N_FIXED_CHALLENGES).into_iter().map(Some));
    let (z_skip, claim) = if k > 0 {
        let coset = transcript.next_scalars(1 << k)?;
        let z = transcript.sample();
        let values = [vec![S::zero(); 1 << k], coset].concat();
        (Some(z), lagrange_interpolate(2 << k, &values, z))
    } else {
        (None, S::zero())
    };
    let (chi, running) = {
        let _rounds = enter("flock zerocheck: rounds");
        sumcheck(transcript, claim, 3, &r)?
    };
    let (v_a, v_b) = (transcript.next_scalar()?, transcript.next_scalar()?);
    Ok((z_skip, chi, [v_a, v_b, running + v_a * v_b]))
}

/// The weights of the row's 6 packing bits: the skip's Lagrange weights on its `k`, eq on the `6 - k` others.
fn row_low_weights<S: Scalar>(z_skip: Option<S>, low: &[S]) -> (Vec<S>, Vec<S>) {
    let skip = match z_skip {
        Some(z) => lagrange_weights(1 << (PACKING - low.len()), z),
        None => vec![S::one()],
    };
    let mle = eq_kernel(low);
    let weights = mle.iter().flat_map(|&m| skip.iter().map(move |&l| l * m)).collect();
    (skip, weights)
}

/// Flock at `log_n = 14 + log(instances)` variables, as `variant` has it.
pub fn verify<S: Scalar>(
    log_n: usize,
    variant: Variant,
    transcript: &mut impl Channel<S>,
) -> Result<Reduced<S>, VerifierError> {
    let front = front(log_n, variant, transcript)?;
    let (matrices, combination) = reduce_terminal(
        transcript,
        front.z_skip,
        &front.row_low,
        &front.chi_in,
        &front.chi_in_prime,
        front.alpha,
        front.r_lc,
        front.slices.as_deref(),
    )?;
    let end = match (&front.slices, combination) {
        (Some(s), _) => ring_end(variant, &front, s, transcript),
        (None, Some((weights, value))) => End::Combination { weights, value },
        (None, None) => unreachable!("without the slices, the terminal is a combination"),
    };
    Ok(Reduced {
        point: front.point,
        matrices,
        end,
    })
}

/// Flock with its matrices' reduction left to a later sumcheck that runs its `k + 6` rounds beside its own (the
/// batching sumcheck of `crates/leanvm_univariate`, SPEC.md §13): the zerocheck, the lincheck, and with the slices
/// sent, the slices and the ring switch's map and target; then what that sumcheck needs of the matrices' reduction.
/// Without the slices ([`Slices::Claim`]) there is no end yet: the later sumcheck's terminal leaves the combination
/// ([`Pending::combination`]).
pub fn verify_deferred<S: Scalar>(
    log_n: usize,
    variant: Variant,
    transcript: &mut impl Channel<S>,
) -> Result<(Vec<S>, Option<End<S>>, Pending<S>), VerifierError> {
    let front = front(log_n, variant, transcript)?;
    let pending = Pending::new(
        front.z_skip,
        &front.row_low,
        &front.chi_in,
        &front.chi_in_prime,
        front.alpha,
        front.r_lc,
        front.slices.as_deref(),
    );
    let end = front.slices.as_ref().map(|slices| ring_end(variant, &front, slices, transcript));
    Ok((front.point, end, pending))
}

/// The matrices' reduction, its rounds run by a later sumcheck: `Σ_(x, y) G(x, y) L̂(x) ŝ(y) = claim` over the skip's
/// `k` row bits `x` and the column's 6 packing bits `y`, `G = Â0 + α B̂0` at the row and column points.
#[derive(Clone, Debug)]
pub struct Pending<S> {
    pub claim: S,
    k: usize,
    skip_weights: Vec<S>,
    low_weights: Vec<S>,
    c_weight: S,
    pin_weight: S,
    row_low: Vec<S>,
    chi_in: Vec<S>,
    chi_in_prime: Vec<S>,
    alpha: S,
    /// The slices if sent; else the terminal leaves their combination.
    slices: Option<Vec<S>>,
}

impl<S: Scalar> Pending<S> {
    /// The matrices' reduction of the lincheck's terminal `r_lc`, as `reduce_terminal` starts it: with the slices,
    /// its claim has their known part; without, it is `r_lc` and their part stays unknown.
    fn new(
        z_skip: Option<S>,
        row_low: &[S],
        chi_in: &[S],
        chi_in_prime: &[S],
        alpha: S,
        r_lc: S,
        slices: Option<&[S]>,
    ) -> Self {
        let _phase = enter("flock matrices: reduction to A0, B0 claims");
        let (skip_weights, low_weights) = row_low_weights(z_skip, row_low);
        let (c_weight, pin_weight) = known_weights(alpha, chi_in, chi_in_prime);
        let known = slices.map(|slices| {
            c_weight * dot(&low_weights, slices) + pin_weight * slices[BLAKE2S_CONSTANT_COLUMN % K_BITS]
        });
        Self {
            claim: r_lc + known.unwrap_or(S::zero()),
            k: PACKING - row_low.len(),
            skip_weights,
            low_weights,
            c_weight,
            pin_weight,
            row_low: row_low.to_vec(),
            chi_in: chi_in.to_vec(),
            chi_in_prime: chi_in_prime.to_vec(),
            alpha,
            slices: slices.map(|s| s.to_vec()),
        }
    }

    /// Whether the slices were sent (else [`Self::combination`] is the terminal).
    pub fn has_slices(&self) -> bool {
        self.slices.is_some()
    }

    /// Without the slices: the terminal of the sumcheck that ran the matrices' rounds as its first, at its point
    /// (every round's challenge), with `a = Â0`, `b = B̂0` there, the matrices' zero-extension `extension` and its power
    /// `scale` in that sumcheck. Each round maps its claim `c` to `c0 + (c + c2) r + c2 r^2`, so the slices' unknown
    /// part of the initial claim reaches the last claim times `Λ`, the product of every challenge: the terminal is
    /// `Σ_i μ_i s_i = rest`, `rest` the terminal's known terms and the last claim, and
    /// `μ = scale (extension (a + α b) L̂(ρ) eq(σ, ·) + Λ (c_weight e + pin_weight [· = pin]))`. Returns `μ` and the
    /// claims on `A0`, `B0`.
    pub fn combination(&self, point: &[S], a: S, b: S, extension: S, scale: S) -> Result<(Vec<S>, MatrixClaim<S>), VerifierError> {
        assert!(self.slices.is_none(), "the combination is for unsent slices");
        let _phase = enter("flock matrices: the slices' combination");
        let (rho, sigma) = point[..self.rounds()].split_at(self.k);
        let skip_at_rho = if self.k > 0 {
            multilinear_eval(&self.skip_weights, rho)?
        } else {
            S::one()
        };
        let lambda = point.iter().fold(S::one(), |acc, &r| acc * r);
        let factor = scale * extension * (a + self.alpha * b) * skip_at_rho;
        let (lambda_c, lambda_pin) = (scale * lambda * self.c_weight, scale * lambda * self.pin_weight);
        let mut weights: Vec<S> = eq_kernel(sigma).into_iter().map(|e| factor * e).collect();
        for (weight, &low) in weights.iter_mut().zip(&self.low_weights) {
            *weight += lambda_c * low;
        }
        weights[BLAKE2S_CONSTANT_COLUMN % K_BITS] += lambda_pin;
        let claim = MatrixClaim {
            point: [rho, &self.row_low, &self.chi_in, sigma, &self.chi_in_prime].concat(),
            a,
            b,
        };
        Ok((weights, claim))
    }

    /// The variables of the sum, the sumcheck's first ones.
    pub fn rounds(&self) -> usize {
        self.k + PACKING
    }

    /// At the sumcheck's point (its first [`Self::rounds`] coordinates), with `a = Â0`, `b = B̂0` there: the
    /// summand's value `(a + α b) L̂(ρ) ŝ(σ)`, and the claims on `A0`, `B0`.
    pub fn terminal(&self, point: &[S], a: S, b: S) -> Result<(S, MatrixClaim<S>), VerifierError> {
        let _phase = enter("flock matrices: reduction to A0, B0 claims");
        let (rho, sigma) = point[..self.rounds()].split_at(self.k);
        let skip_at_rho = if self.k > 0 {
            multilinear_eval(&self.skip_weights, rho)?
        } else {
            S::one()
        };
        let slices = self.slices.as_ref().expect("the terminal of sent slices");
        let value = (a + self.alpha * b) * skip_at_rho * multilinear_eval(slices, sigma)?;
        let claim = MatrixClaim {
            point: [rho, &self.row_low, &self.chi_in, sigma, &self.chi_in_prime].concat(),
            a,
            b,
        };
        Ok((value, claim))
    }
}

/// What the zerocheck and the lincheck leave, and the slices if sent.
struct Front<S> {
    z_skip: Option<S>,
    chi: Vec<S>,
    row_low: Vec<S>,
    chi_in: Vec<S>,
    chi_in_prime: Vec<S>,
    alpha: S,
    r_lc: S,
    slices: Option<Vec<S>>,
    /// `q_flock`'s word coordinates of the slices: the lincheck's column bits, then the instance bits.
    point: Vec<S>,
}

fn front<S: Scalar>(log_n: usize, variant: Variant, transcript: &mut impl Channel<S>) -> Result<Front<S>, VerifierError> {
    let k = variant.skip;
    assert!(k <= PACKING && log_n >= BLAKE2S_R1CS_LOG_SIZE + N_FIXED_CHALLENGES);
    let (z_skip, chi, [v_a, v_b, v_c]) = zerocheck(log_n, k, transcript)?;
    // The row point: the skip, the packing bits left to rounds, the 8 slot bits, the instance bits.
    let (row_low, rest) = chi.split_at(PACKING - k);
    let (chi_in, chi_rest) = rest.split_at(FLOCK_NUM_LINCHECK_ROUNDS);

    let _phase = enter("flock lincheck: rounds");
    let alpha = transcript.sample();
    let claim = v_a + alpha * v_b + alpha.pow(2) * v_c + alpha.pow(3);
    let (round_challenges, r_lc) = sumcheck(transcript, claim, 3, &[None; FLOCK_NUM_LINCHECK_ROUNDS])?;
    let chi_in_prime: Vec<S> = round_challenges.iter().rev().copied().collect();
    let slices = match variant.slices {
        Slices::Claim => None,
        _ => Some(transcript.next_scalars(K_BITS)?),
    };
    let point: Vec<S> = [&chi_in_prime[..], chi_rest].concat();
    Ok(Front {
        z_skip,
        row_low: row_low.to_vec(),
        chi_in: chi_in.to_vec(),
        chi_in_prime,
        chi,
        alpha,
        r_lc,
        slices,
        point,
    })
}

/// The ring switch on the sent slices: its map drawn, its target; the weight at a point if the contract computes it.
fn ring_end<S: Scalar>(variant: Variant, front: &Front<S>, s: &[S], transcript: &mut impl Channel<S>) -> End<S> {
    let _phase = enter("ring switch: map, coefficients, target");
    let map = transcript.samples(crate::flock::RING_MAP_SHIFTS.len());
    let target = if variant.slices == Slices::Tower {
        crate::ring_tower::target(s, &map)
    } else {
        let images: Vec<S> = s.iter().map(|&value| ring_map(value, &map)).collect();
        poly_eval(&images, S::constant(GEN))
    };
    let weight = (variant.slices == Slices::InContract).then(|| {
        let weight = crate::flock::ring_switch_weight(front.point.clone(), &map);
        // At a point of the stack's batch: any 26 coordinates cost the same; the zerocheck's are at hand.
        weight.at(&front.chi[..front.point.len()])
    });
    End::Ring { map, target, weight }
}

/// The weights of the terminal's two known terms: the `C = I` claim's and the constant position's pin.
fn known_weights<S: Scalar>(alpha: S, chi_in: &[S], chi_in_prime: &[S]) -> (S, S) {
    let constant_bits: Vec<S> = (0..FLOCK_NUM_LINCHECK_ROUNDS)
        .map(|bit| S::constant(E::new((BLAKE2S_CONSTANT_COLUMN / K_BITS) as u64 >> bit & 1, 0, 0)))
        .collect();
    let pin_weight = alpha.pow(3) * eq_eval(&constant_bits, chi_in_prime);
    let c_weight = alpha.pow(2) * eq_eval(chi_in, chi_in_prime);
    (c_weight, pin_weight)
}

/// The lincheck's terminal `r_lc`, by the matrices' reduction over the skip's `k` row bits and the 6 packing bits
/// of the column: claims on `A0`, `B0`, and, without the slices, the combination `Σ weights_i s_i = value` the
/// terminal leaves (with them, the terminal is checked here).
#[allow(clippy::type_complexity)]
pub fn reduce_terminal<S: Scalar>(
    transcript: &mut impl Channel<S>,
    z_skip: Option<S>,
    row_low: &[S],
    chi_in: &[S],
    chi_in_prime: &[S],
    alpha: S,
    r_lc: S,
    s: Option<&[S]>,
) -> Result<(MatrixClaim<S>, Option<(Vec<S>, S)>), VerifierError> {
    let _phase = enter("flock matrices: reduction to A0, B0 claims");
    let k = PACKING - row_low.len();
    let (skip_weights, low_weights) = row_low_weights(z_skip, row_low);
    let (c_weight, pin_weight) = known_weights(alpha, chi_in, chi_in_prime);
    let pin = BLAKE2S_CONSTANT_COLUMN % K_BITS;
    // The terminal's two known terms, when the slices are; else the claim's part the slices hold.
    let known = s.map(|s| c_weight * dot(&low_weights, s) + pin_weight * s[pin]);
    let rounds = vec![None; k + PACKING];
    let (challenges, running) = {
        let _rounds = enter("flock matrices: sumcheck rounds");
        sumcheck(transcript, r_lc + known.unwrap_or(S::zero()), 3, &rounds)?
    };
    let (rho, sigma) = challenges.split_at(k);
    let (a, b) = (transcript.next_scalar()?, transcript.next_scalar()?);
    let skip_at_rho = if k > 0 {
        multilinear_eval(&skip_weights, rho)?
    } else {
        S::one()
    };
    let factor = (a + alpha * b) * skip_at_rho;
    let matrices = MatrixClaim {
        point: [rho, row_low, chi_in, sigma, chi_in_prime].concat(),
        a,
        b,
    };
    let combination = match s {
        Some(s) => {
            transcript.require_zero(
                factor * multilinear_eval(s, sigma)? + running,
                VerifierError::FlockMatrixTerminal,
            )?;
            None
        }
        None => {
            // The running claim is `running + λ · (the slices' part)`, `λ` the product of the rounds' challenges
            // (a round maps its claim `c` to `c0 + (c + c2) r + c2 r^2`): the terminal
            // `factor · ŝ(σ) = running + λ (c_weight Σ e_i s_i + pin_weight s_pin)`.
            let _phase = enter("flock matrices: the slices' combination");
            let lambda = challenges.iter().fold(S::one(), |acc, &r| acc * r);
            let (lambda_c, lambda_pin) = (lambda * c_weight, lambda * pin_weight);
            let mut weights: Vec<S> = eq_kernel(sigma).into_iter().map(|e| factor * e).collect();
            for (weight, &low) in weights.iter_mut().zip(&low_weights) {
                *weight += lambda_c * low;
            }
            weights[pin] += lambda_pin;
            Some((weights, running))
        }
    };
    Ok((matrices, combination))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{ONE, ZERO};
    use crate::flock::blake2s_row_values;
    use crate::matrices::matrix_values;
    use crate::matrices::prover::prove_product_sum;
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

    /// `G'(x, y) = (Â0 + α B̂0)((x, low, chi_in), (y, chi_in'))` at index `x + 2^k y`, `x` the skip's `k` row bits.
    fn sliced(k: usize, low: &[E], chi_in: &[E], chi_in_prime: &[E], alpha: E) -> Vec<E> {
        let high = eq_kernel(chi_in_prime);
        let rows = eq_kernel(&[low, chi_in].concat());
        let mut g = vec![ZERO; (1 << k) * K_BITS];
        for y in 0..K_BITS {
            let mut w = vec![ZERO; 1 << BLAKE2S_R1CS_LOG_SIZE];
            for (h, &weight) in high.iter().enumerate() {
                w[h * K_BITS + y] = weight;
            }
            let (left, right) = blake2s_row_values(&w);
            for (row, (&l, &r)) in left.iter().zip(&right).enumerate() {
                g[(row & ((1 << k) - 1)) + (y << k)] += rows[row >> k] * (l + alpha * r);
            }
        }
        g
    }

    /// The lincheck's terminal as leanVM's walk computes it, generalised to the skip's `k` bits: the matrix terms
    /// (`Σ e_x s_y G(x, y)` over the 6 packing bits of each side), the `C = I` claim and the constant's pin.
    fn walked(k: usize, z_skip: E, low: &[E], chi_in: &[E], chi_in_prime: &[E], s: &[E], alpha: E) -> E {
        let (_, low_weights) = row_low_weights((k > 0).then_some(z_skip), low);
        let high = eq_kernel(chi_in_prime);
        let mut w = vec![ZERO; 1 << BLAKE2S_R1CS_LOG_SIZE];
        for (l, &slice) in s.iter().enumerate() {
            for (h, &weight) in high.iter().enumerate() {
                w[h * K_BITS + l] = slice * weight;
            }
        }
        let (left, right) = blake2s_row_values(&w);
        let rows = eq_kernel(chi_in);
        let mut matrix = ZERO;
        for (row, (&l, &r)) in left.iter().zip(&right).enumerate() {
            matrix += low_weights[row % K_BITS] * rows[row / K_BITS] * (l + alpha * r);
        }
        matrix
            + alpha.pow(2) * eq_eval(chi_in, chi_in_prime) * dot(&low_weights, s)
            + alpha.pow(3) * w[BLAKE2S_CONSTANT_COLUMN]
    }

    /// For each skip size: with the slices sent, the honest matrices' reduction verifies and its claims are `A0`,
    /// `B0`; without them, the combination the verifier leaves holds of the true slices, and fails for others.
    #[test]
    fn the_slices_combination_is_the_terminal() {
        for k in [6, 3, 0] {
            let mut seed = 0x0F10_C0DE ^ k as u64;
            let z_skip = element(&mut seed);
            let low: Vec<E> = (0..PACKING - k).map(|_| element(&mut seed)).collect();
            let chi_in: Vec<E> = (0..8).map(|_| element(&mut seed)).collect();
            let chi_in_prime: Vec<E> = (0..8).map(|_| element(&mut seed)).collect();
            let s: Vec<E> = (0..K_BITS).map(|_| element(&mut seed)).collect();
            let alpha = element(&mut seed);
            let r_lc = walked(k, z_skip, &low, &chi_in, &chi_in_prime, &s, alpha);

            // The honest reduction: Σ_(x, y) L(x) s(y) G'(x, y) over k + 6 variables.
            let g = sliced(k, &low, &chi_in, &chi_in_prime, alpha);
            let skip = if k > 0 {
                lagrange_weights(1 << k, z_skip)
            } else {
                vec![ONE]
            };
            let size = (1 << k) * K_BITS;
            let skip_table: Vec<E> = (0..size).map(|i| skip[i % (1 << k)]).collect();
            let s_table: Vec<E> = (0..size).map(|i| s[i >> k]).collect();
            let bytes = keccak_seed(b"flock levers 16B", &[k as u8; 32], &[2; 32]);
            let mut writer = KeccakWriter::new(bytes);
            let point = prove_product_sum(&mut writer, vec![g, skip_table, s_table], k + PACKING);
            let (rho, sigma) = point.split_at(k);
            let full = [rho, &low, &chi_in, sigma, &chi_in_prime].concat();
            let (a, b) = matrix_values(&full).unwrap();
            writer.send(a);
            writer.send(b);

            // The verifier's step, on that stream, both ways.
            let run = |slices: Option<&[E]>| {
                let mut channel = KeccakChannel::new(bytes, &writer.stream, Checks::Enforce);
                let z = (k > 0).then_some(z_skip);
                reduce_terminal(&mut channel, z, &low, &chi_in, &chi_in_prime, alpha, r_lc, slices)
            };
            let (claim, none) = run(Some(&s)).expect("the explicit terminal holds");
            assert!(none.is_none());
            assert_eq!(claim.point, full, "k = {k}");
            assert_eq!((claim.a, claim.b), (a, b));
            let (claim, combination) = run(None).expect("a combination is left");
            assert_eq!(claim.point, full);
            let (weights, value) = combination.expect("a combination");
            assert_eq!(
                dot(&weights, &s),
                value,
                "k = {k}: the combination holds of the true slices"
            );
            // Other slices, committed instead, make it false.
            let mut other = s.clone();
            other[17] += ONE;
            assert_ne!(dot(&weights, &other), value, "k = {k}");
            assert_eq!(
                run(Some(&other)).err(),
                Some(VerifierError::FlockMatrixTerminal),
                "k = {k}: the explicit terminal rejects them"
            );
        }
    }

    /// Prove `Σ_i Σ_p c_p Π_t parts[p][t][i]` over `rounds` variables, low bit first, with degree-2 messages `(c0, c2)`:
    /// the batch of several product sums in one sumcheck.
    fn prove_sums(writer: &mut KeccakWriter, mut parts: Vec<(E, Vec<Vec<E>>)>, rounds: usize) -> Vec<E> {
        let mut point = Vec::new();
        for _ in 0..rounds {
            let half = parts[0].1[0].len() / 2;
            let mut coefficients = [ZERO; 4];
            for (scale, tables) in &parts {
                for i in 0..half {
                    let mut product = vec![*scale];
                    for table in tables {
                        let (lo, hi) = (table[2 * i], table[2 * i + 1]);
                        let mut next = vec![ZERO; product.len() + 1];
                        for (d, &p) in product.iter().enumerate() {
                            next[d] += p * lo;
                            next[d + 1] += p * (lo + hi);
                        }
                        product = next;
                    }
                    for (c, p) in coefficients.iter_mut().zip(&product) {
                        *c += *p;
                    }
                }
            }
            assert_eq!(coefficients[3], ZERO, "degree 2 in every variable");
            writer.send(coefficients[0]);
            writer.send(coefficients[2]);
            let r = writer.sample();
            point.push(r);
            for (_, tables) in parts.iter_mut() {
                for table in tables.iter_mut() {
                    for i in 0..half {
                        table[i] = table[2 * i] + r * (table[2 * i] + table[2 * i + 1]);
                    }
                    table.truncate(half);
                }
            }
        }
        point
    }

    /// The matrices' reduction left pending runs its `k + 6` rounds as the first rounds of a longer sumcheck, batched
    /// with another product sum by a power of `λ`, zero-extended by `eq(·, 0)`: the honest proof verifies, its claims
    /// on `A0`, `B0` are the matrices' values at the point, and other slices fail it.
    #[test]
    fn the_pending_matrices_reduction_merges_into_a_longer_sumcheck() {
        for k in [3, 0] {
            let vars = 12;
            let mut seed = 0x0de7_e44e ^ k as u64;
            let z_skip = element(&mut seed);
            let low: Vec<E> = (0..PACKING - k).map(|_| element(&mut seed)).collect();
            let chi_in: Vec<E> = (0..8).map(|_| element(&mut seed)).collect();
            let chi_in_prime: Vec<E> = (0..8).map(|_| element(&mut seed)).collect();
            let s: Vec<E> = (0..K_BITS).map(|_| element(&mut seed)).collect();
            let alpha = element(&mut seed);
            let r_lc = walked(k, z_skip, &low, &chi_in, &chi_in_prime, &s, alpha);
            let z = (k > 0).then_some(z_skip);
            let pending = Pending::new(z, &low, &chi_in, &chi_in_prime, alpha, r_lc, Some(&s));
            assert_eq!(pending.rounds(), k + PACKING);

            // The matrices' tables over `vars` variables: G' zero-extended (δ_0 on the rest), L and s repeated.
            let g = sliced(k, &low, &chi_in, &chi_in_prime, alpha);
            let skip = if k > 0 {
                lagrange_weights(1 << k, z_skip)
            } else {
                vec![ONE]
            };
            let size = (1 << k) * K_BITS;
            let full = 1 << vars;
            let g_ext: Vec<E> = (0..full).map(|i| if i < size { g[i] } else { ZERO }).collect();
            let l_ext: Vec<E> = (0..full).map(|i| skip[i % (1 << k)]).collect();
            let s_ext: Vec<E> = (0..full).map(|i| s[(i % size) >> k]).collect();
            // Another product sum, the batch's own.
            let w: Vec<E> = (0..full).map(|_| element(&mut seed)).collect();
            let c: Vec<E> = (0..full).map(|_| element(&mut seed)).collect();
            let other: E = w.iter().zip(&c).fold(ZERO, |acc, (&x, &y)| acc + x * y);

            let bytes = keccak_seed(b"flock merged 16B", &[k as u8; 32], &[3; 32]);
            let mut writer = KeccakWriter::new(bytes);
            let lambda = writer.sample();
            let point = prove_sums(
                &mut writer,
                vec![(ONE, vec![w.clone(), c.clone()]), (lambda, vec![g_ext, l_ext, s_ext])],
                vars,
            );
            let (rho, rest) = point.split_at(k);
            let sigma = &rest[..PACKING];
            let matrix_point = [rho, &low, &chi_in, sigma, &chi_in_prime].concat();
            let (a, b) = matrix_values(&matrix_point).unwrap();
            let (w_r, c_r) = (multilinear_eval(&w, &point).unwrap(), multilinear_eval(&c, &point).unwrap());
            writer.send(c_r);
            writer.send(a);
            writer.send(b);

            // The verifier's side, as `crates/leanvm_univariate`'s batch runs it.
            let run = |pending: &Pending<E>| -> Result<MatrixClaim<E>, VerifierError> {
                let mut channel = KeccakChannel::new(bytes, &writer.stream, Checks::Enforce);
                let lambda = channel.sample();
                let target = other + lambda * pending.claim;
                let (r, last) = sumcheck(&mut channel, target, 3, &vec![None; vars])?;
                let c_r = channel.next_scalar()?;
                let (a, b) = (channel.next_scalar()?, channel.next_scalar()?);
                let (value, claim) = pending.terminal(&r, a, b)?;
                let extension = (pending.rounds()..vars).fold(ONE, |acc, j| acc * (ONE + r[j]));
                let sum = multilinear_eval(&w, &r)? * c_r + lambda * value * extension;
                channel.require_zero(sum + last, VerifierError::StackBatchTerminal)?;
                Ok(claim)
            };
            let claim = run(&pending).expect("the merged proof verifies");
            assert_eq!(claim.point, matrix_point, "k = {k}");
            assert_eq!((claim.a, claim.b), (a, b));
            assert_eq!(w_r * c_r, multilinear_eval(&w, &point).unwrap() * c_r);
            // Without the slices: the terminal leaves Σ μ_i s_i = rest, which the true slices hold.
            {
                let unsent = Pending::new(z, &low, &chi_in, &chi_in_prime, alpha, r_lc, None);
                let mut channel = KeccakChannel::new(bytes, &writer.stream, Checks::Enforce);
                let lambda = channel.sample();
                let target = other + lambda * unsent.claim;
                let (r, last) = sumcheck(&mut channel, target, 3, &vec![None; vars]).unwrap();
                let c_r = channel.next_scalar().unwrap();
                let (a, b) = (channel.next_scalar().unwrap(), channel.next_scalar().unwrap());
                let extension = (unsent.rounds()..vars).fold(ONE, |acc, j| acc * (ONE + r[j]));
                let (weights, claim) = unsent.combination(&r, a, b, extension, lambda).unwrap();
                let rest = multilinear_eval(&w, &r).unwrap() * c_r + last;
                assert_eq!(dot(&weights, &s), rest, "k = {k}: the combination holds of the true slices");
                assert_eq!(claim.point, matrix_point);
                let mut wrong = s.clone();
                wrong[9] += ONE;
                assert_ne!(dot(&weights, &wrong), rest);
            }
            let mut other_slices = s.clone();
            other_slices[5] += ONE;
            let forged = Pending::new(z, &low, &chi_in, &chi_in_prime, alpha, r_lc, Some(&other_slices));
            assert!(run(&forged).is_err(), "k = {k}: other slices fail");
        }
    }

    /// The stream lengths `Variant::scalars` states are what `verify` reads.
    #[test]
    fn scalars_are_what_verify_reads() {
        for skip in [0, 1, 3, 4, 5, 6] {
            for slices in [Slices::InContract, Slices::Weighted, Slices::Claim, Slices::Tower] {
                let variant = Variant { skip, slices };
                let log_n = 14 + 18;
                let stream = vec![0x5au8; 24 * variant.scalars(log_n)];
                let mut channel = KeccakChannel::new(
                    [7; 32],
                    &stream,
                    Checks::Collect {
                        zero: vec![],
                        nonzero: vec![],
                    },
                );
                verify::<E>(log_n, variant, &mut channel).expect("reads what it states");
                channel.finish().expect("nothing left");
            }
        }
    }
}
