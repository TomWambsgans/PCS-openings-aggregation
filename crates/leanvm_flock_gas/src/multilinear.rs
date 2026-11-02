// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/multilinear.rs:
// the same functions on a generic `Scalar`, without the table-driven `Scaler` (a speed-up of the native code, not a
// different computation). MIT OR Apache-2.0; see NOTICE.md.
//! Multilinear and stacking helpers.

use crate::field::{E, GEN, ONE};
use crate::scalar::Scalar;
use crate::{VerifierError, require};

/// `eq(i, point)` for every index `i`, LSB-first, at one product per entry: `v * (1 + r) = v + v * r`.
pub fn eq_kernel<S: Scalar>(point: &[S]) -> Vec<S> {
    let mut out = vec![S::zero(); 1 << point.len()];
    out[0] = S::one();
    for (k, &r) in point.iter().enumerate() {
        let (low, high) = out[..2 << k].split_at_mut(1 << k);
        for (v, h) in low.iter_mut().zip(high) {
            *h = *v * r;
            *v += *h;
        }
    }
    out
}

pub fn multilinear_eval<S: Scalar>(mle: &[S], point: &[S]) -> Result<S, VerifierError> {
    require(
        point.len() < 64 && mle.len() == 1 << point.len(),
        VerifierError::MultilinearSize,
    )?;
    let mut cur: Vec<S> = mle.to_vec();
    for &r in point {
        for i in 0..cur.len() / 2 {
            cur[i] = cur[2 * i] + r * (cur[2 * i] + cur[2 * i + 1]);
        }
        cur.truncate(cur.len() / 2);
    }
    Ok(cur[0])
}

pub fn log2_ceil(value: u64) -> usize {
    (64 - value.saturating_sub(1).leading_zeros()) as usize
}

pub fn log2_strict(value: u64) -> Result<usize, VerifierError> {
    require(value.is_power_of_two(), VerifierError::NotPowerOfTwo)?;
    Ok(value.trailing_zeros() as usize)
}

pub fn eq_eval<S: Scalar>(left: &[S], right: &[S]) -> S {
    assert_eq!(left.len(), right.len());
    let mut result = S::one();
    for (&x, &y) in left.iter().zip(right) {
        result *= S::one() + x + y;
    }
    result
}

pub fn dot<S: Scalar>(left: &[S], right: &[S]) -> S {
    assert_eq!(left.len(), right.len());
    let mut result = S::zero();
    for (&x, &y) in left.iter().zip(right) {
        result += x * y;
    }
    result
}

/// `pad_n(point)`, the multilinear extension of `[z >= n]`, `n <= 2^len(point)` (lemma lem:suffix).
pub fn padding_weight<S: Scalar>(point: &[S], n: u64) -> S {
    let bit = |k: usize| S::constant(E::new(n >> k & 1, 0, 0));
    let one = S::one();
    let low = point
        .iter()
        .enumerate()
        .fold(one, |pad, (k, &r)| (one + bit(k)) * r + (one + bit(k) + r) * pad);
    (one + bit(point.len())) * low
}

/// MLE of `[1, g, g^2, ...]` at an LSB-first point.
pub fn index_mle<S: Scalar>(point: &[S]) -> S {
    let mut result = S::one();
    let mut generator_power = GEN;
    for &challenge in point {
        result *= S::one() + challenge * S::constant(ONE + generator_power);
        generator_power = generator_power.square();
    }
    result
}

/// A polynomial at `point`, by Horner over its coefficients, constant first.
pub fn poly_eval<S: Scalar>(coefficients: &[S], point: S) -> S {
    coefficients.iter().rev().fold(S::zero(), |acc, &c| acc * point + c)
}

/// Where something sits in the stacked cube: a claim's point fills the `variables` coordinates above `low`, the bits of `index` fixing the rest.
/// `low` is zero for a block with a cube of its own, and the slot width for a column interleaved into a bigger block.
#[derive(Clone, Copy, Debug)]
pub struct Placement {
    pub variables: usize,
    pub index: u64,
    pub low: usize,
}

impl Placement {
    pub fn stack_point<S: Scalar>(&self, point: &[S], stack_log: usize) -> Vec<S> {
        let bits = selector_point::<S>(self.index, stack_log);
        [&bits[..self.low], point, &bits[self.low + self.variables..]].concat()
    }

    /// eq weight of the coordinates above the window.
    pub fn eq_above<S: Scalar>(&self, point: &[S]) -> S {
        let window = self.low + self.variables;
        let bits = selector_point::<S>(self.index >> window, point.len() - window);
        eq_eval(&bits, &point[window..])
    }
}

pub fn stack_offsets(sizes: &[usize]) -> (Vec<u64>, usize) {
    let mut order: Vec<usize> = (0..sizes.len()).collect();
    order.sort_by_key(|&index| (std::cmp::Reverse(sizes[index]), index));
    let mut offsets = vec![0; sizes.len()];
    let mut total = 0;
    for index in order {
        offsets[index] = total;
        total += 1 << sizes[index];
    }
    (offsets, log2_ceil(total))
}

fn selector_point<S: Scalar>(selector: u64, length: usize) -> Vec<S> {
    (0..length)
        .map(|bit| S::constant(E::new(selector >> bit & 1, 0, 0)))
        .collect()
}
