// Part of this repository. The batching (one challenge's powers over the claims' values and weights) is leanVM's
// `verify_stacked_opening` (https://github.com/leanEthereum/leanVM, commit 42422001, crates/verifier/src/lib.rs);
// the sumcheck that ends it on one evaluation is new here. MIT OR Apache-2.0; see NOTICE.md.
//! The claims on the committed stack, reduced to one evaluation claim for `PCS_OPEN`.
//!
//! leanVM hands its stack claims to WHIR as one weighted claim, `Σ_u W(u) q(u) = T` with `W = Σ_j λ^j W_j` and
//! `T = Σ_j λ^j v_j`: WHIR's own sumcheck runs on `W q`, and its verifier evaluates `W` at WHIR's terminal point.
//! `PCS_OPEN` takes evaluation claims, a point and a value. So the contract runs that sumcheck itself, over the
//! stack's `n` variables, low bit first, with degree-2 messages; the prover then sends `v = q(r)`, the verifier
//! checks `v W(r)` against the sumcheck, and `(r, v)` is the one claim on the stack's root. Evaluating `W(r)` is
//! what WHIR's verifier does at its terminal point: the same cost, in the contract.

use crate::multilinear::dot;
use crate::scalar::{Scalar, enter, powers};
use crate::transcript::{Channel, sumcheck};
use crate::{StackClaim, VerifierError};

/// The claims as one evaluation claim on the stack of `2^stack_log` words: the point, then the value.
pub fn batch_stack_claims<S: Scalar>(
    transcript: &mut impl Channel<S>,
    stack_log: usize,
    claims: &[StackClaim<S>],
) -> Result<(Vec<S>, S), VerifierError> {
    let _phase = enter("stack batch: sumcheck rounds");
    let values: Vec<S> = claims.iter().map(|(_, value)| *value).collect();
    let scales = powers(transcript.sample(), claims.len());
    let target = dot(&scales, &values);
    let (point, claim) = sumcheck(transcript, target, 3, &vec![None; stack_log])?;
    let value = transcript.next_scalar()?;
    let weight = {
        let _phase = enter("stack batch: eq / selector weights at the point");
        let weights: Vec<S> = claims.iter().map(|(weight, _)| weight(&point)).collect();
        dot(&scales, &weights)
    };
    transcript.require_zero(value * weight + claim, VerifierError::StackBatchTerminal)?;
    Ok((point, value))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{E, ONE, ZERO};
    use crate::matrices::prover::prove_product_sum;
    use crate::multilinear::{eq_eval, eq_kernel, multilinear_eval};
    use crate::scalar::powers;
    use crate::transcript::{Checks, KeccakChannel, KeccakWriter, keccak_seed, scalar_bytes};

    /// A stack of base-field words, claims at points of it with eq weights and one claim with a weight that is not an
    /// eq (a sum of two): the honest reduction verifies and its claim is the stack's value; a wrong value is caught.
    #[test]
    fn reduction_is_complete() {
        let n = 10;
        let mut seed = 0xB47C_u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let stack: Vec<E> = (0..1 << n).map(|_| E::new(next(), 0, 0)).collect();
        let points: Vec<Vec<E>> = (0..3)
            .map(|_| (0..n).map(|_| E::new(next(), next(), next())).collect())
            .collect();
        let mut claims: Vec<StackClaim<E>> = points
            .iter()
            .map(|p| {
                let value = multilinear_eval(&stack, p).unwrap();
                let p = p.clone();
                (Box::new(move |x: &[E]| eq_eval(&p, x)) as Box<dyn Fn(&[E]) -> E>, value)
            })
            .collect();
        let (p0, p1) = (points[0].clone(), points[1].clone());
        let two = multilinear_eval(&stack, &p0).unwrap() + multilinear_eval(&stack, &p1).unwrap();
        claims.push((Box::new(move |x: &[E]| eq_eval(&p0, x) + eq_eval(&p1, x)), two));

        let seed_bytes = keccak_seed(b"stack batch test", &[3; 32], &[4; 32]);
        let mut writer = KeccakWriter::new(seed_bytes);
        let lambda = writer.sample();
        let scales = powers(lambda, claims.len());
        let mut weight_table = vec![ZERO; 1 << n];
        for (j, p) in points.iter().enumerate() {
            for (w, e) in weight_table.iter_mut().zip(eq_kernel(p)) {
                *w += scales[j] * e;
            }
        }
        for (w, (e0, e1)) in weight_table.iter_mut().zip(eq_kernel(&points[0]).into_iter().zip(eq_kernel(&points[1]))) {
            *w += scales[3] * (e0 + e1);
        }
        let point = prove_product_sum(&mut writer, vec![stack.clone(), weight_table], n);
        let value = multilinear_eval(&stack, &point).unwrap();
        writer.send(value);

        let mut channel = KeccakChannel::new(seed_bytes, &writer.stream, Checks::Enforce);
        let (got, v) = batch_stack_claims(&mut channel, n, &claims).expect("the honest batch verifies");
        assert_eq!((got, v), (point, value));

        let mut stream = writer.stream.clone();
        let at = stream.len() - 24;
        stream[at..].copy_from_slice(&scalar_bytes(value + ONE));
        let mut channel = KeccakChannel::new(seed_bytes, &stream, Checks::Enforce);
        assert_eq!(
            batch_stack_claims(&mut channel, n, &claims).err(),
            Some(VerifierError::StackBatchTerminal)
        );
    }
}
