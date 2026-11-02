// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The batching sumcheck's prover (SPEC.md §8, the point-claim ABI; the verifier's `verifier::batch`):
//! `Σ_k λ^k Σ_u W_k(u) C_k(u) = Σ_k λ^k v_k` over the longest stack, the others zero-extended, two scalars a round
//! (`q(0)` and `q`'s `X^2` coefficient), then every stack's value at its part of the end point.
//!
//! [`dense_weight`] writes a commitment's combined claim out as its weight on the stack, which is what the verifier's
//! `weight_at` evaluates at the end point; the rounds fold the weights and the stacks low variable first.

use std::collections::BTreeMap;

use leanvm_flock_gas::field::E;
use leanvm_flock_gas::transcript::KeccakWriter;
use primitives::field::{F64, F192};
use primitives::multilinear::eq_table;

use super::poly::{from_v, to_v};
use crate::claims::{Column, Combined};
use crate::stacks::StackLayout;

/// A combined claim's weight on its stack, written out over `len` words. Terms are grouped by the eq table they read
/// (point, length, twist): each table is built once, and dropped after its terms.
pub fn dense_weight(claim: &Combined<E>, layout: &StackLayout, len: usize) -> Vec<F192> {
    let mut weight = vec![F192::ZERO; len];
    let basis = [F192::ONE, F192::new(0, 1, 0), F192::new(0, 0, 1)];
    // (point, eq length, twist) -> its uses: (block offset, scale, q_flock slot).
    let mut groups: BTreeMap<(usize, usize, u8), Vec<(usize, F192, Option<usize>)>> = BTreeMap::new();
    for &(column, p, twist, coefficient) in &claim.terms {
        let coefficient = from_v(coefficient);
        let (target, slot) = match column {
            Column::QflockSlot(j) => (Column::Qflock, Some(j)),
            other => (other, None),
        };
        for (limb, vars, offset) in layout.limbs(target) {
            let len = if slot.is_some() { vars - 8 } else { vars };
            groups
                .entry((p, len, twist))
                .or_default()
                .push((offset as usize, coefficient * basis[limb], slot));
        }
    }
    for ((p, len, twist), uses) in groups {
        let twisted: Vec<F192> = claim.points[p][..len]
            .iter()
            .map(|&x| (0..twist).fold(from_v(x), |y, _| y.square()))
            .collect();
        let eq = eq_table(&twisted);
        for (offset, scale, slot) in uses {
            match slot {
                // q_flock's word `j + 256 u`: the slot's bits, then the point.
                Some(j) => {
                    for (u, &e) in eq.iter().enumerate() {
                        weight[offset + j + (u << 8)] += scale * e;
                    }
                }
                None => {
                    let block = &mut weight[offset..offset + eq.len()];
                    parallel::chunks_mut_zip(block, &eq, 1 << 14, |_, out, eq| {
                        for (o, &e) in out.iter_mut().zip(eq) {
                            *o += scale * e;
                        }
                    });
                }
            }
        }
    }
    weight
}

/// Sum and fold one round over a weight and an E-table: `(Σ w_0 c_0, Σ (w_0 + w_1)(c_0 + c_1))`, then both folded
/// at `r` (an odd tail's partner is zero).
fn round_sums(w: &[F192], c: &[F192]) -> (F192, F192) {
    let half = w.len().div_ceil(2);
    let at = |v: &[F192], i: usize| v.get(i).copied().unwrap_or(F192::ZERO);
    parallel::map_reduce(
        half.div_ceil(1 << 12),
        || (F192::ZERO, F192::ZERO),
        |chunk| {
            let (mut a, mut b) = (F192::ZERO, F192::ZERO);
            for i in chunk << 12..((chunk + 1) << 12).min(half) {
                let (w0, w1, c0, c1) = (at(w, 2 * i), at(w, 2 * i + 1), at(c, 2 * i), at(c, 2 * i + 1));
                a += w0 * c0;
                b += (w0 + w1) * (c0 + c1);
            }
            (a, b)
        },
        |x, y| (x.0 + y.0, x.1 + y.1),
    )
}

fn round_sums_k(w: &[F192], c: &[F64]) -> (F192, F192) {
    let half = w.len().div_ceil(2);
    parallel::map_reduce(
        half.div_ceil(1 << 12),
        || (F192::ZERO, F192::ZERO),
        |chunk| {
            let (mut a, mut b) = (F192::ZERO, F192::ZERO);
            for i in chunk << 12..((chunk + 1) << 12).min(half) {
                let (w0, w1) = (w[2 * i], w.get(2 * i + 1).copied().unwrap_or(F192::ZERO));
                let (c0, c1) = (c[2 * i], c.get(2 * i + 1).copied().unwrap_or(F64::ZERO));
                a += w0.mul_base(c0);
                b += (w0 + w1).mul_base(c0 + c1);
            }
            (a, b)
        },
        |x, y| (x.0 + y.0, x.1 + y.1),
    )
}

fn fold(v: &[F192], r: F192) -> Vec<F192> {
    let half = v.len().div_ceil(2);
    parallel::map_collect(half, |i| {
        let (a, b) = (v[2 * i], v.get(2 * i + 1).copied().unwrap_or(F192::ZERO));
        a + r * (a + b)
    })
}

fn fold_k(v: &[F64], r: F192) -> Vec<F192> {
    let half = v.len().div_ceil(2);
    parallel::map_collect(half, |i| {
        let (a, b) = (v[2 * i], v.get(2 * i + 1).copied().unwrap_or(F64::ZERO));
        F192::from(a) + r.mul_base(a + b)
    })
}

/// The batching sumcheck over `stacks` (each its words and variables) and their `weights`, with `λ`, written to
/// `writer`: returns the end point and each stack's value at its part of it.
pub fn prove(
    writer: &mut KeccakWriter,
    stacks: &[(&[F64], usize)],
    weights: Vec<Vec<F192>>,
    lambda: F192,
) -> (Vec<F192>, Vec<F192>) {
    let vars = stacks.iter().map(|&(_, v)| v).max().expect("stacks");
    let scales: Vec<F192> = primitives::field::powers(lambda, stacks.len());
    let mut w = weights;
    let mut c: Vec<Vec<F192>> = vec![Vec::new(); stacks.len()];
    let mut values = vec![F192::ZERO; stacks.len()];
    let mut point = Vec::with_capacity(vars);
    for round in 0..vars {
        let (mut q0, mut q2) = (F192::ZERO, F192::ZERO);
        for k in 0..stacks.len() {
            let (a, b) = if round == 0 {
                round_sums_k(&w[k], stacks[k].0)
            } else {
                round_sums(&w[k], &c[k])
            };
            q0 += scales[k] * a;
            q2 += scales[k] * b;
        }
        writer.send(to_v(q0));
        writer.send(to_v(q2));
        let r = from_v(writer.sample());
        point.push(r);
        for k in 0..stacks.len() {
            c[k] = if round == 0 { fold_k(stacks[k].0, r) } else { fold(&c[k], r) };
            w[k] = fold(&w[k], r);
            if round + 1 == stacks[k].1 {
                values[k] = c[k][0];
            }
        }
    }
    for &v in &values {
        writer.send(to_v(v));
    }
    (point, values)
}
