// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The batching sumcheck's prover (SPEC.md §8, the point-claim ABI; the verifier's `verifier::batch`):
//! `Σ_k λ^k Σ_u W_k(u) C_k(u) = Σ_k λ^k v_k` over the longest stack, the others zero-extended, two scalars a round
//! (`q(0)` and `q`'s `X^2` coefficient), then every stack's value at its part of the end point.
//!
//! [`dense_weight`] writes a commitment's combined claim out as its weight on the stack, which is what the verifier's
//! `weight_at` evaluates at the end point; the rounds fold the weights and the stacks low variable first. Flock's
//! matrices' reduction, when pending, runs its rounds as the batch's first (SPEC.md §13, lever 4a).

use std::collections::BTreeMap;

use leanvm_flock_gas::field::E;
use leanvm_flock_gas::transcript::KeccakWriter;
use primitives::field::{F64, F192};
use primitives::multilinear::eq_table;

use super::poly::{from_v, to_v};
use crate::claims::{Column, Combined};
use crate::stacks::StackLayout;

/// `x ↦ Σ_k c_k x^(2^k)`, GF(2)-linear on `E`, as 24 byte tables: `L(x) = Σ_j T_j[byte_j(x)]`.
struct Linearised {
    tables: Vec<[F192; 256]>,
}

impl Linearised {
    fn new(twists: &[(u8, F192)]) -> Self {
        let image = |x: F192| {
            let mut power = x;
            let mut sum = F192::ZERO;
            let top = twists.iter().map(|&(k, _)| k).max().unwrap_or(0);
            for k in 0..=top {
                for &(t, c) in twists {
                    if t == k {
                        sum += c * power;
                    }
                }
                power = power.square();
            }
            sum
        };
        let mut tables = vec![[F192::ZERO; 256]; 24];
        for (j, table) in tables.iter_mut().enumerate() {
            let (limb, byte) = (j / 8, j % 8);
            let bits: Vec<F192> = (0..8)
                .map(|i| {
                    let mut c = [0u64; 3];
                    c[limb] = 1u64 << (8 * byte + i);
                    image(F192::new(c[0], c[1], c[2]))
                })
                .collect();
            for v in 1..256usize {
                let low = v.trailing_zeros() as usize;
                table[v] = table[v & (v - 1)] + bits[low];
            }
        }
        Self { tables }
    }

    #[inline]
    fn at(&self, x: F192) -> F192 {
        let mut acc = F192::ZERO;
        for (limb, word) in [x.c0, x.c1, x.c2].into_iter().enumerate() {
            for byte in 0..8 {
                acc += self.tables[8 * limb + byte][(word >> (8 * byte)) as usize & 0xff];
            }
        }
        acc
    }
}

/// A combined claim's weight on its stack, written out over `len` words. Terms are grouped by the eq table they read
/// (point and length): each table is built once, and dropped after its terms. Frobenius-twisted terms of one point on
/// one block (the ring switch's) read the same table, since on the cube `eq(φ^k(p), u) = eq(p, u)^(2^k)`: their sum
/// is one GF(2)-linear map of it ([`Linearised`]).
pub fn dense_weight(claim: &Combined<E>, layout: &StackLayout, len: usize) -> Vec<F192> {
    let mut weight = vec![F192::ZERO; len];
    let basis = [F192::ONE, F192::new(0, 1, 0), F192::new(0, 0, 1)];
    // (point, eq length) -> its uses: (block offset, q_flock slot) -> [(twist, scale)].
    type Uses = BTreeMap<(usize, Option<usize>), Vec<(u8, F192)>>;
    let mut groups: BTreeMap<(usize, usize), Uses> = BTreeMap::new();
    for &(column, p, twist, coefficient) in &claim.terms {
        let coefficient = from_v(coefficient);
        let (target, slot) = match column {
            Column::QflockSlot(j) => (Column::Qflock, Some(j)),
            other => (other, None),
        };
        for (limb, vars, offset) in layout.limbs(target) {
            let len = if slot.is_some() { vars - 8 } else { vars };
            groups
                .entry((p, len))
                .or_default()
                .entry((offset as usize, slot))
                .or_default()
                .push((twist, coefficient * basis[limb]));
        }
    }
    for ((p, len), uses) in groups {
        let point: Vec<F192> = claim.points[p][..len].iter().map(|&x| from_v(x)).collect();
        let eq = eq_table(&point);
        for ((offset, slot), twists) in uses {
            let plain = twists.iter().all(|&(k, _)| k == 0);
            let scale = twists.iter().fold(F192::ZERO, |acc, &(_, c)| acc + c);
            match slot {
                // q_flock's word `j + 256 u`: the slot's bits, then the point.
                Some(j) => {
                    assert!(plain, "no twisted slot terms");
                    for (u, &e) in eq.iter().enumerate() {
                        weight[offset + j + (u << 8)] += scale * e;
                    }
                }
                None => {
                    let block = &mut weight[offset..offset + eq.len()];
                    if plain {
                        parallel::chunks_mut_zip(block, &eq, 1 << 14, |_, out, eq| {
                            for (o, &e) in out.iter_mut().zip(eq) {
                                *o += scale * e;
                            }
                        });
                    } else {
                        let map = Linearised::new(&twists);
                        parallel::chunks_mut_zip(block, &eq, 1 << 14, |_, out, eq| {
                            for (o, &e) in out.iter_mut().zip(eq) {
                                *o += map.at(e);
                            }
                        });
                    }
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

/// `Σ_i Π_t tables[t][i]`'s round over the low variable: `q(0)` and the `X^2` coefficient of `q(X)`, whose `X^3`
/// coefficient must vanish (each variable of degree 2), for three tables.
fn product_round(tables: &[Vec<F192>; 3]) -> (F192, F192) {
    let half = tables[0].len() / 2;
    let (mut q0, mut q2, mut q3) = (F192::ZERO, F192::ZERO, F192::ZERO);
    for i in 0..half {
        let [(g0, dg), (l0, dl), (s0, ds)] = std::array::from_fn(|t| {
            let (lo, hi) = (tables[t][2 * i], tables[t][2 * i + 1]);
            (lo, lo + hi)
        });
        q0 += g0 * l0 * s0;
        q2 += g0 * dl * ds + dg * l0 * ds + dg * dl * s0;
        q3 += dg * dl * ds;
    }
    assert!(q3.is_zero(), "the matrices' sum has degree 2 in every variable");
    (q0, q2)
}

/// The batching sumcheck over `stacks` (each its words and variables) and their `weights`, with `λ`, written to
/// `writer`: returns the end point and each stack's value at its part of it.
///
/// With Flock's matrices' reduction `pending` (SPEC.md §13, lever 4a), its product sum `Σ G' L̂ ŝ` over the first
/// `k + 6` variables joins at the next power of `λ`, zero-extended by `eq(·, 0)` on the others: its tables fold in the
/// first rounds, then its value goes `(1 + X)` a round. After the stacks' values come `a`, `b`, its claims on `A0`,
/// `B0` at the point, returned with it.
pub fn prove(
    writer: &mut KeccakWriter,
    stacks: &[(&[F64], usize)],
    weights: Vec<Vec<F192>>,
    lambda: F192,
    pending: Option<&super::flock::Pending>,
) -> Result<(Vec<F192>, Vec<F192>, Option<(Vec<E>, E, E)>), String> {
    let vars = stacks.iter().map(|&(_, v)| v).max().expect("stacks");
    let scales: Vec<F192> = primitives::field::powers(lambda, stacks.len() + 1);
    let mut w = weights;
    let mut c: Vec<Vec<F192>> = vec![Vec::new(); stacks.len()];
    let mut values = vec![F192::ZERO; stacks.len()];
    let mut point = Vec::with_capacity(vars);
    let mut matrix_tables: Option<[Vec<F192>; 3]> =
        pending.map(|p| std::array::from_fn(|t| p.tables[t].iter().map(|&x| from_v(x)).collect()));
    let rounds = pending.map_or(0, |p| p.rounds());
    if rounds > vars {
        return Err(format!("the matrices' reduction has {rounds} variables, the batch {vars}"));
    }
    // Past its variables, the matrices' sum is its value times Π (1 + r_j).
    let mut matrix_value = F192::ZERO;
    let matrix_scale = scales[stacks.len()];
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
        if let Some(tables) = &matrix_tables {
            if round < rounds {
                let (a, b) = product_round(tables);
                q0 += matrix_scale * a;
                q2 += matrix_scale * b;
            } else {
                q0 += matrix_scale * matrix_value;
            }
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
        if let Some(tables) = &mut matrix_tables {
            if round < rounds {
                for table in tables.iter_mut() {
                    *table = fold(table, r);
                }
                if round + 1 == rounds {
                    matrix_value = tables[0][0] * tables[1][0] * tables[2][0];
                }
            } else {
                matrix_value *= F192::ONE + r;
            }
        }
    }
    for &v in &values {
        writer.send(to_v(v));
    }
    let matrices = match pending {
        Some(p) => {
            let at: Vec<E> = point.iter().map(|&x| to_v(x)).collect();
            let (claim_point, a, b) = p.claim(&at)?;
            writer.send(a);
            writer.send(b);
            Some((claim_point, a, b))
        }
        None => None,
    };
    Ok((point, values, matrices))
}
