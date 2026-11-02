// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The batching sumcheck's prover (SPEC.md §8, the point-claim ABI; the verifier's `verifier::batch`):
//! `Σ_k λ^k Σ_u W_k(u) C_k(u) = Σ_k λ^k v_k` over the longest stack, the others zero-extended, two scalars a round
//! (`q(0)` and `q`'s `X^2` coefficient), then every stack's value at its part of the end point.
//!
//! Each commitment's combined claim is its weight on the stack, which the verifier's `weight_at` evaluates at the end
//! point. The rounds go low variable first: the first [`BASE_ROUNDS`] read the stacks' words and the weights' pieces
//! ([`Weight`]: eq tensors, one table per several-point column, the ring switch's one map), nothing of the stacks'
//! size written; then the folded stacks and weights are written out and folded on. Flock's matrices' reduction, when
//! pending, runs its rounds as the batch's first (SPEC.md §13, lever 4a).

use leanvm_flock_gas::field::E;
use leanvm_flock_gas::transcript::KeccakWriter;
use primitives::field::{F64, F192, F192Unreduced};

use super::poly::{from_v, to_v};
use super::weight::{Weight, fold, fold_stack};

/// The rounds that read the stacks' words, as [`Weight`] pieces; then every stack and its weight are written out
/// folded (`2^(vars - BASE_ROUNDS)` words each) and the rounds go on over the tables.
pub const BASE_ROUNDS: usize = 5;

/// A stack and its weight, written out once folded past the rounds that read the words.
struct Folded {
    w: Vec<F192>,
    c: Vec<F192>,
}

impl Folded {
    /// `(Σ w_0 c_0, Σ (w_0 + w_1)(c_0 + c_1))` over the pairs; one word is its own pair with zero.
    fn sums(&self) -> (F192, F192) {
        let (w, c) = (&self.w, &self.c);
        if w.len() == 1 {
            let x = w[0] * c[0];
            return (x, x);
        }
        let half = w.len() / 2;
        let chunk = 1usize << 12;
        let (a, b) = parallel::map_reduce(
            half.div_ceil(chunk),
            || (F192Unreduced::ZERO, F192Unreduced::ZERO),
            |t| {
                let (mut a, mut b) = (F192Unreduced::ZERO, F192Unreduced::ZERO);
                for i in t * chunk..((t + 1) * chunk).min(half) {
                    let (w0, w1, c0, c1) = (w[2 * i], w[2 * i + 1], c[2 * i], c[2 * i + 1]);
                    a ^= w0.mul_unreduced(c0);
                    b ^= (w0 + w1).mul_unreduced(c0 + c1);
                }
                (a, b)
            },
            |x, y| (x.0 ^ y.0, x.1 ^ y.1),
        );
        (a.reduce(), b.reduce())
    }

    /// Bind the low variable to `r`; one word is folded with its zero partner.
    fn fold(&mut self, r: F192) {
        if self.w.len() == 1 {
            self.w[0] *= F192::ONE + r;
            self.c[0] *= F192::ONE + r;
        } else {
            self.w = fold(&self.w, r);
            self.c = fold(&self.c, r);
        }
    }
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
    weights: Vec<Weight>,
    lambda: F192,
    pending: Option<&super::flock::Pending>,
) -> Result<(Vec<F192>, Vec<F192>, Option<(Vec<E>, E, E)>), String> {
    let vars = stacks.iter().map(|&(_, v)| v).max().expect("stacks");
    let shortest = stacks.iter().map(|&(_, v)| v).min().expect("stacks");
    let base_rounds = BASE_ROUNDS.min(shortest - 1);
    assert!(base_rounds <= super::weight::LOW_VARS);
    let scales: Vec<F192> = primitives::field::powers(lambda, stacks.len() + 1);
    let mut weights = weights;
    let mut folded: Vec<Folded> = Vec::new();
    // eq(r_(<j), ·) at the rounds' challenges so far, while the rounds read the words.
    let mut e = vec![F192::ONE];
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
        if round == base_rounds {
            folded = stacks
                .iter()
                .zip(&weights)
                .map(|(&(words, v), weight)| {
                    let len = 1 << (v - base_rounds);
                    Folded {
                        w: weight.dense(len),
                        c: fold_stack(words, &e, len),
                    }
                })
                .collect();
            weights = Vec::new();
        }
        let (mut q0, mut q2) = (F192::ZERO, F192::ZERO);
        for k in 0..stacks.len() {
            let (a, b) = if round < base_rounds {
                weights[k].round(stacks[k].0, &e)
            } else {
                folded[k].sums()
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
        if round < base_rounds {
            for weight in &mut weights {
                weight.fold(r);
            }
            e = e.iter().map(|&x| x * (F192::ONE + r)).chain(e.iter().map(|&x| x * r)).collect();
        } else {
            for (k, f) in folded.iter_mut().enumerate() {
                f.fold(r);
                if round + 1 == stacks[k].1 {
                    values[k] = f.c[0];
                }
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
