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
use super::weight::{Weight, fold, fold_stack, zeros};

/// The rounds that read the stacks' words, as [`Weight`] pieces; then every stack and its weight are written out
/// folded (`2^(vars - BASE_ROUNDS)` words each) and the rounds go on over the tables.
pub const BASE_ROUNDS: usize = 6;

/// Outputs per task of a fold.
const FOLD_CHUNK: usize = 1 << 12;

/// `(Σ w_0 c_0, Σ (w_0 + w_1)(c_0 + c_1))` over the pairs, unreduced.
fn pair_sums(w: &[F192], c: &[F192]) -> (F192Unreduced, F192Unreduced) {
    let (mut a, mut b) = (F192Unreduced::ZERO, F192Unreduced::ZERO);
    for (w, c) in w.as_chunks::<2>().0.iter().zip(c.as_chunks::<2>().0) {
        a ^= w[0].mul_unreduced(c[0]);
        b ^= (w[0] + w[1]).mul_unreduced(c[0] + c[1]);
    }
    (a, b)
}

/// A stack and its weight, written out once folded past the rounds that read the words: the tables (the first
/// `len` words of `w` and `c`), the buffers they fold into, and the next round's sums.
#[derive(Clone)]
struct Folded {
    w: Vec<F192>,
    c: Vec<F192>,
    len: usize,
    spare: (Vec<F192>, Vec<F192>),
    /// `(Σ w_0 c_0, Σ (w_0 + w_1)(c_0 + c_1))` over the pairs; one word is its own pair with zero.
    sums: (F192, F192),
}

impl Folded {
    fn new(w: Vec<F192>, c: Vec<F192>) -> Self {
        let len = w.len();
        let sums = if len == 1 {
            (w[0] * c[0], w[0] * c[0])
        } else {
            let (a, b) = parallel::map_reduce(
                len.div_ceil(2 * FOLD_CHUNK),
                || (F192Unreduced::ZERO, F192Unreduced::ZERO),
                |t| {
                    let range = 2 * FOLD_CHUNK * t..(2 * FOLD_CHUNK * (t + 1)).min(len);
                    pair_sums(&w[range.clone()], &c[range])
                },
                |x, y| (x.0 ^ y.0, x.1 ^ y.1),
            );
            (a.reduce(), b.reduce())
        };
        Self {
            w,
            c,
            len,
            spare: (Vec::new(), Vec::new()),
            sums,
        }
    }

    /// The sums [`Folded::fold`] at `r` would leave, without writing the folded tables (nor cloning these).
    fn sums_at(&self, r: F192) -> (F192, F192) {
        if self.len == 1 {
            let x = (self.w[0] * (F192::ONE + r)) * (self.c[0] * (F192::ONE + r));
            return (x, x);
        }
        let half = self.len / 2;
        let (w, c) = (&self.w[..self.len], &self.c[..self.len]);
        let at = |g: usize| (w[g] + r * (w[g] + w[g + 1]), c[g] + r * (c[g] + c[g + 1]));
        if half == 1 {
            let (wo, co) = at(0);
            let x = wo * co;
            return (x, x);
        }
        let (a, b) = parallel::map_reduce(
            half.div_ceil(FOLD_CHUNK),
            || (F192Unreduced::ZERO, F192Unreduced::ZERO),
            |k| {
                let (first, end) = (k * FOLD_CHUNK, ((k + 1) * FOLD_CHUNK).min(half));
                let (mut a, mut b) = (F192Unreduced::ZERO, F192Unreduced::ZERO);
                // The folded tables' pairs `(i, i + 1)` of this chunk, as `pair_sums` takes them.
                for i in (first..end).step_by(2).take((end - first) / 2) {
                    let ((w0, c0), (w1, c1)) = (at(2 * i), at(2 * i + 2));
                    a ^= w0.mul_unreduced(c0);
                    b ^= (w0 + w1).mul_unreduced(c0 + c1);
                }
                (a, b)
            },
            |x, y| (x.0 ^ y.0, x.1 ^ y.1),
        );
        (a.reduce(), b.reduce())
    }

    /// Bind the low variable to `r` (one word is folded with its zero partner), and take the next round's sums in
    /// the same pass.
    fn fold(&mut self, r: F192) {
        if self.len == 1 {
            self.w[0] *= F192::ONE + r;
            self.c[0] *= F192::ONE + r;
            let x = self.w[0] * self.c[0];
            self.sums = (x, x);
            return;
        }
        let half = self.len / 2;
        let (mut w_out, mut c_out) = std::mem::take(&mut self.spare);
        for out in [&mut w_out, &mut c_out] {
            if out.len() < half {
                *out = zeros(half);
            }
        }
        let (w, c) = (&self.w[..self.len], &self.c[..self.len]);
        let mut parts: Vec<_> = w_out[..half]
            .chunks_mut(FOLD_CHUNK)
            .zip(c_out[..half].chunks_mut(FOLD_CHUNK))
            .map(|(w, c)| (w, c, (F192Unreduced::ZERO, F192Unreduced::ZERO)))
            .collect();
        parallel::for_each_mut(&mut parts, |k, (w_out, c_out, sums)| {
            let first = k * FOLD_CHUNK;
            for (i, (wo, co)) in w_out.iter_mut().zip(c_out.iter_mut()).enumerate() {
                let g = 2 * (first + i);
                *wo = w[g] + r * (w[g] + w[g + 1]);
                *co = c[g] + r * (c[g] + c[g + 1]);
            }
            *sums = pair_sums(w_out, c_out);
        });
        self.sums = if half == 1 {
            (w_out[0] * c_out[0], w_out[0] * c_out[0])
        } else {
            let (a, b) = parts.iter().fold((F192Unreduced::ZERO, F192Unreduced::ZERO), |acc, p| {
                (acc.0 ^ p.2.0, acc.1 ^ p.2.1)
            });
            (a.reduce(), b.reduce())
        };
        self.spare = (
            std::mem::replace(&mut self.w, w_out),
            std::mem::replace(&mut self.c, c_out),
        );
        self.len = half;
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
    narrow: bool,
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
        return Err(format!(
            "the matrices' reduction has {rounds} variables, the batch {vars}"
        ));
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
                    Folded::new(weight.dense(len), fold_stack(words, &e, len))
                })
                .collect();
            weights = Vec::new();
        }
        let (mut q0, mut q2) = (F192::ZERO, F192::ZERO);
        for k in 0..stacks.len() {
            let (a, b) = if round < base_rounds {
                weights[k].round(stacks[k].0, &e)
            } else {
                folded[k].sums
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
        // π1-rec2's narrow challenges (`FsShape::Rec2`), as the verifier draws them.
        let r = from_v(if narrow { writer.sample_narrow() } else { writer.sample() });
        point.push(r);
        if round < base_rounds {
            for weight in &mut weights {
                weight.fold(r);
            }
            e = e
                .iter()
                .map(|&x| x * (F192::ONE + r))
                .chain(e.iter().map(|&x| x * r))
                .collect();
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

/// `e ⊗ (1 + r, r)`: the eq table of one more bound variable.
fn extend(e: &[F192], r: F192) -> Vec<F192> {
    e.iter().map(|&x| x * (F192::ONE + r)).chain(e.iter().map(|&x| x * r)).collect()
}

/// A polynomial's product with another (monomial coefficients, low first).
fn poly_mul(a: &[F192], b: &[F192]) -> Vec<F192> {
    let mut out = vec![F192::ZERO; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

/// π1-rec3's batching sumcheck (`crates/leanvm_rec/SPEC-POINTS.md`, the verifier's `transcript::sumcheck_pairs_drawn`
/// at degree 2, narrow challenges): as [`prove`] without the matrices' reduction, two variables a round. Pair `j`'s
/// polynomial is `G(X) = G̃(y_0(X), y_1(X))`, `G̃(u_0, u_1)` the sum with its two variables free (degree 2 in each),
/// `(y_0, y_1)` `V_2`'s coordinate functionals (`pair_point`): its stream holds `c_0, c_1, c_2, c_4 … c_8` (the claim
/// gives `c_3`). `G̃` comes from four rounds on the state as [`prove`] has it: the round on `u_0` (with the claim, all of
/// `h(u_0)`), and the round on `u_1` with `u_0` bound to `0`, `1` and `β_1` on clones, whose sums give `G̃(a, ·)` for
/// those `a` (`h(a)` its sum): then `G̃`'s coefficients in `u_0` by interpolation (`β_1² + β_1 = 1`, no inversion). With
/// `vars` odd the last variable is a plain round. Returns the point and each stack's value.
pub fn prove_pairs(
    writer: &mut KeccakWriter,
    stacks: &[(&[F64], usize)],
    weights: Vec<Weight>,
    lambda: F192,
    target: F192,
) -> Result<(Vec<F192>, Vec<F192>), String> {
    use leanvm_flock_gas::transcript::{cantor_beta1, pair_point};
    let vars = stacks.iter().map(|&(_, v)| v).max().expect("stacks");
    let shortest = stacks.iter().map(|&(_, v)| v).min().expect("stacks");
    // The rounds that read the words end on a pair's boundary.
    let base_rounds = BASE_ROUNDS.min(shortest - 1) & !1;
    if stacks.iter().any(|&(_, v)| v % 2 == 1 && v != vars) {
        return Err("a stack shorter than the batch ends inside a pair".into());
    }
    let scales: Vec<F192> = primitives::field::powers(lambda, stacks.len());
    let beta1 = from_v(cantor_beta1());
    let mut weights = weights;
    let mut folded: Vec<Folded> = Vec::new();
    let mut e = vec![F192::ONE];
    let mut values = vec![F192::ZERO; stacks.len()];
    let mut point = Vec::with_capacity(vars);
    let mut claim = target;
    // The combined sums `(c_0, c_2)` of the next variable, the state's, or its clone's with the low variable at `a`.
    let sums = |weights: &[Weight], folded: &[Folded], e: &[F192], at: Option<F192>| -> (F192, F192) {
        let (mut q0, mut q2) = (F192::ZERO, F192::ZERO);
        for k in 0..stacks.len() {
            let (a, b) = match (folded.is_empty(), at) {
                (true, None) => weights[k].round(stacks[k].0, e),
                (true, Some(x)) => {
                    let mut w = weights[k].clone();
                    w.fold(x);
                    w.round(stacks[k].0, &extend(e, x))
                }
                (false, None) => folded[k].sums,
                (false, Some(x)) => folded[k].sums_at(x),
            };
            q0 += scales[k] * a;
            q2 += scales[k] * b;
        }
        (q0, q2)
    };
    let mut round = 0;
    let prof = std::env::var("PI1_PROFILE").is_ok();
    if prof {
        eprintln!("    batch: stacks {:?}, base rounds {base_rounds}", stacks.iter().map(|s| (s.0.len(), s.1)).collect::<Vec<_>>());
    }
    let mut clock = std::time::Instant::now();
    let mut lap = |what: &str, round: usize| {
        if prof {
            eprintln!("    batch r{round}: {what} {:.4} s", clock.elapsed().as_secs_f64());
        }
        clock = std::time::Instant::now();
    };
    while round + 2 <= vars {
        if round == base_rounds {
            folded = stacks
                .iter()
                .zip(&weights)
                .map(|(&(words, v), weight)| {
                    let len = 1 << (v - base_rounds);
                    Folded::new(weight.dense(len), fold_stack(words, &e, len))
                })
                .collect();
            weights = Vec::new();
            lap("written out", round);
        }
        // While the rounds read the words: the plain round's sums and the three clones' in one read
        // (`Weight::round_pair`), when every weight's blocks allow it.
        let paired: Option<[(F192, F192); 4]> = if folded.is_empty() && std::env::var("PI1_NO_PAIR_ROUND").is_err() {
            stacks
                .iter()
                .zip(&weights)
                .map(|(&(words, _), w)| w.round_pair(words, &e, beta1))
                .collect::<Option<Vec<_>>>()
                .map(|per| {
                    std::array::from_fn(|s| {
                        per.iter().zip(&scales).fold((F192::ZERO, F192::ZERO), |acc, (p, &scale)| {
                            (acc.0 + scale * p[s].0, acc.1 + scale * p[s].1)
                        })
                    })
                })
        } else {
            None
        };
        if prof {
            eprintln!("    batch r{round}: paired {}", paired.is_some());
        }
        // h(u_0) = Σ G̃(u_0, ·): c_0 and c_2 from the round, c_1 from the claim (h(0) + h(1) = claim).
        let (a0, a2) = match paired {
            Some(p) => p[0],
            None => sums(&weights, &folded, &e, None),
        };
        lap("sums", round);
        let a1 = claim + a2;
        let h = |x: F192| a0 + a1 * x + a2 * x * x;
        // G̃(a, u_1) for a = 0, 1, β_1: (c_0, c_1, c_2) in u_1.
        let at = [F192::ZERO, F192::ONE, beta1];
        let g_at: Vec<[F192; 3]> = at
            .iter()
            .enumerate()
            .map(|(i, &a)| {
                let (b0, b2) = match paired {
                    Some(p) => p[1 + i],
                    None => sums(&weights, &folded, &e, Some(a)),
                };
                [b0, h(a) + b2, b2]
            })
            .collect();
        lap("three clones' sums", round);
        // G̃'s coefficient of u_1^j as a polynomial in u_0 of degree 2 through (0, v_0), (1, v_1), (β_1, v_b):
        // g_0 = v_0, g_2 = (v_0 + v_b) + β_1 (v_0 + v_1) (as β_1² + β_1 = 1), g_1 = v_0 + v_1 + g_2.
        let mut g = [[F192::ZERO; 3]; 3]; // g[i][j]: u_0^i u_1^j
        for j in 0..3 {
            let (v0, v1, vb) = (g_at[0][j], g_at[1][j], g_at[2][j]);
            let g2 = (v0 + vb) + beta1 * (v0 + v1);
            g[0][j] = v0;
            g[1][j] = v0 + v1 + g2;
            g[2][j] = g2;
        }
        // G(X) = Σ g_ij y_0(X)^i y_1(X)^j, y_1 = X + X², y_0 = X + β_1 y_1.
        let y1 = [F192::ZERO, F192::ONE, F192::ONE];
        let y0 = [F192::ZERO, F192::ONE + beta1, beta1];
        let p0 = [vec![F192::ONE], y0.to_vec(), poly_mul(&y0, &y0)];
        let p1 = [vec![F192::ONE], y1.to_vec(), poly_mul(&y1, &y1)];
        let mut c = vec![F192::ZERO; 9];
        for i in 0..3 {
            for j in 0..3 {
                for (d, &x) in poly_mul(&p0[i], &p1[j]).iter().enumerate() {
                    c[d] += g[i][j] * x;
                }
            }
        }
        if c[3] + c[6] != claim {
            return Err("a pair's polynomial does not sum to the claim over V_2".into());
        }
        for (d, &x) in c.iter().enumerate() {
            if d != 3 {
                writer.send(to_v(x));
            }
        }
        let z = writer.sample_narrow();
        let [u0, u1] = pair_point(z).map(from_v);
        let zf = from_v(z);
        claim = c.iter().rev().fold(F192::ZERO, |acc, &x| acc * zf + x);
        for (offset, r) in [(1, u0), (2, u1)] {
            point.push(r);
            if folded.is_empty() {
                for weight in &mut weights {
                    weight.fold(r);
                }
                e = extend(&e, r);
            } else {
                for (k, f) in folded.iter_mut().enumerate() {
                    f.fold(r);
                    if round + offset == stacks[k].1 {
                        values[k] = f.c[0];
                    }
                }
            }
        }
        lap("fold", round);
        round += 2;
    }
    if round < vars {
        // The last variable, a plain round (`transcript::sumcheck_drawn`'s, narrow).
        assert!(!folded.is_empty(), "past the rounds that read the words");
        let (q0, q2) = sums(&weights, &folded, &e, None);
        writer.send(to_v(q0));
        writer.send(to_v(q2));
        let r = from_v(writer.sample_narrow());
        point.push(r);
        for (k, f) in folded.iter_mut().enumerate() {
            f.fold(r);
            if round + 1 == stacks[k].1 {
                values[k] = f.c[0];
            }
        }
    }
    for &v in &values {
        writer.send(to_v(v));
    }
    Ok((point, values))
}
