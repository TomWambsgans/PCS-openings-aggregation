// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The second commitment's quotients (SPEC.md §5.2, §6), each computed on an extension coset `D_m` of its
//! numerator's domain: the numerator's values there over the vanishing polynomial's, interpolated back to novel
//! coefficients. A quotient whose numerator does not vanish on its domain is no polynomial of the declared degree:
//! [`Quotient::degree`] is the highest nonzero coefficient, which must be below the verifier's count.

use leanvm_flock_gas::layout::{OP_BLAKE2S, OP_JUMP, SEP_MEM, tables};
use leanvm_univariate_domain::{prefix_factors, suffix_factors};
use primitives::field::{F64, F192};

use super::bus::Bus;
use super::columns::{C1Polys, SetupPolys};
use super::poly::{novel_from_extension, omega, on_coset, subset_sums};
use super::trace::Trace;

/// The domain helpers the vanishing polynomials need, kept apart for the tests.
mod leanvm_univariate_domain {
    /// `[0, rows)` as aligned cosets `ω_a + V_b`: the factors `(b, a)` of `Z_act = Π (w_b + ω_a)`.
    pub fn prefix_factors(rows: u64) -> Vec<(usize, u64)> {
        let mut out = Vec::new();
        let mut start = 0u64;
        for b in (0..64).rev() {
            if rows >> b & 1 == 1 {
                out.push((b, start >> b));
                start += 1 << b;
            }
        }
        out
    }

    /// `[rows, 2^r)` likewise: the factors of `Z_pad` (`crate::domain::suffix_vanishing`).
    pub fn suffix_factors(rows: u64, r: usize) -> Vec<(usize, u64)> {
        let mut out = Vec::new();
        let mut start = rows;
        while start < 1 << r {
            let mut b = (start.trailing_zeros() as usize).min(r);
            while start + (1 << b) > 1 << r {
                b -= 1;
            }
            out.push((b, start >> b));
            start += 1 << b;
        }
        out
    }
}

/// A quotient's novel coefficients on `D_m`, the count the verifier declares, and its actual degree.
pub struct Quotient {
    pub novel: Vec<F192>,
    pub count: u64,
    /// The highest nonzero coefficient, `-1` for zero.
    pub degree: i64,
}

impl Quotient {
    fn finish(mut values: Vec<F192>, m: usize, count: u64) -> Self {
        novel_from_extension(&mut values, m);
        let degree = values.iter().rposition(|x| !x.is_zero()).map_or(-1, |d| d as i64);
        Self {
            novel: values,
            count,
            degree,
        }
    }

    /// Whether its degree is below the verifier's count.
    pub fn fits(&self) -> bool {
        self.degree < self.count as i64
    }

    /// Its chunks `Q = Q_0 + w_(e_0) (Q_1 + w_(e_1) Q_2)` as `B` coefficients: the novel coefficients' slices (since
    /// `X_(2^e + k) = w_e X_k` for `k < 2^e`), each in basis `B`.
    pub fn chunks_b(&self, sizes: &[usize]) -> Vec<Vec<F192>> {
        let mut at = 0usize;
        let mut out = Vec::new();
        for &e in sizes {
            let mut chunk = vec![F192::ZERO; 1 << e];
            let end = (at + (1 << e)).min(self.novel.len());
            if at < end {
                chunk[..end - at].copy_from_slice(&self.novel[at..end]);
            }
            subset_sums(&mut chunk);
            out.push(chunk);
            at += 1 << e;
        }
        assert!(
            self.novel[at.min(self.novel.len())..].iter().all(|x| x.is_zero()),
            "the chunks hold the whole quotient"
        );
        out
    }
}

/// The extension's variables: at least the domain's, and enough for `count` coefficients.
pub fn extension_vars(count: u64, r: usize) -> usize {
    let need = 64 - count.max(1).saturating_sub(1).leading_zeros() as usize;
    r.max(need)
}

/// `ω_i` for `i < 2^r`.
fn points(r: usize) -> Vec<F64> {
    parallel::map_collect(1 << r, omega)
}

/// The product of factors `(b, a)`, `w_b(x) + ω_a`, at `x = ω_(first + i)` for every `i < 2^r` (`2^r | first`).
fn vanishing_on(factors: &[(usize, u64)], first: usize, r: usize, pts: &[F64]) -> Vec<F64> {
    let constants: Vec<(usize, F64)> = factors
        .iter()
        .map(|&(b, a)| (b, omega(first >> b) + omega(a as usize)))
        .collect();
    parallel::map_collect(1 << r, |i| {
        constants.iter().fold(F64::ONE, |acc, &(b, c)| acc * (c + pts[i >> b]))
    })
}

/// Table `t`'s leaf quotient: `((R P + P') Z_pad + (R + 1) Z_act) / w_r`, `R` the heap's block (its novel
/// coefficients `r_novel`), `P`, `P'` the row's pull and push products.
pub fn table_leaf(trace: &Trace, t: usize, c1: &C1Polys, bus: &Bus, r_novel: &[F192], count: u64) -> Quotient {
    let r = trace.heights[t];
    let n = 1usize << r;
    let rows = trace.rows[t];
    let m = extension_vars(count, r);
    let (pull, push) = (&bus.pull[t], &bus.push[t]);
    let mut used: Vec<usize> = pull.iter().chain(push).flat_map(|f| f.columns()).collect();
    used.sort_unstable();
    used.dedup();
    let pts = points(r);
    let (act, pad) = (prefix_factors(rows), suffix_factors(rows, r));
    let width = c1.tables[t].len();
    let mut q = vec![F192::ZERO; 1 << m];
    for (j, out) in q.chunks_exact_mut(n).enumerate() {
        let first = (1 << m) + j * n;
        let mut values: Vec<Vec<F64>> = vec![Vec::new(); width];
        for &c in &used {
            values[c] = on_coset(&c1.tables[t][c].novel, first);
        }
        let heap = on_coset(r_novel, first);
        let z_act = vanishing_on(&act, first, r, &pts);
        let z_pad = vanishing_on(&pad, first, r, &pts);
        let w_r_inv = F192::from(omega(first >> r).inv());
        // A block of points at a time, a fingerprint at a time: each term one pass over a column's block.
        const BLOCK: usize = 1 << 10;
        parallel::chunks_mut(out, BLOCK, |b, slots| {
            let base = b * BLOCK;
            let len = slots.len();
            let product = |prints: &[super::fingerprint::Fingerprint]| {
                let mut acc = vec![F192::ONE; len];
                let mut value = vec![F192::ZERO; len];
                for f in prints {
                    value.fill(f.constant);
                    for &(c, k) in &f.linear {
                        let col = &values[c][base..base + len];
                        for (v, &x) in value.iter_mut().zip(col) {
                            *v += k.mul_base(x);
                        }
                    }
                    for &(c, d, k) in &f.quadratic {
                        let (u, w) = (&values[c][base..base + len], &values[d][base..base + len]);
                        for ((v, &x), &y) in value.iter_mut().zip(u).zip(w) {
                            *v += k.mul_base(x * y);
                        }
                    }
                    for (a, &v) in acc.iter_mut().zip(&value) {
                        *a *= v;
                    }
                }
                acc
            };
            let (p, p2) = (product(pull), product(push));
            for (k, slot) in slots.iter_mut().enumerate() {
                let i = base + k;
                let (za, zp) = (F192::from(z_act[i]), z_pad[i]);
                let numerator = heap[i] * (p[k].mul_base(zp) + za) + p2[k].mul_base(zp) + za;
                *slot = numerator * w_r_inv;
            }
        });
    }
    Quotient::finish(q, m, count)
}

/// The memory's leaf quotient: `(R D_fin + D_init) / w_lm`.
pub fn memory_leaf(trace: &Trace, c1: &C1Polys, setup: &SetupPolys, bus: &Bus, r_novel: &[F192], count: u64) -> Quotient {
    let r = trace.log_memory;
    let n = 1usize << r;
    let m = extension_vars(count, r);
    let mut q = vec![F192::ZERO; 1 << m];
    for (j, out) in q.chunks_exact_mut(n).enumerate() {
        let first = (1 << m) + j * n;
        let limbs: Vec<Vec<F64>> = c1.memory.iter().map(|c| on_coset(&c.novel, first)).collect();
        let address = on_coset(&setup.address.novel, first);
        let heap = on_coset(r_novel, first);
        let w_r_inv = F192::from(omega(first >> r).inv());
        parallel::for_each_mut(out, |i, slot| {
            let three = [limbs[0][i], limbs[1][i], limbs[2][i]];
            let fin = bus.memory(address[i], limbs[3][i], three);
            let init = bus.memory(address[i], F64::ONE, three);
            *slot = (heap[i] * fin + init) * w_r_inv;
        });
    }
    let _ = SEP_MEM;
    Quotient::finish(q, m, count)
}

/// The bytecode's leaf quotient: `(R D_fin + D_init) / w_lb`, the tuple's slots from the setup.
pub fn bytecode_leaf(trace: &Trace, c1: &C1Polys, setup: &SetupPolys, bus: &Bus, r_novel: &[F192], count: u64) -> Quotient {
    let r = trace.log_bytecode;
    let n = 1usize << r;
    let m = extension_vars(count, r);
    let mut q = vec![F192::ZERO; 1 << m];
    for (j, out) in q.chunks_exact_mut(n).enumerate() {
        let first = (1 << m) + j * n;
        let slots: Vec<Vec<F64>> = setup.slots.iter().map(|c| on_coset(&c.novel, first)).collect();
        let count_values = on_coset(&c1.bytecode_final.novel, first);
        let heap = on_coset(r_novel, first);
        let w_r_inv = F192::from(omega(first >> r).inv());
        parallel::for_each_mut(out, |i, slot| {
            let fin = bus.bytecode(|s| if s == 2 { count_values[i] } else { slots[s][i] });
            let init = bus.bytecode(|s| if s == 2 { F64::ONE } else { slots[s][i] });
            *slot = (heap[i] * fin + init) * w_r_inv;
        });
    }
    Quotient::finish(q, m, count)
}

/// The tree quotient: `w_1 (T(s(x)) + T(x) T(x + 1)) / w_H`, of `2^H + 1` coefficients.
pub fn tree(heap_novel: &[F192]) -> Quotient {
    let h = heap_novel.len().trailing_zeros() as usize;
    let m = h + 1;
    let n = 1usize << h;
    // T on D_m's two halves, and T at s(D_m) = ω_(2^h) + V_h.
    let halves: Vec<Vec<F192>> = (0..2).map(|j| on_coset(heap_novel, (1 << m) + j * n)).collect();
    let at_s = on_coset(heap_novel, n);
    let pts = points(h);
    let mut q = vec![F192::ZERO; 1 << m];
    for (j, out) in q.chunks_exact_mut(n).enumerate() {
        let first = (1 << m) + j * n;
        let values = &halves[j];
        let w_h_inv = F192::from(omega(first >> h).inv());
        // x = ω_(first + i): s(x) = ω_(2^h + (first - 2^m + i) / 2), x + 1 = ω_(first + (i ^ 1)), w_1(x) = ω_((first + i) >> 1).
        let base_s = (first - (1 << m)) / 2;
        let w1_high = omega(first >> 1);
        parallel::for_each_mut(out, |i, slot| {
            let t_s = at_s[base_s + (i >> 1)];
            let w1 = w1_high + pts[i >> 1];
            let numerator = (t_s + values[i] * values[i ^ 1]).mul_base(w1);
            *slot = numerator * w_h_inv;
        });
    }
    Quotient::finish(q, m, n as u64 + 1)
}

/// The constraint quotient `Σ_i γ^i M_i W_i / w_(r_W)`, in the verifier's order of powers: per table, JUMP's two
/// constraints, the counters, BLAKE2S's eighteen limb copies; then the public input's three limbs.
pub fn constraints(
    trace: &Trace,
    c1: &C1Polys,
    gamma: F192,
    r_w: usize,
    count: u64,
    public_lines: [(F64, F64); 3],
) -> Quotient {
    let m = extension_vars(count, r_w);
    let size = 1usize << m;
    let mut acc = vec![F192::ZERO; size];
    let mut power = F192::ONE;
    let mut next = || {
        let current = power;
        power *= gamma;
        current
    };
    let layout = tables();
    for table in &layout {
        let t = table.opcode;
        let r = trace.heights[t];
        let n = 1usize << r;
        let rows = trace.rows[t];
        let pts = points(r);
        let pad = suffix_factors(rows, r);
        let cols = &c1.tables[t];
        let index = |name: &str| table.columns.iter().position(|&c| c == name).expect("a column");
        let jump = (t == OP_JUMP).then(|| (next(), next(), index("v_cond"), index("w"), index("b")));
        let counters: Vec<usize> = table.count_columns().collect();
        let g_counter = next();
        let copies: Vec<(F192, usize, usize)> = if t == OP_BLAKE2S {
            table
                .columns
                .iter()
                .enumerate()
                .filter_map(|(c, &name)| {
                    leanvm_flock_gas::layout::BLAKE2S_SLOTS
                        .iter()
                        .position(|&s| s == Some(name))
                        .map(|slot| (next(), c, slot))
                })
                .collect()
        } else {
            Vec::new()
        };
        // The q_flock slots as tables of the BLAKE2S rows.
        let slot_values: Vec<Vec<F64>> = copies
            .iter()
            .map(|&(_, _, slot)| (0..n).map(|i| trace.qflock[(i << 8) | slot]).collect())
            .collect();
        let functionals = (!copies.is_empty()).then(|| crate::domain::coordinate_functionals(r));
        for (j, out) in acc.chunks_exact_mut(n).enumerate() {
            let first = (1 << m) + j * n;
            // w_(r_W) / w_r is constant on the coset.
            let lift = F192::from(omega(first >> r_w) * omega(first >> r).inv());
            let z_pad = vanishing_on(&pad, first, r, &pts);
            let value = |c: usize| on_coset(&cols[c].novel, first);
            let counter_values: Vec<Vec<F64>> = counters.iter().map(|&c| value(c)).collect();
            let inverse = on_coset(&c1.inverses[t].novel, first);
            let jump_values = jump.map(|(_, _, cond, w, b)| (value(cond), value(w), value(b)));
            // ℓ_j on the coset: the slot's multilinear at y(x) = y(ω_first) + bits(i), a shifted cube.
            let shifted: Vec<(F192, Vec<F64>, Vec<F64>)> = copies
                .iter()
                .zip(&slot_values)
                .map(|(&(g, c, _), v)| {
                    let functionals = functionals.as_ref().expect("BLAKE2S");
                    let delta = coordinates_k(omega(first), functionals);
                    (g, value(c), shifted_cube(v, &delta))
                })
                .collect();
            parallel::for_each_mut(out, |i, slot| {
                let mut sum = F192::ZERO;
                if let (Some((g1, g2, ..)), Some((cond, w, b))) = (jump, &jump_values) {
                    sum += g1.mul_base(b[i] + cond[i] * w[i]);
                    sum += g2.mul_base(cond[i] * (b[i] + F64::ONE));
                }
                let product = counter_values.iter().fold(inverse[i], |acc, c| acc * c[i]);
                sum += g_counter.mul_base((product + F64::ONE) * z_pad[i]);
                for (g, copy, composed) in &shifted {
                    sum += g.mul_base(copy[i] + composed[i]);
                }
                *slot += sum * lift;
            });
        }
    }
    // The public input: (mem_k + I_k) w_(r_W) / w_1, I_k(x) = low + x (low + high).
    let lm = trace.log_memory;
    let n = 1usize << lm;
    let pts = points(lm);
    let gs: Vec<F192> = (0..3).map(|_| next()).collect();
    for (j, out) in acc.chunks_exact_mut(n).enumerate() {
        let first = (1 << m) + j * n;
        let limbs: Vec<Vec<F64>> = (0..3).map(|k| on_coset(&c1.memory[k].novel, first)).collect();
        let highs: Vec<F64> = (0..64).map(|b| omega(first >> b.min(63))).collect();
        parallel::for_each_mut(out, |i, slot| {
            let x = omega(first) + pts[i];
            // w_(r_W)(x) / w_1(x) = Π_{j=1}^{r_W - 1} (w_j(x) + 1), w_j(x) = ω_(first >> j) + ω_(i >> j).
            let lift = (1..r_w).fold(F64::ONE, |acc, b| {
                let wb = if b < lm { highs[b] + pts[i >> b] } else { omega((first + i) >> b) };
                acc * (wb + F64::ONE)
            });
            let mut sum = F192::ZERO;
            for (k, &(low, high)) in public_lines.iter().enumerate() {
                let line = low + x * (low + high);
                sum += gs[k].mul_base(limbs[k][i] + line);
            }
            *slot += sum.mul_base(lift);
        });
    }
    // Divide by w_(r_W): ω_((2^m + i) >> r_W).
    let mut inverses: Vec<F64> = parallel::map_collect(size >> r_w, |k| omega(((1 << m) >> r_w) + k).inv());
    if inverses.is_empty() {
        inverses.push(F64::ONE);
    }
    parallel::for_each_mut(&mut acc, |i, slot| *slot = slot.mul_base(inverses[i >> r_w]));
    Quotient::finish(acc, m, count)
}

/// `y_l(x)` for a K point: `Σ_m a_(l,m) x^(2^m)`.
pub fn coordinates_k(x: F64, functionals: &[Vec<leanvm_flock_gas::K>]) -> Vec<F64> {
    let r = functionals.len();
    let frobenius: Vec<F64> = std::iter::successors(Some(x), |&y| Some(y.square())).take(r).collect();
    functionals
        .iter()
        .map(|row| row.iter().zip(&frobenius).fold(F64::ZERO, |acc, (a, &f)| acc + F64(a.0) * f))
        .collect()
}

/// `ṽ(bits(i) + δ)` for every `i < 2^r`: per variable, `(v_0, v_1) ↦ (v_0 + δ (v_0 + v_1), v_1 + δ (v_0 + v_1))`.
pub fn shifted_cube(values: &[F64], delta: &[F64]) -> Vec<F64> {
    let mut v = values.to_vec();
    for (l, &d) in delta.iter().enumerate() {
        let half = 1usize << l;
        parallel::chunks_mut(&mut v, (2 * half).max(1 << 12), |_, chunk| {
            for pair in chunk.chunks_exact_mut(2 * half) {
                let (lo, hi) = pair.split_at_mut(half);
                for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                    let t = d * (*a + *b);
                    *a += t;
                    *b += t;
                }
            }
        });
    }
    v
}
