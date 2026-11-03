// Part of this repository. The quotient's computation on an extension coset, the tables' layouts and the openings
// follow crates/quotient/src/protocol.rs (`prove_with_randomness`, adapted there from leanVM's `flock::quotient`,
// branch PCS-openings-aggregation, commit 651453c6), without its hiding; the transforms are crates/quotient's
// (`ntt`, AVX-512), the commitments and openings leanVM's WHIR (c445e3d5) through `quotient::opening`. MIT OR
// Apache-2.0; see NOTICE.md.
//! π2's prover (`PI2.md` §3), for any [`Circuit`]:
//!
//! 1. `w`'s novel coefficients (one transform on `V_m`), then its `B` coefficients (subset sums): the table `W`,
//!    committed (`2^m` words);
//! 2. `α, β, γ`; the pushes `P` on `V_m`, and `h = [pull]/(α + w + βx) + 1/(α + P + βσ)` there (one batched inversion
//!    per run), whose sum is the public target; `h`'s novel coefficients;
//! 3. on the coset `D = β_{m+2} + V_{m+2}` (`4N` points, disjoint from `V_m`): `w`, `σ`, `κ`, `h` by transforms, the
//!    row's cells `w(x + ω_c)` (a coset of `V_r` stays in `D`), every pair's indicator (one batched inversion per
//!    point), `P`, `d_pull`, `d_push`, and `q = (h d_pull d_push + (1 + 1_S) d_push + d_pull) / Z_V`; `q`'s novel
//!    coefficients (degree below `4N`);
//! 4. the table `Q`: `h` (degree below `N`) and `q`'s four chunks, each of three limbs, `15 N` words, committed;
//! 5. `t`; the fold values, `σ(t)`, `κ(t)`, `h(t)`; `ρ`; the claims (the verifier's), opened: one opening per
//!    commitment, `Q`'s two claims together.

use std::time::Instant;

use fiat_shamir::merkle::Hash;
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::transcript::{KeccakWriter, keccak_seed};
use primitives::field::{F64, F192};
use quotient::domain::{beta, chain, point};
use quotient::ntt::{self, ESplat, Ex8, Kx8, MixedSum};
use quotient::opening::{self, Committed, Layout, Table};
use quotient::transcript::root_scalars;

use super::circuit::{Circuit, Formula, Lin, Read};
use super::verifier::{self, NAME, Reduced, Spec, claim, to_e, to_f192};

/// The smallest stack leanVM's WHIR takes.
pub const MIN_LOG_STACK: usize = 15;

/// The three tables' layouts (`quotient::opening::Layout`, public): `W` (`m` variables), `Q` (`m + 5`: the position,
/// `q`'s two chunk digits, `h` or `q`, two limb digits; 15 chunks of `2^m`), the setup (`m + 1`: `σ` then `κ`).
pub struct Layouts {
    pub witness: Layout,
    pub quotient: Layout,
    pub setup: Layout,
}

/// The chunks of `Q`, chunk `c = 8 limb + 4 kind + digit`: `h` (kind 0, digit 0) and `q`'s four chunks (kind 1).
pub fn quotient_chunks(log_n: usize) -> Vec<(usize, usize)> {
    let n = 1usize << log_n;
    let mut chunks = vec![];
    for limb in 0..3 {
        chunks.push((8 * limb, n));
        chunks.extend((0..4).map(|d| (8 * limb + 4 + d, n)));
    }
    chunks
}

/// The certified rate-1/2 query ladders (`review/whir_params.py --large`, leanerVM's `largeQueries`), by stack size:
/// what `pcs::whir::config_for_rate(log_n, 1)` must give for the stacks π2 commits (tested).
pub const CERTIFIED_QUERIES: [(usize, &[usize]); 5] = [
    (24, &[224, 56, 32, 23, 17]),
    (25, &[224, 56, 32, 23, 17]),
    (26, &[224, 56, 32, 23, 18]),
    (27, &[225, 56, 32, 23, 18]),
    (28, &[225, 56, 32, 23, 18, 14]),
];

/// The smallest stack leanerVM's certified parameters cover (`review/whir_params.py --large`): circuits of
/// `2^CERTIFIED_FROM` positions or more commit no smaller stack (D32v's `W`, `2^23` words, takes a `2^24` stack, half
/// its lanes absent); smaller circuits, the tests', take [`MIN_LOG_STACK`].
pub const MIN_CERTIFIED_STACK: usize = 24;
pub const CERTIFIED_FROM: usize = 20;

pub fn layouts(log_n: usize) -> Layouts {
    let (m, n) = (log_n, 1usize << log_n);
    let least = if m >= CERTIFIED_FROM { MIN_CERTIFIED_STACK } else { MIN_LOG_STACK };
    let stack = |vars: usize| vars.max(least);
    Layouts {
        witness: Layout::new(m, m, stack(m), &[(0, n)]),
        quotient: Layout::new(m + 5, m, stack(m + 4), &quotient_chunks(m)),
        setup: Layout::new(m + 1, m, stack(m + 1), &[(0, n), (1, n)]),
    }
}

/// The `B` coefficients from the novel ones (or back).
fn b_coefficients(novel: &[F64]) -> Vec<F64> {
    let mut b = novel.to_vec();
    ntt::subset_sums(&mut b);
    b
}

/// The setup: `σ` and `κ`, their novel coefficients (kept for the prover's extension coset) and the committed
/// table of their `B` coefficients.
pub struct Setup {
    pub sigma: Vec<F64>,
    pub kappa: Vec<F64>,
    pub table: Table,
    pub committed: Committed,
}

impl Setup {
    pub fn new(circuit: &Circuit) -> Self {
        let (m, n) = (circuit.log_n, circuit.n());
        let mut sigma: Vec<F64> = parallel::map_collect(n, |i| point(circuit.sigma[i] as usize));
        ntt::coefficients(&mut sigma, F64::ZERO);
        let mut kappa = circuit.kappa.clone();
        ntt::coefficients(&mut kappa, F64::ZERO);
        let (sb, kb) = (b_coefficients(&sigma), b_coefficients(&kappa));
        let layout = layouts(m).setup;
        let lane = 1usize << layout.log_lane();
        let table = Table::new(layout, |_, block, out| {
            let start = block * lane;
            let src = if start >> m == 0 { &sb } else { &kb };
            out.copy_from_slice(&src[start & (n - 1)..(start & (n - 1)) + lane]);
        });
        let committed = opening::commit(&table);
        Self {
            sigma,
            kappa,
            table,
            committed,
        }
    }

    pub fn root(&self) -> Hash {
        self.committed.root
    }
}

/// π2's IV: Keccak-256 of a tag, π1's contract IV, the setup root, the circuit's digest and the three layouts' ids.
pub fn iv(pi1_iv: &[u8; 32], circuit_digest: &[u8; 32], setup_root: &Hash, log_n: usize) -> [u8; 32] {
    let l = layouts(log_n);
    primitives::hash::hash(
        &[
            b"leanvm-rec-iv-v1".as_slice(),
            pi1_iv,
            setup_root,
            circuit_digest,
            &opening::layout_id(&l.witness),
            &opening::layout_id(&l.quotient),
            &opening::layout_id(&l.setup),
        ]
        .concat(),
    )
}

/// A public value as the stream carries it, one per [`Read`]: an integer, 32 bytes as they are (π1's roots, which
/// its `PCS_OPEN` calls take as words), an element of `E`.
#[derive(Clone, Copy, Debug)]
pub enum PublicValue {
    Integer(u64),
    Root([u8; 32]),
    Scalar(F192),
}

/// The two scalars `Channel::next_root` reads from 32 bytes: each 16-byte half big-endian, `c1` then `c0`.
pub fn halves(bytes: &[u8; 32]) -> [F192; 2] {
    let word = |at: usize| u64::from_be_bytes(bytes[at..at + 8].try_into().unwrap());
    [F192::new(word(8), word(0), 0), F192::new(word(24), word(16), 0)]
}

/// The public scalars: the public input's four words, then the values ([`Circuit::public_scalars`]).
pub fn public_scalars(public_input: &[u8; 32], values: &[PublicValue]) -> Vec<F192> {
    let mut out: Vec<F192> = verifier::statement_words(public_input).map(to_f192).to_vec();
    for v in values {
        match *v {
            PublicValue::Integer(x) => out.push(F192::new(x, 0, 0)),
            PublicValue::Root(bytes) => out.extend(halves(&bytes)),
            PublicValue::Scalar(x) => out.push(x),
        }
    }
    out
}

/// A proof: the stream (the calldata after the public input), the roots, and what the openings need.
pub struct Proved {
    pub stream: Vec<u8>,
    pub roots: [Hash; 2],
    pub witness: (Table, Committed),
    pub quotient: (Table, Committed),
    /// The verifier's reduction of the stream: its claims.
    pub reduced: Reduced<E>,
    /// Seconds per step.
    pub timings: Vec<(&'static str, f64)>,
}

fn batch_inverse_e(values: &mut [F192]) {
    let mut prefix = Vec::with_capacity(values.len());
    let mut acc = F192::ONE;
    for &v in values.iter() {
        prefix.push(acc);
        acc *= v;
    }
    let mut inverse = acc.inv();
    for (v, p) in values.iter_mut().zip(prefix).rev() {
        let next = inverse * *v;
        *v = inverse * p;
        inverse = next;
    }
}


/// A linear form in `K` on eight points, its cells' indices permuted by a role.
struct KLin {
    terms: Vec<(F64, usize)>,
    constant: F64,
}

impl KLin {
    fn new(l: &Lin, role: usize) -> Self {
        Self {
            terms: l.terms.iter().map(|&(c, cell)| (F64(c.value[0]), cell as usize ^ role)).collect(),
            constant: l.constant.map_or(F64::ZERO, |c| F64(c.value[0])),
        }
    }

    #[inline(always)]
    fn eval(&self, cells: &[Kx8]) -> Kx8 {
        self.terms.iter().fold(Kx8::splat(self.constant), |acc, &(c, i)| {
            acc + if c == F64::ONE { cells[i] } else { Kx8::splat(c) * cells[i] }
        })
    }
}

/// A group's formula on the extension coset: in `K` (every internal push), linear in `E` (a port's fingerprint, its
/// powers of `γ` evaluated), or any other formula of `E` (point by point).
enum Compiled {
    K {
        lin: KLin,
        products: Vec<(F64, KLin, KLin)>,
    },
    ELinear {
        terms: Vec<(ESplat, usize)>,
        constant: F192,
    },
    E {
        formula: Formula,
        role: usize,
    },
}

impl Compiled {
    fn new(f: &Formula, role: usize, gammas: &[F192]) -> Self {
        if f.is_base() {
            Compiled::K {
                lin: KLin::new(&f.lin, role),
                products: f
                    .products
                    .iter()
                    .map(|(c, a, b)| (F64(c.value[0]), KLin::new(a, role), KLin::new(b, role)))
                    .collect(),
            }
        } else if f.products.is_empty() {
            Compiled::ELinear {
                terms: f
                    .lin
                    .terms
                    .iter()
                    .map(|(c, cell)| (ESplat::new(c.eval(gammas)), *cell as usize ^ role))
                    .collect(),
                constant: f.lin.constant.map_or(F192::ZERO, |c| c.eval(gammas)),
            }
        } else {
            Compiled::E {
                formula: f.clone(),
                role,
            }
        }
    }
}

/// The lanes of eight elements.
fn lanes(x: Kx8) -> [F64; 8] {
    x.to_row().0
}

/// `q`'s values on `D = β_{m+2} + V_{m+2}`, limb by limb, eight consecutive points at a time (`quotient::ntt`'s
/// lanes: one AVX-512 carry-less product for eight).
#[allow(clippy::too_many_arguments)]
fn quotient_on_extension(
    circuit: &Circuit,
    spec: &Spec,
    setup: &Setup,
    w_novel: &[F64],
    h_novel: &[Vec<F64>; 3],
    [alpha, beta_, gamma]: [F192; 3],
) -> [Vec<F64>; 3] {
    let (m, r, n) = (circuit.log_n, circuit.log_row, circuit.n());
    let big = 4 * n;
    let offset = beta()[m + 2];
    let on_d = |novel: &[F64]| {
        let mut out = vec![F64::ZERO; big];
        out[..novel.len()].copy_from_slice(novel);
        ntt::values(&mut out, offset);
        out
    };
    let (wd, sd, kd) = (on_d(w_novel), on_d(&setup.sigma), on_d(&setup.kappa));
    let hd = [on_d(&h_novel[0]), on_d(&h_novel[1]), on_d(&h_novel[2])];
    let gammas = primitives::field::powers(gamma, spec.max_gamma + 1);

    // `Z_V` on `D`: `w_m(β_{m+2}) + ω_{i >> m}`, one value per coset of `V_m`, and its inverses.
    let zv_off = chain(offset, m + 1)[m];
    let zv: [F64; 4] = std::array::from_fn(|c| zv_off + point(c));
    let zv_inv = zv.map(|z| z.inv());

    // The normalised `Ẑ_s` on `D`, linear: at `β_{m+2}`, and on the low and high bits of the index.
    let s_max = spec.max_log_rows();
    let zhat = |x: F64, s: usize| (0..s).fold(x, |z, j| z + spec.c[j] * z.square());
    const LOW: usize = 12;
    let at_offset: Vec<F64> = (0..=s_max).map(|s| zhat(offset, s)).collect();
    let low: Vec<Vec<F64>> = (0..=s_max)
        .map(|s| (0..1usize << LOW).map(|j| zhat(point(j), s)).collect())
        .collect();
    let high: Vec<Vec<F64>> = (0..=s_max)
        .map(|s| (0..(big >> LOW).max(1)).map(|j| zhat(point(j << LOW), s)).collect())
        .collect();

    let pairs: Vec<(usize, Kx8)> = spec.pairs.iter().map(|p| (p.log_rows, Kx8::splat(p.z))).collect();
    let groups: Vec<(Compiled, &[usize])> = spec
        .groups
        .iter()
        .map(|g| (Compiled::new(&g.formula, g.role, &gammas), &g.pairs[..]))
        .collect();
    let pull_less = &spec.pull_less;
    let width = 1usize << r;
    let points8 = Kx8::new(std::array::from_fn(point));
    let (alpha8, beta8) = (Ex8::splat(alpha), Ex8::splat(beta_));
    let one8 = Kx8::splat(F64::ONE);

    let mut q = vec![F192::ZERO; big];
    let run = big.min(1 << LOW);
    parallel::chunks_mut(&mut q, run, |chunk, out| {
        let start = chunk * run;
        let mut dens = vec![one8; pairs.len()];
        let mut prefix = vec![one8; pairs.len()];
        let mut ind = vec![one8; pairs.len()];
        let mut zs = vec![one8; s_max + 1];
        let mut cells = vec![one8; width];
        for block in (0..out.len()).step_by(8) {
            let i = start + block;
            let coset = i >> m;
            for s in 0..=s_max {
                zs[s] = Kx8::load(&low[s][i & ((1 << LOW) - 1)..]) + Kx8::splat(at_offset[s] + high[s][i >> LOW]);
            }
            // The indicators: one batched inversion over the pairs, lane by lane.
            let mut acc = one8;
            for (p, &(s, z)) in pairs.iter().enumerate() {
                dens[p] = zs[s] + z;
                prefix[p] = acc;
                acc = acc * dens[p];
            }
            let mut inv = Kx8::new(lanes(acc).map(|x| x.inv())) * Kx8::splat(zv[coset]);
            for p in (0..pairs.len()).rev() {
                ind[p] = inv * prefix[p];
                inv = inv * dens[p];
            }
            // Lane `l` is the point `i + l`, its row's cell `c` the point `(i + l) ^ c`.
            for (c, cell) in cells.iter_mut().enumerate() {
                let (b, x) = ((i ^ c) & !7, c & 7);
                *cell = Kx8::new(std::array::from_fn(|l| wd[b + (l ^ x)]));
            }
            let w = cells[0];
            let mut selected = Kx8::splat(F64::ZERO);
            let mut pushed_k = Kx8::splat(F64::ZERO);
            let mut pushed_e = Ex8::splat(F192::ZERO);
            for (compiled, members) in &groups {
                let sum = members.iter().fold(Kx8::splat(F64::ZERO), |acc, &p| acc + ind[p]);
                selected = selected + sum;
                match compiled {
                    Compiled::K { lin, products } => {
                        let v = products.iter().fold(lin.eval(&cells), |acc, (c, a, b)| {
                            let p = a.eval(&cells) * b.eval(&cells);
                            acc + if *c == F64::ONE { p } else { Kx8::splat(*c) * p }
                        });
                        pushed_k = pushed_k + sum * v;
                    }
                    Compiled::ELinear { terms, constant } => {
                        let mut v = MixedSum::default();
                        terms.iter().for_each(|(c, cell)| v.add(c, cells[*cell]));
                        pushed_e = pushed_e + (v.reduce() + Ex8::splat(*constant)).mul_k(sum);
                    }
                    Compiled::E { formula, role } => {
                        let rows: Vec<[F64; 8]> = cells.iter().map(|&c| lanes(c)).collect();
                        let sums = lanes(sum);
                        let v: [F192; 8] = std::array::from_fn(|l| {
                            formula.eval(&|c| F192::from(rows[c ^ role][l]), &gammas).mul_base(sums[l])
                        });
                        let limb = |k: usize| Kx8::new(v.map(|x| F64([x.c0, x.c1, x.c2][k])));
                        pushed_e = pushed_e + Ex8::from_limbs([limb(0), limb(1), limb(2)]);
                    }
                }
            }
            let one_s = pull_less.iter().fold(Kx8::splat(F64::ZERO), |acc, &p| acc + ind[p]);
            let p_t = Ex8::from_k(w + w * selected + pushed_k + Kx8::load(&kd[i..])) + pushed_e;
            let x = Kx8::splat(offset + point(i)) + points8;
            let d_pull = alpha8 + Ex8::from_k(w) + beta8.mul_k(x);
            let d_push = alpha8 + p_t + beta8.mul_k(Kx8::load(&sd[i..]));
            let h = Ex8::from_limbs([Kx8::load(&hd[0][i..]), Kx8::load(&hd[1][i..]), Kx8::load(&hd[2][i..])]);
            let num = h * d_pull * d_push + d_push.mul_k(one8 + one_s) + d_pull;
            out[block..block + 8].copy_from_slice(&num.mul_k(Kx8::splat(zv_inv[coset])).to_array());
        }
    });
    drop((wd, sd, kd, hd));
    let limbs: [Vec<F64>; 3] = std::array::from_fn(|l| {
        let mut limb: Vec<F64> = parallel::map_collect(big, |i| F64([q[i].c0, q[i].c1, q[i].c2][l]));
        ntt::coefficients(&mut limb, offset);
        limb
    });
    limbs
}

/// Prove that `w` satisfies `circuit` with the public data `values` (the public input's words in the seed): the
/// stream, the committed tables and the claims. Panics if `w` does not (the public side's sum differs).
pub fn prove(
    circuit: &Circuit,
    spec: &Spec,
    setup: &Setup,
    iv: &[u8; 32],
    public_input: &[u8; 32],
    values: &[PublicValue],
    w: &[F64],
) -> Proved {
    prove_with(circuit, spec, setup, iv, public_input, values, w, true)
}

/// [`prove`], with `check` false for any `w`: the proof is then made as for a witness (for the tests that show a
/// claim is false).
#[allow(clippy::too_many_arguments)]
pub fn prove_with(
    circuit: &Circuit,
    spec: &Spec,
    setup: &Setup,
    iv: &[u8; 32],
    public_input: &[u8; 32],
    values: &[PublicValue],
    w: &[F64],
    check: bool,
) -> Proved {
    let (m, r, n) = (circuit.log_n, circuit.log_row, circuit.n());
    assert_eq!(w.len(), n);
    assert_eq!(values.len(), circuit.reads.len());
    let mut timings = vec![];
    let mut clock = Instant::now();
    let mut lap = |name: &'static str, timings: &mut Vec<(&'static str, f64)>| {
        timings.push((name, clock.elapsed().as_secs_f64()));
        clock = Instant::now();
    };
    let l = layouts(m);
    let mut writer = KeccakWriter::new(keccak_seed(&NAME, iv, public_input));
    for (read, value) in circuit.reads.iter().zip(values) {
        match (*read, *value) {
            (Read::Integer(bytes), PublicValue::Integer(x)) => writer.send_integer(x, bytes as usize),
            (Read::Root, PublicValue::Root(bytes)) => writer.send_root(halves(&bytes).map(to_e)),
            (Read::Scalar, PublicValue::Scalar(x)) => writer.send(to_e(x)),
            other => panic!("a public value of another kind than its read: {other:?}"),
        }
    }
    let public = public_scalars(public_input, values);

    // W: the B coefficients of w.
    let mut w_novel = w.to_vec();
    ntt::coefficients(&mut w_novel, F64::ZERO);
    let w_b = b_coefficients(&w_novel);
    let lane = 1usize << l.witness.log_lane();
    let witness = Table::new(l.witness, |_, block, out| {
        out.copy_from_slice(&w_b[block * lane..(block + 1) * lane])
    });
    let witness_committed = opening::commit(&witness);
    writer.send_root(root_scalars(&witness_committed.root).map(to_e));
    let [alpha, beta_, gamma] = [(); 3].map(|_| to_f192(writer.sample()));
    lap("W: transform, commit", &mut timings);

    // h on V_m.
    let pushes = circuit.pushes(w, gamma);
    let pulls = circuit.pulls();
    let mut h = vec![F192::ZERO; n];
    parallel::chunks_mut(&mut h, 1 << 12, |chunk, out| {
        let start = chunk << 12;
        let mut d: Vec<F192> = (0..out.len())
            .flat_map(|j| {
                let i = start + j;
                let pull = if pulls[i] {
                    alpha + F192::from(w[i]) + beta_.mul_base(point(i))
                } else {
                    F192::ONE
                };
                [pull, alpha + pushes[i] + beta_.mul_base(point(circuit.sigma[i] as usize))]
            })
            .collect();
        batch_inverse_e(&mut d);
        for (j, o) in out.iter_mut().enumerate() {
            *o = if pulls[start + j] { d[2 * j] } else { F192::ZERO } + d[2 * j + 1];
        }
    });
    drop(pushes);
    let run = n.min(1 << 12);
    let sum = parallel::map_reduce(
        n / run,
        || F192::ZERO,
        |c| h[c * run..(c + 1) * run].iter().fold(F192::ZERO, |a, &x| a + x),
        |a, b| a + b,
    );
    let mut target_dens: Vec<F192> = circuit
        .public_values(&public, gamma)
        .iter()
        .zip(&circuit.public)
        .map(|(&f, term)| alpha + f + beta_.mul_base(point(term.tag as usize)))
        .collect();
    batch_inverse_e(&mut target_dens);
    let target = target_dens.iter().fold(F192::ZERO, |a, &x| a + x);
    assert!(
        !check || sum == target,
        "the copy argument's sum is not the public target: the witness does not satisfy the circuit"
    );
    let h_novel: [Vec<F64>; 3] = std::array::from_fn(|limb| {
        let mut out: Vec<F64> = parallel::map_collect(n, |i| F64([h[i].c0, h[i].c1, h[i].c2][limb]));
        ntt::coefficients(&mut out, F64::ZERO);
        out
    });
    drop(h);
    lap("h on V_m, its coefficients", &mut timings);

    let q_novel = quotient_on_extension(circuit, spec, setup, &w_novel, &h_novel, [alpha, beta_, gamma]);
    lap("q on the extension coset, its coefficients", &mut timings);

    let qlane = 1usize << l.quotient.log_lane();
    let quotient = Table::new(l.quotient, |_, block, out| {
        let start = block * qlane;
        let (c, within) = (start >> m, start & (n - 1));
        let (limb, kind, digit) = (c >> 3, (c >> 2) & 1, c & 3);
        let src = if kind == 0 {
            assert_eq!(digit, 0);
            &h_novel[limb][within..within + qlane]
        } else {
            &q_novel[limb][digit * n + within..digit * n + within + qlane]
        };
        out.copy_from_slice(src);
    });
    drop(q_novel);
    let quotient_committed = opening::commit(&quotient);
    writer.send_root(root_scalars(&quotient_committed.root).map(to_e));
    let t = to_f192(writer.sample());
    lap("Q: table, commit", &mut timings);

    let digits: Vec<F192> = std::iter::successors(Some(t), |&x| Some(x * x + x)).take(m + 2).collect();
    let eq = primitives::multilinear::eq_table(&digits[r..m]);
    let width = 1usize << r;
    let folds = parallel::map_reduce(
        eq.len() >> 6.min(m - r),
        || vec![F192::ZERO; width],
        |c| {
            let run = 1usize << 6.min(m - r);
            let mut acc = vec![F192::ZERO; width];
            for j in c * run..(c + 1) * run {
                for k in 0..width {
                    acc[k] += eq[j].mul_base(w_b[(j << r) + k]);
                }
            }
            acc
        },
        |mut a, b| {
            a.iter_mut().zip(b).for_each(|(x, y)| *x += y);
            a
        },
    );
    let setup_stack = &setup.table.stack;
    let sigma_t = primitives::multilinear::mle_eval_par(&setup_stack[..n], &digits[..m]);
    let kappa_t = primitives::multilinear::mle_eval_par(&setup_stack[n..2 * n], &digits[..m]);
    let h_t = (0..3).rev().fold(F192::ZERO, |acc, limb| {
        acc * F192::Y + quotient::domain::evaluate(&h_novel[limb], 0, 1, &digits[..m])
    });
    folds.iter().chain([&sigma_t, &kappa_t, &h_t]).for_each(|&x| writer.send(to_e(x)));
    let _rho = writer.sample();
    lap("t: the values", &mut timings);

    let stream = writer.stream;
    let reduced = verifier::verify(spec, iv, public_input, &stream).expect("the verifier accepts its own stream");
    Proved {
        stream,
        roots: [witness_committed.root, quotient_committed.root],
        witness: (witness, witness_committed),
        quotient: (quotient, quotient_committed),
        reduced,
        timings,
    }
}

/// The three openings: `W`'s one claim, `Q`'s two, the setup's one.
pub struct Openings {
    pub witness: fiat_shamir::transcript::Proof,
    pub quotient: fiat_shamir::transcript::Proof,
    pub setup: fiat_shamir::transcript::Proof,
}

pub fn open(proved: Proved, setup: &Setup) -> (Reduced<E>, [Hash; 2], Openings) {
    let Proved {
        roots,
        witness,
        quotient,
        reduced,
        ..
    } = proved;
    let openings = Openings {
        witness: opening::open_owned(witness.0, witness.1, &[claim(&reduced.witness)]),
        quotient: opening::open_owned(quotient.0, quotient.1, &[claim(&reduced.quotient), claim(&reduced.sum)]),
        setup: opening::open(&setup.table, &setup.committed, &[claim(&reduced.setup)]),
    };
    (reduced, roots, openings)
}

/// What `PCS_OPEN` checks of π2's three calls: each opening against its root and layout, with `opening::verify`.
pub fn verify_openings(
    log_n: usize,
    reduced: &Reduced<E>,
    roots: &[Hash; 2],
    setup_root: &Hash,
    openings: &Openings,
) -> Result<(), ::verifier::VerifierError> {
    let l = layouts(log_n);
    use opening::{verify, wire_proof};
    verify(&l.witness, &roots[0], &[claim(&reduced.witness)], &wire_proof(&openings.witness))?;
    verify(
        &l.quotient,
        &roots[1],
        &[claim(&reduced.quotient), claim(&reduced.sum)],
        &wire_proof(&openings.quotient),
    )?;
    verify(&l.setup, setup_root, &[claim(&reduced.setup)], &wire_proof(&openings.setup))
}

/// Whether each claim holds on the tables (by evaluation): `W`, `Q`'s identity, `Q`'s sum, the setup.
pub fn claims_hold(proved: &Proved, setup: &Setup) -> [bool; 4] {
    let holds = |table: &Table, c: &(Vec<E>, E)| {
        let c = claim(c);
        table.eval(&c.point) == c.value
    };
    let r = &proved.reduced;
    [
        holds(&proved.witness.0, &r.witness),
        holds(&proved.quotient.0, &r.quotient),
        holds(&proved.quotient.0, &r.sum),
        holds(&setup.table, &r.setup),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    /// π2's stacks are committed and opened at the certified rate-1/2 parameters: `W` (`2^m`), `Q` (`2^(m+4)`), the
    /// setup (`2^(m+1)`), for D16v (`m = 24`) and D32v (`m = 23`), all within `2^24 … 2^28`.
    #[test]
    fn stacks_take_the_certified_queries() {
        assert_eq!(opening::LOG_INV_RATE, 1);
        for m in [23, 24] {
            let l = layouts(m);
            for layout in [&l.witness, &l.quotient, &l.setup] {
                let config = pcs::whir::config_for_rate(layout.log_n, opening::LOG_INV_RATE).expect("a WHIR shape");
                let certified = CERTIFIED_QUERIES.iter().find(|(n, _)| *n == layout.log_n).map(|(_, q)| *q);
                assert_eq!(Some(&config.queries[..]), certified, "2^{} words", layout.log_n);
            }
        }
    }
}
