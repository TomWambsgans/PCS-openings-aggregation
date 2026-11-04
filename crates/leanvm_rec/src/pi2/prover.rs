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
//! 5. `t`; the fold values and `ξ = κ(t) + β σ(t)` (PI2.md §9); `ρ`; the claims (the verifier's), opened: one opening per
//!    commitment, `Q`'s two claims together.

use std::time::Instant;

use fiat_shamir::merkle::Hash;
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::transcript::{KeccakWriter, keccak_seed};
use primitives::field::{F64, F192};
use quotient::domain::{beta, chain, point};
use quotient::ntt::{self, ESplat, Ex8, Kx8, Kx8U, MixedSum};
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
    let least = if m >= CERTIFIED_FROM {
        MIN_CERTIFIED_STACK
    } else {
        MIN_LOG_STACK
    };
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

/// The setup: `σ` and `κ` on the prover's extension coset `D = β_{m+2} + V_{m+2}` (fixed by the circuit, so computed
/// once here, not per proof), and the committed table of their `B` coefficients.
pub struct Setup {
    pub sigma_on_d: Vec<F64>,
    pub kappa_on_d: Vec<F64>,
    pub table: Table,
    pub committed: Committed,
}

impl Setup {
    /// The setup of `circuit`, which must be valid ([`Circuit::validate`], REVIEW-REC.md L1).
    pub fn new(circuit: &Circuit) -> Self {
        circuit.validate().unwrap_or_else(|e| panic!("the circuit is not valid: {e}"));
        let (m, n) = (circuit.log_n, circuit.n());
        let mut sigma: Vec<F64> = parallel::map_collect(n, |i| point(circuit.sigma[i] as usize));
        ntt::coefficients(&mut sigma, F64::ZERO);
        let mut kappa = circuit.kappa.clone();
        ntt::coefficients(&mut kappa, F64::ZERO);
        // The halves `κ` and `κ + σ` (PI2.md §9): the claim at the last coordinate `β` is `κ(t) + β σ(t)`, the one value
        // `d_push` needs.
        let (sb, kb) = (b_coefficients(&sigma), b_coefficients(&kappa));
        let skb: Vec<F64> = sb.iter().zip(&kb).map(|(&a, &b)| a + b).collect();
        drop(sb);
        let layout = layouts(m).setup;
        let lane = 1usize << layout.log_lane();
        let table = Table::new(layout, |_, block, out| {
            let start = block * lane;
            let src = if start >> m == 0 { &kb } else { &skb };
            out.copy_from_slice(&src[start & (n - 1)..(start & (n - 1)) + lane]);
        });
        let committed = opening::commit(&table);
        drop((kb, skb));
        let offset = beta()[m + 2];
        Self {
            sigma_on_d: on_extension(&sigma, m, offset),
            kappa_on_d: on_extension(&kappa, m, offset),
            table,
            committed,
        }
    }

    pub fn root(&self) -> Hash {
        self.committed.root
    }
}

/// The codes of π2's tables in their `PCS_OPEN` layout words (π1's are `0x5501` … `0x5505`).
pub const WITNESS_CODE: u16 = 0x5601;
pub const QUOTIENT_CODE: u16 = 0x5602;
pub const SETUP_CODE: u16 = 0x5603;

/// A `PCS_OPEN` layout word of π2's tables (REVIEW-REC.md M1), in π1's format (`leanvm_univariate::contract::
/// layout_word`): bytes 0..8 the tag `"pi2"` then `log_n` (π1's are its shape's bytes, each below 32), the table's
/// code (bytes 22..24), its variables (byte 24) and the words its lanes fill (`placed`, bytes 25..32). A precompile's
/// registry maps it to the layout (`quotient::opening::Layout`, a function of `log_n` and the code: [`layouts`]),
/// whose opening it checks (`quotient::opening::verify`, whose transcript hashes that layout's id).
pub fn layout_word(code: u16, log_n: usize, layout: &Layout) -> [u8; 32] {
    assert!(layout.vars < 256 && layout.placed() < 1 << 56 && log_n < 256);
    let mut word = [0u8; 32];
    word[..4].copy_from_slice(b"pi2\0");
    word[4] = log_n as u8;
    word[22..24].copy_from_slice(&code.to_be_bytes());
    word[24] = layout.vars as u8;
    word[25..].copy_from_slice(&(layout.placed() as u64).to_be_bytes()[1..]);
    word
}

/// The three tables' layout words: `W`, `Q`, the setup.
pub fn layout_words(log_n: usize) -> [[u8; 32]; 3] {
    let l = layouts(log_n);
    [
        layout_word(WITNESS_CODE, log_n, &l.witness),
        layout_word(QUOTIENT_CODE, log_n, &l.quotient),
        layout_word(SETUP_CODE, log_n, &l.setup),
    ]
}

/// π2's IV: Keccak-256 of a tag, π1's contract IV, the setup root, the circuit's digest and the three layout words.
pub fn iv(pi1_iv: &[u8; 32], circuit_digest: &[u8; 32], setup_root: &Hash, log_n: usize) -> [u8; 32] {
    let [w, q, s] = layout_words(log_n);
    primitives::hash::hash(
        &[
            b"leanvm-rec-iv-v2".as_slice(),
            pi1_iv,
            setup_root,
            circuit_digest,
            &w,
            &q,
            &s,
        ]
        .concat(),
    )
}

/// A public value as the stream carries it, one per [`Read`]: an integer, 32 bytes as they are (π1's roots as
/// `PCS_OPEN`'s root words, which its calls take as they are), an element of `E`.
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
    /// The cells of coefficient 1, and the others with theirs (summed unreduced, one reduction).
    ones: Vec<usize>,
    scaled: Vec<(Kx8, usize)>,
    constant: F64,
}

impl KLin {
    fn new(l: &Lin, role: usize) -> Self {
        let terms = l.terms.iter().map(|&(c, cell)| (F64(c.value[0]), cell as usize ^ role));
        Self {
            ones: terms.clone().filter(|&(c, _)| c == F64::ONE).map(|(_, i)| i).collect(),
            scaled: terms.filter(|&(c, _)| c != F64::ONE).map(|(c, i)| (Kx8::splat(c), i)).collect(),
            constant: l.constant.map_or(F64::ZERO, |c| F64(c.value[0])),
        }
    }

    #[inline(always)]
    fn eval(&self, cells: &[Kx8]) -> Kx8 {
        let sum = self.ones.iter().fold(Kx8::splat(self.constant), |acc, &i| acc + cells[i]);
        if self.scaled.is_empty() {
            sum
        } else {
            sum + self
                .scaled
                .iter()
                .fold(Kx8U::zero(), |acc, &(c, i)| acc + Kx8U::product(c, cells[i]))
                .reduce()
        }
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
    [l0, l1, l2]: [&mut [F64]; 3],
) {
    let (m, r, n) = (circuit.log_n, circuit.log_row, circuit.n());
    let big = 4 * n;
    let offset = beta()[m + 2];
    let profile = std::env::var_os("PI2_PROFILE").is_some();
    let mut clock = Instant::now();
    let mut lap = |name: &str| {
        if profile {
            eprintln!("    q: {:7.3} s  {name}", clock.elapsed().as_secs_f64());
        }
        clock = Instant::now();
    };
    if profile {
        let mut hist = std::collections::BTreeMap::new();
        spec.pairs.iter().for_each(|p| *hist.entry(p.log_rows).or_insert(0usize) += 1);
        let kinds = spec.groups.iter().fold([0usize; 3], |mut k, g| {
            k[if g.formula.is_base() { 0 } else if g.formula.products.is_empty() { 1 } else { 2 }] += 1;
            k
        });
        let terms: usize = spec.groups.iter().map(|g| g.formula.lin.terms.len()).sum();
        let products: usize = spec.groups.iter().map(|g| g.formula.products.len()).sum();
        eprintln!(
            "    q: m {m} r {r}; {} pairs by log_rows {hist:?}; {} pull-less; {} groups (K, E-linear, E: {kinds:?}), {terms} terms, {products} products",
            spec.pairs.len(),
            spec.pull_less.len(),
            spec.groups.len()
        );
    }
    let on_d = |novel: &[F64]| on_extension(novel, m, offset);
    let wd = on_d(w_novel);
    let (sd, kd) = (&setup.sigma_on_d, &setup.kappa_on_d);
    let hd = [on_d(&h_novel[0]), on_d(&h_novel[1]), on_d(&h_novel[2])];
    let gammas = primitives::field::powers(gamma, spec.max_gamma + 1);
    lap("w, σ, κ, h on D");

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

    // The indicators, a chunk of `run` points at a time: a chunk lies in one coset of `V_m` (one `Z_V` value) and
    // fixes the index's bits from `log run` up. `Ẑ_s` vanishes on `U_s = ⟨β_r, …, β_{r+s-1}⟩`, so pair `p`'s indicator
    // reads the bits below `r` and from `r + s_p` up only: if `r + s_p ≥ log run` it is periodic in the chunk, of
    // period `2^r` (a *wide* pair: `period` points of it per chunk); otherwise it is computed at every point of the
    // chunk. Every chunk's indicators are one batched inversion.
    let width = 1usize << r;
    let run = n.min(1 << LOW);
    assert!(run % 8 == 0 && run.is_power_of_two());
    let log_run = run.trailing_zeros() as usize;
    let period = width.max(8);
    let pv = period / 8;
    let wide: Vec<bool> = spec
        .pairs
        .iter()
        .map(|p| period <= run && r + p.log_rows >= log_run)
        .collect();
    // Pair `p`'s vectors in a chunk's table: from `at[p]`, `pv` of them if wide, else `run / 8`.
    let mut at = Vec::with_capacity(spec.pairs.len());
    let mut vectors = 0;
    for &w in &wide {
        at.push(vectors);
        vectors += if w { pv } else { run / 8 };
    }
    let narrow = |members: &[usize]| -> Vec<usize> { members.iter().copied().filter(|&p| !wide[p]).collect() };

    let pairs: Vec<(usize, F64)> = spec.pairs.iter().map(|p| (p.log_rows, p.z)).collect();
    let groups: Vec<(Compiled, &[usize], Vec<usize>)> = spec
        .groups
        .iter()
        .map(|g| (Compiled::new(&g.formula, g.role, &gammas), &g.pairs[..], narrow(&g.pairs)))
        .collect();
    let pull_less = &spec.pull_less;
    let pull_less_narrow = narrow(pull_less);
    let points8 = Kx8::new(std::array::from_fn(point));
    let (alpha8, beta8) = (Ex8::splat(alpha), Ex8::splat(beta_));
    let one8 = Kx8::splat(F64::ONE);
    let zero8 = Kx8::splat(F64::ZERO);

    assert!(l0.len() == big && l1.len() == big && l2.len() == big);
    parallel::chunks_mut3(&mut *l0, &mut *l1, &mut *l2, run, |chunk, o0, o1, o2| {
        let start = chunk * run;
        let coset = start >> m;
        // The chunk's indicators: denominators, then one batched inversion, times `Z_V`.
        let mut table = vec![one8; vectors];
        for (p, &(s, z)) in pairs.iter().enumerate() {
            let len = if wide[p] { pv } else { run / 8 };
            for v in 0..len {
                let i = start + 8 * v;
                table[at[p] + v] =
                    Kx8::load(&low[s][i & ((1 << LOW) - 1)..]) + Kx8::splat(at_offset[s] + high[s][i >> LOW] + z);
            }
        }
        let mut prefix = vec![one8; vectors];
        let mut acc = one8;
        for (pre, &d) in prefix.iter_mut().zip(&table) {
            *pre = acc;
            acc = acc * d;
        }
        let mut inv = Kx8::new(lanes(acc).map(|x| x.inv())) * Kx8::splat(zv[coset]);
        for (d, &pre) in table.iter_mut().zip(&prefix).rev() {
            let next = inv * *d;
            *d = inv * pre;
            inv = next;
        }
        drop(prefix);
        // The wide pairs' sums by group (and the pull-less pairs'), `pv` vectors each.
        let wide_sum = |members: &[usize], k: usize| {
            members
                .iter()
                .filter(|&&p| wide[p])
                .fold(zero8, |acc, &p| acc + table[at[p] + k])
        };
        let group_wide: Vec<Kx8> = groups
            .iter()
            .flat_map(|(_, members, _)| (0..pv).map(|k| wide_sum(members, k)).collect::<Vec<_>>())
            .collect();
        let pull_less_wide: Vec<Kx8> = (0..pv).map(|k| wide_sum(pull_less, k)).collect();

        let mut cells = vec![one8; width];
        for j in 0..run / 8 {
            let i = start + 8 * j;
            let jw = j % pv;
            // Lane `l` is the point `i + l`, its row's cell `c` the point `(i + l) ^ c`.
            for (c, cell) in cells.iter_mut().enumerate() {
                *cell = Kx8::load(&wd[i ^ (c & !7)..]).xor_lanes(c & 7);
            }
            let w = cells[0];
            let mut selected = zero8;
            // `Σ_g sum_g v_g` (and `w · selected`), unreduced until the row's end.
            let mut pushed_k = Kx8U::zero();
            let mut pushed_e = Ex8::splat(F192::ZERO);
            for (g, (compiled, _, narrow)) in groups.iter().enumerate() {
                let sum = narrow
                    .iter()
                    .fold(group_wide[g * pv + jw], |acc, &p| acc + table[at[p] + j]);
                selected = selected + sum;
                match compiled {
                    Compiled::K { lin, products } => {
                        let v = if products.is_empty() {
                            lin.eval(&cells)
                        } else {
                            let p = products.iter().fold(Kx8U::zero(), |acc, (c, a, b)| {
                                let (x, y) = (a.eval(&cells), b.eval(&cells));
                                acc + Kx8U::product(if *c == F64::ONE { x } else { Kx8::splat(*c) * x }, y)
                            });
                            lin.eval(&cells) + p.reduce()
                        };
                        pushed_k = pushed_k + Kx8U::product(sum, v);
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
                            formula
                                .eval(&|c| F192::from(rows[c ^ role][l]), &gammas)
                                .mul_base(sums[l])
                        });
                        let limb = |k: usize| Kx8::new(v.map(|x| F64([x.c0, x.c1, x.c2][k])));
                        pushed_e = pushed_e + Ex8::from_limbs([limb(0), limb(1), limb(2)]);
                    }
                }
            }
            let one_s = pull_less_narrow
                .iter()
                .fold(pull_less_wide[jw], |acc, &p| acc + table[at[p] + j]);
            let pushed_k = (pushed_k + Kx8U::product(w, selected)).reduce();
            let p_t = Ex8::from_k(w + pushed_k + Kx8::load(&kd[i..])) + pushed_e;
            let x = Kx8::splat(offset + point(i)) + points8;
            let d_pull = alpha8 + Ex8::from_k(w) + beta8.mul_k(x);
            let d_push = alpha8 + p_t + beta8.mul_k(Kx8::load(&sd[i..]));
            let h = Ex8::from_limbs([Kx8::load(&hd[0][i..]), Kx8::load(&hd[1][i..]), Kx8::load(&hd[2][i..])]);
            let num = h * d_pull * d_push + d_push.mul_k(one8 + one_s) + d_pull;
            let [q0, q1, q2] = num.mul_k(Kx8::splat(zv_inv[coset])).limbs();
            o0[8 * j..8 * j + 8].copy_from_slice(&q0.to_row().0);
            o1[8 * j..8 * j + 8].copy_from_slice(&q1.to_row().0);
            o2[8 * j..8 * j + 8].copy_from_slice(&q2.to_row().0);
        }
    });
    lap("the numerator over Z_V");
    drop((wd, hd));
    for limb in [l0, l1, l2] {
        ntt::coefficients(limb, offset);
    }
    lap("q's coefficients");
}

/// `f`'s values on `offset + V_{m+2}` from its novel coefficients (`2^m` of them: degree below `2^m`): one transform
/// of `2^m` points on each coset `offset + ω_{c 2^m} + V_m`, `c < 4`; the values of the transform of the coefficients
/// zero-padded to `2^(m+2)`, whose top two layers copy them to the four quarters.
fn on_extension(novel: &[F64], m: usize, offset: F64) -> Vec<F64> {
    let n = novel.len();
    assert_eq!(n, 1 << m);
    let mut out: Vec<F64> = parallel::map_collect(4 * n, |i| novel[i & (n - 1)]);
    for (c, quarter) in out.chunks_mut(n).enumerate() {
        ntt::values(quarter, offset + point(c << m));
    }
    out
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

    // h on V_m, limb by limb. Each position's pull and push are `Circuit::pulls`'s and `Circuit::pushes`'s, found
    // without their tables: a position's pair by a search in its role's pairs (sorted row intervals), every
    // formula's kind once.
    let gammas = super::circuit::gamma_powers(gamma, circuit.max_gamma());
    let base_formula: Vec<bool> = circuit.formulas.iter().map(|f| f.is_base()).collect();
    let width = circuit.width();
    let mut by_role: Vec<Vec<(usize, usize, usize)>> = vec![vec![]; width];
    for (p, pair) in circuit.pairs.iter().enumerate() {
        by_role[pair.role].push((pair.first_row, pair.first_row + (1 << pair.log_rows), p));
    }
    by_role.iter_mut().for_each(|l| l.sort_unstable());
    let pair_at = |i: usize| -> Option<usize> {
        let (row, list) = (i >> r, &by_role[i & (width - 1)]);
        let k = list.partition_point(|e| e.0 <= row);
        (k > 0 && row < list[k - 1].1).then(|| list[k - 1].2)
    };
    let run = n.min(1 << 12);
    let mut h_novel: [Vec<F64>; 3] = std::array::from_fn(|_| parallel::map_collect(n, |_| F64::ZERO));
    {
        let [h0, h1, h2] = &mut h_novel;
        parallel::chunks_mut3(h0, h1, h2, run, |chunk, o0, o1, o2| {
            let start = chunk * run;
            let mut pulls = vec![false; o0.len()];
            let mut d: Vec<F192> = Vec::with_capacity(2 * o0.len());
            for (j, pulls_j) in pulls.iter_mut().enumerate() {
                let i = start + j;
                let base = i & !(width - 1);
                let (pull, own) = match pair_at(i) {
                    None => (true, F192::from(w[i])),
                    Some(p) => {
                        let pair = &circuit.pairs[p];
                        let formula = &circuit.formulas[pair.formula];
                        let own = if base_formula[pair.formula] {
                            F192::from(formula.eval_k(&|c| w[base + c]))
                        } else {
                            formula.eval(&|c| F192::from(w[base + c]), &gammas)
                        };
                        (pair.pulls, own)
                    }
                };
                *pulls_j = pull;
                d.push(if pull {
                    alpha + F192::from(w[i]) + beta_.mul_base(point(i))
                } else {
                    F192::ONE
                });
                d.push(alpha + own + F192::from(circuit.kappa[i]) + beta_.mul_base(point(circuit.sigma[i] as usize)));
            }
            batch_inverse_e(&mut d);
            for (j, &pull) in pulls.iter().enumerate() {
                let x = if pull { d[2 * j] } else { F192::ZERO } + d[2 * j + 1];
                (o0[j], o1[j], o2[j]) = (F64(x.c0), F64(x.c1), F64(x.c2));
            }
        });
    }
    let limb_sum = |l: &[F64]| {
        parallel::map_reduce(
            n / run,
            || F64::ZERO,
            |c| l[c * run..(c + 1) * run].iter().fold(F64::ZERO, |a, &x| a + x),
            |a, b| a + b,
        )
    };
    let sum = F192::new(limb_sum(&h_novel[0]).0, limb_sum(&h_novel[1]).0, limb_sum(&h_novel[2]).0);
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
    for limb in &mut h_novel {
        ntt::coefficients(limb, F64::ZERO);
    }
    lap("h on V_m, its coefficients", &mut timings);

    // Q's stack, built in place: its lanes are the chunks in `quotient_chunks`'s order, so the stack is, limb by
    // limb, `h`'s coefficients (`N` words) then `q`'s (`4N`, its four chunks in order). Checked lane by lane
    // against the table's layout (lane `L` holds block `b`: chunk `c = b·lane >> m`, `8 limb + 4 kind + digit`).
    let qlane = 1usize << l.quotient.log_lane();
    assert_eq!(l.quotient.placed(), 15 * n);
    for lane in 0..15 * n / qlane {
        let start = l.quotient.block(lane) * qlane;
        let (c, within) = (start >> m, start & (n - 1));
        let (limb, kind, digit) = (c >> 3, (c >> 2) & 1, c & 3);
        assert!(kind == 1 || digit == 0);
        assert_eq!(5 * n * limb + kind * n + digit * n + within, lane * qlane, "Q's lane {lane}");
    }
    let mut stack: Vec<F64> = parallel::map_collect(15 * n, |_| F64::ZERO);
    {
        let mut parts = stack.chunks_exact_mut(5 * n).map(|limb| limb.split_at_mut(n));
        let [(h0, q0), (h1, q1), (h2, q2)] = [(); 3].map(|_| parts.next().expect("three limbs"));
        for (dst, src) in [h0, h1, h2].into_iter().zip(&h_novel) {
            parallel::chunks_mut(dst, 1 << 16, |k, out| out.copy_from_slice(&src[k << 16..(k << 16) + out.len()]));
        }
        quotient_on_extension(circuit, spec, setup, &w_novel, &h_novel, [alpha, beta_, gamma], [q0, q1, q2]);
    }
    drop(h_novel);
    lap("q on the extension coset, its coefficients", &mut timings);

    let quotient = Table {
        layout: l.quotient.clone(),
        stack,
    };
    let quotient_committed = opening::commit(&quotient);
    writer.send_root(root_scalars(&quotient_committed.root).map(to_e));
    let t = to_f192(writer.sample());
    lap("Q: table, commit", &mut timings);

    let digits: Vec<F192> = std::iter::successors(Some(t), |&x| Some(x * x + x))
        .take(m + 2)
        .collect();
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
    // ξ = κ(t) + β σ(t), from the setup's halves `κ` and `κ + σ`; `h(t)` is not sent (PI2.md §9).
    let setup_stack = &setup.table.stack;
    let kappa_t = primitives::multilinear::mle_eval_par(&setup_stack[..n], &digits[..m]);
    let sum_t = primitives::multilinear::mle_eval_par(&setup_stack[n..2 * n], &digits[..m]);
    let xi = kappa_t + beta_ * (kappa_t + sum_t);
    folds.iter().chain([&xi]).for_each(|&x| writer.send(to_e(x)));
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
    verify(
        &l.witness,
        &roots[0],
        &[claim(&reduced.witness)],
        &wire_proof(&openings.witness),
    )?;
    verify(
        &l.quotient,
        &roots[1],
        &[claim(&reduced.quotient), claim(&reduced.sum)],
        &wire_proof(&openings.quotient),
    )?;
    verify(
        &l.setup,
        setup_root,
        &[claim(&reduced.setup)],
        &wire_proof(&openings.setup),
    )
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
                let certified = CERTIFIED_QUERIES
                    .iter()
                    .find(|(n, _)| *n == layout.log_n)
                    .map(|(_, q)| *q);
                assert_eq!(Some(&config.queries[..]), certified, "2^{} words", layout.log_n);
            }
        }
    }
}
