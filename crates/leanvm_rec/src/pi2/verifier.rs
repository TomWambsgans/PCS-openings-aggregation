// Part of this repository. The reduction's shape (one quotient identity at `t`, claims on the tables that hold the
// polynomials, the Cantor digits and the extension's coordinates) follows crates/quotient/src/protocol.rs (`reduce`,
// adapted there from leanVM's `flock::quotient`, branch PCS-openings-aggregation, commit 651453c6); the transcript is
// crates/leanvm_flock_gas's Keccak-256 chain (`KeccakChannel`). MIT OR Apache-2.0; see NOTICE.md.
//! π2's verifier, generic over the scalar (`leanvm_flock_gas::scalar::Scalar`): on `E` with the Keccak-256 chain it is
//! the contract's verifier in Rust ([`verify`]); on the recorder's symbol it is the graph the contract is compiled from
//! (`pi2::contract`). See `PI2.md` §2 for the protocol.
//!
//! The stream: the public data ([`Read`]s), `W`'s root, then `α, β, γ`; `Q`'s root, then `t`; the row's `2^r` fold
//! values `a_k` and `ξ = κ(t) + β σ(t)`, then `ρ` (`PI2.md` §9: `h(t)` is not sent, nor `σ(t)` and `κ(t)` apart). At
//! `t` the verifier computes, as fractions with one inversion at the end:
//!
//! 1. the digits `w_l = w_l(t)`, `w_{l+1} = w_l^2 + w_l`;
//! 2. the row's cells `v_c = w(t + ω_c) = Σ_k a_k eq(k, (w_l + ω_{c >> l})_{l<r})`;
//! 3. every pair's indicator `I_p(t) = w_m / (Ẑ_s(t) + Ẑ_s(c_p))`, the indicators of a group (pairs of one role and
//!    formula) summed as one fraction `N_g / D_g`;
//! 4. `P(t) = v_0 + w_m A / B + κ(t)`, `A / B = Σ_g (N_g / D_g)(E_g(v_{c ⊕ k_g}) + v_0)` accumulated as one fraction,
//!    so `d_push = α + P(t) + β σ(t) = D_n / B` with `D_n = (α + v_0 + ξ) B + w_m A`; `d_pull = α + v_0 + β t`;
//!    `1_S = w_m S_n / S_d` over the pull-less groups;
//! 5. the public target `T = N / D = Σ_J 1/(α + F_J + β τ_J)`;
//! 6. the identity `h d_pull d_push + q w_m = (1 + 1_S) d_push + d_pull` at `t` is one combination of `h(t)` and
//!    `q(t)`, `c_h = d_pull d_push`, `c_q = w_m`: with `Y = d_pull D_n + w_m B` (`B (c_h + c_q)`) and
//!    `X = (S_d + w_m S_n) D_n + d_pull B S_d` (`B S_d` times the right side), the claim `(1 + ρ') h + ρ' q = X / (S_d Y)`
//!    at `ρ' = w_m B / Y`;
//! 7. one inversion of `S_d Y · w_{m+2} · D` (nonzero required), and the digits' inverses down from `1/w_{m+2}`:
//!    `1/w_l = (1 + w_l) / w_{l+1}`;
//!
//! and leaves four claims: `W` at `(ρ, ρ², …, ρ^{2^{r-1}}, w_r, …, w_{m-1})`, value `Σ_k eq(ρ⃗, k) a_k`; `Q` at
//! `(u_0, …, u_{m+1}, ρ', y_0, y_1)`, `u_l = w_l / (1 + w_l)`, value `s Π (1 + w_l)^{-1} X / (S_d Y)`, and at
//! `(1^m, 0, 0, 0, y_0, y_1)` (the top coefficient of `h`: `Σ_V h`), value `s T`; the setup (its halves `κ` and
//! `κ + σ`) at `(w_0, …, w_{m-1}, β)`, value `ξ`.

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::scalar::{Scalar, enter};
use leanvm_flock_gas::transcript::{Channel, Checks, KeccakChannel, keccak_seed};
use primitives::field::{F64, F192};
use quotient::domain::point;

use super::circuit::{Circuit, Coeff, Formula, Lin, NONE, PublicTerm, Read, coset_constants, pair_constants};

/// The transcript's 16-byte name.
pub const NAME: [u8; 16] = *b"leanvm-rec-pi2v1";

/// A pair as the verifier needs it: its block size `s` and `Z_{U_s}(c_p)`.
#[derive(Clone, Copy, Debug)]
pub struct SpecPair {
    pub log_rows: usize,
    /// `Ẑ_s(c_p)`, the block's normalised vanishing polynomial ([`Spec::c`]) at the coset's base.
    pub z: F64,
}

/// The pairs of one role and one formula (pulling, or all pull-less): the sum of their indicators multiplies the
/// formula's value, and is one fraction `N_g / D_g` (`D_g` the product of the pairs' denominators).
#[derive(Clone, Debug)]
pub struct Group {
    pub role: usize,
    pub formula: Formula,
    pub pulls: bool,
    pub pairs: Vec<usize>,
}

/// What the verifier is built from: the circuit's shape, its pairs grouped by (role, formula), the public side.
#[derive(Clone, Debug)]
pub struct Spec {
    pub log_n: usize,
    pub log_row: usize,
    pub pairs: Vec<SpecPair>,
    pub groups: Vec<Group>,
    /// The pull-less pairs.
    pub pull_less: Vec<usize>,
    /// The normalised vanishing polynomials `Ẑ_s = Z_{U_s} / Π_{j ≤ s} e_j` (linear coefficient 1):
    /// `Ẑ_s(x) = Ẑ_{s-1}(x) + c_s Ẑ_{s-1}(x)^2`, `c_s = Π_{j < s} e_j / e_s`; this is `c_1, …`. Then
    /// `I_p(x) = Z_V(x) / (Ẑ_s(x) + Ẑ_s(c_p))`.
    pub c: Vec<F64>,
    pub reads: Vec<Read>,
    /// The public terms but the zero coset's.
    pub public: Vec<PublicTerm>,
    pub max_gamma: usize,
    /// The public terms of value 0 whose tags are an aligned coset `c + V_k` (`k ≥ 1`; the zero checks and their
    /// padding, `PI2.md` §9 lever 3c): `(c's tag, k, the coefficients a_i of V_k's subspace polynomial
    /// w_k(X) = Σ a_i X^(2^i))`. Their sum `Σ_(u ∈ V_k) 1/(Y + βu)`, `Y = α + β ω_c`, is `β^(2^k − 1) / F(Y)` with
    /// `F(Y) = Σ a_i Y^(2^i) β^(2^k − 2^i)` (`F = β^(2^k) w_k(Y/β)`, whose derivative is `a_0 β^(2^k-1)`, `a_0 = 1`).
    pub zero_coset: Option<(u32, usize, Vec<F64>)>,
}

/// The coefficients of `w_k = s^k`, `s(X) = X² + X` (`V_k`'s subspace polynomial in the Cantor basis), low first:
/// `a_i` of `X^(2^i)`, `i ≤ k`.
pub fn subspace_coefficients(k: usize) -> Vec<F64> {
    let mut a = vec![F64::ONE];
    for _ in 0..k {
        // s(Σ a_i X^(2^i)) = Σ a_i² X^(2^(i+1)) + Σ a_i X^(2^i).
        let mut next = vec![F64::ZERO; a.len() + 1];
        for (i, &c) in a.iter().enumerate() {
            next[i + 1] += c * c;
            next[i] += c;
        }
        a = next;
    }
    a
}

/// The zero-valued public terms, if their tags are exactly an aligned coset of `2^k` tags (`k ≥ 1`); and the others.
fn zero_coset(public: &[PublicTerm]) -> (Option<(u32, usize, Vec<F64>)>, Vec<PublicTerm>) {
    let (zeros, rest): (Vec<&PublicTerm>, Vec<&PublicTerm>) = public
        .iter()
        .partition(|t| t.value.terms.is_empty() && t.value.constant.is_none());
    let mut tags: Vec<u32> = zeros.iter().map(|t| t.tag).collect();
    tags.sort_unstable();
    let n = tags.len();
    let aligned = n >= 2
        && n.is_power_of_two()
        && tags[0] as usize % n == 0
        && tags.windows(2).all(|w| w[1] == w[0] + 1);
    if !aligned {
        return (None, public.to_vec());
    }
    let k = n.trailing_zeros() as usize;
    (Some((tags[0], k, subspace_coefficients(k))), rest.into_iter().cloned().collect())
}

/// `Ẑ_s`'s recursion constants `c_1 … c_count`.
pub fn normalised_constants(e: &[F64]) -> Vec<F64> {
    let mut norm = F64::ONE;
    e.iter()
        .map(|&x| {
            let c = norm * x.inv();
            norm *= x;
            c
        })
        .collect()
}

impl Spec {
    /// The verifier of `circuit`, which must be valid ([`Circuit::validate`], REVIEW-REC.md L1: no formula reads a
    /// hole, `κ` only at expression slots).
    pub fn of(circuit: &Circuit) -> Self {
        circuit.validate().unwrap_or_else(|e| panic!("the circuit is not valid: {e}"));
        let (m, r) = (circuit.log_n, circuit.log_row);
        let e = coset_constants(r, m - r);
        let pairs: Vec<SpecPair> = circuit
            .pairs
            .iter()
            .map(|p| {
                let (z, norm) = pair_constants(p, r, &e);
                SpecPair {
                    log_rows: p.log_rows,
                    z: z * norm.inv(),
                }
            })
            .collect();
        let mut groups: Vec<Group> = Vec::new();
        for (index, p) in circuit.pairs.iter().enumerate() {
            let formula = &circuit.formulas[p.formula];
            match groups
                .iter_mut()
                .find(|g| g.role == p.role && g.pulls == p.pulls && g.formula == *formula)
            {
                Some(g) => g.pairs.push(index),
                None => groups.push(Group {
                    role: p.role,
                    formula: formula.clone(),
                    pulls: p.pulls,
                    pairs: vec![index],
                }),
            }
        }
        let (coset, public) = zero_coset(&circuit.public);
        Self {
            log_n: m,
            log_row: r,
            pairs,
            groups,
            pull_less: (0..circuit.pairs.len()).filter(|&p| !circuit.pairs[p].pulls).collect(),
            c: normalised_constants(&e),
            reads: circuit.reads.clone(),
            public,
            max_gamma: circuit.max_gamma(),
            zero_coset: coset,
        }
    }

    /// Scalars the proof sends after the roots: the `2^r` fold values and `ξ = κ(t) + β σ(t)`.
    pub fn values(&self) -> usize {
        (1 << self.log_row) + 1
    }

    /// The largest block size.
    pub fn max_log_rows(&self) -> usize {
        self.pairs.iter().map(|p| p.log_rows).max().unwrap_or(0)
    }
}

/// What [`reduce`] leaves: the public scalars, `W`'s and `Q`'s roots, and the four claims, each a point and a value.
#[derive(Clone, Debug)]
pub struct Reduced<S> {
    pub public: Vec<S>,
    /// `transcript::pair_point` of every public scalar: the coordinates of π1-rec3's paired batch, which its calls
    /// take (`CallWord::Pair`); a contract computes only those its calls read.
    pub pair_points: Vec<[S; 2]>,
    pub roots: [[S; 2]; 2],
    pub witness: (Vec<S>, S),
    pub quotient: (Vec<S>, S),
    pub sum: (Vec<S>, S),
    pub setup: (Vec<S>, S),
}

fn base<S: Scalar>(x: F64) -> S {
    S::constant(E::new(x.0, 0, 0))
}

fn ext<S: Scalar>(x: F192) -> S {
    S::constant(E::new(x.c0, x.c1, x.c2))
}

fn coeff<S: Scalar>(c: &Coeff, gammas: &[S]) -> S {
    let value = ext::<S>(c.field());
    if c.gamma == 0 {
        value
    } else {
        value * gammas[c.gamma as usize]
    }
}

fn lin<S: Scalar>(l: &Lin, cell: &dyn Fn(usize) -> S, gammas: &[S]) -> S {
    let constant = l.constant.map_or(S::zero(), |c| coeff(&c, gammas));
    l.terms.iter().fold(constant, |acc, (c, cell_index)| {
        let v = cell(*cell_index as usize);
        acc + if c.is_one() { v } else { coeff(c, gammas) * v }
    })
}

/// A formula on `S`, its cells given.
pub fn formula<S: Scalar>(f: &Formula, cell: &dyn Fn(usize) -> S, gammas: &[S]) -> S {
    f.products.iter().fold(lin(&f.lin, cell, gammas), |acc, (c, a, b)| {
        let p = lin(a, cell, gammas) * lin(b, cell, gammas);
        acc + if c.is_one() { p } else { coeff(c, gammas) * p }
    })
}

/// What the verifier needs of a scalar beyond `Scalar`: its limbs above the lowest, `x >> 64 = c_1 + c_2 Y` and
/// `x >> 128 = c_2` for `x = c_0 + c_1 Y + c_2 Y²`. On the recorder's symbol they are `Node::Bits(x, 64, 64)` and
/// `Node::Bits(x, 128, 64)`: one `SHR` each in the contract (a 64-bit field takes no mask).
pub trait Limbs: Scalar {
    fn shifted(self) -> [Self; 2];
}

impl Limbs for E {
    fn shifted(self) -> [Self; 2] {
        [E::new(self.c1, self.c2, 0), E::new(self.c2, 0, 0)]
    }
}

impl Limbs for leanvm_flock_gas::evm::record::Sym {
    fn shifted(self) -> [Self; 2] {
        [self.bits(64, 64), self.bits(128, 64)]
    }
}

/// `x^(2^64)`: `(c_0, c_1, c_2) ↦ (c_0, c_2, c_1 + c_2)` (`Y^(2^64) = Y²`), that is `x + (Y + Y²)(x >> 64) + (1 + Y²)(x >> 128)`.
pub fn frobenius<S: Limbs>(x: S) -> S {
    let [u, v] = x.shifted();
    let (y, y2) = (F192::Y, F192::Y * F192::Y);
    x + ext::<S>(y + y2) * u + ext::<S>(F192::ONE + y2) * v
}

/// `x^-1` for a nonzero `x`, by its norm to `K`: `m = x^(2^64) x^(2^128)` makes `N = x m` the norm, in `K`, whose
/// inverse is `N^(2^64 - 2)` by Itoh–Tsujii (`t_k = N^(2^k - 1)`, the chain `1, 2, 3, 6, 7, …, 62, 63`: 63 squarings, 10
/// products); then `x^-1 = m N^-1`. Two Frobenius maps and 76 products (crates/quotient's `protocol::inverse`).
pub fn inverse<S: Limbs>(x: S) -> S {
    let f = frobenius(x);
    let m = f * frobenius(f);
    let norm = x * m;
    let (mut t, mut k) = (norm, 1usize);
    for bit in (0..5).rev() {
        let mut s = t;
        for _ in 0..k {
            s = s.square();
        }
        t = s * t;
        k *= 2;
        if (63 >> bit) & 1 == 1 {
            t = t.square() * norm;
            k += 1;
        }
    }
    debug_assert_eq!(k, 63);
    m * t.square()
}

/// Every `x^-1` by one inversion, the verifier requiring their product nonzero.
pub fn batch_inverse<S: Limbs, C: Channel<S>>(channel: &mut C, xs: &[S]) -> Result<Vec<S>, VerifierError> {
    let mut prefix = Vec::with_capacity(xs.len());
    let mut acc = S::one();
    for &x in xs {
        prefix.push(acc);
        acc *= x;
    }
    channel.require_nonzero(acc, VerifierError::RecDegenerate)?;
    let mut running = {
        let _phase = enter("pi2: the inversion");
        inverse(acc)
    };
    let mut out = vec![S::zero(); xs.len()];
    for i in (0..xs.len()).rev() {
        out[i] = running * prefix[i];
        running *= xs[i];
    }
    Ok(out)
}

/// The order the verifier takes the public terms in: from the smallest tag, each next the one whose tag differs from
/// the last in the fewest bits (the smallest on a tie), so that `β ω_τ` costs an addition or two a term.
pub fn tag_walk(public: &[PublicTerm]) -> Vec<usize> {
    let mut left: Vec<usize> = (0..public.len()).collect();
    left.sort_by_key(|&j| public[j].tag);
    let mut out = Vec::with_capacity(left.len());
    let mut at: Option<u32> = None;
    while !left.is_empty() {
        let k = match at {
            None => 0,
            Some(tag) => (0..left.len())
                .min_by_key(|&k| ((public[left[k]].tag ^ tag).count_ones(), public[left[k]].tag))
                .expect("a term left"),
        };
        let j = left.remove(k);
        at = Some(public[j].tag);
        out.push(j);
    }
    out
}

/// The two coordinates of the extension over `K` and the scale of their weights `(1, Y, Y², Y³)`.
pub fn extension() -> ([F192; 2], F192) {
    quotient::protocol::extension()
}

/// The verifier: the public data and the proof read from `channel`, down to the four claims. `statement` is the
/// public input's four words. It rejects only a challenge at which a denominator vanishes.
pub fn reduce<S: Limbs, C: Channel<S>>(
    spec: &Spec,
    statement: [S; 4],
    channel: &mut C,
) -> Result<Reduced<S>, VerifierError> {
    reduce_traced(spec, statement, channel, &mut |_, _| {})
}

/// What [`reduce_traced`] hands its trace: a step's name and its values (`formal/RecStatement`'s differential test
/// compares every one with the Lean verifier's).
pub type Trace<'a, S> = &'a mut dyn FnMut(&'static str, &[S]);

/// [`reduce`], handing every intermediate value to `trace` after the step that computes it. The trace only reads
/// values already computed: the arithmetic, its order and (on the recorder's symbol) the graph are [`reduce`]'s.
pub fn reduce_traced<S: Limbs, C: Channel<S>>(
    spec: &Spec,
    statement: [S; 4],
    channel: &mut C,
    trace: Trace<'_, S>,
) -> Result<Reduced<S>, VerifierError> {
    let (m, r) = (spec.log_n, spec.log_row);
    let one = S::one();
    let mut public = statement.to_vec();
    for read in &spec.reads {
        match *read {
            Read::Integer(bytes) => public.push(channel.next_integer(bytes as usize)?),
            Read::Root => public.extend(channel.next_root()?),
            Read::Scalar => public.push(channel.next_scalar()?),
        }
    }
    let witness_root = channel.next_root()?;
    let [alpha, beta, gamma] = [(); 3].map(|_| channel.sample());
    let quotient_root = channel.next_root()?;
    let t = channel.sample();
    let a = channel.next_scalars(1 << r)?;
    let xi = channel.next_scalar()?;
    let rho = channel.sample();
    trace("challenges", &[alpha, beta, gamma, t, rho]);

    let w = {
        let _phase = enter("pi2: digits");
        let mut w = vec![t];
        for l in 0..m + 2 {
            let x = w[l];
            w.push(x.square() + x);
        }
        w
    };
    trace("digits", &w);

    // The row's cells: fold the top variable first, each fold splitting by the next bit of `c`. Siblings `2k`, `2k + 1`
    // fold at `z` and `z + 1` (`ω_{2k+1} = ω_{2k} + β_0`, `β_0 = 1`): the odd one is the even one plus the difference
    // `p_j + p_{j+half}`, no product (`PI2.md` §9, lever 3a): `r 2^(r-1)` products, not `r 2^r`.
    let cells = {
        let _phase = enter("pi2: the row's cells (fold)");
        let mut layer: Vec<Vec<S>> = vec![a.clone()];
        for l in (0..r).rev() {
            let half = 1 << l;
            let mut next: Vec<Vec<S>> = Vec::with_capacity(2 * layer.len());
            for (k, parent) in layer.iter().enumerate() {
                let z = w[l] + base::<S>(point(2 * k));
                let d: Vec<S> = (0..half).map(|j| parent[j] + parent[j + half]).collect();
                let even: Vec<S> = (0..half).map(|j| parent[j] + z * d[j]).collect();
                let odd: Vec<S> = (0..half).map(|j| even[j] + d[j]).collect();
                next.push(even);
                next.push(odd);
            }
            layer = next;
        }
        layer.into_iter().map(|v| v[0]).collect::<Vec<S>>()
    };
    trace("cells", &cells);
    let v0 = cells[0];

    // `Ẑ_s(t)` for every block size.
    let zt = {
        let _phase = enter("pi2: indicators (block vanishing polynomials)");
        let mut zt = vec![t];
        for s in 1..=spec.max_log_rows() {
            let z = zt[s - 1];
            zt.push(z + base::<S>(spec.c[s - 1]) * z.square());
        }
        zt
    };
    trace("zt", &zt);

    // Each group's indicators, summed: `Σ_p 1/d_p = N_g / D_g`, by `N ← N d + D`, `D ← D d`; the public side's sum
    // likewise. `Z_V(t) = w_m` multiplies every indicator: it is factored out.
    let fraction = |dens: &mut dyn Iterator<Item = S>| -> (S, S) {
        let first = dens.next().expect("a denominator");
        dens.fold((one, first), |(n, d), x| (n * x + d, d * x))
    };
    let groups: Vec<(S, S)> = {
        let _phase = enter("pi2: indicators (denominators)");
        spec.groups
            .iter()
            .map(|g| {
                fraction(
                    &mut g
                        .pairs
                        .iter()
                        .map(|&p| zt[spec.pairs[p].log_rows] + base::<S>(spec.pairs[p].z)),
                )
            })
            .collect()
    };
    trace("groups", &groups.iter().flat_map(|&(n, d)| [n, d]).collect::<Vec<S>>());
    let gammas = leanvm_flock_gas::scalar::powers(gamma, spec.max_gamma + 1);
    // The public side, its terms in [`tag_walk`]'s order: `β ω_τ` is linear in the tag's bits, so each term's is the
    // last one's plus the products `β β_b` of the bits that differ.
    let public_side = {
        let _phase = enter("pi2: public side (fingerprints)");
        let mut bits: Vec<Option<S>> = vec![None; super::circuit::TAG_BITS];
        let mut last: Option<(u32, S)> = None;
        let mut denominators: Vec<S> = Vec::new();
        let mut terms = tag_walk(&spec.public).into_iter().map(|j| {
            let term = &spec.public[j];
            let beta_tag = match last {
                None => beta * base::<S>(point(term.tag as usize)),
                Some((tag, value)) => {
                    let diff = tag ^ term.tag;
                    (0..super::circuit::TAG_BITS)
                        .filter(|b| diff >> b & 1 == 1)
                        .fold(value, |acc, b| {
                            acc + *bits[b].get_or_insert_with(|| beta * base::<S>(quotient::domain::beta()[b]))
                        })
                }
            };
            last = Some((term.tag, beta_tag));
            let denominator = alpha + lin(&term.value, &|c| public[c], &gammas) + beta_tag;
            denominators.push(denominator);
            denominator
        });
        let side = (!spec.public.is_empty()).then(|| fraction(&mut terms));
        drop(terms);
        trace("public terms", &denominators);
        trace("public side", &side.map_or(vec![], |(n, d)| vec![n, d]));
        // The zero coset `c + V_k`: `β^(2^k − 1) / F(Y)`, `Y = α + β ω_c`, `F(Y) = Σ a_i Y^(2^i) β^(2^k − 2^i)`.
        let coset = spec.zero_coset.as_ref().map(|(tag, k, a)| {
            let y = alpha + beta * base::<S>(point(*tag as usize));
            let (mut y_pow, mut b_pow) = (vec![y], vec![beta]);
            for i in 1..=*k {
                y_pow.push(y_pow[i - 1].square());
                if i < *k {
                    b_pow.push(b_pow[i - 1].square());
                }
            }
            // β^(2^k − 2^i) = Π_(i ≤ j < k) β^(2^j), down from i = k − 1; β^(2^k − 1) the product of them all.
            let mut b_rest = vec![one; *k + 1];
            for i in (0..*k).rev() {
                b_rest[i] = if i + 1 == *k { b_pow[i] } else { b_rest[i + 1] * b_pow[i] };
            }
            let mut f = y_pow[*k];
            for i in 0..*k {
                if a[i] != F64::ZERO {
                    let term = y_pow[i] * b_rest[i];
                    f += if a[i] == F64::ONE { term } else { base::<S>(a[i]) * term };
                }
            }
            (b_rest[0], f)
        });
        trace("zero coset", &coset.map_or(vec![], |(n, d)| vec![n, d]));
        match (side, coset) {
            (Some((n, d)), Some((nz, dz))) => Some((n * dz + d * nz, d * dz)),
            (side, None) => side,
            (None, coset) => coset,
        }
    };

    // The pushes' sum `A / B = Σ_g (N_g / D_g)(E_g + v_0)`, one fraction: a group of one pair adds `X / d` (3 products),
    // a larger one its `N_g X / D_g` (4); the pull-less groups' indicators likewise, `S_n / S_d`.
    let (num, den, s_num, s_den) = {
        let _phase = enter("pi2: push formulas");
        let (mut num, mut den): (Option<S>, Option<S>) = (None, None);
        let (mut s_num, mut s_den): (Option<S>, Option<S>) = (None, None);
        for (group, &(numerator, denominator)) in spec.groups.iter().zip(&groups) {
            let value = formula(&group.formula, &|c| cells[c ^ group.role], &gammas) + v0;
            let single = group.pairs.len() == 1;
            let term = if single { value } else { numerator * value };
            (num, den) = match (num, den) {
                (Some(a), Some(b)) => (Some(a * denominator + b * term), Some(b * denominator)),
                _ => (Some(term), Some(denominator)),
            };
            if !group.pulls {
                (s_num, s_den) = match (s_num, s_den) {
                    (Some(a), Some(b)) if single => (Some(a * denominator + b), Some(b * denominator)),
                    (Some(a), Some(b)) => (Some(a * denominator + b * numerator), Some(b * denominator)),
                    _ => (Some(numerator), Some(denominator)),
                };
            }
        }
        (
            num.unwrap_or(S::zero()),
            den.unwrap_or(one),
            s_num.unwrap_or(S::zero()),
            s_den.unwrap_or(one),
        )
    };
    trace("push", &[num, den, s_num, s_den]);

    let _phase = enter("pi2: identity and claims");
    let d_pull = alpha + v0 + beta * t;
    // d_push = α + P(t) + β σ(t) = D_n / B; the identity's combination as `X / (S_d Y)` at `ρ' = w_m B / Y`.
    let d_num = (alpha + v0 + xi) * den + w[m] * num;
    let y = d_pull * d_num + w[m] * den;
    let x = (s_den + w[m] * s_num) * d_num + d_pull * den * s_den;
    let (public_num, public_den) = public_side.unwrap_or((S::zero(), one));
    // One inversion: of `S_d Y`, `w_{m+2}` and the public side's denominator.
    let p1 = s_den * y;
    let p2 = p1 * w[m + 2];
    let all = p2 * public_den;
    trace("identity", &[d_pull, d_num, y, x, public_num, public_den, p1, p2, all]);
    channel.require_nonzero(all, VerifierError::RecDegenerate)?;
    let inv_all = {
        let _phase = enter("pi2: the inversion");
        inverse(all)
    };
    let inv_p2 = inv_all * public_den;
    let target = public_num * inv_all * p2;
    let inv_p1 = inv_p2 * w[m + 2];
    let inv_top = inv_p2 * p1;
    // `1/w_l = (1 + w_l) / w_{l+1}` (as `w_{l+1} = w_l (1 + w_l)`), down from `1/w_{m+2}`.
    let mut w_invs = vec![S::zero(); m + 3];
    w_invs[m + 2] = inv_top;
    for l in (0..m + 2).rev() {
        w_invs[l] = (one + w[l]) * w_invs[l + 1];
    }
    let rho_q = w[m] * den * s_den * inv_p1;
    let combination = x * inv_p1;
    trace("inverse", &[inv_all, inv_p2, target, inv_p1, inv_top]);
    trace("digit inverses", &w_invs);

    // `1/(1 + w_l) = 1/w_l + 1/w_{l+1}`; their product telescopes to `t / w_{m+2}`.
    let ([y0, y1], scale) = extension();
    let (y0, y1, scale) = (ext::<S>(y0), ext::<S>(y1), ext::<S>(scale));
    let u: Vec<S> = (0..m + 2).map(|l| one + w_invs[l] + w_invs[l + 1]).collect();
    let digits_scale = t * w_invs[m + 2];
    let quotient_value = scale * digits_scale * combination;
    let quotient_point = [&u[..], &[rho_q, y0, y1]].concat();
    let sum_point = [vec![one; m], vec![S::zero(); 3], vec![y0, y1]].concat();
    trace("u", &u);
    trace("quotient", &[rho_q, combination, digits_scale, quotient_value]);

    let mut rhos = vec![rho];
    for l in 1..r {
        let x = rhos[l - 1];
        rhos.push(x.square());
    }
    let mut fold = a;
    for l in (0..r).rev() {
        let half = 1 << l;
        for j in 0..half {
            fold[j] = fold[j] + rhos[l] * (fold[j] + fold[j + half]);
        }
        fold.truncate(half);
    }
    trace("rhos", &rhos);
    trace("fold", &fold);
    let witness_point = [&rhos[..], &w[r..m]].concat();
    let setup_point = [&w[..m], &[beta]].concat();
    let pair_points = public.iter().map(|&x| leanvm_flock_gas::transcript::pair_point(x)).collect();
    Ok(Reduced {
        pair_points,
        public,
        roots: [witness_root, quotient_root],
        witness: (witness_point, fold[0]),
        quotient: (quotient_point, quotient_value),
        sum: (sum_point, scale * target),
        setup: (setup_point, xi),
    })
}

/// The public input's four words, as calldata carries them: big-endian each.
pub fn statement_words(public_input: &[u8; 32]) -> [E; 4] {
    std::array::from_fn(|k| {
        E::new(
            u64::from_be_bytes(public_input[8 * k..8 * k + 8].try_into().unwrap()),
            0,
            0,
        )
    })
}

/// The verifier on `E` with the Keccak-256 chain, the contract's in Rust: the stream must be read whole.
pub fn verify(spec: &Spec, iv: &[u8; 32], public_input: &[u8; 32], stream: &[u8]) -> Result<Reduced<E>, VerifierError> {
    let seed = keccak_seed(&NAME, iv, public_input);
    let mut channel = KeccakChannel::new(seed, stream, Checks::Enforce);
    let reduced = reduce(spec, statement_words(public_input), &mut channel)?;
    channel.finish()?;
    Ok(reduced)
}

/// `E` as the prover's field.
pub fn to_f192(x: E) -> F192 {
    F192::new(x.c0, x.c1, x.c2)
}

pub fn to_e(x: F192) -> E {
    E::new(x.c0, x.c1, x.c2)
}

/// A claim of [`Reduced`] as `quotient::opening` takes it.
pub fn claim((point, value): &(Vec<E>, E)) -> quotient::opening::Claim {
    quotient::opening::Claim {
        point: point.iter().map(|&x| to_f192(x)).collect(),
        value: to_f192(*value),
    }
}

/// Pairs per position and the pair constants, for tests of the indicators against the circuit.
pub fn covered(circuit: &Circuit, i: usize) -> Option<usize> {
    let p = circuit.pair_of()[i];
    (p != NONE).then_some(p as usize)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inverse_inverts() {
        let mut x = E::new(0x1234_5678_9abc_def1, 0x0fed_cba9_8765_4321, 0x5555_aaaa_3333_cccc);
        for _ in 0..8 {
            assert_eq!(inverse(x) * x, E::new(1, 0, 0));
            x = x * x + E::new(3, 1, 4);
        }
    }

    /// The zero coset's closed form (PI2.md §9, lever 3c): `w_k`'s coefficients vanish on `V_k`, and
    /// `Σ_(u ∈ V_k) 1/(Y + βu) = β^(2^k − 1) / F(Y)`, `F(Y) = Σ a_i Y^(2^i) β^(2^k − 2^i)`.
    #[test]
    fn the_zero_coset_sum_is_its_closed_form() {
        assert_eq!(subspace_coefficients(4), [F64::ONE, F64::ZERO, F64::ZERO, F64::ZERO, F64::ONE]);
        let (alpha, beta) = (E::new(3, 1, 4), E::new(1, 5, 9));
        for k in 1..=5 {
            let a = subspace_coefficients(k);
            let w = |x: F64| {
                let (mut acc, mut x_pow) = (F64::ZERO, x);
                for &c in &a {
                    acc += c * x_pow;
                    x_pow = x_pow.square();
                }
                acc
            };
            for u in 0..1usize << k {
                assert_eq!(w(point(u)), F64::ZERO, "w_{k} vanishes on V_{k}");
            }
            let c = 1usize << 24;
            let y = alpha + beta * E::new(point(c).0, 0, 0);
            let sum = (0..1usize << k).fold(E::default(), |acc, u| {
                acc + inverse(alpha + beta * E::new(point(c + u).0, 0, 0))
            });
            let f = a.iter().enumerate().fold(E::default(), |acc, (i, &ai)| {
                acc + E::new(ai.0, 0, 0) * y.pow(1 << i) * beta.pow((1u64 << k) - (1 << i))
            });
            assert_eq!(sum * f, beta.pow((1u64 << k) - 1), "k = {k}");
        }
    }
}
