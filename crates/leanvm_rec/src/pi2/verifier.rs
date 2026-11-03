// Part of this repository. The reduction's shape (one quotient identity at `t`, claims on the tables that hold the
// polynomials, the Cantor digits and the extension's coordinates) follows crates/quotient/src/protocol.rs (`reduce`,
// adapted there from leanVM's `flock::quotient`, branch PCS-openings-aggregation, commit 651453c6); the transcript is
// crates/leanvm_flock_gas's Keccak-256 chain (`KeccakChannel`). MIT OR Apache-2.0; see NOTICE.md.
//! π2's verifier, generic over the scalar (`leanvm_flock_gas::scalar::Scalar`): on `E` with the Keccak-256 chain it is
//! the contract's verifier in Rust ([`verify`]); on the recorder's symbol it is the graph the contract is compiled from
//! (`pi2::contract`). See `PI2.md` §2 for the protocol.
//!
//! The stream: the public data ([`Read`]s), `W`'s root, then `α, β, γ`; `Q`'s root, then `t`; the row's `2^r` fold
//! values `a_k`, `σ(t)`, `κ(t)`, `h(t)`, then `ρ`. At `t` the verifier computes:
//!
//! 1. the digits `w_l = w_l(t)`, `w_{l+1} = w_l^2 + w_l`;
//! 2. the row's cells `v_c = w(t + ω_c) = Σ_k a_k eq(k, (w_l + ω_{c >> l})_{l<r})`;
//! 3. every pair's indicator `I_p(t) = w_m · Π e / (Z_{U_s}(t) + Z_{U_s}(c_p))`, by one batched inversion with the
//!    public side's denominators, the `1 + w_l` and `w_m`;
//! 4. `P(t) = v_0 (1 + Σ_p I_p) + Σ_g (Σ_{p∈g} I_p) E_g(v_{c ⊕ k_g}) + κ(t)`, `d_pull = α + v_0 + β t`,
//!    `d_push = α + P(t) + β σ(t)`, `1_S(t) = Σ` of the pull-less pairs' indicators;
//! 5. the public target `T = Σ_J 1/(α + F_J + β τ_J)`;
//! 6. `q(t) = ((1 + 1_S) d_push + d_pull + h(t) d_pull d_push) / w_m`, from the identity
//!    `h d_pull d_push + (1 + 1_S) d_push + d_pull = q Z_V`;
//!
//! and leaves four claims: `W` at `(ρ, ρ², …, ρ^{2^{r-1}}, w_r, …, w_{m-1})`, value `Σ_k eq(ρ⃗, k) a_k`; `Q` at
//! `(u_0, …, u_{m+1}, ρ, y_0, y_1)`, `u_l = w_l / (1 + w_l)`, value `s Π (1 + w_l)^{-1} ((1 + ρ) h(t) + ρ q(t))`, and
//! at `(1^m, 0, 0, 0, y_0, y_1)` (the top coefficient of `h`: `Σ_V h`), value `s T`; the setup at
//! `(w_0, …, w_{m-1}, ρ)`, value `(1 + ρ) σ(t) + ρ κ(t)`.

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
    pub z: F64,
}

/// The pairs of one role and one formula: their indicators are summed before the formula's value multiplies them.
#[derive(Clone, Debug)]
pub struct Group {
    pub role: usize,
    pub formula: Formula,
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
    /// `e_1, …` ([`coset_constants`]), and the normalisations `Π_{j ≤ s} e_j` by block size `s`.
    pub e: Vec<F64>,
    pub norms: Vec<F64>,
    pub reads: Vec<Read>,
    pub public: Vec<PublicTerm>,
    pub max_gamma: usize,
}

impl Spec {
    pub fn of(circuit: &Circuit) -> Self {
        let (m, r) = (circuit.log_n, circuit.log_row);
        let e = coset_constants(r, m - r);
        let pairs: Vec<SpecPair> = circuit
            .pairs
            .iter()
            .map(|p| SpecPair {
                log_rows: p.log_rows,
                z: pair_constants(p, r, &e).0,
            })
            .collect();
        let mut groups: Vec<Group> = Vec::new();
        for (index, p) in circuit.pairs.iter().enumerate() {
            let formula = &circuit.formulas[p.formula];
            match groups.iter_mut().find(|g| g.role == p.role && g.formula == *formula) {
                Some(g) => g.pairs.push(index),
                None => groups.push(Group {
                    role: p.role,
                    formula: formula.clone(),
                    pairs: vec![index],
                }),
            }
        }
        let norms = (0..=m - r)
            .map(|s| e[..s].iter().fold(F64::ONE, |acc, &x| acc * x))
            .collect();
        Self {
            log_n: m,
            log_row: r,
            pairs,
            groups,
            pull_less: (0..circuit.pairs.len()).filter(|&p| !circuit.pairs[p].pulls).collect(),
            e,
            norms,
            reads: circuit.reads.clone(),
            public: circuit.public.clone(),
            max_gamma: circuit.max_gamma(),
        }
    }

    /// Scalars the proof sends after the roots: the `2^r` fold values, `σ(t)`, `κ(t)`, `h(t)`.
    pub fn values(&self) -> usize {
        (1 << self.log_row) + 3
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
    if c.gamma == 0 { value } else { value * gammas[c.gamma as usize] }
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

/// `x^-1` for a nonzero `x`: `x^(2^192 - 2)` by Itoh–Tsujii, `t_k = x^(2^k - 1)`, `t_{2k} = t_k^(2^k) t_k`,
/// `t_{2k+1} = t_{2k}^2 x`, up to `k = 191`: 191 squarings and 13 products.
pub fn inverse<S: Scalar>(x: S) -> S {
    let (mut t, mut k) = (x, 1usize);
    for bit in (0..7).rev() {
        let mut s = t;
        for _ in 0..k {
            s = s.square();
        }
        t = s * t;
        k *= 2;
        if (191 >> bit) & 1 == 1 {
            t = t.square() * x;
            k += 1;
        }
    }
    debug_assert_eq!(k, 191);
    t.square()
}

/// Every `x^-1` by one inversion, the verifier requiring their product nonzero.
pub fn batch_inverse<S: Scalar, C: Channel<S>>(channel: &mut C, xs: &[S]) -> Result<Vec<S>, VerifierError> {
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

/// The two coordinates of the extension over `K` and the scale of their weights `(1, Y, Y², Y³)`.
pub fn extension() -> ([F192; 2], F192) {
    quotient::protocol::extension()
}

/// The verifier: the public data and the proof read from `channel`, down to the four claims. `statement` is the
/// public input's four words. It rejects only a challenge at which a denominator vanishes.
pub fn reduce<S: Scalar, C: Channel<S>>(
    spec: &Spec,
    statement: [S; 4],
    channel: &mut C,
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
    let sigma_t = channel.next_scalar()?;
    let kappa_t = channel.next_scalar()?;
    let h_t = channel.next_scalar()?;
    let rho = channel.sample();

    let w = {
        let _phase = enter("pi2: digits");
        let mut w = vec![t];
        for l in 0..m + 1 {
            let x = w[l];
            w.push(x.square() + x);
        }
        w
    };

    // The row's cells: fold the top variable first, each fold splitting by the next bit of `c`.
    let cells = {
        let _phase = enter("pi2: the row's cells (fold)");
        let mut layer: Vec<Vec<S>> = vec![a.clone()];
        for l in (0..r).rev() {
            let half = 1 << l;
            layer = (0..1usize << (r - l))
                .map(|key| {
                    let parent = &layer[key >> 1];
                    let z = w[l] + base::<S>(point(key));
                    (0..half).map(|j| parent[j] + z * (parent[j] + parent[j + half])).collect()
                })
                .collect();
        }
        layer.into_iter().map(|v| v[0]).collect::<Vec<S>>()
    };
    let v0 = cells[0];

    // `Z_{U_s}(t)` for every block size.
    let zt = {
        let _phase = enter("pi2: indicators (block vanishing polynomials)");
        let mut zt = vec![t];
        for s in 1..=spec.max_log_rows() {
            let z = zt[s - 1];
            zt.push(z.square() + base::<S>(spec.e[s - 1]) * z);
        }
        zt
    };

    let gammas = leanvm_flock_gas::scalar::powers(gamma, spec.max_gamma + 1);
    let (pair_dens, public_dens) = {
        let _phase = enter("pi2: indicators (denominators)");
        let pairs: Vec<S> = spec.pairs.iter().map(|p| zt[p.log_rows] + base::<S>(p.z)).collect();
        let _public = enter("pi2: public side (fingerprints)");
        let public: Vec<S> = spec
            .public
            .iter()
            .map(|term| alpha + lin(&term.value, &|c| public[c], &gammas) + beta * base::<S>(point(term.tag as usize)))
            .collect();
        (pairs, public)
    };
    let mut dens = pair_dens;
    dens.extend(public_dens);
    dens.extend((0..m + 2).map(|l| one + w[l]));
    dens.push(w[m]);
    let invs = {
        let _phase = enter("pi2: batched inversion");
        batch_inverse(channel, &dens)?
    };
    let (n_pairs, n_public) = (spec.pairs.len(), spec.public.len());
    let (pair_invs, rest) = invs.split_at(n_pairs);
    let (public_invs, rest) = rest.split_at(n_public);
    let (digit_invs, wm_inv) = rest.split_at(m + 2);
    let wm_inv = wm_inv[0];

    let indicators: Vec<S> = {
        let _phase = enter("pi2: indicators (products)");
        let mut scaled = vec![None; m - r + 1];
        spec.pairs
            .iter()
            .zip(pair_invs)
            .map(|(p, &inv)| {
                let scale = *scaled[p.log_rows].get_or_insert_with(|| w[m] * base::<S>(spec.norms[p.log_rows]));
                scale * inv
            })
            .collect()
    };

    let p_t = {
        let _phase = enter("pi2: push formulas");
        let mut selected = S::zero();
        let mut pushed = S::zero();
        for group in &spec.groups {
            let sum = group.pairs.iter().fold(S::zero(), |acc, &p| acc + indicators[p]);
            let value = formula(&group.formula, &|c| cells[c ^ group.role], &gammas);
            selected += sum;
            pushed += sum * value;
        }
        v0 + v0 * selected + pushed + kappa_t
    };
    let one_s = spec.pull_less.iter().fold(S::zero(), |acc, &p| acc + indicators[p]);

    let _phase = enter("pi2: identity and claims");
    let d_pull = alpha + v0 + beta * t;
    let d_push = alpha + p_t + beta * sigma_t;
    let target = public_invs.iter().fold(S::zero(), |acc, &x| acc + x);
    let q_t = ((one + one_s) * d_push + d_pull + h_t * d_pull * d_push) * wm_inv;

    let ([y0, y1], scale) = extension();
    let (y0, y1, scale) = (ext::<S>(y0), ext::<S>(y1), ext::<S>(scale));
    let u: Vec<S> = digit_invs.iter().map(|&x| one + x).collect();
    let digits_scale = digit_invs.iter().fold(one, |acc, &x| acc * x);
    let quotient_value = scale * digits_scale * (h_t + rho * (h_t + q_t));
    let quotient_point = [&u[..], &[rho, y0, y1]].concat();
    let sum_point = [vec![one; m], vec![S::zero(); 3], vec![y0, y1]].concat();

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
    let witness_point = [&rhos[..], &w[r..m]].concat();
    let setup_point = [&w[..m], &[rho]].concat();
    Ok(Reduced {
        public,
        roots: [witness_root, quotient_root],
        witness: (witness_point, fold[0]),
        quotient: (quotient_point, quotient_value),
        sum: (sum_point, scale * target),
        setup: (setup_point, sigma_t + rho * (sigma_t + kappa_t)),
    })
}

/// The public input's four words, as calldata carries them: big-endian each.
pub fn statement_words(public_input: &[u8; 32]) -> [E; 4] {
    std::array::from_fn(|k| E::new(u64::from_be_bytes(public_input[8 * k..8 * k + 8].try_into().unwrap()), 0, 0))
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
}
