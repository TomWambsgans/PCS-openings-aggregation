// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π2's circuit as the PIOP sees it (SPEC-REC.md §2.3–§2.4): the local form of the interface the circuit compiler
//! (branch `leanvm-rec-circuit`, `circuit/spec.rs`) defines, which [`Circuit`] is built from (`pi2::adapt`).
//!
//! **Positions.** `N = 2^log_n` positions on the Cantor subspace `V_m`, position `i` at the point `ω_i`; a row is
//! `2^log_row` consecutive positions (16 in D16v, 32 in D32v), position `i = row · 2^log_row + role`.
//!
//! **Pushes.** Every position pulls its own value `(w(ω_i), ω_i)` and pushes `(P(ω_i), σ(ω_i))`, `σ` a setup column of
//! tags (points `ω_j`: inside `V_m` for `j < N`, outside it for `N ≤ j < 2^28`). `P(ω_i)` is:
//!
//! - the formula of its *(block, role) pair* on its row's cells, if a [`Pair`] covers it (an *expression slot*);
//!   a constant position is in a pair whose formula is zero;
//! - else its own pull (a *forward*);
//!
//! plus `κ(ω_i)`, the setup's constants column (zero off the constant positions). So
//! `P = w + Σ_p I_p · (E_p + w) + κ`, `I_p` the indicator of pair `p`'s coset.
//!
//! **Pull-less positions** (new here, `PI2.md` §1): a pair may be marked as pulling nothing. Its positions push to
//! outside tags only, and their own value is read by no formula. Every check of a value against the public side
//! consumes a push without feeding a pull, so the circuit has exactly as many pull-less positions as outside pushes:
//! with every position pulling, the copy argument could not balance.
//!
//! **The public side.** The verifier reads the public scalars (the public input's four words, then [`Read`]s from
//! the stream) and adds `1/(α + F_J + β τ_J)` for each [`PublicTerm`] `J`, `F_J` a linear form in the public scalars
//! (coefficients in `E`, times powers of `γ`).

use primitives::field::{F64, F192};
use quotient::domain::{beta, point};

/// Tags are points `ω_j` with `j < 2^TAG_BITS` (the basis `quotient::domain` computes).
pub const TAG_BITS: usize = quotient::domain::BASIS;

/// A coefficient: an element of `E` (limbs, low first) times `γ^gamma`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Coeff {
    pub value: [u64; 3],
    pub gamma: u8,
}

impl Coeff {
    pub const ONE: Self = Self {
        value: [1, 0, 0],
        gamma: 0,
    };

    /// An element of `K`.
    pub const fn k(x: u64) -> Self {
        Self {
            value: [x, 0, 0],
            gamma: 0,
        }
    }

    pub const fn e(x: F192) -> Self {
        Self {
            value: [x.c0, x.c1, x.c2],
            gamma: 0,
        }
    }

    /// `γ^g`.
    pub const fn gamma(g: u8) -> Self {
        Self {
            value: [1, 0, 0],
            gamma: g,
        }
    }

    pub fn times(self, x: F192) -> Self {
        Self {
            value: {
                let v = self.field() * x;
                [v.c0, v.c1, v.c2]
            },
            gamma: self.gamma,
        }
    }

    pub fn is_one(&self) -> bool {
        *self == Self::ONE
    }

    /// In `K`, with no power of `γ`.
    pub fn is_base(&self) -> bool {
        self.value[1] == 0 && self.value[2] == 0 && self.gamma == 0
    }

    /// The element of `E`, without its power of `γ`.
    pub fn field(&self) -> F192 {
        F192::new(self.value[0], self.value[1], self.value[2])
    }

    pub fn eval(&self, gammas: &[F192]) -> F192 {
        self.field() * gammas[self.gamma as usize]
    }
}

/// `Σ coefficient · cell`, plus a constant.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Lin {
    pub terms: Vec<(Coeff, u16)>,
    pub constant: Option<Coeff>,
}

impl Lin {
    pub fn cell(c: usize) -> Self {
        Self {
            terms: vec![(Coeff::ONE, c as u16)],
            constant: None,
        }
    }

    /// The sum of these cells.
    pub fn sum(cells: impl IntoIterator<Item = usize>) -> Self {
        Self {
            terms: cells.into_iter().map(|c| (Coeff::ONE, c as u16)).collect(),
            constant: None,
        }
    }

    pub fn plus(mut self, other: &Lin) -> Self {
        self.terms.extend(other.terms.iter().copied());
        self.constant = match (self.constant, other.constant) {
            (None, c) | (c, None) => c,
            (Some(a), Some(b)) => {
                assert_eq!(a.gamma, b.gamma, "constants of one power of γ");
                Some(Coeff {
                    value: {
                        let v = a.field() + b.field();
                        [v.c0, v.c1, v.c2]
                    },
                    gamma: a.gamma,
                })
            }
        };
        self
    }

    pub fn with_constant(mut self, c: Coeff) -> Self {
        self.constant = Some(c);
        self
    }

    pub fn cells(&self) -> impl Iterator<Item = usize> + '_ {
        self.terms.iter().map(|&(_, c)| c as usize)
    }

    pub fn is_base(&self) -> bool {
        self.terms.iter().all(|(c, _)| c.is_base()) && self.constant.is_none_or(|c| c.is_base())
    }

    pub fn eval(&self, cell: &dyn Fn(usize) -> F192, gammas: &[F192]) -> F192 {
        let constant = self.constant.map_or(F192::ZERO, |c| c.eval(gammas));
        self.terms
            .iter()
            .fold(constant, |acc, (coeff, c)| acc + coeff.eval(gammas) * cell(*c as usize))
    }

    pub fn eval_k(&self, cell: &dyn Fn(usize) -> F64) -> F64 {
        let constant = self.constant.map_or(F64::ZERO, |c| F64(c.value[0]));
        self.terms.iter().fold(constant, |acc, (coeff, c)| {
            let v = cell(*c as usize);
            acc + if coeff.is_one() { v } else { F64(coeff.value[0]) * v }
        })
    }
}

/// A formula of degree at most 2 in a row's cells: a linear form plus products of two linear forms.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Formula {
    pub lin: Lin,
    pub products: Vec<(Coeff, Lin, Lin)>,
}

impl Formula {
    /// The formula of a constant slot (its push is `κ`): zero.
    pub fn zero() -> Self {
        Self::default()
    }

    pub fn linear(lin: Lin) -> Self {
        Self { lin, products: vec![] }
    }

    pub fn cell(c: usize) -> Self {
        Self::linear(Lin::cell(c))
    }

    pub fn plus_product(mut self, coeff: Coeff, a: Lin, b: Lin) -> Self {
        self.products.push((coeff, a, b));
        self
    }

    /// Every cell it reads.
    pub fn cells(&self) -> Vec<usize> {
        let mut out: Vec<usize> = self.lin.cells().collect();
        for (_, a, b) in &self.products {
            out.extend(a.cells().chain(b.cells()));
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    /// Its coefficients are in `K`: it pushes a `K` value, as an internal push must.
    pub fn is_base(&self) -> bool {
        self.lin.is_base()
            && self
                .products
                .iter()
                .all(|(c, a, b)| c.is_base() && a.is_base() && b.is_base())
    }

    pub fn eval(&self, cell: &dyn Fn(usize) -> F192, gammas: &[F192]) -> F192 {
        self.products
            .iter()
            .fold(self.lin.eval(cell, gammas), |acc, (c, a, b)| {
                acc + c.eval(gammas) * a.eval(cell, gammas) * b.eval(cell, gammas)
            })
    }

    pub fn eval_k(&self, cell: &dyn Fn(usize) -> F64) -> F64 {
        self.products.iter().fold(self.lin.eval_k(cell), |acc, (c, a, b)| {
            let p = a.eval_k(cell) * b.eval_k(cell);
            acc + if c.is_one() { p } else { F64(c.value[0]) * p }
        })
    }
}

/// A (region block, role) pair: the positions of role `role` in rows `first_row .. first_row + 2^log_rows`, an aligned
/// block (`first_row` a multiple of `2^log_rows`). Their pushes are `formulas[formula]` of their row. If `pulls` is
/// false they pull nothing (their pushes go outside, their values are read by no formula).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Pair {
    pub first_row: usize,
    pub log_rows: usize,
    pub role: usize,
    pub formula: usize,
    pub pulls: bool,
}

/// How a public scalar is read from the stream (after the public input's four words, which the seed hashes).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Read {
    /// An integer of this many bytes, big-endian (`Channel::next_integer`): one scalar.
    Integer(u8),
    /// A root: its two 16-byte halves, two scalars (`Channel::next_root`).
    Root,
    /// A 24-byte element of `E`: one scalar.
    Scalar,
}

impl Read {
    pub fn scalars(self) -> usize {
        match self {
            Read::Root => 2,
            _ => 1,
        }
    }

    pub fn bytes(self) -> usize {
        match self {
            Read::Integer(b) => b as usize,
            Read::Root => 32,
            Read::Scalar => 24,
        }
    }
}

/// One term of the public side: the verifier adds `1/(α + F + β ω_tag)`, `F = value` on the public scalars.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PublicTerm {
    pub tag: u32,
    pub value: Lin,
}

/// The circuit: what the setup commits (`σ`, `κ`) and what the verifier's code is built from (the pairs, the
/// formulas, the public side).
#[derive(Clone, Debug)]
pub struct Circuit {
    pub log_n: usize,
    pub log_row: usize,
    pub formulas: Vec<Formula>,
    pub pairs: Vec<Pair>,
    /// Each position's push tag, an index: the tag is `ω_sigma[i]`.
    pub sigma: Vec<u32>,
    pub kappa: Vec<F64>,
    pub reads: Vec<Read>,
    pub public: Vec<PublicTerm>,
}

/// No pair: the position is a forward.
pub const NONE: u32 = u32::MAX;

impl Circuit {
    pub fn n(&self) -> usize {
        1 << self.log_n
    }

    pub fn width(&self) -> usize {
        1 << self.log_row
    }

    pub fn rows(&self) -> usize {
        self.n() >> self.log_row
    }

    /// The public scalars: the public input's four words, then the reads.
    pub fn public_scalars(&self) -> usize {
        4 + self.reads.iter().map(|r| r.scalars()).sum::<usize>()
    }

    /// The pair covering each position, or [`NONE`].
    pub fn pair_of(&self) -> Vec<u32> {
        let mut out = vec![NONE; self.n()];
        for (p, pair) in self.pairs.iter().enumerate() {
            for y in pair.first_row..pair.first_row + (1 << pair.log_rows) {
                let i = (y << self.log_row) + pair.role;
                assert_eq!(out[i], NONE, "position {i} in two pairs");
                out[i] = p as u32;
            }
        }
        out
    }

    /// Whether each position pulls.
    pub fn pulls(&self) -> Vec<bool> {
        let mut out = vec![true; self.n()];
        for pair in self.pairs.iter().filter(|p| !p.pulls) {
            for y in pair.first_row..pair.first_row + (1 << pair.log_rows) {
                out[(y << self.log_row) + pair.role] = false;
            }
        }
        out
    }

    /// Every position's push value `P(ω_i)`, for the witness `w` and the challenge `γ`.
    pub fn pushes(&self, w: &[F64], gamma: F192) -> Vec<F192> {
        assert_eq!(w.len(), self.n());
        let gammas = gamma_powers(gamma, self.max_gamma());
        let pair_of = self.pair_of();
        let width = self.width();
        parallel::map_collect(self.n(), |i| {
            let base = i & !(width - 1);
            let own = match pair_of[i] {
                NONE => F192::from(w[i]),
                p => {
                    let formula = &self.formulas[self.pairs[p as usize].formula];
                    if formula.is_base() {
                        F192::from(formula.eval_k(&|c| w[base + c]))
                    } else {
                        formula.eval(&|c| F192::from(w[base + c]), &gammas)
                    }
                }
            };
            own + F192::from(self.kappa[i])
        })
    }

    /// The highest power of `γ` a coefficient takes.
    pub fn max_gamma(&self) -> usize {
        let lin = |l: &Lin| {
            l.terms
                .iter()
                .map(|(c, _)| c.gamma)
                .chain(l.constant.map(|c| c.gamma))
                .max()
                .unwrap_or(0)
        };
        let formulas = self.formulas.iter().map(|f| {
            f.products
                .iter()
                .map(|(c, a, b)| c.gamma + lin(a) + lin(b))
                .chain([lin(&f.lin)])
                .max()
                .unwrap_or(0)
        });
        formulas
            .chain(self.public.iter().map(|t| lin(&t.value)))
            .max()
            .unwrap_or(0) as usize
    }

    /// The values `F_J` of the public side, from the public scalars.
    pub fn public_values(&self, public: &[F192], gamma: F192) -> Vec<F192> {
        assert_eq!(public.len(), self.public_scalars());
        let gammas = gamma_powers(gamma, self.max_gamma());
        self.public
            .iter()
            .map(|t| t.value.eval(&|c| public[c], &gammas))
            .collect()
    }

    /// The structure the protocol assumes: sizes, aligned pairs on distinct positions, formulas of degree 2 reading
    /// their row (internal pushes in `K`), distinct push tags, an outside push for every pull-less position and a
    /// public term for every outside push, no formula reading a pull-less position's value, and `κ` zero off the
    /// expression slots (pulling pairs). `Spec::of` and `Setup::new` assert it (REVIEW-REC.md L1): a formula reading
    /// a hole would be unconstrained.
    pub fn validate(&self) -> Result<(), String> {
        let (n, width) = (self.n(), self.width());
        if self.sigma.len() != n || self.kappa.len() != n {
            return Err("σ and κ are N long".into());
        }
        if self.log_n + 3 > TAG_BITS || self.log_n < self.log_row + 1 {
            return Err(format!("2^{} positions", self.log_n));
        }
        for (p, pair) in self.pairs.iter().enumerate() {
            if pair.role >= width
                || pair.formula >= self.formulas.len()
                || !pair.first_row.is_multiple_of(1 << pair.log_rows)
                || pair.first_row + (1 << pair.log_rows) > self.rows()
            {
                return Err(format!("pair {p}: {pair:?}"));
            }
        }
        for (f, formula) in self.formulas.iter().enumerate() {
            if formula.cells().iter().any(|&c| c >= width) {
                return Err(format!("formula {f} reads past the row"));
            }
        }
        let pair_of = self.pair_of();
        let pulls = self.pulls();
        for (i, k) in self.kappa.iter().enumerate() {
            if *k != F64::ZERO && (pair_of[i] == NONE || !self.pairs[pair_of[i] as usize].pulls) {
                return Err(format!("κ at position {i}, not an expression slot"));
            }
        }
        let mut pushed = vec![false; n];
        let mut outside = vec![];
        for i in 0..n {
            let tag = self.sigma[i] as usize;
            let inside = tag < n;
            if tag >> TAG_BITS != 0 || (inside && std::mem::replace(&mut pushed[tag], true)) {
                return Err(format!("position {i}: tag {tag} out of range or pushed twice"));
            }
            if !inside {
                outside.push(tag);
            }
            if !pulls[i] && inside {
                return Err(format!("pull-less position {i} pushes inside"));
            }
            if inside && pair_of[i] != NONE && !self.formulas[self.pairs[pair_of[i] as usize].formula].is_base() {
                return Err(format!("position {i} pushes an E value inside"));
            }
            if inside && !pulls[tag] {
                return Err(format!("position {i} pushes to the pull-less position {tag}"));
            }
        }
        if (0..n).filter(|&i| !pulls[i]).count() != outside.len() {
            return Err("pull-less positions and outside pushes differ in number".into());
        }
        let mut terms: Vec<usize> = self.public.iter().map(|t| t.tag as usize).collect();
        terms.sort_unstable();
        outside.sort_unstable();
        if terms != outside || terms.windows(2).any(|w| w[0] == w[1]) {
            return Err("the public terms' tags are not the outside pushes', once each".into());
        }
        for y in 0..self.rows() {
            let row = y << self.log_row;
            let pull_less: Vec<usize> = (0..width).filter(|&k| !pulls[row + k]).collect();
            if pull_less.is_empty() {
                continue;
            }
            for k in 0..width {
                if pair_of[row + k] != NONE {
                    let cells = self.formulas[self.pairs[pair_of[row + k] as usize].formula].cells();
                    if let Some(c) = cells.iter().find(|c| pull_less.contains(c)) {
                        return Err(format!("row {y}: role {k}'s formula reads the pull-less cell {c}"));
                    }
                }
            }
        }
        Ok(())
    }

    /// The witness `w` satisfies the circuit with these public scalars: every pull is the push sent to it, and every
    /// outside push is its public term's value (at the challenge `γ`).
    pub fn check(&self, w: &[F64], public: &[F192], gamma: F192) -> Result<(), String> {
        self.validate()?;
        let pushes = self.pushes(w, gamma);
        let n = self.n();
        let values: std::collections::HashMap<u32, F192> = self
            .public
            .iter()
            .zip(self.public_values(public, gamma))
            .map(|(t, v)| (t.tag, v))
            .collect();
        for i in 0..n {
            let tag = self.sigma[i];
            let expected = if (tag as usize) < n {
                F192::from(w[tag as usize])
            } else {
                values[&tag]
            };
            if pushes[i] != expected {
                return Err(format!(
                    "position {i} pushes {:?} to tag {tag}, which holds {:?}",
                    pushes[i], expected
                ));
            }
        }
        Ok(())
    }

    /// Keccak-256 of the circuit's encoding: what the transcript's IV binds.
    pub fn digest(&self) -> [u8; 32] {
        let mut bytes = Vec::new();
        let put = |bytes: &mut Vec<u8>, n: u64| bytes.extend_from_slice(&n.to_le_bytes());
        let coeff = |bytes: &mut Vec<u8>, c: &Coeff| {
            c.value.iter().for_each(|&l| put(bytes, l));
            put(bytes, c.gamma as u64);
        };
        let lin = |bytes: &mut Vec<u8>, l: &Lin| {
            put(bytes, l.terms.len() as u64);
            for (c, cell) in &l.terms {
                coeff(bytes, c);
                put(bytes, *cell as u64);
            }
            match &l.constant {
                None => put(bytes, 0),
                Some(c) => {
                    put(bytes, 1);
                    coeff(bytes, c);
                }
            }
        };
        put(&mut bytes, self.log_n as u64);
        put(&mut bytes, self.log_row as u64);
        put(&mut bytes, self.formulas.len() as u64);
        for f in &self.formulas {
            lin(&mut bytes, &f.lin);
            put(&mut bytes, f.products.len() as u64);
            for (c, a, b) in &f.products {
                coeff(&mut bytes, c);
                lin(&mut bytes, a);
                lin(&mut bytes, b);
            }
        }
        put(&mut bytes, self.pairs.len() as u64);
        for p in &self.pairs {
            for v in [p.first_row, p.log_rows, p.role, p.formula, p.pulls as usize] {
                put(&mut bytes, v as u64);
            }
        }
        put(&mut bytes, self.reads.len() as u64);
        for r in &self.reads {
            let (kind, len) = match r {
                Read::Integer(b) => (0, *b as u64),
                Read::Root => (1, 32),
                Read::Scalar => (2, 24),
            };
            put(&mut bytes, kind);
            put(&mut bytes, len);
        }
        put(&mut bytes, self.public.len() as u64);
        for t in &self.public {
            put(&mut bytes, t.tag as u64);
            lin(&mut bytes, &t.value);
        }
        let sigma: Vec<u8> = self.sigma.iter().flat_map(|s| s.to_le_bytes()).collect();
        let kappa: Vec<u8> = self.kappa.iter().flat_map(|k| k.0.to_le_bytes()).collect();
        bytes.extend_from_slice(&primitives::hash::hash(&sigma));
        bytes.extend_from_slice(&primitives::hash::hash(&kappa));
        primitives::hash::hash(&bytes)
    }
}

/// `[1, γ, γ², …]`, up to `γ^max`.
pub fn gamma_powers(gamma: F192, max: usize) -> Vec<F192> {
    primitives::field::powers(gamma, max + 1)
}

/// The vanishing polynomials of the blocks' role cosets: for `U_s = span(β_r, …, β_{r+s-1})` (`r = log_row`),
/// `Z_{U_s}(x) = Z_{U_{s-1}}(x)^2 + e_s Z_{U_{s-1}}(x)` with `e_s = Z_{U_{s-1}}(β_{r+s-1})` and `Z_{U_0}(x) = x`.
/// Returns `e_1 … e_count`.
pub fn coset_constants(log_row: usize, count: usize) -> Vec<F64> {
    let mut e = Vec::with_capacity(count);
    for s in 1..=count {
        e.push(vanishing(beta()[log_row + s - 1], &e, s - 1));
    }
    e
}

/// `Z_{U_s}(x)`, from [`coset_constants`].
pub fn vanishing(x: F64, e: &[F64], s: usize) -> F64 {
    (0..s).fold(x, |z, j| z.square() + e[j] * z)
}

/// A pair's constants: its coset's base `c = ω_{first_row · 2^r + role}` and `Z_{U_s}(c)`, and the indicator's
/// normalisation `Π_{j ≤ s} e_j`, so that `I_p(x) = Z_V(x) · norm / (Z_{U_s}(x) + Z_{U_s}(c))` (SPEC-REC.md §2.3:
/// the product over `V \ U_s` is `lin(Z_V) / lin(Z_{U_s})`, the ratio of the linear coefficients, `1 / Π e_j`).
pub fn pair_constants(pair: &Pair, log_row: usize, e: &[F64]) -> (F64, F64) {
    let base = point((pair.first_row << log_row) + pair.role);
    let norm = e[..pair.log_rows].iter().fold(F64::ONE, |acc, &x| acc * x);
    (vanishing(base, e, pair.log_rows), norm)
}

#[cfg(test)]
mod tests {
    use super::*;
    use quotient::domain::chain;

    /// A pair's indicator is one on its coset and zero on the rest of `V_m`, at every block size and alignment.
    #[test]
    fn indicators_select_their_cosets() {
        let (m, r) = (10, 4);
        let e = coset_constants(r, m - r);
        for (first_row, log_rows, role) in [(0, 0, 0), (8, 3, 5), (16, 4, 15), (0, 6, 9), (37, 0, 3), (48, 4, 0)] {
            let pair = Pair {
                first_row,
                log_rows,
                role,
                formula: 0,
                pulls: true,
            };
            let (z, norm) = pair_constants(&pair, r, &e);
            for i in 0..1usize << m {
                let x = point(i);
                let zv = chain(x, m + 1)[m];
                assert!(zv.is_zero());
                // On V_m the indicator is the limit of Z_V/(Z_U(x) + z): evaluate it off V_m, at x + δ, and on V_m by
                // its defining product instead.
                let den = vanishing(x, &e, log_rows) + z;
                let inside = (i >> r) >= first_row && (i >> r) < first_row + (1 << log_rows) && i % (1 << r) == role;
                assert_eq!(den.is_zero(), inside, "pair {pair:?} at {i}");
            }
            // Off V_m: the indicator equals the product over V_m minus the coset, normalised.
            let off = beta()[m + 1] + point(5);
            let zv = chain(off, m + 1)[m];
            let direct = (0..1usize << m)
                .filter(|&i| !((i >> r) >= first_row && (i >> r) < first_row + (1 << log_rows) && i % (1 << r) == role))
                .fold(F64::ONE, |acc, i| acc * (off + point(i)));
            let on_coset = (0..1usize << m)
                .filter(|&i| !((i >> r) >= first_row && (i >> r) < first_row + (1 << log_rows) && i % (1 << r) == role))
                .fold(F64::ONE, |acc, i| acc * (point((first_row << r) + role) + point(i)));
            assert_eq!(
                direct * on_coset.inv(),
                zv * norm * (vanishing(off, &e, log_rows) + z).inv()
            );
        }
    }
}
