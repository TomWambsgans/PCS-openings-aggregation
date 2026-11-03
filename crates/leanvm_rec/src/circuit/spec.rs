// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! `π2`'s circuit as its PIOP sees it (SPEC-REC.md §2.3, §2.4, §2.6): the interface between the circuit compiler
//! (`crate::circuit`) and `π2`'s prover and verifier (branch `leanvm-rec-piop`). Kept small and stable.
//!
//! **Positions.** `N = 2^log_n` positions `i = W·y + k`: row `y`, role `k < W`, rows of `W = 2^log_width`
//! positions. `log_width = 4` is D16v (§2.4), `log_width = 5` is D32v (§2.6). The witness `w` is one `K` word a
//! position ([`Witness`]).
//!
//! **Pulls and pushes.** Every position `i` has a pull `(w_i, i)` and a push `(P_i, σ_i)`, with
//! `P_i = F_i + κ_i`:
//! - `F_i` is the [`Formula`] of `i`'s role in the region of the [`Block`] holding `i`'s row, evaluated on the row's
//!   `W` pulls (`cells[c] = w_(W·y + c)`). A row in no block is all [`Formula::Forward`].
//!   - `Forward`: `F_i = w_i`.
//!   - `Expr(p)`: `F_i = p(cells)`, a polynomial of degree ≤ 2 with coefficients in `K` and no constant term.
//!   - `Port(limbs)`: `F_i = Σ_l γ^l · cells[limbs[l]]`, with `γ` a challenge of the PIOP (drawn after `w`).
//! - `κ` (setup) is zero except at `Expr` positions ([`Circuit::kappa`], sparse).
//! - `σ_i` (setup) is a **tag index**: a position `< N`, or `N + J`, the outside tag of port `J`. The PIOP maps a
//!   tag index `j` to its field element `ω(j)` (the Cantor enumeration); outside tags are `ω(N + J) ∉ V_m`.
//!
//! **What holds for an accepted witness** ([`Circuit::check`]):
//! 1. `σ` is injective. Its image is every position but the **holes**, plus the ports' tags. The holes are exactly
//!    the ports' positions, and port `J` (`ports[J]`) pushes to `N + J`.
//! 2. Every push to a position equals that position's pull: `w_(σ_i) = P_i` whenever `σ_i < N`.
//! 3. Every hole's pull is `0`.
//! 4. Port `J`'s push is the public fingerprint `F_J = Σ_l γ^l · L_(J,l)`, the limbs `L_J` given by the public
//!    inputs ([`Circuit::public_limbs`]). The check compares the limbs, which is the fingerprint for every `γ`.
//!
//! **The copy argument** this is (SPEC-REC §2.3): with `D(v, τ) = α + v + β·ω(τ)`, (1)–(4) give, in characteristic 2,
//!
//! `Σ_(i<N) [1/D(w_i, i) + 1/D(P_i, σ_i)] = Σ_J 1/D(F_J, N + J) + Σ_(holes h) 1/D(0, h)`.
//!
//! The holes are cosets ([`Circuit::hole_cosets`]): the role-`k` positions of a block of `2^s` aligned rows starting
//! at row `y0`, that is `ω(W·y0 + k) + span(β_log_width, …, β_(log_width + s − 1))`. Their sum has a closed form
//! (`Σ_(u∈U) 1/(X + u) = Z_U'/Z_U(X)`, `Z_U'` the product of `U`'s nonzero elements).
//!
//! **The selectors.** A (block, role) pair whose formula is not `Forward` is one indicator `I_(b,k)` for the PIOP
//! ([`Circuit::pairs`]): `P = w + Σ_(b,k) I_(b,k)·(F_(b,k) − w) + κ`.
//!
//! **The public side.** [`PublicInputs`] are `π1`'s statement (32 bytes), its commitments' roots and its claims'
//! distinct elements. Each port's [`Source`] says which; [`Circuit::calls`] rebuilds `π1`'s `PCS_OPEN` inputs from
//! them, as `π2`'s contract will (`machine.rs`'s ABI: 32-byte words).

use leanvm_flock_gas::field::{E, K};

/// The witness: one `K` word a position, `N` of them.
pub type Witness = Vec<K>;

/// A polynomial of degree ≤ 2 in a row's cells, coefficients in `K`, no constant term (constants are `κ`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Poly {
    /// `(cell, coefficient)`.
    pub linear: Vec<(u8, K)>,
    /// `(cell a, cell b, coefficient)`, `a ≤ b`; `a = b` is a square.
    pub quadratic: Vec<(u8, u8, K)>,
}

impl Poly {
    /// Evaluate on a row's cells, over `K` (the witness) or `E` (the verifier at `t`).
    pub fn eval<F>(&self, cells: &[F]) -> F
    where
        F: Copy + Default + std::ops::Add<Output = F> + std::ops::Mul<Output = F> + From<K>,
    {
        let mut out = F::default();
        for &(c, k) in &self.linear {
            out = out + F::from(k) * cells[c as usize];
        }
        for &(a, b, k) in &self.quadratic {
            out = out + F::from(k) * cells[a as usize] * cells[b as usize];
        }
        out
    }

    /// The cells it reads.
    pub fn reads(&self) -> impl Iterator<Item = u8> + '_ {
        self.linear
            .iter()
            .map(|&(c, _)| c)
            .chain(self.quadratic.iter().flat_map(|&(a, b, _)| [a, b]))
    }
}

static FORWARD: Formula = Formula::Forward;

/// What a role pushes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    /// Its own pull.
    Forward,
    /// A polynomial of degree ≤ 2 in the row's cells (an expression slot).
    Expr(Poly),
    /// `Σ_l γ^l · cells[limbs[l]]`, to its port's outside tag; the position is a hole.
    Port(Vec<u8>),
}

impl Formula {
    /// The push's formula part `F_i` (no `κ`), given the row's cells, the position's own pull and `γ`.
    pub fn eval<F>(&self, cells: &[F], own: F, gamma: F) -> F
    where
        F: Copy + Default + std::ops::Add<Output = F> + std::ops::Mul<Output = F> + From<K>,
    {
        match self {
            Formula::Forward => own,
            Formula::Expr(p) => p.eval(cells),
            Formula::Port(limbs) => {
                let (mut out, mut power) = (F::default(), F::from(K(1)));
                for &c in limbs {
                    out = out + power * cells[c as usize];
                    power = power * gamma;
                }
                out
            }
        }
    }

    /// The cells it reads (a forward reads none: its push is its pull).
    pub fn reads(&self) -> Vec<u8> {
        match self {
            Formula::Forward => vec![],
            Formula::Expr(p) => p.reads().collect(),
            Formula::Port(limbs) => limbs.clone(),
        }
    }
}

/// A row type: the formula of each of its `W` roles.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Region {
    pub name: String,
    pub roles: Vec<Formula>,
}

/// `2^log_rows` rows of one region, starting at row `row`, a multiple of `2^log_rows`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Block {
    pub row: u32,
    pub log_rows: u8,
    pub region: u16,
}

/// Where a port's limbs come from in the [`PublicInputs`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Source {
    /// The statement's four 64-bit words, big-endian, word `l` (bytes `8l..8l+8`) limb `l`.
    Statement,
    /// Root `i`'s 32 bytes as four big-endian words, bytes `24−8l..32−8l` limb `l` (as [`word_limbs`]).
    Root(u32),
    /// Element `i`: its limbs `c0, c1, c2`.
    Element(u32),
    /// A check of `π1`'s verifier: three zero limbs.
    Zero,
}

impl Source {
    pub fn limbs(self) -> usize {
        match self {
            Source::Statement | Source::Root(_) => 4,
            Source::Element(_) | Source::Zero => 3,
        }
    }
}

/// A port: a hole whose push leaves the domain, to the outside tag `N + J` of its index `J` in [`Circuit::ports`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Port {
    pub position: u32,
    pub source: Source,
}

/// A 32-byte word of one of `π1`'s `PCS_OPEN` inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallWord {
    Const([u8; 32]),
    Root(u32),
    /// An element, as `machine::element_word`: `c2, c1, c0` big-endian in bytes `8..32`.
    Element(u32),
}

/// `π2`'s public inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicInputs {
    /// `π1`'s public input.
    pub statement: [u8; 32],
    /// `π1`'s commitments' roots, in stream order (`C1`, `C2`).
    pub roots: Vec<[u8; 32]>,
    /// `π1`'s claims' distinct elements (coordinates, values), in first appearance in the calls.
    pub elements: Vec<E>,
}

/// A 32-byte word's four limbs, limb `l` the big-endian `u64` of bytes `24−8l..32−8l` (an element word's fourth limb
/// is zero).
pub fn word_limbs(word: &[u8; 32]) -> [u64; 4] {
    std::array::from_fn(|l| u64::from_be_bytes(word[24 - 8 * l..32 - 8 * l].try_into().expect("8 bytes")))
}

/// The word of an element: `element_word`'s bytes.
pub fn element_word(x: E) -> [u8; 32] {
    let mut w = [0u8; 32];
    w[8..16].copy_from_slice(&x.c2.to_be_bytes());
    w[16..24].copy_from_slice(&x.c1.to_be_bytes());
    w[24..32].copy_from_slice(&x.c0.to_be_bytes());
    w
}

/// `Σ_l γ^l · limbs[l]`.
pub fn fingerprint(limbs: &[u64], gamma: E) -> E {
    let (mut out, mut power) = (E::default(), E::from(K(1)));
    for &l in limbs {
        out += power * E::from(K(l));
        power *= gamma;
    }
    out
}

/// `π2`'s circuit: the layout, the setup columns, the public side.
#[derive(Clone, Debug)]
pub struct Circuit {
    pub log_n: u8,
    pub log_width: u8,
    pub regions: Vec<Region>,
    /// Aligned, disjoint; rows in none are all forwards.
    pub blocks: Vec<Block>,
    /// The push's tag index, a position `< N` or `N + J`.
    pub sigma: Vec<u32>,
    /// `κ ≠ 0` at these positions (increasing), all of them `Expr` positions.
    pub kappa: Vec<(u32, K)>,
    /// Port `J`'s outside tag is `N + J`. In block order: block by block, row by row, role by role.
    pub ports: Vec<Port>,
    /// `π1`'s `PCS_OPEN` inputs, in call order.
    pub calls: Vec<Vec<CallWord>>,
}

/// Why a witness is not accepted (the first failure found).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Failure {
    Shape(String),
    /// Position `i`'s push `P_i` is not its target `σ_i`'s pull.
    Push { position: u32, target: u32, push: K, pull: K },
    /// A hole's pull is not zero.
    Hole { position: u32 },
    /// Port `J`'s limb `l` is not the public one.
    Public { port: u32, limb: u32, circuit: K, public: K },
}

impl Circuit {
    pub fn n(&self) -> usize {
        1 << self.log_n
    }

    pub fn width(&self) -> usize {
        1 << self.log_width
    }

    /// Each row's region (`u16::MAX`: none, all forwards).
    pub fn row_regions(&self) -> Vec<u16> {
        let mut out = vec![u16::MAX; self.n() >> self.log_width];
        for b in &self.blocks {
            let start = b.row as usize;
            out[start..start + (1 << b.log_rows)].fill(b.region);
        }
        out
    }

    /// The formula of position `i`'s role (`row_regions` as computed once).
    pub fn formula<'a>(&'a self, row_regions: &[u16], i: usize) -> &'a Formula {
        match row_regions[i >> self.log_width] {
            u16::MAX => &FORWARD,
            r => &self.regions[r as usize].roles[i & (self.width() - 1)],
        }
    }

    /// The dense `κ` column.
    pub fn kappa_column(&self) -> Vec<K> {
        let mut out = vec![K(0); self.n()];
        for &(i, k) in &self.kappa {
            out[i as usize] = k;
        }
        out
    }

    /// The (block, role) pairs with a selector: every role of every block whose formula is not `Forward`.
    pub fn pairs(&self) -> Vec<(usize, u8)> {
        let mut out = Vec::new();
        for (b, block) in self.blocks.iter().enumerate() {
            for (k, f) in self.regions[block.region as usize].roles.iter().enumerate() {
                if *f != Formula::Forward {
                    out.push((b, k as u8));
                }
            }
        }
        out
    }

    /// The holes as cosets: `(first row, log rows, role)` for every port role of every block, in [`Circuit::ports`]
    /// order.
    pub fn hole_cosets(&self) -> Vec<(u32, u8, u8)> {
        let mut out = Vec::new();
        for block in &self.blocks {
            for (k, f) in self.regions[block.region as usize].roles.iter().enumerate() {
                if matches!(f, Formula::Port(_)) {
                    out.push((block.row, block.log_rows, k as u8));
                }
            }
        }
        out
    }

    /// Each port's limbs `L_J` from the public inputs.
    pub fn public_limbs(&self, public: &PublicInputs) -> Vec<Vec<u64>> {
        self.ports
            .iter()
            .map(|p| match p.source {
                Source::Statement => (0..4)
                    .map(|l| u64::from_be_bytes(public.statement[8 * l..8 * l + 8].try_into().expect("8 bytes")))
                    .collect(),
                Source::Root(i) => word_limbs(&public.roots[i as usize]).to_vec(),
                Source::Element(i) => {
                    let x = public.elements[i as usize];
                    vec![x.c0, x.c1, x.c2]
                }
                Source::Zero => vec![0; 3],
            })
            .collect()
    }

    /// The public fingerprints `F_J`.
    pub fn public_fingerprints(&self, public: &PublicInputs, gamma: E) -> Vec<E> {
        self.public_limbs(public).iter().map(|l| fingerprint(l, gamma)).collect()
    }

    /// `π1`'s `PCS_OPEN` inputs from the public inputs.
    pub fn call_inputs(&self, public: &PublicInputs) -> Vec<Vec<u8>> {
        self.calls
            .iter()
            .map(|words| {
                words
                    .iter()
                    .flat_map(|w| match *w {
                        CallWord::Const(bytes) => bytes,
                        CallWord::Root(i) => public.roots[i as usize],
                        CallWord::Element(i) => element_word(public.elements[i as usize]),
                    })
                    .collect()
            })
            .collect()
    }

    /// The public inputs that give these `PCS_OPEN` inputs (`None` if they are not of the calls' shape, or disagree
    /// on a repeated element).
    pub fn public_from_calls(&self, statement: [u8; 32], inputs: &[Vec<u8>]) -> Option<PublicInputs> {
        let roots_len = self.calls.iter().flatten().filter_map(|w| match w {
            CallWord::Root(i) => Some(*i as usize + 1),
            _ => None,
        });
        let elements_len = self.calls.iter().flatten().filter_map(|w| match w {
            CallWord::Element(i) => Some(*i as usize + 1),
            _ => None,
        });
        let mut roots: Vec<Option<[u8; 32]>> = vec![None; roots_len.max().unwrap_or(0)];
        let mut elements: Vec<Option<E>> = vec![None; elements_len.max().unwrap_or(0)];
        if inputs.len() != self.calls.len() {
            return None;
        }
        for (words, input) in self.calls.iter().zip(inputs) {
            if input.len() != 32 * words.len() {
                return None;
            }
            for (w, bytes) in words.iter().zip(input.as_chunks::<32>().0) {
                match *w {
                    CallWord::Const(c) if c != *bytes => return None,
                    CallWord::Const(_) => {}
                    CallWord::Root(i) => match roots[i as usize] {
                        Some(r) if r != *bytes => return None,
                        _ => roots[i as usize] = Some(*bytes),
                    },
                    CallWord::Element(i) => {
                        let l = word_limbs(bytes);
                        if l[3] != 0 {
                            return None;
                        }
                        let x = E::new(l[0], l[1], l[2]);
                        match elements[i as usize] {
                            Some(e) if e != x => return None,
                            _ => elements[i as usize] = Some(x),
                        }
                    }
                }
            }
        }
        Some(PublicInputs {
            statement,
            roots: roots.into_iter().collect::<Option<_>>()?,
            elements: elements.into_iter().collect::<Option<_>>()?,
        })
    }

    /// The layout's own consistency: blocks aligned, disjoint, in range; regions `W` roles wide; `σ` an injection
    /// whose image is every non-hole position and the ports' tags; `κ` on `Expr` positions only.
    pub fn check_shape(&self) -> Result<(), Failure> {
        let (n, w) = (self.n(), self.width());
        let bad = |s: String| Err(Failure::Shape(s));
        if self.sigma.len() != n {
            return bad(format!("σ has {} entries, N = {n}", self.sigma.len()));
        }
        for r in &self.regions {
            if r.roles.len() != w {
                return bad(format!("region {} has {} roles", r.name, r.roles.len()));
            }
            for f in &r.roles {
                if f.reads().iter().any(|&c| c as usize >= w) {
                    return bad(format!("region {} reads past the row", r.name));
                }
            }
        }
        let mut covered = vec![false; n / w];
        for b in &self.blocks {
            let (start, len) = (b.row as usize, 1usize << b.log_rows);
            if start % len != 0 || start + len > n / w || b.region as usize >= self.regions.len() {
                return bad(format!("block {b:?} is not aligned and in range"));
            }
            for c in &mut covered[start..start + len] {
                if std::mem::replace(c, true) {
                    return bad(format!("block {b:?} overlaps another"));
                }
            }
        }
        let row_regions = self.row_regions();
        let mut hole = vec![false; n];
        let mut port_positions = Vec::new();
        for b in &self.blocks {
            for y in b.row as usize..b.row as usize + (1 << b.log_rows) {
                for (k, f) in self.regions[b.region as usize].roles.iter().enumerate() {
                    if matches!(f, Formula::Port(_)) {
                        port_positions.push((y * w + k) as u32);
                        hole[y * w + k] = true;
                    }
                }
            }
        }
        if port_positions != self.ports.iter().map(|p| p.position).collect::<Vec<_>>() {
            return bad("the ports are not the Port roles' positions, in block order".into());
        }
        for (j, p) in self.ports.iter().enumerate() {
            let Formula::Port(limbs) = self.formula(&row_regions, p.position as usize) else {
                unreachable!()
            };
            if limbs.len() != p.source.limbs() {
                return bad(format!("port {j} has {} limbs, its source {}", limbs.len(), p.source.limbs()));
            }
        }
        let mut hit = vec![false; n + self.ports.len()];
        for (i, &s) in self.sigma.iter().enumerate() {
            let s = s as usize;
            let expected_outside = hole[i];
            if s >= n + self.ports.len() || (s >= n) != expected_outside {
                return bad(format!("σ({i}) = {s} is out of range or not its port's tag"));
            }
            if expected_outside && s != n + self.ports.iter().position(|p| p.position as usize == i).expect("a port") {
                return bad(format!("σ({i}) = {s} is not its port's tag"));
            }
            if std::mem::replace(&mut hit[s], true) {
                return bad(format!("σ is not injective at {s}"));
            }
        }
        if let Some(i) = (0..n).find(|&i| hit[i] == hole[i]) {
            return bad(format!("position {i} is a hole and pushed to, or neither"));
        }
        let mut last = None;
        for &(i, _) in &self.kappa {
            if last.is_some_and(|l| l >= i) || i as usize >= n {
                return bad("κ's positions are not increasing and in range".into());
            }
            last = Some(i);
            if !matches!(self.formula(&row_regions, i as usize), Formula::Expr(_)) {
                return bad(format!("κ at {i}, not an expression slot"));
            }
        }
        Ok(())
    }

    /// (1)–(4) of the module's description, directly.
    pub fn check(&self, w: &[K], public: &PublicInputs) -> Result<(), Failure> {
        self.check_shape()?;
        let (n, width) = (self.n(), self.width());
        if w.len() != n {
            return Err(Failure::Shape(format!("the witness has {} words, N = {n}", w.len())));
        }
        let row_regions = self.row_regions();
        let kappa = self.kappa_column();
        for (y, &region) in row_regions.iter().enumerate() {
            let cells = &w[y * width..(y + 1) * width];
            for k in 0..width {
                let i = y * width + k;
                let f = match region {
                    u16::MAX => &FORWARD,
                    r => &self.regions[r as usize].roles[k],
                };
                if matches!(f, Formula::Port(_)) {
                    if w[i] != K(0) {
                        return Err(Failure::Hole { position: i as u32 });
                    }
                    continue;
                }
                let push = f.eval(cells, w[i], K(0)) + kappa[i];
                let target = self.sigma[i] as usize;
                if w[target] != push {
                    return Err(Failure::Push {
                        position: i as u32,
                        target: target as u32,
                        push,
                        pull: w[target],
                    });
                }
            }
        }
        let limbs = self.public_limbs(public);
        for (j, (p, expected)) in self.ports.iter().zip(&limbs).enumerate() {
            let Formula::Port(cells) = self.formula(&row_regions, p.position as usize) else {
                unreachable!("checked by check_shape")
            };
            let row = p.position as usize & !(width - 1);
            for (l, (&c, &e)) in cells.iter().zip(expected).enumerate() {
                if w[row + c as usize] != K(e) {
                    return Err(Failure::Public {
                        port: j as u32,
                        limb: l as u32,
                        circuit: w[row + c as usize],
                        public: K(e),
                    });
                }
            }
        }
        Ok(())
    }
}

/// A toy circuit for the PIOP's tests: `N = 32`, `W = 16`, two rows. Row 0 (region `A`): a bit `w_0 = 1` on a
/// self-loop pushing `w_0²`; role 1 pushes `w_2·w_3 + κ_1` (`κ_1 = 4`) into row 1, and its own pull is a free end;
/// roles 2 and 3 forward a free value `6` to each other. Row 1 (region `P`): roles 0, 2, 4 are the port's limbs; role
/// 15 is the port (element 0). One call: a constant word, then element 0.
pub fn example() -> (Circuit, Witness, PublicInputs) {
    let fwd = || Formula::Forward;
    let mut a: Vec<Formula> = (0..16).map(|_| fwd()).collect();
    a[0] = Formula::Expr(Poly {
        linear: vec![],
        quadratic: vec![(0, 0, K(1))],
    });
    a[1] = Formula::Expr(Poly {
        linear: vec![],
        quadratic: vec![(2, 3, K(1))],
    });
    let mut p: Vec<Formula> = (0..16).map(|_| fwd()).collect();
    p[15] = Formula::Port(vec![0, 2, 4]);
    let mut sigma: Vec<u32> = (0..32).collect();
    sigma[1] = 16;
    sigma[16] = 17;
    sigma[17] = 1;
    sigma[2] = 3;
    sigma[3] = 2;
    sigma[31] = 32;
    let circuit = Circuit {
        log_n: 5,
        log_width: 4,
        regions: vec![
            Region {
                name: "A".into(),
                roles: a,
            },
            Region {
                name: "P".into(),
                roles: p,
            },
        ],
        blocks: vec![
            Block {
                row: 0,
                log_rows: 0,
                region: 0,
            },
            Block {
                row: 1,
                log_rows: 0,
                region: 1,
            },
        ],
        sigma,
        kappa: vec![(1, K(4))],
        ports: vec![Port {
            position: 31,
            source: Source::Element(0),
        }],
        calls: vec![vec![CallWord::Const([7; 32]), CallWord::Element(0)]],
    };
    let v = K(6) * K(6) + K(4);
    let mut w = vec![K(0); 32];
    w[0] = K(1);
    (w[1], w[16], w[17]) = (v, v, v);
    (w[2], w[3]) = (K(6), K(6));
    let public = PublicInputs {
        statement: [0; 32],
        roots: vec![],
        elements: vec![E::new(v.0, 0, 0)],
    };
    (circuit, w, public)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_example_holds_and_mutations_break_it() {
        let (c, w, public) = example();
        assert_eq!(c.check(&w, &public), Ok(()));
        assert_eq!(c.pairs(), vec![(0, 0), (0, 1), (1, 15)]);
        assert_eq!(c.hole_cosets(), vec![(1, 0, 15)]);
        let inputs = c.call_inputs(&public);
        assert_eq!(c.public_from_calls(public.statement, &inputs), Some(public.clone()));
        for i in [0usize, 1, 2, 16, 17, 31] {
            let mut bad = w.clone();
            bad[i] = bad[i] + K(1 << 9);
            assert!(c.check(&bad, &public).is_err(), "a change at {i} is caught");
        }
        let mut other = public.clone();
        other.elements[0] = E::new(1, 0, 0);
        assert!(matches!(c.check(&w, &other), Err(Failure::Public { .. })));
        let mut bad = c.clone();
        bad.sigma[2] = 4;
        assert!(matches!(bad.check(&w, &public), Err(Failure::Shape(_))));
    }
}
