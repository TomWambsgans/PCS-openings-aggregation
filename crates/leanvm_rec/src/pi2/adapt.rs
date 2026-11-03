// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The circuit compiler's description (`crate::circuit::spec`, the PIOP-facing interface) as the PIOP's
//! [`Circuit`], and its public inputs as the stream's public data.
//!
//! - Every (block, role) pair whose formula is not a forward is a [`Pair`]; a `Port` pair pulls nothing (its
//!   positions are the holes: `PI2.md` §1 explains why the PIOP leaves the holes' pulls out of the copy argument
//!   instead of adding the holes' sums `Σ 1/D(0, h)` to the target; [`adapt`] checks that no formula reads a hole).
//! - A port's push is a fingerprint of its limbs that the verifier evaluates from the public data as calldata carries
//!   it: three limbs (an element of `E`, a zero check) as `L_0 + Y L_1 + Y² L_2`, which is the element itself; four
//!   limbs (the statement, a root) as `(L_0 + Y L_1) + γ (L_2 + Y L_3)`, a root's two 16-byte halves. Both bind the
//!   limbs (the first is injective on `K³`, the second for all but one `γ`), as the interface's `Σ γ^l L_l` does: its
//!   `Circuit::check` compares the limbs.
//! - The public data: π1's roots (32 bytes each, as `PCS_OPEN`'s root words: each 16-byte half of the hash reversed,
//!   REVIEW-REC.md M1), then its claims' elements (24 bytes each); the statement is the public input the seed hashes.

use leanvm_flock_gas::field::K;
use primitives::field::{F64, F192};

use super::circuit::{Circuit, Coeff, Formula, Lin, Pair, PublicTerm, Read};
use super::prover::PublicValue;
use crate::circuit::spec;

/// The fingerprint of a port's limbs, on the cells `limbs` (see the module's description).
pub fn port_formula(limbs: &[u8]) -> Formula {
    let y = Coeff::e(F192::Y);
    let coeffs = match limbs.len() {
        3 => vec![Coeff::ONE, y, Coeff::e(F192::Y * F192::Y)],
        4 => vec![Coeff::ONE, y, Coeff::gamma(1), Coeff { gamma: 1, ..y }],
        n => panic!("a port of {n} limbs"),
    };
    Formula::linear(Lin {
        terms: coeffs.into_iter().zip(limbs.iter().map(|&c| c as u16)).collect(),
        constant: None,
    })
}

fn expr(poly: &spec::Poly) -> Formula {
    let mut f = Formula::default();
    for &(c, k) in &poly.linear {
        f.lin.terms.push((Coeff::k(k.0), c as u16));
    }
    for &(a, b, k) in &poly.quadratic {
        f.products
            .push((Coeff::k(k.0), Lin::cell(a as usize), Lin::cell(b as usize)));
    }
    f
}

/// How many roots and elements the public inputs hold: one past the largest index the ports and the calls name.
pub fn public_counts(c: &spec::Circuit) -> (usize, usize) {
    let (mut roots, mut elements) = (0, 0);
    let mut see = |root: Option<u32>, element: Option<u32>| {
        if let Some(i) = root {
            roots = roots.max(i as usize + 1);
        }
        if let Some(i) = element {
            elements = elements.max(i as usize + 1);
        }
    };
    for p in &c.ports {
        match p.source {
            spec::Source::Root(i) => see(Some(i), None),
            spec::Source::Element(i) => see(None, Some(i)),
            _ => {}
        }
    }
    for w in c.calls.iter().flatten() {
        match *w {
            spec::CallWord::Root(i) => see(Some(i), None),
            spec::CallWord::Element(i) => see(None, Some(i)),
            spec::CallWord::Const(_) => {}
        }
    }
    (roots, elements)
}

/// The PIOP's circuit of the interface's. Panics if a formula reads a hole (a port's own cell), which the PIOP's
/// pull-less holes would leave unconstrained.
pub fn adapt(c: &spec::Circuit) -> Circuit {
    let (n, width) = (c.n(), c.width());
    let mut formulas: Vec<Formula> = vec![];
    let mut pairs = vec![];
    for (r, region) in c.regions.iter().enumerate() {
        let holes: Vec<usize> = (0..width)
            .filter(|&k| matches!(region.roles[k], spec::Formula::Port(_)))
            .collect();
        for (k, f) in region.roles.iter().enumerate() {
            if let Some(&h) = f.reads().iter().find(|&&cell| holes.contains(&(cell as usize))) {
                panic!("region {}: role {k} reads the hole {h}", region.name);
            }
        }
        let _ = r;
    }
    let id = |f: Formula, formulas: &mut Vec<Formula>| match formulas.iter().position(|g| *g == f) {
        Some(i) => i,
        None => {
            formulas.push(f);
            formulas.len() - 1
        }
    };
    for block in &c.blocks {
        let region = &c.regions[block.region as usize];
        for (k, f) in region.roles.iter().enumerate() {
            let (formula, pulls) = match f {
                spec::Formula::Forward => continue,
                spec::Formula::Expr(p) => (expr(p), true),
                spec::Formula::Port(limbs) => (port_formula(limbs), false),
            };
            pairs.push(Pair {
                first_row: block.row as usize,
                log_rows: block.log_rows as usize,
                role: k,
                formula: id(formula, &mut formulas),
                pulls,
            });
        }
    }
    let (roots, elements) = public_counts(c);
    let reads = [vec![Read::Root; roots], vec![Read::Scalar; elements]].concat();
    let element_at = |i: u32| (4 + 2 * roots + i as usize) as u16;
    let y = Coeff::e(F192::Y);
    let public = c
        .ports
        .iter()
        .enumerate()
        .map(|(j, p)| {
            let terms = match p.source {
                // (S_0 + Y S_1) + γ (S_2 + Y S_3), the statement's words the scalars 0..4.
                spec::Source::Statement => vec![
                    (Coeff::ONE, 0),
                    (y, 1),
                    (Coeff::gamma(1), 2),
                    (Coeff { gamma: 1, ..y }, 3),
                ],
                // A root's halves are bytes 0..16 (L_3, L_2) and 16..32 (L_1, L_0): half 1 + γ half 0.
                spec::Source::Root(i) => vec![(Coeff::ONE, 4 + 2 * i as u16 + 1), (Coeff::gamma(1), 4 + 2 * i as u16)],
                spec::Source::Element(i) => vec![(Coeff::ONE, element_at(i))],
                spec::Source::Zero | spec::Source::Pad => vec![],
            };
            PublicTerm {
                tag: (n + j) as u32,
                value: Lin { terms, constant: None },
            }
        })
        .collect();
    let mut kappa = vec![F64::ZERO; n];
    for &(i, k) in &c.kappa {
        kappa[i as usize] = F64(k.0);
    }
    Circuit {
        log_n: c.log_n as usize,
        log_row: c.log_width as usize,
        formulas,
        pairs,
        sigma: c.sigma.clone(),
        kappa,
        reads,
        public,
    }
}

/// The witness in the prover's field.
pub fn witness(w: &[K]) -> Vec<F64> {
    w.iter().map(|k| F64(k.0)).collect()
}

/// The public input and the stream's public values (the roots as root words, then the elements).
pub fn public_values(public: &spec::PublicInputs) -> ([u8; 32], Vec<PublicValue>) {
    let values = public
        .roots
        .iter()
        .map(|&r| PublicValue::Root(r))
        .chain(
            public
                .elements
                .iter()
                .map(|x| PublicValue::Scalar(F192::new(x.c0, x.c1, x.c2))),
        )
        .collect();
    (public.statement, values)
}
