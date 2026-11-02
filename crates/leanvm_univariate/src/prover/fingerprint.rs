// Part of this repository. The tuples are leanVM 42422001's (crates/verifier/src/layout.rs there, through
// `leanvm_flock_gas::layout`). MIT OR Apache-2.0; see NOTICE.md.
//! Bus fingerprints `β + Σ_s eq(α, s) τ_s` of a table's tuples, compiled once into a constant, linear terms and
//! products of two columns, to be evaluated at every row (or at every point of a coset) from the columns' values.

use leanvm_flock_gas::layout::Form;
use primitives::field::{F64, F192};

use super::poly::from_v;

/// `constant + Σ c x_i + Σ c x_i x_j` over a row's column values.
#[derive(Clone, Debug)]
pub struct Fingerprint {
    pub constant: F192,
    pub linear: Vec<(usize, F192)>,
    pub quadratic: Vec<(usize, usize, F192)>,
}

impl Fingerprint {
    /// `β + Σ_s weights[s] tuple[s]`.
    pub fn new(tuple: &[Form], weights: &[F192], beta: F192) -> Self {
        let mut out = Self {
            constant: beta,
            linear: Vec::new(),
            quadratic: Vec::new(),
        };
        for (form, &weight) in tuple.iter().zip(weights) {
            for (monomial, &coefficient) in form.terms() {
                let c = weight * from_v(coefficient);
                if c.is_zero() {
                    continue;
                }
                match *monomial {
                    [] => out.constant += c,
                    [i] => match out.linear.iter_mut().find(|(j, _)| *j == i) {
                        Some((_, e)) => *e += c,
                        None => out.linear.push((i, c)),
                    },
                    [i, j] => match out.quadratic.iter_mut().find(|(a, b, _)| (*a, *b) == (i, j)) {
                        Some((_, _, e)) => *e += c,
                        None => out.quadratic.push((i, j, c)),
                    },
                    _ => unreachable!("forms are of degree 2"),
                }
            }
        }
        out
    }

    /// At one row, its columns' values read by `col`.
    #[inline]
    pub fn at(&self, col: impl Fn(usize) -> F64) -> F192 {
        let mut acc = self.constant;
        for &(i, c) in &self.linear {
            acc += c.mul_base(col(i));
        }
        for &(i, j, c) in &self.quadratic {
            acc += c.mul_base(col(i) * col(j));
        }
        acc
    }

    /// At an extension point, its columns' values in `E`.
    #[inline]
    pub fn at_e(&self, col: impl Fn(usize) -> F192) -> F192 {
        let mut acc = self.constant;
        for &(i, c) in &self.linear {
            acc += c * col(i);
        }
        for &(i, j, c) in &self.quadratic {
            acc += c * col(i) * col(j);
        }
        acc
    }

    /// The columns it reads.
    pub fn columns(&self) -> Vec<usize> {
        let mut out: Vec<usize> = self.linear.iter().map(|&(i, _)| i).collect();
        for &(i, j, _) in &self.quadratic {
            out.extend([i, j]);
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}
