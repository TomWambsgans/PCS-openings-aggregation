// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Bus fingerprints on eight points at once (`quotient::ntt`'s lanes): a [`Fingerprint`]'s coefficients in every
//! lane, its columns read by key, the terms' products unreduced and one reduction a fingerprint.

use primitives::field::F192;
use quotient::ntt::{ESplat, Ex8, Kx8, MixedSum};

use super::fingerprint::Fingerprint;

/// `constant + Σ c x_i + Σ c x_i x_j` on eight points, column `i` read by key `C`.
pub struct Print<C> {
    constant: Ex8,
    linear: Vec<(C, ESplat)>,
    quadratic: Vec<(C, C, ESplat)>,
}

impl<C: Copy> Print<C> {
    /// `f`, its column `c` read by `key(c)`.
    pub fn new(f: &Fingerprint, key: impl Fn(usize) -> C) -> Self {
        Self {
            constant: Ex8::splat(f.constant),
            linear: f.linear.iter().map(|&(c, k)| (key(c), ESplat::new(k))).collect(),
            quadratic: f
                .quadratic
                .iter()
                .map(|&(c, d, k)| (key(c), key(d), ESplat::new(k)))
                .collect(),
        }
    }

    /// The linear form `constant + Σ c x`.
    pub fn linear(constant: F192, terms: impl IntoIterator<Item = (C, F192)>) -> Self {
        Self {
            constant: Ex8::splat(constant),
            linear: terms.into_iter().map(|(s, c)| (s, ESplat::new(c))).collect(),
            quadratic: Vec::new(),
        }
    }

    /// Its values, the columns' read by `col`.
    #[inline(always)]
    pub fn at(&self, col: impl Fn(C) -> Kx8) -> Ex8 {
        let mut sum = MixedSum::default();
        for &(s, ref c) in &self.linear {
            sum.add(c, col(s));
        }
        for &(s, t, ref c) in &self.quadratic {
            sum.add(c, col(s) * col(t));
        }
        sum.reduce() + self.constant
    }
}

/// The product of `prints`, the columns' read by `col`.
#[inline(always)]
pub fn product<C: Copy>(prints: &[Print<C>], col: impl Fn(C) -> Kx8 + Copy) -> Ex8 {
    match prints.split_first() {
        Some((first, rest)) => rest.iter().fold(first.at(col), |acc, f| acc * f.at(col)),
        None => Ex8::splat(F192::ONE),
    }
}
