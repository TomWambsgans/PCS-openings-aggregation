// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! What the verifier computes on: an element of `E`, or (for the contract) a node of a recorded graph.
//!
//! leanVM's verifier at 42422001 is written on `E`. Every function of it the contract runs is written here on a
//! [`Scalar`] instead, which `E` is and the recorder's symbol is (`crate::evm::record::Sym`): the same code computes
//! the verdict natively and records the graph the contract is compiled from.

use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, MulAssign};

use crate::field::{E, ONE, ZERO};

pub trait Scalar: Copy + Debug + Add<Output = Self> + Mul<Output = Self> + AddAssign + MulAssign + 'static {
    fn constant(value: E) -> Self;

    fn zero() -> Self {
        Self::constant(ZERO)
    }

    fn one() -> Self {
        Self::constant(ONE)
    }

    fn square(self) -> Self {
        self * self
    }

    /// leanVM's `E::pow`: square and multiply, low bit first.
    fn pow(self, exponent: u64) -> Self {
        let (mut base, mut out, mut n) = (self, Self::one(), exponent);
        while n != 0 {
            if n & 1 == 1 {
                out *= base;
            }
            base = base.square();
            n >>= 1;
        }
        out
    }

    fn sum(values: impl IntoIterator<Item = Self>) -> Self {
        values.into_iter().fold(Self::zero(), |acc, value| acc + value)
    }
}

impl Scalar for E {
    fn constant(value: E) -> Self {
        value
    }

    fn square(self) -> Self {
        E::square(self)
    }

    fn pow(self, exponent: u64) -> Self {
        E::pow(self, exponent)
    }
}

/// `[1, base, base^2, ...]`, `count` terms (leanVM's `field::powers`).
pub fn powers<S: Scalar>(base: S, count: usize) -> Vec<S> {
    let mut out = Vec::with_capacity(count);
    let mut power = S::one();
    for _ in 0..count {
        out.push(power);
        power *= base;
    }
    out
}

thread_local! {
    static PHASE: std::cell::Cell<&'static str> = const { std::cell::Cell::new("setup") };
}

/// The part of the protocol being computed, which the recorder tags every new node with (the gas report's breakdown).
pub fn phase() -> &'static str {
    PHASE.get()
}

/// Tag what is computed until the guard drops with `name`.
pub fn enter(name: &'static str) -> PhaseGuard {
    PhaseGuard(PHASE.replace(name))
}

pub struct PhaseGuard(&'static str);

impl Drop for PhaseGuard {
    fn drop(&mut self) {
        PHASE.set(self.0);
    }
}
