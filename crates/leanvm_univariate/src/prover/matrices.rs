// Part of this repository. The matrices are leanVM 42422001's BLAKE2s R1CS, as `leanvm_flock_gas::flock`'s walk of the
// circuit (adapted from leanVM's crates/verifier/src/flock.rs) computes them. MIT OR Apache-2.0; see NOTICE.md.
//! The setup commitments `A0`, `B0` (SPEC.md §3): Flock's BLAKE2s R1CS matrices as multilinears of `2^28` words,
//! entry `row + 2^14 col`, which Flock's matrices' reduction leaves one claim on each.
//!
//! The circuit's walk is additive in the column weights (every row value a sum of weights), so walking it on 64
//! columns at once, each weight one bit of a word ([`Bits`]: addition XOR), gives 64 columns of both matrices.

use std::ops::{Add, AddAssign, Mul, MulAssign};

use leanvm_flock_gas::field::E;
use leanvm_flock_gas::flock::blake2s_row_values;
use leanvm_flock_gas::layout::BLAKE2S_R1CS_LOG_SIZE;
use leanvm_flock_gas::scalar::Scalar;
use primitives::field::F64;

/// 64 GF(2) values, one a bit.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Bits(pub u64);

impl Add for Bits {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self(self.0 ^ other.0)
    }
}

impl AddAssign for Bits {
    fn add_assign(&mut self, other: Self) {
        self.0 ^= other.0;
    }
}

impl Mul for Bits {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }
}

impl MulAssign for Bits {
    fn mul_assign(&mut self, other: Self) {
        self.0 &= other.0;
    }
}

impl Scalar for Bits {
    fn constant(value: E) -> Self {
        match (value.c0, value.c1, value.c2) {
            (0, 0, 0) => Self(0),
            (1, 0, 0) => Self(!0),
            _ => panic!("the circuit's walk uses no constant but 0 and 1"),
        }
    }
}

/// `A0` and `B0`, `2^28` words each (0 or 1), entry `row + 2^14 col`.
pub fn setup_matrices() -> (Vec<F64>, Vec<F64>) {
    let size = 1usize << BLAKE2S_R1CS_LOG_SIZE;
    let chunks: Vec<(Vec<Bits>, Vec<Bits>)> = parallel::map_collect(size / 64, |chunk| {
        let mut weights = vec![Bits(0); size];
        for j in 0..64 {
            weights[64 * chunk + j] = Bits(1 << j);
        }
        blake2s_row_values(&weights)
    });
    let mut a = vec![F64::ZERO; size * size];
    let mut b = vec![F64::ZERO; size * size];
    for (matrix, side) in [(&mut a, 0), (&mut b, 1)] {
        // Column `col` is the block `[col 2^14, (col + 1) 2^14)`.
        parallel::chunks_mut(matrix, size, |col, block| {
            let (chunk, bit) = (col / 64, col % 64);
            let rows = if side == 0 { &chunks[chunk].0 } else { &chunks[chunk].1 };
            for (row, word) in block.iter_mut().enumerate() {
                *word = F64(rows[row].0 >> bit & 1);
            }
        });
    }
    (a, b)
}
