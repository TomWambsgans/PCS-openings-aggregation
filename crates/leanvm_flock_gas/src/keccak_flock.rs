// Part of this repository (new here, not from leanVM). The verifier's walk of the Keccak-f[1600] Flock block of
// `crates/lv42_flock/src/keccak.rs` (crates/slh_dsa/SPEC-FAST.md §4.2, §4.5), on a generic `Scalar`, as
// `crate::flock::blake2s_row_values` is BLAKE2s's. MIT OR Apache-2.0; see NOTICE.md.
//! The Keccak-f block's rows' values `(A0 w, B0 w)` by one forward walk, for the walked terminal
//! ([`crate::flock_min::verify_walked_with`] with [`Keccak`]). The block's layout and rows are `lv42_flock::keccak`'s
//! (its module documentation); this walk restates them on a [`Scalar`] (a test of `crates/leanvm_univariate`,
//! `flock_keccak.rs`, checks the two walks agree), at about 24 · 25 · 64 · 12 additions. It is the reference the
//! structured terminal (SPEC-FAST §4.2, M3) is checked against, not a terminal for a recursion: too many additions.

use crate::flock_min::WalkedCircuit;
use crate::scalar::Scalar;

/// `log2` of the block's slots.
pub const LOG_SIZE: usize = 17;
const LANES: usize = 25;
const ROUNDS: usize = 24;
const QUADS: usize = 32;
const PORT_WORDS: usize = 4 * QUADS;
const ROLE_X: usize = 0;
const ROLE_Y: usize = 1;
const ROLE_C: usize = 2;
const ROLE_V: usize = 3;
/// The quad `(x, 1, 0, x)`.
pub const X_QUAD: usize = 25;
/// The constant wire: quad 0's `Y` word, bit 0.
pub const CONSTANT_COLUMN: usize = 64 * port_word(0, ROLE_Y);

/// ι's round constants (FIPS 202).
const RC: [u64; ROUNDS] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// ρ's rotation of lane `x + 5 y`.
const RHO: [usize; LANES] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// `SOURCE[x + 5 y] = (lane, rotation)`: `b[x, y] = rotl(θ(A)[lane], rotation)` (π: `(x', y') → (y', 2x' + 3y')`).
const SOURCE: [(usize, usize); LANES] = {
    let mut s = [(0, 0); LANES];
    let mut x = 0;
    while x < 5 {
        let mut y = 0;
        while y < 5 {
            s[y + 5 * ((2 * x + 3 * y) % 5)] = (x + 5 * y, RHO[x + 5 * y]);
            y += 1;
        }
        x += 1;
    }
    s
};

const fn port_word(q: usize, role: usize) -> usize {
    4 * q + role
}

/// The word of `t_j`'s lane `l`.
pub const fn t_word(j: usize, l: usize) -> usize {
    64 * (j + 2) + l
}

/// The word of state `A_j`'s lane `l`, `-1 ≤ j ≤ 23`: the input port's `C`, a materialised state, the output port's `X`.
pub const fn state_word(j: isize, l: usize) -> usize {
    if j < 0 {
        port_word(l, ROLE_C)
    } else if j as usize == ROUNDS - 1 {
        port_word(l, ROLE_X)
    } else {
        64 * (j as usize + 2) + 32 + l
    }
}

/// The Keccak-f block (`lv42_flock::keccak`).
#[derive(Clone, Copy, Debug)]
pub struct Keccak;

impl WalkedCircuit for Keccak {
    const LOG_SIZE: usize = LOG_SIZE;
    const CONSTANT_COLUMN: usize = CONSTANT_COLUMN;
    fn row_values<S: Scalar>(w: &[S]) -> (Vec<S>, Vec<S>) {
        row_values(w)
    }
}

/// `(A0 w, B0 w)`: every row's inner product with the column weights `w`.
pub fn row_values<S: Scalar>(w: &[S]) -> (Vec<S>, Vec<S>) {
    let size = 1 << LOG_SIZE;
    assert_eq!(w.len(), size);
    let mut left = vec![S::zero(); size];
    let mut right = vec![S::zero(); size];
    let one = w[CONSTANT_COLUMN];
    // The port region: constants (every Y bit 0, the x quad's X and V bit 1), inputs, the outputs' copies; the outputs
    // themselves are round 23's.
    for q in 0..QUADS {
        let s = 64 * port_word(q, ROLE_Y);
        (left[s], right[s]) = (one, one);
        if q < LANES {
            for z in 0..64 {
                let c = 64 * port_word(q, ROLE_C) + z;
                (left[c], right[c]) = (w[c], one);
                let v = 64 * port_word(q, ROLE_V) + z;
                (left[v], right[v]) = (w[64 * port_word(q, ROLE_X) + z], one);
            }
        }
    }
    for role in [ROLE_X, ROLE_V] {
        let s = 64 * port_word(X_QUAD, role) + 1;
        (left[s], right[s]) = (one, one);
    }
    debug_assert!(PORT_WORDS <= t_word(0, 0));
    for j in 0..ROUNDS {
        // b's forms: θ's column sums of A_{j-1}, then each lane's 11 terms at its ρ-rotated position.
        let lane = |l: usize| &w[64 * state_word(j as isize - 1, l)..][..64];
        let col: Vec<Vec<S>> = (0..5)
            .map(|x| (0..64).map(|z| S::sum((0..5).map(|y| lane(x + 5 * y)[z]))).collect())
            .collect();
        let b: Vec<Vec<S>> = (0..LANES)
            .map(|i| {
                let (src, rot) = SOURCE[i];
                let x = src % 5;
                (0..64)
                    .map(|z| {
                        let zp = (z + 64 - rot) % 64;
                        lane(src)[zp] + col[(x + 4) % 5][zp] + col[(x + 1) % 5][(zp + 63) % 64]
                    })
                    .collect()
            })
            .collect();
        for l in 0..LANES {
            let (x, y) = (l % 5, l / 5);
            for z in 0..64 {
                let t = 64 * t_word(j, l) + z;
                left[t] = one + b[(x + 1) % 5 + 5 * y][z];
                right[t] = b[(x + 2) % 5 + 5 * y][z];
                let s = 64 * state_word(j as isize, l) + z;
                left[s] = b[l][z] + w[t];
                if l == 0 && RC[j] >> z & 1 == 1 {
                    left[s] += one;
                }
                right[s] = one;
            }
        }
    }
    (left, right)
}
