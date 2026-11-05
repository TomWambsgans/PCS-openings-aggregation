// New in this repository (not from leanVM): the Keccak-f[1600] permutation as a Flock block R1CS, for
// `crates/slh_dsa/SPEC-FAST.md` §4.2 and §4.5 (design C*, milestone M1). Its walks and its prover entry follow this
// crate's BLAKE2s block (`hash.rs`, leanVM 42422001's): the same row kinds, `C = I`, the same `LincheckCircuit` seam
// and the same zerocheck-with-skip and lincheck calls. MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and
// NOTICE.md at the repository root).
//! Keccak-f\[1600\] as one Flock block: `k_log = 17`, `C = I`, every round's state materialised.
//!
//! ## Rows
//!
//! Every slot is the output of one row (`(A_0 z)·(B_0 z) = z`), of one of five kinds:
//!
//! - **constant** `A = [1]`, `B = [1]`: the slot is 1. The constant wire is [`CONST_POS`] (lincheck pins it to 1 in
//!   every block); the other constant bits are pinned by it.
//! - **free input** `A = [slot]`, `B = [1]`: the input lanes `A_{-1}`.
//! - **lin-id** `A = form`, `B = [1]`: the slot is the affine form. The states `A_0..A_23`, and the copy of `A_23`.
//! - **product** `A = 1 + form`, `B = form'`: `t_j`, χ's products.
//! - **empty** `A = B = 0`: the slot is 0 (padding, inside the layout and after it).
//!
//! Round `j` (`0 ≤ j < 24`) reads `A_{j-1}` only: `b = π ρ θ (A_{j-1})` is linear, each of its bits the sum of 11 bits
//! of `A_{j-1}` (θ's column parities of lanes `x - 1` and `x + 1`, the latter at `z - 1`, and the lane's own bit, all
//! at the ρ-rotated position), so with `b[x, y]` this round's lane `(x, y)` (`x + 5 y`):
//!
//! ```text
//!   t_j[x, y][z] = (1 + b[x+1, y][z]) · b[x+2, y][z]        product: 12 + 11 nonzeros
//!   A_j[x, y][z] = (b[x, y][z] + t_j[x, y][z] + RC_j[z]·[x = y = 0]) · 1       lin-id: 12 or 13 + 1
//! ```
//!
//! No form reaches back further than one round, so the matrices are sparse (about 1.39M nonzeros a block) and both
//! walks are one pass over the rounds.
//!
//! ## Layout (words of 64 bits; bit `z` of a lane is bit `z` of its word, the packing position)
//!
//! ```text
//!   word 4q + r, q < 32         port quads (SPEC-FAST §4.5): the glue's port row (X, Y, C, V) of quad q
//!     q < 25:  r = 0  A_23[q]    (X: output lane q, lin-id of round 23)
//!              r = 1  1          (Y: the K-element 1, bit 0 a constant row; q = 0's is the constant wire)
//!              r = 2  A_{-1}[q]  (C: input lane q, free)
//!              r = 3  A_23[q]    (V: output lane q again, a lin-id copy of word 4q)
//!     q = 25:  (x, 1, 0, x)      x = bit 1 set (constant rows)
//!     q ≥ 26:  (0, 1, 0, 0)
//!   word 64 (j + 2) + l         t_j[l], j < 24, l < 25 (lanes 25..32 of the run empty)
//!   word 64 (j + 2) + 32 + l    A_j[l], j < 23
//!   [104,000, 131,072)          empty (the zerocheck's and lincheck's padding suffix, `USEFUL_BITS`)
//! ```
//!
//! So a slot's index factors as `(z: 6 bits, lane: 5, kind: 1, round + 2: 5)` outside the port region, which is what
//! a structured terminal (SPEC-FAST §4.2, M3) uses: rounds are a 5-bit field (a shift between consecutive rounds),
//! lanes a 5-bit field. 80,034 slots are constrained (the port region's 8,192 and the rounds' 75,200, less the
//! empty bits of the Y, x and 0 words), of 104,000 before the suffix (the runs' lanes 25..32 are empty), of 131,072.
//!
//! ## What this does not enforce
//!
//! The input lanes are free: binding them (and reading the outputs) is the embedding's job, through the port quads.

use crate::hash::SliceClaim;
use crate::witness::{drive_witness_packed_and_lincheck, packed_bytes};
use primitives::field::F192;

/// Block dimension: one Keccak-f occupies `2^K_LOG = 131,072` z slots.
pub const K_LOG: usize = 17;
/// `k = 2^K_LOG`.
pub const K: usize = 1 << K_LOG;
/// 64-bit words a block.
pub const WORDS: usize = K / 64;
/// Lanes of the state.
pub const LANES: usize = 25;
/// Rounds of Keccak-f\[1600\].
pub const ROUNDS: usize = 24;
/// The lincheck's packing width (the slices' count is `2^K_SKIP`), as BLAKE2s's.
pub const K_SKIP: usize = 6;

/// Port quads at the start of the block.
pub const QUADS: usize = 32;
/// Words of the port region (`4 · QUADS`).
pub const PORT_WORDS: usize = 4 * QUADS;
/// A quad's roles, in the glue's port row `(X, Y, C, V) = (O_q, 1, I_q, O_q)`.
pub const ROLE_X: usize = 0;
pub const ROLE_Y: usize = 1;
pub const ROLE_C: usize = 2;
pub const ROLE_V: usize = 3;
/// The quad `(x, 1, 0, x)`, the glue's K-constant `x`.
pub const X_QUAD: usize = 25;

/// The constant wire: quad 0's `Y` word, bit 0.
pub const CONST_POS: usize = 64 * port_word(0, ROLE_Y);
/// Words a round's run takes (`t_j` then `A_j`, 32 words each).
pub const ROUND_WORDS: usize = 64;
/// Bits before the zero suffix: through `t_23`'s last lane.
pub const USEFUL_BITS: usize = 64 * (t_word(ROUNDS - 1, LANES - 1) + 1);

const _: () = assert!(USEFUL_BITS == 104_000 && USEFUL_BITS <= K);
const _: () = assert!(K_SKIP == pcs::pack::LOG_PACKING, "the slices are q_flock's packing positions");

/// The word of quad `q`'s role `r`.
pub const fn port_word(q: usize, role: usize) -> usize {
    4 * q + role
}

/// The word of `t_j`'s lane `l`.
pub const fn t_word(j: usize, l: usize) -> usize {
    ROUND_WORDS * (j + 2) + l
}

/// The word of `A_j`'s lane `l`, `j < 23` (materialised states).
pub const fn a_word(j: usize, l: usize) -> usize {
    ROUND_WORDS * (j + 2) + 32 + l
}

/// The word holding state `A_j`'s lane `l`, `-1 ≤ j ≤ 23`: the input port, a materialised state, the output port.
pub const fn state_word(j: isize, l: usize) -> usize {
    if j < 0 {
        port_word(l, ROLE_C)
    } else if j as usize == ROUNDS - 1 {
        port_word(l, ROLE_X)
    } else {
        a_word(j as usize, l)
    }
}

// ---------------------------------------------------------------------------
// Keccak-f[1600], the witness oracle.
// ---------------------------------------------------------------------------

/// ι's round constants.
pub const RC: [u64; ROUNDS] = [
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
pub const RHO: [u32; LANES] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// `b`'s source: `SOURCE[x + 5 y] = (lane, rotation)` with `b[x, y] = rotl(θ(A)[lane], rotation)`, π moving lane
/// `(x', y')` to `(y', 2 x' + 3 y')`.
pub const SOURCE: [(usize, u32); LANES] = {
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

/// One round's `b = π ρ θ (a)`.
#[inline(always)]
pub fn pi_rho_theta(a: &[u64; LANES]) -> [u64; LANES] {
    let c: [u64; 5] = std::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
    let d: [u64; 5] = std::array::from_fn(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1));
    std::array::from_fn(|i| {
        let (src, rot) = SOURCE[i];
        (a[src] ^ d[src % 5]).rotate_left(rot)
    })
}

/// One round: `χ` and `ι` on `b = π ρ θ (a)`; also returns the products `t`.
#[inline(always)]
fn round(a: &[u64; LANES], j: usize) -> ([u64; LANES], [u64; LANES], [u64; LANES]) {
    let b = pi_rho_theta(a);
    let t: [u64; LANES] = std::array::from_fn(|i| {
        let (x, y) = (i % 5, i / 5);
        !b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]
    });
    let mut out: [u64; LANES] = std::array::from_fn(|i| b[i] ^ t[i]);
    out[0] ^= RC[j];
    (b, t, out)
}

/// Keccak-f\[1600\], in place (lane `x + 5 y`, FIPS 202).
pub fn keccak_f(state: &mut [u64; LANES]) {
    for j in 0..ROUNDS {
        *state = round(state, j).2;
    }
}

/// The padding instance: Keccak-f of the zero state.
pub const PADDING_INPUT: [u64; LANES] = [0; LANES];

/// Minimum `n_blocks_log` for `n_blocks` permutations.
pub fn min_n_blocks_log(n_blocks: usize) -> usize {
    crate::hash::min_n_blocks_log(n_blocks)
}

// ---------------------------------------------------------------------------
// Witness generation.
// ---------------------------------------------------------------------------

/// One block's `(z, a, b)` (`C = I`, so `c = z`), into zeroed buffers of `WORDS` words.
fn build_block_witness(input: &[u64; LANES], z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    debug_assert!(z.len() == WORDS && a.len() == WORDS && b.len() == WORDS);
    let mut set = |w: usize, zv: u64, av: u64, bv: u64| {
        z[w] = zv;
        a[w] = av;
        b[w] = bv;
    };
    // Constant rows: every quad's Y bit 0 (quad 0's is the constant wire), and the x quad's X and V bit 1.
    for q in 0..QUADS {
        set(port_word(q, ROLE_Y), 1, 1, 1);
    }
    set(port_word(X_QUAD, ROLE_X), 2, 2, 2);
    set(port_word(X_QUAD, ROLE_V), 2, 2, 2);
    // Free inputs.
    for (l, &v) in input.iter().enumerate() {
        set(port_word(l, ROLE_C), v, v, !0);
    }
    let mut s = *input;
    for j in 0..ROUNDS {
        let (bl, t, out) = round(&s, j);
        for l in 0..LANES {
            let (x, y) = (l % 5, l / 5);
            let left = !bl[(x + 1) % 5 + 5 * y];
            let right = bl[(x + 2) % 5 + 5 * y];
            set(t_word(j, l), t[l], left, right);
            set(state_word(j as isize, l), out[l], out[l], !0);
        }
        s = out;
    }
    for (l, &v) in s.iter().enumerate() {
        set(port_word(l, ROLE_V), v, v, !0);
    }
}

/// `(z, a, b, z_lincheck)` for `inputs.len()` permutations padded to `2^n_blocks_log` blocks with Keccak-f(0): the
/// packed tables (`WORDS` words a block) and the lincheck's stripes, as BLAKE2s's generator leaves them.
pub fn generate_witness_with_ab_packed_and_lincheck(
    inputs: &[[u64; LANES]],
    n_blocks_log: usize,
) -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u8>) {
    drive_witness_packed_and_lincheck(inputs, Some(&PADDING_INPUT), n_blocks_log, K_LOG, |input, z, a, b| {
        build_block_witness(input, z, a, b)
    })
}

/// A block's input lanes (the `C` words of its quads), from its `WORDS` packed words.
pub fn block_input(block: &[u64]) -> [u64; LANES] {
    std::array::from_fn(|l| block[port_word(l, ROLE_C)])
}

/// A block's output lanes (the `X` words of its quads).
pub fn block_output(block: &[u64]) -> [u64; LANES] {
    std::array::from_fn(|l| block[port_word(l, ROLE_X)])
}

// ---------------------------------------------------------------------------
// The walks: `(A_0 w, B_0 w)` forwards, `A_0ᵀ u + B_0ᵀ v` backwards, over matrices that are never built.
// ---------------------------------------------------------------------------

/// What a slot's row is, outside the rounds' runs (the port region).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PortRow {
    /// `A = B = 0`.
    Empty,
    /// `A = B = [1]`.
    Constant,
    /// `A = [slot]`, `B = [1]`: an input lane.
    Free,
    /// `A = (round 23's form)`, `B = [1]`: an output lane.
    Output,
    /// `A = [word 4q bit z]`, `B = [1]`: the output lane's copy.
    Copy,
}

/// The row of port slot `64 w + z`, `w < PORT_WORDS`.
pub fn port_row(w: usize, z: usize) -> PortRow {
    let (q, role) = (w / 4, w % 4);
    match role {
        ROLE_Y => {
            if z == 0 {
                PortRow::Constant
            } else {
                PortRow::Empty
            }
        }
        _ if q < LANES => match role {
            ROLE_X => PortRow::Output,
            ROLE_C => PortRow::Free,
            _ => PortRow::Copy,
        },
        ROLE_X | ROLE_V if q == X_QUAD && z == 1 => PortRow::Constant,
        _ => PortRow::Empty,
    }
}

/// `bw[l][z] = Σ` of `w` over the 11 slots of `A_{j-1}` that `b[l][z]` sums, `state(l)` the word of `A_{j-1}`'s lane
/// `l`.
fn b_forms(w: &[F192], state: impl Fn(usize) -> usize) -> [[F192; 64]; LANES] {
    let lane = |l: usize| &w[64 * state(l)..64 * state(l) + 64];
    let mut col = [[F192::ZERO; 64]; 5];
    for (x, col) in col.iter_mut().enumerate() {
        for y in 0..5 {
            for (c, &v) in col.iter_mut().zip(lane(x + 5 * y)) {
                *c += v;
            }
        }
    }
    std::array::from_fn(|i| {
        let (src, rot) = SOURCE[i];
        let (x, own) = (src % 5, lane(src));
        let (left, right) = (&col[(x + 4) % 5], &col[(x + 1) % 5]);
        // θ(A)[src][z'] = A[src][z'] + C[x-1][z'] + C[x+1][z'-1], read at z' = z - rot.
        std::array::from_fn(|z| {
            let zp = (z + 64 - rot as usize) % 64;
            own[zp] + left[zp] + right[(zp + 63) % 64]
        })
    })
}

/// The matrix-vector products `(A_0 w, B_0 w)` (every row's inner product with `w`) by one forward walk.
pub fn row_values_walk(w: &[F192]) -> (Vec<F192>, Vec<F192>) {
    assert_eq!(w.len(), K);
    let mut left = vec![F192::ZERO; K];
    let mut right = vec![F192::ZERO; K];
    let one = w[CONST_POS];
    for wd in 0..PORT_WORDS {
        for z in 0..64 {
            let s = 64 * wd + z;
            match port_row(wd, z) {
                PortRow::Empty | PortRow::Output => {}
                PortRow::Constant => (left[s], right[s]) = (one, one),
                PortRow::Free => (left[s], right[s]) = (w[s], one),
                PortRow::Copy => (left[s], right[s]) = (w[64 * (wd - ROLE_V) + z], one),
            }
        }
    }
    for j in 0..ROUNDS {
        let bw = b_forms(w, |l| state_word(j as isize - 1, l));
        for l in 0..LANES {
            let (x, y) = (l % 5, l / 5);
            let (tw, aw) = (t_word(j, l), state_word(j as isize, l));
            for z in 0..64 {
                let t = 64 * tw + z;
                left[t] = one + bw[(x + 1) % 5 + 5 * y][z];
                right[t] = bw[(x + 2) % 5 + 5 * y][z];
                let s = 64 * aw + z;
                let rc = if l == 0 && RC[j] >> z & 1 == 1 { one } else { F192::ZERO };
                left[s] = bw[l][z] + w[t] + rc;
                right[s] = one;
            }
        }
    }
    (left, right)
}

/// The column marginal `A_0ᵀ u + B_0ᵀ v` by one backward walk: `m[c] = Σ_r u[r] A_0(r, c) + v[r] B_0(r, c)`.
pub fn marginal_walk_sides(u: &[F192], v: &[F192]) -> Vec<F192> {
    assert_eq!(u.len(), K);
    assert_eq!(v.len(), K);
    let mut m = vec![F192::ZERO; K];
    // The constant column's total, added at the end.
    let mut one = F192::ZERO;
    for wd in 0..PORT_WORDS {
        for z in 0..64 {
            let s = 64 * wd + z;
            match port_row(wd, z) {
                PortRow::Empty | PortRow::Output => {}
                PortRow::Constant => one += u[s] + v[s],
                PortRow::Free => {
                    m[s] += u[s];
                    one += v[s];
                }
                PortRow::Copy => {
                    m[64 * (wd - ROLE_V) + z] += u[s];
                    one += v[s];
                }
            }
        }
    }
    for j in 0..ROUNDS {
        // The adjoint of b's bits.
        let mut adj = [[F192::ZERO; 64]; LANES];
        for l in 0..LANES {
            let (x, y) = (l % 5, l / 5);
            let (tw, aw) = (t_word(j, l), state_word(j as isize, l));
            for z in 0..64 {
                let t = 64 * tw + z;
                one += u[t];
                adj[(x + 1) % 5 + 5 * y][z] += u[t];
                adj[(x + 2) % 5 + 5 * y][z] += v[t];
                let s = 64 * aw + z;
                adj[l][z] += u[s];
                m[t] += u[s];
                if l == 0 && RC[j] >> z & 1 == 1 {
                    one += u[s];
                }
                one += v[s];
            }
        }
        // ρπ transposed: θ(A)[src][z'] receives b[i][z' + rot].
        let mut theta = [[F192::ZERO; 64]; LANES];
        for (i, adj) in adj.iter().enumerate() {
            let (src, rot) = SOURCE[i];
            for zp in 0..64 {
                theta[src][zp] += adj[(zp + rot as usize) % 64];
            }
        }
        // θ transposed: A[x, y][z] feeds θ(A)[x, y][z], C[x] (into lanes x + 1 at z and x - 1 at z + 1).
        let col: [[F192; 64]; 5] = std::array::from_fn(|x| {
            std::array::from_fn(|z| (0..5).fold(F192::ZERO, |acc, y| acc + theta[x + 5 * y][z]))
        });
        for l in 0..LANES {
            let x = l % 5;
            let base = 64 * state_word(j as isize - 1, l);
            for z in 0..64 {
                m[base + z] += theta[l][z] + col[(x + 1) % 5][z] + col[(x + 4) % 5][(z + 1) % 64];
            }
        }
    }
    m[CONST_POS] += one;
    m
}

/// The α-batched column marginal `(A_0 + α B_0)ᵀ u` lincheck folds.
pub fn marginal_walk(alpha: F192, u: &[F192]) -> Vec<F192> {
    // Rows past `USEFUL_BITS` are empty: their weights are not read.
    let mut v = vec![F192::ZERO; K];
    for (v, &x) in v.iter_mut().zip(&u[..USEFUL_BITS]) {
        *v = alpha * x;
    }
    marginal_walk_sides(u, &v)
}

/// The Keccak-f R1CS as a [`crate::lincheck::LincheckCircuit`], by the backward walk.
pub struct KeccakLincheckCircuit;

impl crate::lincheck::LincheckCircuit for KeccakLincheckCircuit {
    fn n_cols(&self) -> usize {
        K
    }
    fn const_pin_col(&self) -> usize {
        CONST_POS
    }
    fn fold_alpha_batched(&self, alpha: F192, eq_inner: &[F192]) -> Vec<F192> {
        marginal_walk(alpha, eq_inner)
    }
}

// ---------------------------------------------------------------------------
// The reduction (prover): BLAKE2s's `prove_reduction_skip` on this block.
// ---------------------------------------------------------------------------

/// The Keccak-f R1CS for `2^n_blocks_log` blocks.
#[derive(Clone, Debug)]
pub struct KeccakSetup {
    n_blocks_log: usize,
}

impl KeccakSetup {
    /// A setup for `n_blocks` permutations.
    pub fn new(n_blocks: usize) -> Self {
        Self {
            n_blocks_log: min_n_blocks_log(n_blocks),
        }
    }

    /// The witness's variables, `K_LOG + n_blocks_log`.
    pub fn m(&self) -> usize {
        K_LOG + self.n_blocks_log
    }

    pub fn n_blocks_log(&self) -> usize {
        self.n_blocks_log
    }

    /// **The reduction with a zerocheck skip of `k`** (3 to 6): [`crate::zerocheck::skip::prove_skip`] at the eq
    /// point `eq` describes, then the lincheck at the row weights it leaves, `L(z) ⊗ eq(ρ_(<6-k)) ⊗ eq(x_inner_rest)`,
    /// which leaves the 64 slices at `(r_inner_rest, x_outer)`: `Blake2sSetup::prove_reduction_skip`'s skip path with
    /// this block's shape (`K_LOG = 17`: 11 lincheck rounds).
    #[allow(clippy::too_many_arguments)]
    pub fn prove_reduction_skip(
        &self,
        k: usize,
        eq: crate::zerocheck::skip::EqPoint,
        z_packed: &[u64],
        a_packed_words: &[u64],
        b_packed_words: &[u64],
        z_packed_lincheck: &[u8],
        ps: &mut fiat_shamir::transcript::ProverState,
    ) -> SliceClaim {
        let zc = {
            let _span = tracing::info_span!("Zerocheck").entered();
            let packed_len = 1usize << (self.m() - 6);
            assert_eq!(z_packed.len(), packed_len, "wrong packed witness length");
            assert_eq!(a_packed_words.len(), packed_len, "wrong packed A·z length");
            assert_eq!(b_packed_words.len(), packed_len, "wrong packed B·z length");
            let padding = crate::zerocheck::PaddingSpec {
                k_log: K_LOG,
                useful_bits_per_block: USEFUL_BITS,
            };
            crate::zerocheck::skip::prove_skip(
                packed_bytes(a_packed_words),
                packed_bytes(b_packed_words),
                packed_bytes(z_packed),
                self.m(),
                k,
                eq,
                &padding,
                ps,
            )
        };
        let _span = tracing::info_span!("Lincheck").entered();
        assert_eq!(
            z_packed_lincheck.len(),
            K << self.n_blocks_log.saturating_sub(3),
            "wrong lincheck stripe length"
        );
        let chi = &zc.mlv_challenges;
        let (low, rest) = chi.split_at(K_SKIP - k);
        let (x_inner_rest, x_outer) = rest.split_at(K_LOG - K_SKIP);
        let skip = primitives::multilinear::lagrange_weights_naive(k, zc.z);
        let low_weights: Vec<F192> = primitives::multilinear::eq_table(low)
            .iter()
            .flat_map(|&e| skip.iter().map(move |&l| l * e))
            .collect();
        let eq_inner: Vec<F192> = primitives::multilinear::eq_table(x_inner_rest)
            .iter()
            .flat_map(|&e| low_weights.iter().map(move |&l| l * e))
            .collect();
        let lc = crate::lincheck::prove_padded_capture_s_hat_v_rows(
            z_packed_lincheck,
            self.m(),
            K_LOG,
            K_SKIP,
            USEFUL_BITS,
            &KeccakLincheckCircuit,
            &eq_inner,
            x_outer,
            ps,
        );
        let mut suffix_point = lc.r_inner_rest;
        suffix_point.extend_from_slice(x_outer);
        SliceClaim {
            suffix_point,
            s_hat_v: lc.s_hat_v,
        }
    }
}
