// Part of this repository (new here, not from leanVM). The verifier's walk of the Keccak-f[1600] Flock block of
// `crates/lv42_flock/src/keccak.rs` (crates/slh_dsa/SPEC-FAST.md §4.2, §4.5), on a generic `Scalar`, as
// `crate::flock::blake2s_row_values` is BLAKE2s's, and the block's structured lincheck terminal (M3). MIT OR
// Apache-2.0; see NOTICE.md.
//! The Keccak-f block's lincheck terminal, two ways:
//!
//! - [`row_values`]: the rows' values `(A0 w, B0 w)` by one forward walk, for the walked terminal
//!   ([`crate::flock_min::verify_walked_with`] with [`KeccakWalked`]). The block's layout and rows are
//!   `lv42_flock::keccak`'s (its module documentation); this walk restates them on a [`Scalar`] (a test of
//!   `crates/leanvm_univariate`, `flock_keccak.rs`, checks the two walks agree), at about 24 · 25 · 64 · 12
//!   additions: the reference, not a terminal for a recursion.
//! - [`structured_terminal`]: the same value from the block's structure (eq factors, ρ and θ as cyclic shifts,
//!   corrections), a few thousand `E` operations: [`Keccak`]'s terminal, the one π2 records.

use crate::flock_min::WalkedCircuit;
use crate::multilinear::eq_kernel;
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

/// The Keccak-f block (`lv42_flock::keccak`), its lincheck terminal the structured one ([`structured_terminal`]).
#[derive(Clone, Copy, Debug)]
pub struct Keccak;

impl WalkedCircuit for Keccak {
    const LOG_SIZE: usize = LOG_SIZE;
    const CONSTANT_COLUMN: usize = CONSTANT_COLUMN;
    const TERMINAL_PHASE: &'static str = "flock lincheck: the Keccak terminal (structured)";
    fn row_values<S: Scalar>(w: &[S]) -> (Vec<S>, Vec<S>) {
        row_values(w)
    }
    fn terminal<S: Scalar>(z_skip: Option<S>, row_low: &[S], chi_in: &[S], chi_in_prime: &[S], s: &[S], alpha: S) -> S {
        structured_terminal(z_skip, row_low, chi_in, chi_in_prime, s, alpha)
    }
}

/// The same block with the walked terminal ([`crate::flock_min::walked_terminal_with`] on [`row_values`]): the
/// reference [`Keccak`]'s structured terminal is checked against.
#[derive(Clone, Copy, Debug)]
pub struct KeccakWalked;

impl WalkedCircuit for KeccakWalked {
    const LOG_SIZE: usize = LOG_SIZE;
    const CONSTANT_COLUMN: usize = CONSTANT_COLUMN;
    fn row_values<S: Scalar>(w: &[S]) -> (Vec<S>, Vec<S>) {
        row_values(w)
    }
}

/// The words `ẑ`'s slices are read at by `b`'s forms, as cyclic shifts `z ↦ z - off` of the packing position: ρ's
/// rotations and those plus one (θ's `C[x + 1][z - 1]`). 40 distinct offsets.
fn shift_offsets() -> [bool; 64] {
    let mut needed = [false; 64];
    for rot in RHO {
        needed[rot] = true;
        needed[(rot + 1) % 64] = true;
    }
    needed
}

/// `Σ_(g < 4) weights[g] Σ_(q in group g, q < n) x(q)`: a sum over quads `q < n` whose eq weight factors as a lane
/// part `x(q)` and a group part, `g = q >> 3` (the quad's word `4q + r` has lane field `4 (q & 7) + r`, kind bit
/// `g & 1` and round field `g >> 1`).
fn grouped<S: Scalar>(n: usize, weights: &[S; 4], x: impl Fn(usize) -> S) -> S {
    S::sum(
        (0..4)
            .filter(|&g| 8 * g < n)
            .map(|g| weights[g] * S::sum((8 * g..n.min(8 * g + 8)).map(&x))),
    )
}

/// **The structured terminal** (`crates/slh_dsa/SPEC-FAST.md` §4.2, M3): exactly
/// [`crate::flock_min::walked_terminal_with`]`::<S, KeccakWalked>`, `Σ_(row, col) e(row) (Â0 + α B̂0)(row, col) w(col)`
/// `+ α² eq(chi_in, chi_in') Σ e_z s_z + α³ eq(word 1, chi_in') s_0`, with `e = E ⊗ eq(chi_in, ·)` (`E` the 64
/// packing weights, the skip's Lagrange weights ⊗ `eq(row_low, ·)`) and `w = s ⊗ eq(chi_in', ·)`, computed from the
/// block's structure instead of a walk:
///
/// - **eq factors.** A word's 11 bits are `(lane: 5, kind: 1, round field: 5)`, so `eq(chi_in, word)` is
///   `Lr[lane] · Kd[kind] · Rd[round]`, three tables of 32, 2 and 32 entries (`Lh, Kh, Rh` on the column side). A
///   port word `4q + r` is lane field `4 (q & 7) + r` in group `q >> 3` ([`grouped`]).
/// - **ρ, θ as cyclic shifts.** Every bit of `b = πρθ(A_{j-1})` at position `z` is a sum of `A_{j-1}`'s slots at
///   `z - off`, `off` a rotation or a rotation plus one. A row `(word, z)` weighs `… E_z`, a column `(word', z')` weighs
///   `… s_z'`, so each (row lane, column lane, offset) term is a product of eq factors and `Corr[off] = Σ_z E_z s_(z -
///   off)`, the same for every round. The 40 correlations cost `8 · 64 + 40 · 8` products at a skip of 3 or less
///   (`E` is a tensor product above the skip's bits: `Corr` through 8 partial correlations of 8), `40 · 64` at a skip
///   of 6.
/// - **Rounds.** Rounds 1..22 differ only in `RC_j` (which is not in `b`): their `b` terms share one round factor
///   `Σ_(j=1..22) Rd[j + 2] Rh[j + 1]`. Round 0 reads the port `C` words (a port column table), round 23 writes `A_23` to
///   the port `X` words (a port row weight in the lane sums).
/// - **Corrections**: the constant column (`t` rows' `1 +`, ι's bits, the constant rows of the Y words and the `x`
///   quad, every `B = [1]`), the free inputs, the `V` copies and the `A` rows' `t` term (all with `Corr[0] = Σ E_z
///   s_z`, which is also the `C = I` claim's sum). Lanes 25..31 of every run and the suffix are empty rows and unread
///   columns: no term.
///
/// 3,019 `E` operations at a skip of 3, 6,799 at 6 (recorded: SPEC-FAST's M3 notes). `Σ_z E_z = 1`
/// (Lagrange weights and an eq table each sum to 1) is used for the rows whose 64 positions all carry the same form.
pub fn structured_terminal<S: Scalar>(
    z_skip: Option<S>,
    row_low: &[S],
    chi_in: &[S],
    chi_in_prime: &[S],
    s: &[S],
    alpha: S,
) -> S {
    const PACKING: usize = 6;
    assert_eq!(chi_in.len(), LOG_SIZE - PACKING);
    assert_eq!(chi_in_prime.len(), LOG_SIZE - PACKING);
    assert_eq!(s.len(), 1 << PACKING);
    assert!(row_low.len() <= PACKING);
    let k = PACKING - row_low.len();
    assert_eq!(z_skip.is_some(), k > 0, "a skip point exactly when the skip has bits");
    let one = S::one();

    // E = (skip's Lagrange weights) ⊗ eq(row_low, ·) on the packing bits (skip low), split at bit p as
    // E_low ⊗ E_high.
    let p = k.max(3);
    let lag = match z_skip {
        Some(z) => crate::flock::lagrange_weights(1 << k, z),
        None => vec![one],
    };
    let (mid, high) = row_low.split_at(p - k);
    let e_low: Vec<S> = eq_kernel(mid)
        .iter()
        .flat_map(|&m| lag.iter().map(move |&l| l * m))
        .collect();
    let e_high = eq_kernel(high);
    let (lo, n_hi) = (1usize << p, 1usize << (PACKING - p));
    let e_at = |z: usize| e_low[z % lo] * e_high[z / lo];

    // Corr[off] = Σ_z E_z s_(z - off) = Σ_zh E_high[zh] Q[off mod lo][zh - off / lo], with the partial correlations
    // Q[ol][m] = Σ_zl E_low[zl] s_(lo m + zl - ol).
    let needed = shift_offsets();
    let mut partial: Vec<Option<Vec<S>>> = vec![None; lo];
    let mut corr = vec![S::zero(); 64];
    for off in (0..64).filter(|&off| needed[off]) {
        let (ol, oh) = (off % lo, off / lo);
        let q = partial[ol].get_or_insert_with(|| {
            (0..n_hi)
                .map(|m| S::sum((0..lo).map(|zl| e_low[zl] * s[(lo * m + zl + 64 - ol) % 64])))
                .collect()
        });
        corr[off] = S::sum((0..n_hi).map(|zh| e_high[zh] * q[(zh + n_hi - oh) % n_hi]));
    }
    let es = corr[0];

    // The eq factors of a word: lane, kind, round field.
    let (lr, rd) = (eq_kernel(&chi_in[..5]), eq_kernel(&chi_in[6..]));
    let (lh, rh) = (eq_kernel(&chi_in_prime[..5]), eq_kernel(&chi_in_prime[6..]));
    let (kr5, kh5) = (chi_in[5], chi_in_prime[5]);
    let kd = [one + kr5, kr5];
    let kh = [one + kh5, kh5];
    // A port group's kind and round factor, rows and columns, and their products.
    let kr_g: [S; 4] = std::array::from_fn(|g| kd[g & 1] * rd[g >> 1]);
    let kh_g: [S; 4] = std::array::from_fn(|g| kh[g & 1] * rh[g >> 1]);
    let krh_g: [S; 4] = std::array::from_fn(|g| kr_g[g] * kh_g[g]);
    let lane_of = |q: usize, role: usize| (4 * q + role) % 32;
    // The rows' weights of the X words (A_23, round 23's lin-id rows), and the columns' of the C words (A_{-1}).
    let rx: Vec<S> = (0..LANES).map(|q| lr[lane_of(q, ROLE_X)] * kr_g[q >> 3]).collect();
    let pc: Vec<S> = (0..LANES).map(|q| lh[lane_of(q, ROLE_C)] * kh_g[q >> 3]).collect();

    // --- The constant column's coefficient (`one = s_0 · eq(chi_in', word 1)`), the pin's α³ with it.
    let sum_lr = S::sum(lr[..LANES].iter().copied());
    let sum_rd_a = S::sum(rd[2..=ROUNDS].iter().copied()); // A_0..A_22's round fields
    let sum_rd_t = sum_rd_a + rd[ROUNDS + 1]; // t_0..t_23's
    // t rows: A = 1 + b[x+1], at every position.
    let t_one = kd[0] * sum_lr * sum_rd_t;
    // ι: lane 0's A rows at RC_j's bits (A_23's in the X word of quad 0).
    let (mut rc_mid, mut rc_last) = (S::zero(), S::zero());
    for z in 0..64 {
        let rounds: Vec<usize> = (0..ROUNDS).filter(|&j| RC[j] >> z & 1 == 1).collect();
        if rounds.is_empty() {
            continue;
        }
        let ez = e_at(z);
        let mid = S::sum(rounds.iter().filter(|&&j| j < ROUNDS - 1).map(|&j| rd[j + 2]));
        rc_mid += ez * mid;
        if rounds.contains(&(ROUNDS - 1)) {
            rc_last += ez;
        }
    }
    let rc_one = lr[0] * kd[1] * rc_mid + rx[0] * rc_last;
    // Constant rows (A = B = [1]): bit 0 of the 32 Y words (Σ of the 4 groups' factors is rd[0] + rd[1], as
    // kd[0] + kd[1] = 1), bit 1 of the x quad's X and V words (group 3).
    let y_words = (rd[0] + rd[1]) * S::sum((0..8).map(|a| lr[lane_of(a, ROLE_Y)]));
    let constants = e_at(0) * y_words + e_at(1) * kr_g[3] * (lr[lane_of(X_QUAD, ROLE_X)] + lr[lane_of(X_QUAD, ROLE_V)]);
    // B = [1]: the A rows (materialised and A_23), the free inputs, the copies.
    let b_one = kd[1] * sum_lr * sum_rd_a
        + S::sum(rx.iter().copied())
        + grouped(LANES, &kr_g, |q| lr[lane_of(q, ROLE_C)])
        + grouped(LANES, &kr_g, |q| lr[lane_of(q, ROLE_V)]);
    let alpha2 = alpha.square();
    let alpha3 = alpha2 * alpha;
    let one_coefficient = t_one + rc_one + constants + alpha * (constants + b_one) + alpha3;
    let one_column = s[0] * (lh[1] * kh_g[0]);

    // --- Terms in Corr[0] = Σ_z E_z s_z: the free inputs (A = [own slot]), the copies (A = [X word, same z]), the
    // A rows' t term, and the C = I claim.
    let free = grouped(LANES, &krh_g, |q| lr[lane_of(q, ROLE_C)] * lh[lane_of(q, ROLE_C)]);
    let copies = grouped(LANES, &krh_g, |q| lr[lane_of(q, ROLE_V)] * lh[lane_of(q, ROLE_X)]);
    let a_t_mid = kd[1]
        * kh[0]
        * S::sum((0..LANES).map(|l| lr[l] * lh[l]))
        * S::sum((2..=ROUNDS).map(|f| rd[f] * rh[f]));
    let a_t_last = kh[0] * rh[ROUNDS + 1] * S::sum((0..LANES).map(|l| rx[l] * lh[l]));
    let c_claim = alpha2 * crate::multilinear::eq_eval(chi_in, chi_in_prime);
    let diagonal = es * (free + copies + a_t_mid + a_t_last + c_claim);

    // --- b's terms. A row lane weight per b lane i: the t rows reading b[i] on the left (lane x - 1) and, times α, on
    // the right (lane x - 2), and the A row of lane i.
    let rho_mid = S::sum((1..ROUNDS - 1).map(|j| rd[j + 2] * rh[j + 1]));
    let col_lh: [S; 5] = std::array::from_fn(|x| S::sum((0..5).map(|y| lh[x + 5 * y])));
    let col_pc: [S; 5] = std::array::from_fn(|x| S::sum((0..5).map(|y| pc[x + 5 * y])));
    let c23 = rd[ROUNDS + 1] * kd[0];
    let (v_mid, v_last) = (kh[1] * rho_mid, kh[1] * rh[ROUNDS]);
    let mut g = vec![S::zero(); 64];
    for i in 0..LANES {
        let (x, y) = (i % 5, i / 5);
        let t = lr[(x + 4) % 5 + 5 * y] + alpha * lr[(x + 3) % 5 + 5 * y];
        // Rounds 0..22: Kd[0] t + Kd[1] Lr[i]; round 23: its t rows, and the X word's A row.
        let u = t + kr5 * (t + lr[i]);
        let last = c23 * t + rx[i];
        // Columns: A_{j-1} materialised (rounds 1..23, round fields 2..24), A_{-1} (round 0, the C words).
        let v = v_mid * u + v_last * last;
        let w0 = rd[2] * u;
        let (src, rot) = SOURCE[i];
        let xs = src % 5;
        g[rot] += v * (lh[src] + col_lh[(xs + 4) % 5]) + w0 * (pc[src] + col_pc[(xs + 4) % 5]);
        g[(rot + 1) % 64] += v * col_lh[(xs + 1) % 5] + w0 * col_pc[(xs + 1) % 5];
    }
    let shifts = S::sum((0..64).filter(|&off| needed[off]).map(|off| g[off] * corr[off]));

    one_column * one_coefficient + diagonal + shifts
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
