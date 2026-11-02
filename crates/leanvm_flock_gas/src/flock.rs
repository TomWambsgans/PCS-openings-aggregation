// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/flock.rs: the
// same zerocheck, lincheck, BLAKE2s row walk and ring switch on a generic `Scalar` and `Channel` (constants computed
// natively, as leanVM's are), the terminal check stated to the channel, the table-driven `Scaled` products written as
// plain ones, the terminal walk folding both matrices' sides at once, and the gas report's phase names. New here: the
// lincheck may leave its terminal identity to `crate::matrices` instead of walking the circuit. MIT OR Apache-2.0;
// see NOTICE.md.
//! Flock reduction, then ring switching.

use crate::VerifierError;
use crate::field::{E, GEN, ONE};
use crate::hash::{BLAKE2S_G_LANES, BLAKE2S_IV, BLAKE2S_SIGMA};
use crate::layout::{BLAKE2S_CONSTANT_COLUMN, BLAKE2S_R1CS_LOG_SIZE, FLOCK_K_SKIP, FLOCK_NUM_LINCHECK_ROUNDS, K_BITS};
use crate::matrices::{MatrixClaim, reduce_matrices};
use crate::multilinear::{dot, eq_eval, eq_kernel, poly_eval};
use crate::scalar::{Scalar, enter};
use crate::transcript::{Channel, sumcheck};

const PHI_BASIS: [u64; 8] = [
    0x0000000000000001,
    0x033CE8BEDDC8A656,
    0x512620375ED2A108,
    0x0C9E636090AAFC01,
    0xBA4F3CD82801769C,
    0xBA26E7904ADB4A47,
    0x467698598926DC01,
    0x4418AE808B28BDD0,
];

/// `PHI[value]`: the F2-linear image of the byte `value` in the PHI basis.
fn phi(value: usize) -> E {
    let bits = (0..8).filter(|bit| value >> bit & 1 == 1);
    E::new(bits.fold(0, |acc, bit| acc ^ PHI_BASIS[bit]), 0, 0)
}

const MEDIUM_GENERATOR: E = E::new(0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0);
const N_FIXED_CHALLENGES: usize = 7;

fn fixed_challenges() -> [E; N_FIXED_CHALLENGES] {
    let medium = |power: u32| {
        let value = MEDIUM_GENERATOR.pow(1 << power);
        value * (ONE + value).inv()
    };
    [
        phi(0xF7),
        phi(0x53),
        phi(0xB5),
        medium(0),
        medium(1),
        medium(2),
        medium(3),
    ]
}

/// The one barycentric denominator `PHI[:count]` has: `prod_(k != 0) PHI[k]`, inverted.
///
/// PHI is F2-linear in its index, so `PHI[i] + PHI[j] = PHI[i ^ j]`, and over a power-of-two prefix
/// `j -> i ^ j` only permutes the block. Every node is left the same product.
fn window_denominator(count: usize) -> E {
    (1..count).fold(ONE, |acc, k| acc * phi(k)).inv()
}

/// The barycentric weights of `PHI[:count]` at `point`, by prefix and suffix numerator products.
pub fn lagrange_weights<S: Scalar>(count: usize, point: S) -> Vec<S> {
    let differences: Vec<S> = (0..count).map(|node| point + S::constant(phi(node))).collect();
    let mut prefix = vec![S::one(); count + 1];
    let mut suffix = vec![S::one(); count + 1];
    for i in 0..count {
        prefix[i + 1] = prefix[i] * differences[i];
        suffix[count - 1 - i] = suffix[count - i] * differences[count - 1 - i];
    }
    let denominator = S::constant(window_denominator(count));
    (0..count).map(|i| prefix[i] * suffix[i + 1] * denominator).collect()
}

fn lagrange_interpolate<S: Scalar>(count: usize, values: &[S], point: S) -> S {
    dot(&lagrange_weights(count, point), values)
}

pub struct ZerocheckResult<S> {
    pub z_skip: S,
    pub chi: Vec<S>,
    pub v_a: S,
    pub v_b: S,
    pub v_c: S,
}

/// The zerocheck: one univariate skip round, then nflock quadratic ones.
/// C rides those rounds with AB, so all three claims come out at one point.
fn verify_flock_zerocheck<S: Scalar>(
    log_n: usize,
    transcript: &mut impl Channel<S>,
) -> Result<ZerocheckResult<S>, VerifierError> {
    let _phase = enter("flock zerocheck: skip round");
    // The point r: seven fixed coordinates, the rest sampled.
    let mut r: Vec<Option<S>> = fixed_challenges().map(|c| Some(S::constant(c))).into();
    let sampled = transcript.samples(log_n - FLOCK_K_SKIP - N_FIXED_CHALLENGES);
    r.extend(sampled.into_iter().map(Some));

    // P = P^AB + P^C on the coset, then z_skip; the 64 zeros on Lambda are assumed.
    let p_coset = transcript.next_scalars(K_BITS)?;
    let z_skip = transcript.sample();
    let v_p = lagrange_interpolate(2 * K_BITS, &[vec![S::zero(); K_BITS], p_coset].concat(), z_skip);

    // nflock quadratic rounds on P, closed by v_a, v_b.
    let (chi, running) = {
        let _rounds = enter("flock zerocheck: rounds");
        sumcheck(transcript, v_p, 3, &r)?
    };
    let (v_a, v_b) = (transcript.next_scalar()?, transcript.next_scalar()?);
    let v_c = running + v_a * v_b;
    Ok(ZerocheckResult {
        z_skip,
        chi,
        v_a,
        v_b,
        v_c,
    })
}

/// What the reduction leaves: the zerocheck's point and its three claims there, then the lincheck's
/// batching challenge, its round challenges in round order, and the 64 slices it closes on.
#[derive(Clone, Debug)]
pub struct FlockClaims<S> {
    pub z_skip: S,
    pub chi: Vec<S>,
    pub v_a: S,
    pub v_b: S,
    pub v_c: S,
    pub alpha: S,
    pub round_challenges: Vec<S>,
    pub s: Vec<S>,
    /// The claims on flock's matrices, when the lincheck leaves its terminal identity to them.
    pub matrices: Option<MatrixClaim<S>>,
}

impl<S: Scalar> FlockClaims<S> {
    /// The point the slices are claims at: the lincheck's challenges in coordinate order, then the rest of chi.
    pub fn point(&self) -> Vec<S> {
        let chi_in_prime = self.round_challenges.iter().rev().copied();
        let rest = self.chi[FLOCK_NUM_LINCHECK_ROUNDS..].iter().copied();
        chi_in_prime.chain(rest).collect()
    }
}

/// How the lincheck's terminal identity is checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LincheckTerminal {
    /// As leanVM 42422001: by one forward walk of the BLAKE2s circuit (`A0 w`, `B0 w`) against the row weights.
    Walk,
    /// Left to claims on `A0` and `B0` at one point ([`crate::matrices`]), whose commitments are fixed.
    Matrices,
}

/// Lincheck at the quirky point (z_skip, chi): its 64 slices s, claims at [`FlockClaims::point`].
fn verify_flock_lincheck<S: Scalar>(
    zc: ZerocheckResult<S>,
    transcript: &mut impl Channel<S>,
    terminal: LincheckTerminal,
) -> Result<FlockClaims<S>, VerifierError> {
    let _phase = enter("flock lincheck: rounds");
    let alpha = transcript.sample(); // batches the two matrix identities, the c claim and the constant-position claim

    // The 8 rounds that bind the high column coordinates, leaving 64 unfolded.
    let claim = zc.v_a + alpha * zc.v_b + alpha.pow(2) * zc.v_c + alpha.pow(3);
    let (round_challenges, r_lc) = sumcheck(transcript, claim, 3, &[None; FLOCK_NUM_LINCHECK_ROUNDS])?;

    // The residual, then the terminal identity: pin term and c term included.
    let s = transcript.next_scalars(K_BITS)?;
    let chi_in = &zc.chi[..FLOCK_NUM_LINCHECK_ROUNDS];
    let chi_in_prime: Vec<S> = round_challenges.iter().rev().copied().collect();
    let matrices = match terminal {
        LincheckTerminal::Walk => {
            let _phase = enter("flock lincheck: terminal walk of the BLAKE2s circuit");
            // e_row: phi8 Lagrange in the skip coordinate, eq in the slot variables.
            let skip_weights = lagrange_weights(K_BITS, zc.z_skip);
            // C = I, so the c weight is e_row itself, and both sides being tensors it
            // collapses to eq(chi_in, chi_in_prime) times a 64-term Lagrange combination.
            // w_col = eq(chi_in_prime) ⊗ s, a column of it per slice: each slice multiplies the whole eq table.
            let high = eq_kernel(&chi_in_prime);
            let mut w_col = vec![S::zero(); high.len() * K_BITS];
            for (l, &slice) in s.iter().enumerate() {
                for (h, &weight) in high.iter().enumerate() {
                    w_col[h * K_BITS + l] = slice * weight;
                }
            }
            let (left_values, right_values) = blake2s_row_values(&w_col);
            // e_row = eq(chi_in) ⊗ skip_weights, never built: each block of 64 rows meets the skip weights, a column at a
            // time, then chi_in weighs the blocks. leanVM sums the A0 side and the B0 side apart, adds them under alpha,
            // and folds the blocks by chi_in. Here, the same sum in the order the contract can afford: a block takes
            // both sides at once (against the skip weights and alpha times them), and the blocks are weighed by
            // eq(chi_in)'s table, in the order the walk fills them, the output rows (blocks 4 to 7, which need the whole
            // walk) last. So each value of the walk is used soon after it is made, and the contract does not hold
            // them in memory. Products: 64 + 256 more than leanVM's.
            let alpha_skip: Vec<S> = skip_weights.iter().map(|&weight| alpha * weight).collect();
            let block_weights = eq_kernel(chi_in);
            let walk_order = (0..4).chain(8..high.len()).chain(4..8);
            let mut matrices_part = S::zero();
            for h in walk_order {
                let mut block = S::zero();
                for l in 0..K_BITS {
                    block +=
                        skip_weights[l] * left_values[h * K_BITS + l] + alpha_skip[l] * right_values[h * K_BITS + l];
                }
                matrices_part += block_weights[h] * block;
            }
            let terminal = matrices_part
                + alpha.pow(2) * eq_eval(chi_in, &chi_in_prime) * dot(&skip_weights, &s)
                + alpha.pow(3) * w_col[BLAKE2S_CONSTANT_COLUMN];
            transcript.require_zero(terminal + r_lc, VerifierError::FlockLincheckTerminal)?;
            None
        }
        LincheckTerminal::Matrices => Some(reduce_matrices(
            transcript,
            zc.z_skip,
            chi_in,
            &chi_in_prime,
            &s,
            alpha,
            r_lc,
        )?),
    };
    Ok(FlockClaims {
        z_skip: zc.z_skip,
        chi: zc.chi,
        v_a: zc.v_a,
        v_b: zc.v_b,
        v_c: zc.v_c,
        alpha,
        round_challenges,
        s,
        matrices,
    })
}

type Word<S> = [S; 32];

/// The forward walk's state: `A0 w` and `B0 w`, filled row by row.
struct RowValues<'a, S> {
    column_weights: &'a [S],
    left_values: Vec<S>,
    right_values: Vec<S>,
}

impl<S: Scalar> RowValues<'_, S> {
    fn slots(&self, base: usize) -> Word<S> {
        std::array::from_fn(|bit| self.column_weights[base + bit])
    }

    fn literal(&self, value: u32) -> Word<S> {
        let constant = self.column_weights[BLAKE2S_CONSTANT_COLUMN];
        std::array::from_fn(|bit| if value >> bit & 1 == 1 { constant } else { S::zero() })
    }

    fn add(&mut self, x: Word<S>, y: Word<S>, carry_base: usize) -> Word<S> {
        let mut carry = S::zero();
        let mut output = [S::zero(); 32];
        for bit in 0..32 {
            if bit < 31 {
                self.left_values[carry_base + bit] = x[bit] + carry;
                self.right_values[carry_base + bit] = y[bit] + carry;
            }
            output[bit] = x[bit] + y[bit] + carry;
            if bit < 31 {
                carry += self.column_weights[carry_base + bit];
            }
        }
        output
    }

    /// Fused three-operand add: 31 majority rows then 30 ripple rows.
    ///
    /// The majority of bit `i` is `maj_aux[i] + z[i]`, since over GF(2)
    /// `(x+z)(y+z) = xy + xz + yz + z`; then `x + y + z` is the ripple sum of
    /// `p = x^y^z` against `q[i] = maj[i-1]`, whose bit 0 is zero, so the
    /// ripple layer's bit 0 needs no row and slot `base + 31 + i - 1` carries
    /// bit `i`.
    fn add3(&mut self, x: Word<S>, y: Word<S>, z: Word<S>, base: usize) -> Word<S> {
        let mut majority = [S::zero(); 31];
        for bit in 0..31 {
            self.left_values[base + bit] = x[bit] + z[bit];
            self.right_values[base + bit] = y[bit] + z[bit];
            majority[bit] = self.column_weights[base + bit] + z[bit];
        }
        let ripple_base = base + 31;
        let mut carry = S::zero();
        let mut output = [S::zero(); 32];
        for bit in 0..32 {
            let q = if bit == 0 { S::zero() } else { majority[bit - 1] };
            let left = x[bit] + y[bit] + z[bit] + carry;
            output[bit] = left + q;
            if (1..=30).contains(&bit) {
                self.left_values[ripple_base + bit - 1] = left;
                self.right_values[ripple_base + bit - 1] = q + carry;
                carry += self.column_weights[ripple_base + bit - 1];
            }
        }
        output
    }

    fn linear_rows(&mut self, values: Word<S>, base: usize) {
        for bit in 0..32 {
            self.left_values[base + bit] = values[bit];
            self.right_values[base + bit] = self.column_weights[BLAKE2S_CONSTANT_COLUMN];
        }
    }
}

fn xor<S: Scalar>(x: Word<S>, y: Word<S>) -> Word<S> {
    std::array::from_fn(|bit| x[bit] + y[bit])
}

fn rotate_right<S: Scalar>(word: Word<S>, amount: usize) -> Word<S> {
    std::array::from_fn(|bit| word[(bit + amount) & 31])
}

/// Compute `A0 w` and `B0 w` by one forward walk of the circuit.
pub fn blake2s_row_values<S: Scalar>(column_weights: &[S]) -> (Vec<S>, Vec<S>) {
    let size = 1 << BLAKE2S_R1CS_LOG_SIZE;
    let constant = BLAKE2S_CONSTANT_COLUMN;
    let message_base = 640;
    let counter_low = 1152;
    let counter_high = 1184;
    let final_flag = 1216;
    let last_node_flag = 1248;
    let gates_base = 1280;
    let gate_stride = 184;
    let mut rows = RowValues {
        column_weights,
        left_values: vec![S::zero(); size],
        right_values: vec![S::zero(); size],
    };

    for (base, length) in [(0, 256), (message_base, 512), (counter_low, 128)] {
        for row in base..base + length {
            rows.left_values[row] = column_weights[row];
            rows.right_values[row] = column_weights[constant];
        }
    }

    // v[0..8] = h, v[8..12] = IV[0..4], v[12..16] = IV[4..8] ^ (t_lo, t_hi, f0, f1).
    let mut state = [[S::zero(); 32]; 16];
    for word in 0..8 {
        state[word] = rows.slots(32 * word);
    }
    for word in 0..4 {
        state[8 + word] = rows.literal(BLAKE2S_IV[word]);
    }
    for (word, base) in [counter_low, counter_high, final_flag, last_node_flag]
        .into_iter()
        .enumerate()
    {
        state[12 + word] = xor(rows.literal(BLAKE2S_IV[4 + word]), rows.slots(base));
    }

    for (round_index, sigma) in BLAKE2S_SIGMA.iter().enumerate() {
        for (gate_index, &[lane_a, lane_b, lane_c, lane_d]) in BLAKE2S_G_LANES.iter().enumerate() {
            let gate = round_index * 8 + gate_index;
            let gate_base = gates_base + gate_stride * gate;
            let (a, b, c, d) = (state[lane_a], state[lane_b], state[lane_c], state[lane_d]);
            let mx = rows.slots(message_base + 32 * sigma[2 * gate_index]);
            let my = rows.slots(message_base + 32 * sigma[2 * gate_index + 1]);
            let a1 = rows.add3(a, b, mx, gate_base);
            let d1 = rotate_right(xor(d, a1), 16);
            let c1 = rows.add(c, d1, gate_base + 61);
            let b1 = rotate_right(xor(b, c1), 12);
            let a2 = rows.add3(a1, b1, my, gate_base + 92);
            let d2 = rotate_right(xor(d1, a2), 8);
            let c2 = rows.add(c1, d2, gate_base + 153);
            let b2 = rotate_right(xor(b1, c2), 7);
            // Every lane cascades: this encoding materializes no intermediate word.
            state[lane_a] = a2;
            state[lane_b] = b2;
            state[lane_c] = c2;
            state[lane_d] = d2;
        }
    }

    // out[w] = h[w] ^ v[w] ^ v[w+8], the only materialized words.
    for word in 0..8 {
        let out = xor(xor(state[word], state[word + 8]), rows.slots(32 * word));
        rows.linear_rows(out, 256 + 32 * word);
    }

    rows.left_values[constant] = column_weights[constant];
    rows.right_values[constant] = column_weights[constant];
    (rows.left_values, rows.right_values)
}

/// The reduction in protocol order: zerocheck, then lincheck. What it leaves is the
/// point and the 64 claims s\[i\] = z(i, point), i < 64, for ring switching to bind.
pub fn verify_flock<S: Scalar>(
    log_n: usize,
    transcript: &mut impl Channel<S>,
    terminal: LincheckTerminal,
) -> Result<FlockClaims<S>, VerifierError> {
    let zc = verify_flock_zerocheck(log_n, transcript)?;
    verify_flock_lincheck(zc, transcript, terminal)
}

// The Frobenius shifts of the six stages composing Phi, one challenge each.
const RING_MAP_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];

/// The drawn map, stage by stage: `a_p+1 = a_p + f_p a_p^(2^shift)`.
fn ring_map<S: Scalar>(mut value: S, challenges: &[S]) -> S {
    for (&challenge, shift) in challenges.iter().zip(RING_MAP_SHIFTS) {
        value += challenge * value.pow(1 << shift);
    }
    value
}

/// The weight `W(u) = Phi(eq(r, u))`, extended and evaluated by the opening at
/// `r_prime`: `sum_k c_k prod_n (1 + r_n^(2^k) + r'_n)`.
fn ring_weight<S: Scalar>(r: &[S], r_prime: &[S], coefficients: &[S]) -> S {
    assert_eq!(r.len(), r_prime.len());
    let _phase = enter("stack batch: ring-switch weight at the point");
    let mut total = S::zero();
    let mut frobenius = r.to_vec();
    for &c in coefficients {
        let mut product = c;
        for (value, &challenge) in frobenius.iter_mut().zip(r_prime) {
            product *= S::one() + *value + challenge;
            *value = value.square();
        }
        total += product;
    }
    total
}

/// The 64 claims s\[i\] = z(i, point) become the one dense claim `sum_u W(u) qflock(u) = target`.
///
/// Draw Phi once they are fixed, then take the target `T = sum_i x^i Phi(s_i)` against the
/// MLE-friendly weight `W(u) = Phi(eq(point, u))`. Returns the target and W as a closure.
pub fn ring_switch<S: Scalar>(point: Vec<S>, s: &[S], transcript: &mut impl Channel<S>) -> (S, RingWeight<S>) {
    let _phase = enter("ring switch: map, coefficients, target");
    let challenges = transcript.samples(RING_MAP_SHIFTS.len());
    // The same map as a Frobenius sum, `Phi(a) = sum_k c_k a^(2^k)` for k < 64.
    let coefficient = |k: usize| {
        let stages = challenges
            .iter()
            .zip(RING_MAP_SHIFTS)
            .filter(|&(_, shift)| k & shift != 0);
        stages.fold(S::one(), |acc, (&f, shift)| acc * f.pow(1 << (k % shift)))
    };
    let coefficients: Vec<S> = (0..K_BITS).map(coefficient).collect();
    let images: Vec<S> = s.iter().map(|&value| ring_map(value, &challenges)).collect();
    let target = poly_eval(&images, S::constant(GEN));
    (target, RingWeight { point, coefficients })
}

/// The ring switch's weight `W` (leanVM returns it as a closure).
pub struct RingWeight<S> {
    point: Vec<S>,
    coefficients: Vec<S>,
}

impl<S: Scalar> RingWeight<S> {
    pub fn at(&self, r_prime: &[S]) -> S {
        ring_weight(&self.point, r_prime, &self.coefficients)
    }
}
