// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6, crates/flock/src/quotient.rs and crates/flock/src/membership.rs
// (`Scalar`, `Channel`, `VerifyError`): the reduction is the same but for the gate (`V = X + C + Y·C` on bits,
// degree 2) and the tables' layouts (stacks leanVM's WHIR commits as they are). MIT OR Apache-2.0; see NOTICE.md.
//! The membership statement reduced to four evaluation claims by five field elements and no sumcheck.
//!
//! A multilinear claim at a point built from one field element `t` is a univariate evaluation ([`domain`]),
//! so this is a gate-and-copy argument on an additive subspace: one gate on four cells a row ([`circuit`]),
//! copy constraints and the public bits as one sum of logarithmic derivatives, and two quotients. No quotient
//! value is sent, an identity being one claim on the table that holds its polynomials. The verifier is
//! [`reduce`], generic in its scalar so that the same code is the EVM contract, and checks nothing but one
//! nonzero product.
//!
//! [`domain`]: crate::domain
//! [`circuit`]: crate::circuit

use std::ops::{Add, Mul};

use fiat_shamir::merkle::Hash;
use primitives::field::{F64, F192};

use crate::circuit::{Circuit, PUBLIC_ROWS};
use crate::domain::{self, beta, chain, coordinates, point, row_vanishing};
use crate::opening::{self, Claim, Committed, Layout, Table};
use crate::statement::Statement;
use crate::transcript::{Proof, ProverChain, TranscriptError, VerifierChain, scalars_root};

/// The public bits are cells of the span of this many basis vectors: the `X` and `Y` cells of
/// [`PUBLIC_ROWS`] rows.
const REGION: usize = 11;
const _: () = assert!(PUBLIC_ROWS << 2 == 1 << REGION);

/// The degree the public weight adds past the cells: `11 · 2^10 - 2^11`.
const PUBLIC_EXCESS: usize = 9216;

/// Where `q` and the gate's quotient spill past whole chunks, with room for the masks.
pub(crate) const Q_SPILL: usize = PUBLIC_EXCESS + 64;

/// Why the reduction rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyError {
    Transcript(TranscriptError),
    /// A denominator of the claims is zero.
    Degenerate,
    /// A circuit size the layouts do not support: `log_rows` outside [`MIN_LOG_ROWS`]`..=`[`MAX_LOG_ROWS`].
    Shape,
}

/// How the verifier comes by the one inverse it needs ([`reduce_in`]): that of the product of its denominators.
///
/// - [`Inverse::Compute`], the membership protocol (the deployed contract, `formal/`): it computes it, by the norm
///   to `GF(2^64)` (75 products), and requires the product nonzero.
/// - [`Inverse::Hint`]: the prover sends it, as a sixth scalar after the five, absorbed with them before the last
///   challenge, and the verifier requires `product · hint = 1`. The check is deterministic, and the hint a function
///   of the transcript before it, so soundness and zero knowledge are those of [`Inverse::Compute`]. The proof is
///   one scalar longer (24 bytes of calldata), and the contract 1,172 gas of execution cheaper at 2^22 rows.
///
/// The two are different protocols: the transcript's label names the mode ([`Inverse::name`]), so a proof of one
/// is not a proof of the other.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Inverse {
    #[default]
    Compute,
    Hint,
}

impl Inverse {
    /// The protocol's 16-byte name, the transcript label's first bytes ([`label_in`]).
    pub const fn name(self) -> &'static [u8; 16] {
        match self {
            Self::Compute => b"pcs-quotient-kc1",
            Self::Hint => b"pcs-quotient-kh1",
        }
    }

    /// The scalars of a proof: the two commitments' four, the five values, and the hint if there is one.
    pub const fn proof_len(self) -> usize {
        match self {
            Self::Compute => 9,
            Self::Hint => 10,
        }
    }
}

/// What the verifier computes with: the field, or a recorder of its operations, which is how the EVM contract is
/// written (`crates/evm`).
pub trait Scalar: Copy + Add<Output = Self> + Mul<Output = Self> {
    fn constant(value: F192) -> Self;
    /// `self^(2^64)`.
    fn frobenius(self) -> Self;
    /// A recorder answers yes, and records that the verifier requires it.
    fn is_nonzero(self) -> bool;
    /// Whether `self` is zero: a recorder answers yes, and records that the verifier requires it ([`Inverse::Hint`]).
    fn is_zero(self) -> bool;
}

impl Scalar for F192 {
    fn constant(value: F192) -> Self {
        value
    }

    fn frobenius(self) -> Self {
        F192::frobenius(self)
    }

    fn is_nonzero(self) -> bool {
        self != F192::ZERO
    }

    fn is_zero(self) -> bool {
        self == F192::ZERO
    }
}

/// Where the verifier reads the statement and the proof, and draws its challenges.
pub trait Channel<S> {
    /// `y` then `root`, each as its two halves ([`crate::statement::halves`]).
    fn statement(&mut self) -> [S; 4];
    /// A commitment, as the two scalars it rides the proof as.
    fn next_root(&mut self) -> Result<[S; 2], TranscriptError>;
    fn next(&mut self) -> Result<S, TranscriptError>;
    fn sample(&mut self) -> S;
    /// Nothing is left unread.
    fn finish(&mut self) -> Result<(), TranscriptError>;
}

/// The cells per row, and the variables of the cells' tables: `m = log_rows + 2`.
fn cell_vars(log_rows: usize) -> usize {
    log_rows + 2
}

/// The wiring table: its stack is the table itself. It is public, so its layout is not hidden.
pub fn wiring_layout(log_rows: usize) -> Layout {
    let m = cell_vars(log_rows);
    Layout::new(m, m, m, &[(0, 1 << m)])
}

/// The random lanes of the witness table's hidden layout: with the overflow lane, the cube of lanes `32..40`,
/// whose fold weights span `E` but for a set of challenges below `2^-188` (condition (S), HIDING.md).
pub const WITNESS_RANDOM_LANES: usize = 7;

/// The random lanes of the quotient table's hidden layout: as the witness table's ([`WITNESS_RANDOM_LANES`]).
pub const QUOTIENT_RANDOM_LANES: usize = 7;

/// The fewest rows the hidden layouts take: below `2^17` rows the witness table's lanes are too short for its
/// overflow lane to hold the `33` pieces its blocks give up and the masks, at `2^LOG_PIECE` entries a piece.
pub const MIN_LOG_ROWS: usize = 17;

/// The most rows: above `2^22` rows the quotient table's stack is more than the `2^28` words leanVM's WHIR takes.
pub const MAX_LOG_ROWS: usize = 22;

/// The most rows the reduction alone takes (its domain's basis, `m + 3 <= EXT_BASIS`): circuits past
/// [`MAX_LOG_ROWS`] reduce to claims on tables leanVM's WHIR cannot commit, for a `PCS_OPEN` that takes larger
/// tables ([`verify_reduction_in`]).
pub const MAX_REDUCTION_LOG_ROWS: usize = domain::EXT_BASIS - 5;

/// Whether the reduction alone takes a circuit of `2^log_rows` rows.
pub fn reduction_supported(log_rows: usize) -> bool {
    (MIN_LOG_ROWS..=MAX_REDUCTION_LOG_ROWS).contains(&log_rows)
}

/// Whether the layouts support a circuit of `2^log_rows` rows.
pub fn supported(log_rows: usize) -> bool {
    (MIN_LOG_ROWS..=MAX_LOG_ROWS).contains(&log_rows)
}

/// The witness table: the four row polynomials, then their masks, sixteen entries of the next chunk. Hidden:
/// `32` block lanes, the overflow lane and [`WITNESS_RANDOM_LANES`], `40` lanes.
pub fn witness_layout(log_rows: usize) -> Layout {
    let m = cell_vars(log_rows);
    Layout::hidden(m + 1, m, m + 1, &[(0, 1 << m), (1, 16)], WITNESS_RANDOM_LANES)
}

/// The quotient table: `m + 6` variables, its chunks of `2^m` indexed by two digits, `h` or `q`, that pair or
/// the gate's quotient, and the extension's two limbs. Stacked in lanes of a quarter chunk: `h` below `2^m`,
/// `q` below `3 · 2^m` plus what the public weight's degree adds, and the gate's quotient below
/// `(2 - 1/4) · 2^m` plus what the masks add. Hidden: `55` block lanes, the overflow lane (the pieces the blocks
/// give up, and the four spills) and [`QUOTIENT_RANDOM_LANES`], `63` lanes.
pub fn quotient_layout(log_rows: usize) -> Layout {
    let m = cell_vars(log_rows);
    Layout::hidden(m + 6, m, m + 4, &quotient_chunks(m, Q_SPILL, 64), QUOTIENT_RANDOM_LANES)
}

/// The quotient table's chunks, for `2^m` cells: `q` spills `spill` entries past three chunks, the gate's
/// quotient `tail` past `(2 - 1/4)` chunks.
pub(crate) fn quotient_chunks(m: usize, spill: usize, tail: usize) -> Vec<(usize, usize)> {
    let n = 1usize << m;
    let mut chunks = vec![];
    for e in 0..3 {
        chunks.push((16 * e, n));
        chunks.extend((0..3).map(|digit| (16 * e + 4 + digit, n)));
        chunks.push((16 * e + 7, spill));
    }
    chunks.push((8, n));
    chunks.push((9, 3 * n / 4 + tail));
    chunks
}

/// The seed of one table's padding, from the proof's: Keccak-256 of a label, the table's name and the seed.
pub(crate) fn table_seed(seed: &[u8; 32], table: &[u8]) -> [u8; 32] {
    primitives::hash::hash(&[b"pcs-quotient-pad-".as_slice(), table, seed].concat())
}

/// The secret randomness of one proof (HIDING.md, "Randomness"): the masks, three `K`-coefficients for each of the
/// four row polynomials, and the seed of both tables' padding. It must be uniform, secret, and **fresh per proof,
/// never reused**: two proofs that share the padding's seed have the same random first pieces, and two that share
/// the masks let the second proof's `a_j` be predicted from the first's for a guessed witness, so either confirms
/// the guess (`review_hiding.rs`). [`prove`] draws its own seed, [`prove_with_seed`] takes one; both derive this
/// from it ([`Randomness::derive`]).
#[derive(Clone)]
pub struct Randomness {
    /// `masks[j][i]`: coefficient `i` of row polynomial `j`'s mask.
    pub masks: [[F64; 3]; 4],
    /// The tables' padding: each table's is Keccak-256 of a label, its name and this.
    pub padding: [u8; 32],
}

/// The key derivation's tags: each in one use, none a prefix of another, each followed by fields of fixed length
/// or (the cells' digests) after their count.
const KDF_KEY: &[u8] = b"pcs-quotient-kdf-v1-key";
const KDF_CELLS: &[u8] = b"pcs-quotient-kdf-v1-cells";
const KDF_MASKS: &[u8] = b"pcs-quotient-kdf-v1-masks";
const KDF_PADDING: &[u8] = b"pcs-quotient-kdf-v1-padding";

impl Randomness {
    /// The randomness of a proof from its 32-byte `seed`, by Keccak-256 with distinct tags. A key binds the seed,
    /// the transcript's label (the protocol, the circuit's commitment and the statement: [`label`]) and a digest of
    /// the witness's cells; the masks are the words of Keccak-256(tag ‖ key ‖ `k`) for `k = 0, 1, 2` (word `4k + i`
    /// is `masks[(4k + i) / 3][(4k + i) % 3]`), the padding is Keccak-256(tag ‖ key). A seed reused for another
    /// witness or another statement (a generator that repeats, in a forked process or a restored snapshot) gives
    /// unrelated randomness; reused for the same ones, it gives the same proof again. The seed must still be fresh
    /// per proof and secret: [`prove`] draws it from the operating system.
    pub fn derive(seed: &[u8; 32], index_root: &Hash, statement: &Statement, cells: &[F64]) -> Self {
        Self::derive_in(seed, index_root, statement, cells, Inverse::Compute)
    }

    /// [`Randomness::derive`] for a proof in mode `inverse`: the key binds that mode's label ([`label_in`]), so a
    /// seed reused across the modes gives unrelated randomness too.
    pub fn derive_in(seed: &[u8; 32], index_root: &Hash, statement: &Statement, cells: &[F64], inverse: Inverse) -> Self {
        let label = label_in(index_root, statement, inverse);
        let key = primitives::hash::hash(&[KDF_KEY, seed, &label, &cells_digest(cells)].concat());
        let words: Vec<u64> = (0..3u8)
            .flat_map(|k| {
                let block = primitives::hash::hash(&[KDF_MASKS, &key, &[k]].concat());
                (0..4).map(move |i| u64::from_le_bytes(block[8 * i..8 * i + 8].try_into().unwrap()))
            })
            .collect();
        Self {
            masks: std::array::from_fn(|j| std::array::from_fn(|i| F64(words[3 * j + i]))),
            padding: primitives::hash::hash(&[KDF_PADDING, &key].concat()),
        }
    }
}

/// The cells' digest the key binds: Keccak-256 of its tag, the number of cells, and the digests of their runs of
/// `2^12` cells (each the Keccak-256 of its cells' words, 8 little-endian bytes each), the runs hashed in parallel.
fn cells_digest(cells: &[F64]) -> Hash {
    const RUN: usize = 1 << 12;
    let runs = parallel::map_collect(cells.len().div_ceil(RUN), |r| {
        let run = &cells[r * RUN..cells.len().min((r + 1) * RUN)];
        let bytes: Vec<u8> = run.iter().flat_map(|w| w.0.to_le_bytes()).collect();
        primitives::hash::hash(&bytes)
    });
    let mut hasher = primitives::hash::Hasher::new();
    hasher.update(KDF_CELLS).update(&(cells.len() as u64).to_le_bytes());
    runs.iter().for_each(|digest| {
        hasher.update(digest);
    });
    hasher.finalize()
}

/// A proof's 32-byte seed from the operating system's generator (`rand`'s `OsRng`, that is `getrandom`), which
/// keeps no state in the process: a forked process does not repeat it. [`prove`] draws one per proof.
pub fn fresh_seed() -> [u8; 32] {
    use rand::TryRngCore;
    let mut seed = [0; 32];
    rand::rngs::OsRng
        .try_fill_bytes(&mut seed)
        .expect("the operating system's random generator");
    seed
}

/// The circuit as the verifier's commitment sees it: the coefficients of its wiring polynomial, which sends a
/// cell's point to its successor's.
pub struct Index {
    pub log_rows: usize,
    pub table: Table,
}

impl Index {
    pub fn new(circuit: &Circuit) -> Self {
        let mut sigma = parallel::map_collect(circuit.sigma.len(), |i| point(circuit.sigma[i] as usize));
        domain::coefficients(&mut sigma, F64::ZERO);
        let lane = 1 << wiring_layout(circuit.log_rows).log_lane();
        let table = Table::new(wiring_layout(circuit.log_rows), |l, _, out| {
            out.copy_from_slice(&sigma[l * lane..(l + 1) * lane])
        });
        Self {
            log_rows: circuit.log_rows,
            table,
        }
    }

    fn sigma(&self) -> &[F64] {
        &self.table.stack
    }
}

/// Into `data`, zero and four times the `n` cells long: the polynomial of coefficients `parts`, the `k`-th from
/// `k * n` on, on the quotients' coset.
fn coset_values(data: &mut [F64], parts: &[&[F64]]) {
    let n = data.len() / 4;
    for (k, part) in parts.iter().enumerate() {
        data[k * n..k * n + part.len()].copy_from_slice(part);
    }
    domain::values(data, coset(n.trailing_zeros() as usize));
}

/// The words of extension elements, in their allocation: an `F192` is three `F64`s.
fn into_words(values: Vec<F192>) -> Vec<F64> {
    const _: () = assert!(size_of::<F192>() == 3 * size_of::<F64>() && align_of::<F192>() == align_of::<F64>());
    let mut values = std::mem::ManuallyDrop::new(values);
    let (ptr, len, capacity) = (values.as_mut_ptr(), values.len(), values.capacity());
    // SAFETY: `F192` is `repr(C)` of three `u64`s and `F64` a `repr(transparent)` `u64`: the allocation is
    // `3 * capacity` words of the same alignment, the first `3 * len` of them initialized, and it is no longer
    // owned by `values`.
    unsafe { Vec::from_raw_parts(ptr.cast::<F64>(), 3 * len, 3 * capacity) }
}

/// The offset of the quotients' coset, for `2^m` cells.
fn coset(m: usize) -> F64 {
    domain::beta_ext()[m + 2]
}

/// What a proof leaves: one claim on the witness table, one on the circuit's, two on the quotient table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub witness: Claim,
    pub wiring: Claim,
    pub quotient: Claim,
    /// At a fixed point: the top coefficient of the sum's polynomial.
    pub sum: Claim,
}

/// The weight of bit `j` of a public word: the sum of a word's weighted bits is the element it is read as.
fn bit_weight(j: usize) -> F192 {
    if j < 64 {
        F192::new(1 << j, 0, 0)
    } else {
        F192::new(0, 1 << (j - 64), 0)
    }
}

/// The weight of a cell of the public region: `gamma^J` times its bit's, or zero off the `X` and `Y` cells.
fn public_weight(cell: usize, gamma: F192) -> F192 {
    if cell & 2 != 0 {
        return F192::ZERO;
    }
    let (j, word) = ((cell & 1) | ((cell >> 2) & 63) << 1, cell >> 8);
    (0..word).fold(bit_weight(j), |acc, _| acc * gamma)
}

/// `m_k` for coordinate `k` of the public region, `None` where it is a power of `gamma`: the region's weight is
/// the product of `1 + x_k (1 + m_k)`.
fn coordinate_weight(k: usize) -> Option<F192> {
    match k {
        0 => Some(bit_weight(1)),
        1 => Some(F192::ZERO),
        2..8 => Some(bit_weight(1 << (k - 1))),
        _ => None,
    }
}

/// The two coordinates of the extension over the base field, and the scale of their weights `(1, Y, Y^2, Y^3)`.
pub fn extension() -> ([F192; 2], F192) {
    let (y, y2) = (F192::Y, F192::Y * F192::Y);
    let (d0, d1) = (F192::ONE + y, F192::ONE + y2);
    ([y * d0.inv(), y2 * d1.inv()], (d0 * d1).inv())
}

/// The fixed point of the second claim on the quotient table: the top coefficient of its first chunk.
pub fn sum_point(log_rows: usize) -> Vec<F192> {
    let m = cell_vars(log_rows);
    [&vec![F192::ONE; m][..], &[F192::ZERO; 4], &extension().0].concat()
}

/// The transcript's seed: the protocol's name, the circuit's commitment and the statement (112 bytes).
pub fn label(index_root: &Hash, statement: &Statement) -> Vec<u8> {
    label_in(index_root, statement, Inverse::Compute)
}

/// [`label`] in mode `inverse`: its name is [`Inverse::name`].
pub fn label_in(index_root: &Hash, statement: &Statement, inverse: Inverse) -> Vec<u8> {
    [
        inverse.name().as_slice(),
        index_root,
        &statement.y,
        &statement.root,
    ]
    .concat()
}

/// The gate, `V + X + C + Y·C`, which vanishes on a row's cells.
fn gate<T: Copy + Add<Output = T> + Mul<Output = T>>([x, y, c, v]: [T; 4]) -> T {
    v + x + c + y * c
}

fn batch_inverse(values: &mut [F192]) {
    let mut prefix = Vec::with_capacity(values.len());
    let mut acc = F192::ONE;
    for &v in values.iter() {
        prefix.push(acc);
        acc *= v;
    }
    let mut inverse = acc.inv();
    for (v, p) in values.iter_mut().zip(prefix).rev() {
        let next = inverse * *v;
        *v = inverse * p;
        inverse = next;
    }
}

/// `x^-1` for a nonzero `x`, by its norm to `GF(2^64)`: `m = x^(2^64) x^(2^128)` makes `x m` the norm, whose
/// inverse is its power `2^64 - 2`, reached through the powers `2^k - 1`.
fn inverse<S: Scalar>(x: S) -> S {
    let m = x.frobenius() * x.frobenius().frobenius();
    let norm = x * m;
    let (mut ones, mut k) = (norm, 1);
    for bit in (0..5).rev() {
        let mut shifted = ones;
        for _ in 0..k {
            shifted = shifted * shifted;
        }
        (ones, k) = (shifted * ones, 2 * k);
        if (63 >> bit) & 1 == 1 {
            (ones, k) = (ones * ones * norm, k + 1);
        }
    }
    debug_assert_eq!(k, 63);
    m * (ones * ones)
}

/// The product of the denominators [`reduce_in`] inverts, from the challenges `alpha`, `beta`, `t` and the five
/// values: every `1 + w_k` for `k ≤ m + 1`, the copy identity's `d · d' + w_m`, and the rows' polynomial at `t`.
/// The reduction's value, by other operations: the hint is its inverse.
fn denominators_product(log_rows: usize, [alpha, beta_]: [F192; 2], t: F192, a: [F192; 4], next: F192) -> F192 {
    let m = cell_vars(log_rows);
    let mut w = vec![t];
    for k in 0..m + 1 {
        w.push(w[k] * w[k] + w[k]);
    }
    let x = a[0] + t * a[1] + w[1] * (a[2] + t * a[3]);
    let product = (alpha + x + beta_ * t) * (alpha + x + beta_ * next);
    let tau = row_vanishing(m);
    let rows = (0..m - 1).fold(F192::ZERO, |acc, k| acc + w[k].mul_base(tau[k]));
    w.iter().fold((product + w[m]) * rows, |acc, &w| acc * (F192::ONE + w))
}

/// The hint [`verify_in`] requires of a proof in mode [`Inverse::Hint`], from its first nine scalars (the
/// commitments and the five values; any after them are not read): the inverse of the product of the denominators
/// at the challenges they lead to, or `Degenerate` where that product is zero, which no hint passes.
pub fn hint(index_root: &Hash, statement: &Statement, proof: &Proof, log_rows: usize) -> Result<F192, VerifyError> {
    if !reduction_supported(log_rows) {
        return Err(VerifyError::Shape);
    }
    let transcript = VerifyError::Transcript;
    let first = Proof {
        stream: proof.stream.iter().take(Inverse::Compute.proof_len()).copied().collect(),
    };
    let mut chain = VerifierChain::new(&label_in(index_root, statement, Inverse::Hint), &first);
    chain.next_root().map_err(transcript)?;
    let [alpha, beta_, _gamma] = [(); 3].map(|_| chain.sample());
    chain.next_root().map_err(transcript)?;
    let t = chain.sample();
    let mut a = [F192::ZERO; 4];
    for value in &mut a {
        *value = chain.next().map_err(transcript)?;
    }
    let next = chain.next().map_err(transcript)?;
    let product = denominators_product(log_rows, [alpha, beta_], t, a, next);
    if product.is_zero() {
        return Err(VerifyError::Degenerate);
    }
    Ok(product.inv())
}

/// A proof and what the prover keeps to open its claims.
pub struct Proved {
    pub proof: Proof,
    /// Whether the quotients fit their layout, as they do for a witness.
    pub fits: bool,
    pub claims: Claims,
    pub roots: [Hash; 2],
    pub tables: Tables,
}

/// The two tables a proof commits, which [`open`] consumes.
pub struct Tables {
    pub witness: Table,
    pub witness_committed: Committed,
    pub quotient: Table,
    pub quotient_committed: Committed,
}

/// Prove `statement` from the cells of a witness, against the circuit committed as `index_root`, with randomness
/// of its own, fresh per proof and never reused: a 32-byte seed from the operating system ([`fresh_seed`]), from
/// which [`Randomness::derive`] makes the masks and the tables' padding. Panics on a challenge the verifier rejects.
pub fn prove(circuit: &Circuit, index: &Index, index_root: &Hash, statement: &Statement, cells: &[F64]) -> Proved {
    prove_in(circuit, index, index_root, statement, cells, Inverse::Compute)
}

/// [`prove`] in mode `inverse` ([`Inverse`]): the proof is one [`verify_in`] accepts in that mode.
pub fn prove_in(
    circuit: &Circuit,
    index: &Index,
    index_root: &Hash,
    statement: &Statement,
    cells: &[F64],
    inverse: Inverse,
) -> Proved {
    prove_with_seed_in(circuit, index, index_root, statement, cells, &fresh_seed(), inverse)
}

/// [`prove`] with its 32-byte seed given, deterministic: for tests and reproducible benchmarks. The randomness is
/// always [`Randomness::derive`]'s, bound to the statement and the witness, so a seed reused for another witness
/// gives unrelated randomness; the proof hides the witness only if `seed` is secret and fresh per proof, as
/// [`prove`]'s is. Panics on a challenge the verifier rejects.
pub fn prove_with_seed(
    circuit: &Circuit,
    index: &Index,
    index_root: &Hash,
    statement: &Statement,
    cells: &[F64],
    seed: &[u8; 32],
) -> Proved {
    prove_with_seed_in(circuit, index, index_root, statement, cells, seed, Inverse::Compute)
}

/// [`prove_with_seed`] in mode `inverse`: its randomness is [`Randomness::derive_in`]'s for that mode.
pub fn prove_with_seed_in(
    circuit: &Circuit,
    index: &Index,
    index_root: &Hash,
    statement: &Statement,
    cells: &[F64],
    seed: &[u8; 32],
    inverse: Inverse,
) -> Proved {
    let randomness = Randomness::derive_in(seed, index_root, statement, cells, inverse);
    prove_with_randomness_in(circuit, index, index_root, statement, cells, &randomness, inverse)
}

/// [`prove`] with its randomness given. Crate-private: outside the crate, randomness reaches the prover only through
/// [`Randomness::derive`] ([`prove`], [`prove_with_seed`]), so it cannot be reused across witnesses; the crate's
/// tests use this to show what reuse would reveal (`review_hiding.rs`). Panics on a challenge the verifier rejects.
#[cfg(test)]
pub(crate) fn prove_with_randomness(
    circuit: &Circuit,
    index: &Index,
    index_root: &Hash,
    statement: &Statement,
    cells: &[F64],
    randomness: &Randomness,
) -> Proved {
    prove_with_randomness_in(circuit, index, index_root, statement, cells, randomness, Inverse::Compute)
}

/// [`prove_with_randomness`] in mode `inverse` (for the crate's tests, and what [`prove_with_seed_in`] calls).
pub(crate) fn prove_with_randomness_in(
    circuit: &Circuit,
    index: &Index,
    index_root: &Hash,
    statement: &Statement,
    cells: &[F64],
    randomness: &Randomness,
    inverse: Inverse,
) -> Proved {
    let Randomness { masks, padding } = randomness;
    assert!(
        supported(circuit.log_rows),
        "2^{} rows: the layouts take 2^{MIN_LOG_ROWS} to 2^{MAX_LOG_ROWS}",
        circuit.log_rows
    );
    let m = cell_vars(circuit.log_rows);
    let n = 1usize << m;
    assert_eq!(cells.len(), n);
    assert!(m > REGION + 2 && m + 3 <= domain::EXT_BASIS);
    let mut ps = ProverChain::new(&label_in(index_root, statement, inverse));

    // The witness: four polynomials in the row, each with a multiple of the rows' vanishing polynomial.
    let span = tracing::info_span!("Witness").entered();
    let mut w_hat = cells.to_vec();
    domain::coefficients(&mut w_hat, F64::ZERO);
    let mut mask = [F64::ZERO; 16];
    for (j, coeffs) in masks.iter().enumerate() {
        for (i, &coeff) in coeffs.iter().enumerate() {
            mask[4 * i + j] = coeff;
        }
    }
    // Hidden, its stack holds the coefficients out of order: they are read back from it where they are needed.
    let witness = Table::hidden(
        witness_layout(circuit.log_rows),
        &table_seed(padding, b"witness"),
        |start, out| {
            for (i, o) in (start..).zip(out.iter_mut()) {
                *o = if i < n {
                    w_hat[i]
                } else {
                    mask.get(i - n).copied().unwrap_or(F64::ZERO)
                };
            }
        },
    );
    drop(w_hat);
    let witness_committed = tracing::info_span!("Commit").in_scope(|| opening::commit(&witness));
    ps.send_root(&witness_committed.root);
    drop(span);
    let [alpha, beta_, gamma] = [(); 3].map(|_| ps.sample());

    // The sum's polynomial on the cells.
    let span = tracing::info_span!("Sum").entered();
    let mut h = vec![F192::ZERO; n];
    parallel::chunks_mut(&mut h, 1 << 12, |chunk_index, chunk| {
        let base = chunk_index << 12;
        let mut d: Vec<F192> = (0..chunk.len())
            .flat_map(|k| {
                let i = base + k;
                let common = alpha + F192::from(cells[i]);
                [point(i), point(circuit.sigma[i] as usize)].map(|to| common + beta_.mul_base(to))
            })
            .collect();
        batch_inverse(&mut d);
        for (k, out) in chunk.iter_mut().enumerate() {
            *out = d[2 * k] + d[2 * k + 1];
            if base + k < 1 << REGION {
                *out += public_weight(base + k, gamma).mul_base(cells[base + k]);
            }
        }
    });
    domain::coefficients(&mut h, F64::ZERO);
    let h_hat = h;
    drop(span);

    // Both quotients, on a coset four times the cells.
    let span = tracing::info_span!("Quotients").entered();
    let big = 4 * n;
    let offset = coset(m);
    let offsets = chain(offset, m + 1);
    // Two of this loop's buffers serve the quotient table once it is done: `values`, the witness's and the
    // wiring polynomial's values (the latter not kept with the index: only this loop reads them), becomes the
    // table's stack, and `q` the half codeword its commitment encodes in. Reused whole, they spare the allocator
    // mapping fresh memory its freed pieces could not serve.
    let layout = quotient_layout(circuit.log_rows);
    let placed = layout.placed();
    let mut values = Vec::with_capacity(placed.max(2 * big));
    values.resize(2 * big, F64::ZERO);
    let (w_values, sigma_values) = values.split_at_mut(big);
    witness.read(0, &mut w_values[..n]);
    coset_values(w_values, &[&[], &mask]);
    // Note: these depend on the circuit alone, yet every proof computes them again (a `4n`-point transform);
    // the index could keep them, for `4n` more words held between proofs.
    coset_values(sigma_values, &[index.sigma()]);
    let mut q = Vec::with_capacity(big.max(placed.div_ceil(3)));
    q.resize(big, F192::ZERO);
    q[..n].copy_from_slice(&h_hat);
    domain::values(&mut q, offset);
    let mut q_gate = vec![F64::ZERO; big];

    let (b, tau) = (coordinates(REGION), row_vanishing(m));
    let row_poly = |x: F64| {
        chain(x, m - 1)
            .iter()
            .zip(&tau)
            .fold(F64::ZERO, |acc, (&w, &t)| acc + t * w)
    };
    let row_low: [F64; 4] = std::array::from_fn(|c| row_poly(point(c)));
    let gammas = [gamma, gamma * gamma, (gamma * gamma) * (gamma * gamma)];
    parallel::chunks_mut2(&mut q, &mut q_gate, 1 << REGION, |high, q, q_gate| {
        let base = high << REGION;
        let w_at = |k: usize| offsets[k] + point(base >> k);
        // The public weight on this block: its region coordinates are the low index's bits, shifted.
        let indicator = (REGION..m).fold(F64::ONE, |acc, k| acc * (F64::ONE + w_at(k)));
        let mut weights = vec![F192::from(indicator)];
        if !indicator.is_zero() {
            for k in 0..REGION {
                let shift = (k..REGION).fold(F64::ZERO, |acc, j| acc + b[j - k] * w_at(j));
                let slope = F192::ONE + coordinate_weight(k).unwrap_or_else(|| gammas[k - 8]);
                let low = F192::ONE + slope.mul_base(shift);
                for i in 0..weights.len() {
                    weights.push(weights[i] * (low + slope));
                    weights[i] *= low;
                }
            }
        }
        let cell_vanishing = w_at(m).inv();
        let row_base = row_poly(offset + point(base));
        let row_vanishing: [F64; 4] = std::array::from_fn(|c| (row_base + row_low[c]).inv());
        for (low, (q, q_gate)) in q.iter_mut().zip(q_gate.iter_mut()).enumerate() {
            let i = base + low;
            let w = w_values[i];
            let common = alpha + F192::from(w);
            let d = common + beta_.mul_base(offset + point(i));
            let d_next = common + beta_.mul_base(sigma_values[i]);
            let public = weights.get(low).map_or(F192::ZERO, |weight| weight.mul_base(w));
            *q = ((*q + public) * d * d_next + d + d_next).mul_base(cell_vanishing);
            let row = [w, w_values[i ^ 1], w_values[i ^ 2], w_values[i ^ 3]];
            *q_gate = gate(row) * row_vanishing[low & 3];
        }
    });
    domain::coefficients(&mut q, offset);
    domain::coefficients(&mut q_gate, offset);

    // The quotient table: `m` variables of a polynomial, two more digits, `h` or `q`, that pair or the gate's
    // quotient, and the extension's two.
    // For a witness, both quotients are polynomials of the degrees the layout holds. For anything else they may
    // not be, and what the layout leaves out is dropped: the claims are then false.
    // The stack is built in `values`, whose old words stay wherever the fill does not write: it writes every word
    // of each run it is handed (debug builds check it).
    let fits = q[3 * n + layout.covered(m, 7)..].iter().all(|v| v.is_zero())
        && q_gate[n + layout.covered(m, 9)..].iter().all(|v| v.is_zero());
    let quotient = Table::hidden_in(layout, values, &table_seed(padding, b"quotient"), |start, out| {
        // A run of pieces of one block, or a piece: in one chunk.
        let (c, within) = (start >> m, start & (n - 1));
        let (digit, limb) = (c & 3, c >> 4);
        let from = digit * n + within;
        let len = out.len();
        let at = |values: &[F192], out: &mut [F64]| {
            for (o, v) in out.iter_mut().zip(&values[from..from + len]) {
                *o = F64([v.c0, v.c1, v.c2][limb]);
            }
        };
        match c & 12 {
            0 => at(&h_hat, out),
            4 => at(&q, out),
            _ => out.copy_from_slice(&q_gate[from..from + len]),
        }
    });
    drop((h_hat, q_gate));
    let scratch = into_words(q);
    let quotient_committed = tracing::info_span!("Commit").in_scope(|| opening::commit_in(&quotient, scratch));
    ps.send_root(&quotient_committed.root);
    drop(span);

    let t = ps.sample();
    let digits: Vec<F192> = std::iter::successors(Some(t), |&w| Some(w * w + w))
        .take(m + 1)
        .collect();
    let mut w_hat = vec![F64::ZERO; n];
    witness.read(0, &mut w_hat);
    let a: [F192; 4] = std::array::from_fn(|j| {
        domain::evaluate(&w_hat, j, 4, &digits[2..m]) + digits[m] * domain::evaluate(&mask, j, 4, &digits[2..4])
    });
    drop(w_hat);
    a.iter().for_each(|&x| ps.send(x));
    let next = domain::evaluate(index.sigma(), 0, 1, &digits[..m]);
    ps.send(next);
    if inverse == Inverse::Hint {
        // Zero where the verifier rejects whatever the hint, which then panics below.
        let product = denominators_product(circuit.log_rows, [alpha, beta_], t, a, next);
        ps.send(if product.is_zero() { F192::ZERO } else { product.inv() });
    }

    let proof = ps.into_proof();
    let (roots, claims) =
        verify_in(index_root, statement, &proof, circuit.log_rows, inverse).expect("a challenge to reject");
    Proved {
        proof,
        fits,
        claims,
        roots,
        tables: Tables {
            witness,
            witness_committed,
            quotient,
            quotient_committed,
        },
    }
}

/// What [`reduce`] leaves: the two commitments, each as its two scalars, three claims as a point and a value, and
/// the value of the one at [`sum_point`].
pub struct Reduced<S> {
    pub roots: [[S; 2]; 2],
    pub witness: (Vec<S>, S),
    pub wiring: (Vec<S>, S),
    pub quotient: (Vec<S>, S),
    pub sum: S,
}

/// The verifier, on any [`Scalar`]: the proof read from `channel`, down to the commitments it names and the four
/// claims. It rejects only a challenge at which a denominator vanishes.
pub fn reduce<S: Scalar>(channel: &mut impl Channel<S>, log_rows: usize) -> Result<Reduced<S>, VerifyError> {
    reduce_in(channel, log_rows, Inverse::Compute)
}

/// [`reduce`] in mode `mode`. With [`Inverse::Hint`] it reads a sixth scalar after the five, the hint, before it
/// draws `rho`, and rejects unless the product of the denominators times the hint is one, where [`reduce`] rejects
/// a zero product and computes its inverse. With [`Inverse::Compute`] it is [`reduce`], operation for operation.
pub fn reduce_in<S: Scalar>(
    channel: &mut impl Channel<S>,
    log_rows: usize,
    mode: Inverse,
) -> Result<Reduced<S>, VerifyError> {
    let transcript = VerifyError::Transcript;
    let m = cell_vars(log_rows);
    let base = |x: F64| S::constant(F192::from(x));
    let one = S::constant(F192::ONE);

    let statement = channel.statement();
    let witness_root = channel.next_root().map_err(transcript)?;
    let [alpha, beta_, gamma] = [(); 3].map(|_| channel.sample());
    let quotient_root = channel.next_root().map_err(transcript)?;
    let t = channel.sample();
    let mut a = [t; 4];
    for value in &mut a {
        *value = channel.next().map_err(transcript)?;
    }
    let next = channel.next().map_err(transcript)?;
    let hint = match mode {
        Inverse::Compute => None,
        Inverse::Hint => Some(channel.next().map_err(transcript)?),
    };
    let rho = channel.sample();
    channel.finish().map_err(transcript)?;

    // `w_k(t)`, up to the two digits past the cells.
    let mut w = vec![t];
    for k in 0..m + 1 {
        w.push(w[k] * w[k] + w[k]);
    }

    // The four cells of the row of `t`, and its gate.
    let theta = beta()[1];
    let cell = |shift: F64, second: bool| {
        let (first, second) = (t + base(shift), if second { w[1] + one } else { w[1] });
        a[0] + first * a[1] + second * (a[2] + first * a[3])
    };
    let row = [
        cell(F64::ZERO, false),
        cell(F64::ONE, false),
        cell(theta, true),
        cell(theta + F64::ONE, true),
    ];
    let x = row[0];
    let gate = gate(row);

    // The public weight at `t`, and what the weighted public bits must sum to.
    let b = coordinates(REGION);
    let gamma2 = gamma * gamma;
    let gammas = [gamma, gamma2, gamma2 * gamma2];
    let mut public = (REGION..m).fold(one, |acc, k| acc * (one + w[k]));
    for k in 0..REGION {
        let coordinate = (k + 1..REGION).fold(w[k], |acc, j| acc + base(b[j - k]) * w[j]);
        let slope = match coordinate_weight(k) {
            Some(weight) => S::constant(F192::ONE + weight),
            None => one + gammas[k - 8],
        };
        public = public * (one + coordinate * slope);
    }
    let target = statement[0] + gamma * statement[1] + gamma2 * (statement[2] + gamma * statement[3]) + gammas[2];

    let tau = row_vanishing(m);
    let rows = (0..m - 1).fold(S::constant(F192::ZERO), |acc, k| acc + base(tau[k]) * w[k]);
    let (d, d_next) = (alpha + x + beta_ * t, alpha + x + beta_ * next);
    let product = d * d_next;
    let copies = d + d_next + public * x * product;

    // One inversion: of every `1 + w_k`, of the copy identity's denominator, and of the rows' polynomial.
    let mut denominators: Vec<S> = w.iter().map(|&w| one + w).collect();
    denominators.extend([product + w[m], rows]);
    let mut prefix = vec![one];
    for &value in &denominators {
        prefix.push(*prefix.last().unwrap() * value);
    }
    // (`product` is the copy identity's, used below.)
    let all = prefix[denominators.len()];
    let mut running = match hint {
        None => {
            if !all.is_nonzero() {
                return Err(VerifyError::Degenerate);
            }
            inverse(all)
        }
        Some(hint) => {
            if !(all * hint + one).is_zero() {
                return Err(VerifyError::Degenerate);
            }
            hint
        }
    };
    let mut inverses = denominators.clone();
    for i in (0..denominators.len()).rev() {
        inverses[i] = running * prefix[i];
        running = running * denominators[i];
    }
    let u: Vec<S> = (0..m + 2).map(|k| w[k] * inverses[k]).collect();
    let (copy_inverse, rows_inverse) = (inverses[m + 2], inverses[m + 3]);
    let middle = (3..m).fold(inverses[2], |acc, k| acc * inverses[k]);
    let wiring_scale = middle * inverses[0] * inverses[1];
    let quotient_scale = wiring_scale * inverses[m] * inverses[m + 1];

    let rho2 = rho * rho;
    let opened = (one + rho2) * (a[0] + rho * (a[0] + a[1])) + rho2 * (a[2] + rho * (a[2] + a[3]));
    let ([y0, y1], scale) = extension();
    let scale = S::constant(scale);
    let identities = (one + rho) * copies * rows + rho * product * gate;
    Ok(Reduced {
        roots: [witness_root, quotient_root],
        witness: ([&[rho, rho2][..], &u[2..m + 1]].concat(), opened * middle * inverses[m]),
        wiring: (u[..m].to_vec(), next * wiring_scale),
        quotient: (
            [&u[..], &[w[m] * copy_inverse, rho, S::constant(y0), S::constant(y1)]].concat(),
            scale * quotient_scale * copy_inverse * rows_inverse * identities,
        ),
        sum: scale * target,
    })
}

/// The proof as the field verifier reads it.
pub struct Stream<'a> {
    pub chain: VerifierChain<'a>,
    pub statement: Statement,
}

impl Channel<F192> for Stream<'_> {
    fn statement(&mut self) -> [F192; 4] {
        self.statement.halves()
    }

    fn next_root(&mut self) -> Result<[F192; 2], TranscriptError> {
        self.chain.next_root()
    }

    fn next(&mut self) -> Result<F192, TranscriptError> {
        self.chain.next()
    }

    fn sample(&mut self) -> F192 {
        self.chain.sample()
    }

    fn finish(&mut self) -> Result<(), TranscriptError> {
        self.chain.finish()
    }
}

/// Verify a proof of `statement` against the circuit committed as `index_root`, down to the two commitments it
/// names (the witness table's, then the quotient table's) and four claims: it holds if, for each commitment, one
/// table of its level-0 Johnson list satisfies all the claims on it (one opening per commitment, [`verify_openings`]).
pub fn verify(
    index_root: &Hash,
    statement: &Statement,
    proof: &Proof,
    log_rows: usize,
) -> Result<([Hash; 2], Claims), VerifyError> {
    verify_in(index_root, statement, proof, log_rows, Inverse::Compute)
}

/// [`verify`] in mode `inverse`: the transcript's label is that mode's ([`label_in`]), the reduction [`reduce_in`]'s.
pub fn verify_in(
    index_root: &Hash,
    statement: &Statement,
    proof: &Proof,
    log_rows: usize,
    inverse: Inverse,
) -> Result<([Hash; 2], Claims), VerifyError> {
    if !supported(log_rows) {
        return Err(VerifyError::Shape);
    }
    verify_reduction_in(index_root, statement, proof, log_rows, inverse)
}

/// [`verify_in`] at any size the reduction takes ([`reduction_supported`]), past the sizes whose claims leanVM's
/// WHIR opens: the commitments and the claims, for a `PCS_OPEN` that takes the tables.
pub fn verify_reduction_in(
    index_root: &Hash,
    statement: &Statement,
    proof: &Proof,
    log_rows: usize,
    inverse: Inverse,
) -> Result<([Hash; 2], Claims), VerifyError> {
    if !reduction_supported(log_rows) {
        return Err(VerifyError::Shape);
    }
    let mut stream = Stream {
        chain: VerifierChain::new(&label_in(index_root, statement, inverse), proof),
        statement: *statement,
    };
    let reduced = reduce_in(&mut stream, log_rows, inverse)?;
    let [witness_root, quotient_root] = reduced.roots.map(|root| scalars_root(&root));
    let roots = [
        witness_root.map_err(VerifyError::Transcript)?,
        quotient_root.map_err(VerifyError::Transcript)?,
    ];
    let claim = |(point, value)| Claim { point, value };
    Ok((
        roots,
        Claims {
            witness: claim(reduced.witness),
            wiring: claim(reduced.wiring),
            quotient: claim(reduced.quotient),
            sum: Claim {
                point: sum_point(log_rows),
                value: reduced.sum,
            },
        },
    ))
}

/// The openings of a proof's four claims: one per commitment, the quotient table's two claims together.
pub struct Openings {
    pub witness: fiat_shamir::transcript::Proof,
    pub wiring: fiat_shamir::transcript::Proof,
    pub quotient: fiat_shamir::transcript::Proof,
}

/// Open a proof's `claims` on the tables it committed, each table freed as its opening is done with it. The
/// wiring's opening is about public data: anyone can make it.
pub fn open(tables: Tables, claims: &Claims, index: &Index, index_committed: &Committed) -> Openings {
    let Tables {
        witness,
        witness_committed,
        quotient,
        quotient_committed,
    } = tables;
    let witness = tracing::info_span!("Open witness")
        .in_scope(|| opening::open_owned(witness, witness_committed, std::slice::from_ref(&claims.witness)));
    let wiring = tracing::info_span!("Open wiring")
        .in_scope(|| opening::open(&index.table, index_committed, std::slice::from_ref(&claims.wiring)));
    let quotient = tracing::info_span!("Open quotient").in_scope(|| {
        opening::open_owned(
            quotient,
            quotient_committed,
            &[claims.quotient.clone(), claims.sum.clone()],
        )
    });
    Openings {
        witness,
        wiring,
        quotient,
    }
}

/// A fingerprint of a proof and its openings: the Keccak-256 of every scalar, row word and digest they carry,
/// each list after its length. Two provers that agree on it made the same proof.
pub fn digest(proof: &Proof, openings: &Openings) -> Hash {
    let mut bytes = vec![];
    let scalars = |bytes: &mut Vec<u8>, xs: &[F192]| {
        bytes.extend_from_slice(&(xs.len() as u64).to_le_bytes());
        for x in xs {
            for limb in [x.c0, x.c1, x.c2] {
                bytes.extend_from_slice(&limb.to_le_bytes());
            }
        }
    };
    scalars(&mut bytes, &proof.stream);
    for opening in [&openings.witness, &openings.wiring, &openings.quotient] {
        scalars(&mut bytes, &opening.stream);
        bytes.extend_from_slice(&(opening.merkle.len() as u64).to_le_bytes());
        for paths in &opening.merkle {
            bytes.extend_from_slice(&(paths.leaf_data.len() as u64).to_le_bytes());
            for row in &paths.leaf_data {
                bytes.extend_from_slice(&(row.len() as u64).to_le_bytes());
                row.iter()
                    .for_each(|word| bytes.extend_from_slice(&word.0.to_le_bytes()));
            }
            bytes.extend_from_slice(&(paths.sibling_hashes.len() as u64).to_le_bytes());
            paths
                .sibling_hashes
                .iter()
                .for_each(|hash| bytes.extend_from_slice(hash));
        }
    }
    primitives::hash::hash(&bytes)
}

/// Check the openings of four claims against the commitments they name.
pub fn verify_openings(
    log_rows: usize,
    index_root: &Hash,
    roots: &[Hash; 2],
    claims: &Claims,
    openings: &Openings,
) -> Result<(), verifier::VerifierError> {
    use opening::{verify, wire_proof};
    if !supported(log_rows) {
        return Err(verifier::VerifierError::WhirShape);
    }
    verify(
        &witness_layout(log_rows),
        &roots[0],
        std::slice::from_ref(&claims.witness),
        &wire_proof(&openings.witness),
    )?;
    verify(
        &wiring_layout(log_rows),
        index_root,
        std::slice::from_ref(&claims.wiring),
        &wire_proof(&openings.wiring),
    )?;
    verify(
        &quotient_layout(log_rows),
        &roots[1],
        &[claims.quotient.clone(), claims.sum.clone()],
        &wire_proof(&openings.quotient),
    )
}

#[cfg(test)]
mod adversarial;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{Builder, Src, public_words};
    use primitives::test_rng::Rng;

    /// A size the layouts do not take is rejected, not a panic: the verifiers return an error before reading.
    #[test]
    fn unsupported_sizes_are_rejected() {
        let statement = Statement {
            y: [1; 32],
            root: [2; 32],
        };
        let proof = Proof {
            stream: vec![F192::ZERO; 9],
        };
        for log_rows in [0, 13, MIN_LOG_ROWS - 1, MAX_LOG_ROWS + 1, 40] {
            assert!(!supported(log_rows));
            assert_eq!(verify(&[0; 32], &statement, &proof, log_rows), Err(VerifyError::Shape));
        }
        assert!((MIN_LOG_ROWS..=MAX_LOG_ROWS).all(supported));
    }

    /// A small circuit with the membership statement's shape: `root` is a Keccak-256 of `y`, the input.
    fn toy() -> Circuit {
        let mut b = Builder::new();
        let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
        let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
        b.finish(17, &public_words(&x, &digest))
    }

    fn toy_statement(x: &[u8; 32]) -> Statement {
        Statement {
            y: *x,
            root: crate::statement::pair(x, x),
        }
    }

    fn seed(rng: &mut Rng) -> [u8; 32] {
        std::array::from_fn(|_| rng.next_u8())
    }

    fn truth(index: &Index, proved: &Proved) -> [bool; 4] {
        let holds = |table: &Table, claim: &Claim| table.eval(&claim.point) == claim.value;
        let claims = &proved.claims;
        [
            holds(&proved.tables.witness, &claims.witness),
            holds(&index.table, &claims.wiring),
            holds(&proved.tables.quotient, &claims.quotient),
            holds(&proved.tables.quotient, &claims.sum),
        ]
    }

    /// The prover's output, pinned: the proof and its three openings on the toy circuit hash to what the prover
    /// made when the hidden layouts took the gadget (`HIDING.md`; the pin before, when the openings' transcripts
    /// took leanVM's shape (`opening::iv`) and the randomness came to be derived from one seed, was `4462f71d…`;
    /// with the masks and the padding's seed drawn directly, `aebdde8c…`; before the hidden layouts, at d940553,
    /// `7d2d3430…`), so a change to how the prover computes
    /// cannot change a byte of what it proves. The proof's seed is part of the input: [`prove_with_randomness`] is
    /// deterministic, and the randomness is [`Randomness::derive`]'s, as [`prove`]'s is.
    #[test]
    fn proofs_are_pinned() {
        let mut rng = Rng::new(0x1D);
        let circuit = toy();
        let index = Index::new(&circuit);
        let index_committed = opening::commit(&index.table);
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let statement = toy_statement(&x);
        let inputs: Vec<bool> = (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect();
        let cells = circuit.cells(&inputs);
        let randomness = Randomness::derive(&seed(&mut rng), &index_committed.root, &statement, &cells);
        let proved = prove_with_randomness(&circuit, &index, &index_committed.root, &statement, &cells, &randomness);
        let openings = open(proved.tables, &proved.claims, &index, &index_committed);
        let hex: String = digest(&proved.proof, &openings)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(hex, "8e39cf6a95ae46bf134f38f32a0044c9eca690bc37c68f6134a24df7eaaa2fec");
    }

    /// On a small circuit: an honest proof leaves four true claims that open, and a witness that breaks one gate,
    /// one copy, one input's range or one public bit leaves a false one.
    #[test]
    fn claims_hold_exactly_for_a_witness() {
        let mut rng = Rng::new(0x51);
        let circuit = toy();
        let index = Index::new(&circuit);
        let index_committed = opening::commit(&index.table);
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let statement = toy_statement(&x);
        let inputs: Vec<bool> = (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect();
        let cells = circuit.cells(&inputs);
        for r in 0..cells.len() / 4 {
            assert!(gate(std::array::from_fn::<_, 4, _>(|c| cells[4 * r + c])).is_zero());
        }
        for (i, &next) in circuit.sigma.iter().enumerate() {
            assert_eq!(cells[i], cells[next as usize]);
        }

        let proved = prove(&circuit, &index, &index_committed.root, &statement, &cells);
        assert!(proved.fits);
        assert_eq!(truth(&index, &proved), [true; 4]);
        assert_eq!(proved.proof.stream.len(), 9);
        let openings = open(proved.tables, &proved.claims, &index, &index_committed);
        assert_eq!(
            verify_openings(
                circuit.log_rows,
                &index_committed.root,
                &proved.roots,
                &proved.claims,
                &openings
            ),
            Ok(())
        );

        // A proof made for one statement, read against another.
        let mut other = statement;
        other.root[3] ^= 0x10;
        let wrong = prove(&circuit, &index, &index_committed.root, &other, &cells);
        assert_eq!(truth(&index, &wrong), [true, true, true, false]);

        let input_row = PUBLIC_ROWS + 5;
        let some_row = PUBLIC_ROWS + 256 + 9000;
        type Tamper<'a> = &'a dyn Fn(&mut Vec<F64>);
        let cases: [(&str, Tamper); 4] = [
            // A row's output alone.
            ("gate", &|cells| cells[4 * some_row + 3] += F64::ONE),
            // An input that is not a bit, wherever it is read.
            ("range", &|cells| {
                let (from, to) = (cells[4 * input_row + 3], F64(0x1234_5678));
                let cycle: Vec<usize> =
                    std::iter::successors(Some(4 * input_row + 3), |&i| Some(circuit.sigma[i] as usize))
                        .skip(1)
                        .take_while(|&i| i != 4 * input_row + 3)
                        .collect();
                assert_eq!(cells[cycle[0]], from);
                for i in cycle.into_iter().chain([4 * input_row + 3]) {
                    cells[i] = to;
                }
            }),
            // The constant one, read as zero everywhere.
            ("one", &|cells| {
                let anchor = 4 * (4 * 64);
                let mut i = anchor;
                loop {
                    cells[i] = F64::ZERO;
                    i = circuit.sigma[i] as usize;
                    if i == anchor {
                        break;
                    }
                }
            }),
            // A reader that departs from what it reads.
            ("copy", &|cells| cells[4 * some_row] += F64::ONE),
        ];
        for (name, tamper) in cases {
            let mut bad = cells.clone();
            tamper(&mut bad);
            let truth = truth(
                &index,
                &prove(&circuit, &index, &index_committed.root, &statement, &bad),
            );
            assert!(truth.contains(&false), "{name}: {truth:?}");
            assert!(truth[0] && truth[1], "{name}: {truth:?}");
        }
    }

    /// A toy proof in mode `inverse`, its commitments' tables and its openings.
    struct Toy {
        circuit: Circuit,
        index: Index,
        index_committed: Committed,
        statement: Statement,
        cells: Vec<F64>,
    }

    fn toy_witness(rng: &mut Rng) -> Toy {
        let circuit = toy();
        let index = Index::new(&circuit);
        let index_committed = opening::commit(&index.table);
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let inputs: Vec<bool> = (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect();
        let cells = circuit.cells(&inputs);
        Toy {
            circuit,
            index,
            index_committed,
            statement: toy_statement(&x),
            cells,
        }
    }

    impl Toy {
        fn prove(&self, seed: &[u8; 32], inverse: Inverse) -> Proved {
            let root = &self.index_committed.root;
            prove_with_seed_in(&self.circuit, &self.index, root, &self.statement, &self.cells, seed, inverse)
        }

        fn verify(&self, proof: &Proof, inverse: Inverse) -> Result<([Hash; 2], Claims), VerifyError> {
            verify_in(&self.index_committed.root, &self.statement, proof, self.circuit.log_rows, inverse)
        }

        fn opens(&self, roots: &[Hash; 2], claims: &Claims, openings: &Openings) -> bool {
            let root = &self.index_committed.root;
            verify_openings(self.circuit.log_rows, root, roots, claims, openings).is_ok()
        }
    }

    /// In hint mode: an honest proof is ten scalars, its last the inverse [`hint`] computes, and leaves the four
    /// true claims [`verify_in`] leaves, which open; any other hint (one bit off, another element, zero, the
    /// inverse's inverse) is `Degenerate`. The compute mode's verifier is untouched by the mode's existence: the
    /// pinned proof (`proofs_are_pinned`) is the same.
    #[test]
    fn hint_proofs_verify_and_open() {
        let mut rng = Rng::new(0x41);
        let toy = toy_witness(&mut rng);
        let proved = toy.prove(&seed(&mut rng), Inverse::Hint);
        assert!(proved.fits);
        assert_eq!(truth(&toy.index, &proved), [true; 4]);
        let proof = proved.proof.clone();
        assert_eq!(proof.stream.len(), Inverse::Hint.proof_len());
        let log_rows = toy.circuit.log_rows;
        let expected = hint(&toy.index_committed.root, &toy.statement, &proof, log_rows).expect("a hint");
        assert_eq!(proof.stream[9], expected);
        assert_ne!(expected, F192::ZERO);
        let (roots, claims) = toy.verify(&proof, Inverse::Hint).expect("an honest proof");
        assert_eq!((roots, &claims), (proved.roots, &proved.claims));
        let openings = open(proved.tables, &proved.claims, &toy.index, &toy.index_committed);
        assert!(toy.opens(&roots, &claims, &openings));

        for other in [
            expected + F192::ONE,
            expected + F192::new(0, 0, 1 << 63),
            expected * F192::Y,
            F192::ZERO,
            F192::ONE,
            expected.inv(),
        ] {
            let mut tampered = proof.clone();
            tampered.stream[9] = other;
            assert_eq!(toy.verify(&tampered, Inverse::Hint), Err(VerifyError::Degenerate), "{other:?}");
        }
        // Any other scalar changed: the hint no longer fits, since the challenges move with it, but for a root's
        // third limb, which is no root.
        for at in 0..9 {
            let mut tampered = proof.clone();
            tampered.stream[at] += F192::new(1, 2, 0);
            assert_eq!(toy.verify(&tampered, Inverse::Hint), Err(VerifyError::Degenerate), "{at}");
        }
        let mut tampered = proof.clone();
        tampered.stream[1].c2 = 1;
        assert_eq!(
            toy.verify(&tampered, Inverse::Hint),
            Err(VerifyError::Transcript(TranscriptError::NotARoot))
        );
        // Short or long.
        let mut short = proof.clone();
        short.stream.pop();
        assert_eq!(
            toy.verify(&short, Inverse::Hint),
            Err(VerifyError::Transcript(TranscriptError::Exhausted))
        );
        let mut long = proof.clone();
        long.stream.push(F192::ZERO);
        assert_eq!(
            toy.verify(&long, Inverse::Hint),
            Err(VerifyError::Transcript(TranscriptError::Trailing))
        );
    }

    /// The modes are separated: their labels differ and so does their randomness from one seed. A proof of one
    /// is not a proof of the other: as it is, its length is wrong; with the hint dropped, or with the hint the
    /// other mode would want appended, it is read under the other label and leaves claims that do not hold, which
    /// its openings do not open.
    #[test]
    fn modes_are_separated() {
        let mut rng = Rng::new(0x42);
        let toy = toy_witness(&mut rng);
        let root = toy.index_committed.root;
        let labels = [Inverse::Compute, Inverse::Hint].map(|inverse| label_in(&root, &toy.statement, inverse));
        assert_eq!(labels[0], label(&root, &toy.statement));
        assert_eq!(&labels[0][..16], b"pcs-quotient-kc1");
        assert_eq!(&labels[1][..16], b"pcs-quotient-kh1");
        assert_eq!(labels[0][16..], labels[1][16..]);
        let s = seed(&mut rng);
        let derived = [Inverse::Compute, Inverse::Hint]
            .map(|inverse| Randomness::derive_in(&s, &root, &toy.statement, &toy.cells, inverse));
        assert!(derived[0].masks == Randomness::derive(&s, &root, &toy.statement, &toy.cells).masks);
        assert!(derived[0].masks.as_flattened().iter().all(|w| !derived[1].masks.as_flattened().contains(w)));
        assert_ne!(derived[0].padding, derived[1].padding);

        let compute = toy.prove(&s, Inverse::Compute);
        let hinted = toy.prove(&s, Inverse::Hint);
        assert_ne!(compute.roots, hinted.roots, "the padding is the mode's");
        let (compute_proof, hinted_proof) = (compute.proof.clone(), hinted.proof.clone());
        let compute_openings = open(compute.tables, &compute.claims, &toy.index, &toy.index_committed);
        let hinted_openings = open(hinted.tables, &hinted.claims, &toy.index, &toy.index_committed);
        assert!(toy.opens(&compute.roots, &compute.claims, &compute_openings));
        assert!(toy.opens(&hinted.roots, &hinted.claims, &hinted_openings));

        // As they are.
        assert_eq!(
            toy.verify(&hinted_proof, Inverse::Compute),
            Err(VerifyError::Transcript(TranscriptError::Trailing))
        );
        assert_eq!(
            toy.verify(&compute_proof, Inverse::Hint),
            Err(VerifyError::Transcript(TranscriptError::Exhausted))
        );
        // The hint proof without its hint, read by the compute verifier.
        let mut dropped = hinted_proof.clone();
        dropped.stream.pop();
        let (roots, claims) = toy.verify(&dropped, Inverse::Compute).expect("a reduction");
        assert_eq!(roots, hinted.roots);
        assert_ne!(claims, hinted.claims);
        assert!(!toy.opens(&roots, &claims, &hinted_openings));
        // The compute proof with the hint the hint verifier wants, read by it.
        let mut appended = compute_proof.clone();
        let log_rows = toy.circuit.log_rows;
        appended.stream.push(hint(&root, &toy.statement, &compute_proof, log_rows).expect("a hint"));
        let (roots, claims) = toy.verify(&appended, Inverse::Hint).expect("a reduction");
        assert_eq!(roots, compute.roots);
        assert_ne!(claims, compute.claims);
        assert!(!toy.opens(&roots, &claims, &compute_openings));
    }

    /// [`Randomness::derive`] is a function of the seed, the circuit's commitment, the statement and the cells: the
    /// same ones give the same randomness, and another seed, commitment or statement, one cell changed or one cell
    /// fewer give masks and padding that share nothing with it.
    #[test]
    fn derived_randomness_binds_the_statement_and_the_witness() {
        let mut rng = Rng::new(0xD5);
        let cells: Vec<F64> = (0..(1 << 14) + 5).map(|_| F64(rng.next_u64())).collect();
        let statement = toy_statement(&[3; 32]);
        let (s, root) = (seed(&mut rng), [7; 32]);
        let base = Randomness::derive(&s, &root, &statement, &cells);
        let again = Randomness::derive(&s, &root, &statement, &cells);
        assert!(base.masks == again.masks && base.padding == again.padding);
        let words = base.masks.as_flattened();
        assert!(
            (1..12).all(|k| !words[..k].contains(&words[k])),
            "twelve distinct words"
        );
        let mut other_cells = cells.clone();
        other_cells[9000].0 ^= 1;
        let mut other_statement = statement;
        other_statement.y[0] ^= 1;
        let others = [
            Randomness::derive(&seed(&mut rng), &root, &statement, &cells),
            Randomness::derive(&s, &[8; 32], &statement, &cells),
            Randomness::derive(&s, &root, &other_statement, &cells),
            Randomness::derive(&s, &root, &statement, &other_cells),
            Randomness::derive(&s, &root, &statement, &cells[..cells.len() - 1]),
        ];
        for (k, other) in others.iter().enumerate() {
            let shared = other.masks.as_flattened().iter().filter(|w| words.contains(w)).count();
            assert_eq!(shared, 0, "case {k}: the masks");
            assert_ne!(base.padding, other.padding, "case {k}: the padding");
        }
        assert_ne!(fresh_seed(), fresh_seed(), "the operating system's seeds");
    }
}
