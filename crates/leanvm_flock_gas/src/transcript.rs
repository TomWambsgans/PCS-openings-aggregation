// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/transcript.rs:
// its `Proof`, `Transcript` (the BLAKE2s chain, used by the reference verifier) and `sumcheck`, the latter two behind a
// `Channel` trait; new here: that trait, the Keccak-256 chain the contract runs, adapted from this repository's
// `crates/quotient/src/transcript.rs`, and the Fiat–Shamir shapes (`FsShape`, π1-rec). MIT OR Apache-2.0; see NOTICE.md.
//! Proof transport and Fiat-Shamir.
//!
//! Two chains, one protocol: the walk reads its scalars and draws its challenges through a [`Channel`].
//!
//! - [`Transcript`] is leanVM's at 42422001: a BLAKE2s compression per scalar observed and per challenge. The
//!   reference verifier ([`crate::verify_execution`]) runs it on real leanVM proofs.
//! - [`KeccakChannel`] is the contract's: the proof is calldata bytes, and a challenge is one Keccak-256 of the state
//!   and of the bytes read since the last challenge, exactly as they are in calldata (one `CALLDATACOPY` and one
//!   `KECCAK256` in the contract). A scalar is 24 bytes, big-endian (`c2`, `c1`, `c0`); a commitment's root is its two
//!   16-byte halves (`c1`, `c0`), so it has one encoding. The seed is the Keccak-256 of a 16-byte name, the program's
//!   32-byte IV and the public input's 32 bytes. The challenge is the low 192 bits of the state, limb 0 lowest.

use crate::field::{E, K, ZERO};
use crate::hash::{Digest, blake2s_hash};
use crate::merkle::{MerkleOpenings, MerklePath};
use crate::multilinear::{log2_strict, poly_eval};
use crate::scalar::Scalar;
use crate::{VerifierError, require};

/// Where the walk reads the proof and draws challenges, and where it states what it checks.
pub trait Channel<S: Scalar> {
    fn next_scalar(&mut self) -> Result<S, VerifierError>;

    fn next_scalars(&mut self, count: usize) -> Result<Vec<S>, VerifierError> {
        (0..count).map(|_| self.next_scalar()).collect()
    }

    /// A commitment: its root's two 128-bit halves, low first.
    fn next_root(&mut self) -> Result<[S; 2], VerifierError>;

    fn sample(&mut self) -> S;

    /// A challenge of [`NARROW_BITS`] bits (π1-rec2's batching sumcheck, `crates/leanvm_rec/SPEC-REC.md` §12): the
    /// hash's low 160 bits instead of 192, so that its 24 calldata bytes start with four zeros.
    fn sample_narrow(&mut self) -> S {
        unimplemented!("this channel draws no narrow challenges")
    }

    fn samples(&mut self, count: usize) -> Vec<S> {
        (0..count).map(|_| self.sample()).collect()
    }

    /// The verifier requires `value` to be zero: an identity `a == b` is `a + b`.
    fn require_zero(&mut self, value: S, error: VerifierError) -> Result<(), VerifierError>;

    fn require_nonzero(&mut self, value: S, error: VerifierError) -> Result<(), VerifierError>;

    /// The next `bytes` bytes of the stream (at most 8), a big-endian integer, as a scalar holding it in its low
    /// limb: a packed count, not a field element. Absorbed like every byte of the stream.
    fn next_integer(&mut self, _bytes: usize) -> Result<S, VerifierError> {
        unimplemented!("this channel reads no packed integers")
    }
}

/// The verifier's Fiat–Shamir shape: which runs of challenges are drawn one by one, and which derived
/// (`crates/leanvm_rec/SPEC-REC.md` §1.4).
///
/// Two runs may be derived: Flock's zerocheck eq point after its seven fixed coordinates (`flock_min`), and the bus's
/// tuple weights `α` (`crates/leanvm_univariate`'s `reduce`). Every other challenge is drawn in both shapes, and the
/// stream, the claims and their points' structure are the same; only the challenges' values differ.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum FsShape {
    /// Every challenge drawn, one Keccak-256 each: leanVM's shape, the main line's.
    #[default]
    Main,
    /// `π1-rec`: in each of the two runs, the first challenge `c` is drawn and the others are `c², c⁴, …`, each the
    /// square of the one before (no hash). 24 fewer Keccak-256 calls on the main line (131 → 107 Keccak-f).
    Rec,
    /// `π1-rec2`'s (`crates/leanvm_rec/SPEC-REC.md` §12): [`FsShape::Rec`], and the batching sumcheck's challenges of
    /// [`NARROW_BITS`] bits ([`Channel::sample_narrow`]): the claims' point, which the recursion's contract carries in
    /// calldata, has four zero bytes a coordinate.
    Rec2,
}

/// The bits of a narrow challenge: its top limb's low 32 (`c2 < 2^32`). Soundness: a sumcheck round of degree 2 errs
/// with probability `2/2^160`; π1-rec2's batch, 27 rounds over `C1`'s and `C2`'s lists (`2^24.3`), at `2^-130`.
pub const NARROW_BITS: usize = 160;

/// The narrow challenge of a hash's challenge: its limb 2 cut to 32 bits.
pub fn narrow(x: E) -> E {
    E::new(x.c0, x.c1, x.c2 & 0xFFFF_FFFF)
}

impl FsShape {
    /// A run of `count` challenges that `π1-rec` derives: drawn one by one ([`FsShape::Main`]), or the first drawn and
    /// each next the square of the one before ([`FsShape::Rec`]).
    pub fn draw<S: Scalar, C: Channel<S> + ?Sized>(self, channel: &mut C, count: usize) -> Vec<S> {
        match self {
            FsShape::Main => channel.samples(count),
            FsShape::Rec | FsShape::Rec2 if count == 0 => Vec::new(),
            FsShape::Rec | FsShape::Rec2 => squares(channel.sample(), count),
        }
    }
}

/// `first, first², first⁴, …`: `count` terms, each the square of the one before (no square past the last, so that a
/// recorded graph holds exactly the `count - 1` squarings).
pub fn squares<S: Scalar>(first: S, count: usize) -> Vec<S> {
    let mut out = Vec::with_capacity(count);
    if count > 0 {
        out.push(first);
    }
    while out.len() < count {
        let next = out[out.len() - 1].square();
        out.push(next);
    }
    out
}

/// The scalar stream, and the Merkle openings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub stream: Vec<E>,
    pub merkle_openings: MerkleOpenings,
}

impl Proof {
    /// From the two encodings: the stream as 24-byte little-endian field elements, and the raw Merkle openings as they are.
    pub fn load(stream: &[u8], merkle_openings: &[u8]) -> Result<Self, VerifierError> {
        require(stream.len().is_multiple_of(24), VerifierError::StreamNotWholeElements)?;
        Ok(Self {
            stream: stream
                .as_chunks::<24>()
                .0
                .iter()
                .map(|data| E::from_bytes(data))
                .collect::<Result<_, _>>()?,
            merkle_openings: MerkleOpenings::Raw(merkle_openings.to_vec()),
        })
    }
}

pub const DS_OBSERVE: u64 = 1;
pub const DS_SQUEEZE: u64 = 2;
const DS_POW_BASE: u64 = 3;
const DS_POW_NONCE: u64 = 4;

/// Hash two four-word operands.
pub fn compress(left: [u64; 4], right: [u64; 4]) -> [u64; 4] {
    let mut data = [0u8; 64];
    for (bytes, word) in data.as_chunks_mut().0.iter_mut().zip(left.into_iter().chain(right)) {
        *bytes = word.to_le_bytes();
    }
    blake2s_hash(&data).words()
}

/// leanVM's transcript: the BLAKE2s chain, and the Merkle openings for WHIR.
pub struct Transcript<'a> {
    proof: &'a Proof,
    state: [u64; 4],
    stream_offset: usize,  // in E field elements
    opening_offset: usize, // in bytes, or in batches of the pruned form
    paths: Vec<MerklePath>,
}

impl<'a> Transcript<'a> {
    pub fn new(proof: &'a Proof, fiat_shamir_iv: Digest, public_input: Digest) -> Self {
        Self {
            proof,
            state: compress(fiat_shamir_iv.words(), public_input.words()),
            stream_offset: 0,
            opening_offset: 0,
            paths: Vec::new(),
        }
    }

    pub fn stream_offset(&self) -> usize {
        self.stream_offset
    }

    fn observe(&mut self, value: E) {
        self.state = compress(self.state, [value.c0, value.c1, value.c2, DS_OBSERVE]);
    }

    fn next(&mut self) -> Result<E, VerifierError> {
        require(
            self.stream_offset < self.proof.stream.len(),
            VerifierError::StreamExhausted,
        )?;
        let value = self.proof.stream[self.stream_offset];
        self.stream_offset += 1;
        Ok(value)
    }

    pub fn grind_check(&mut self, bits: u32) -> Result<(), VerifierError> {
        let nonce = self.next()?;
        let block = [nonce.c0, nonce.c1, nonce.c2, DS_POW_NONCE];
        let digest = compress(compress(self.state, [0, 0, 0, DS_POW_BASE]), block)[0];
        let valid = if bits == 0 {
            nonce == ZERO
        } else {
            digest & ((1 << bits) - 1) == 0
        };
        require(valid, VerifierError::GrindingNonce)?;
        self.state = compress(self.state, block);
        Ok(())
    }

    fn merkle_data(&mut self, data: &'a [u8], length: usize) -> Result<&'a [u8], VerifierError> {
        let end = self.opening_offset + length;
        require(end <= data.len(), VerifierError::MerkleOpeningMissing)?;
        let chunk = &data[self.opening_offset..end];
        self.opening_offset = end;
        Ok(chunk)
    }

    /// The leaf images at `queries`, authenticated against `root`. `row_words` is what the pruned form stores of
    /// each, the rest of the image being a zero prefix; the raw form carries whole images.
    ///
    /// Each query's own path is kept for [`Self::finish`], whichever form the proof came in.
    pub fn merkle(
        &mut self,
        root: Digest,
        block_length: u64,
        queries: &[u64],
        row_words: usize,
        leaf_words: usize,
    ) -> Result<Vec<Vec<K>>, VerifierError> {
        let height = log2_strict(block_length)?;
        let paths = match &self.proof.merkle_openings {
            MerkleOpenings::Raw(data) => {
                let mut paths = Vec::with_capacity(queries.len());
                for &leaf_index in queries {
                    let leaf = self.merkle_data(data, 8 * leaf_words)?;
                    let mut siblings = Vec::with_capacity(height);
                    for _ in 0..height {
                        let sibling = self.merkle_data(data, 32)?;
                        siblings.push(sibling.try_into().expect("32 bytes were read"));
                    }
                    let leaf = leaf.as_chunks().0.iter().map(|&word| K(u64::from_le_bytes(word)));
                    let path = MerklePath {
                        leaf_index,
                        leaf: leaf.collect(),
                        siblings,
                    };
                    require(path.root() == root, VerifierError::MerkleRootMismatch)?;
                    paths.push(path);
                }
                paths
            }
            MerkleOpenings::Pruned(batches) => {
                let batch = batches
                    .get(self.opening_offset)
                    .ok_or(VerifierError::MerkleOpeningMissing)?;
                self.opening_offset += 1;
                let (batch_root, paths) = batch.expand(height, queries, row_words, leaf_words)?;
                require(batch_root == root, VerifierError::MerkleRootMismatch)?;
                paths
            }
        };
        let rows = paths.iter().map(|path| path.leaf.clone()).collect();
        self.paths.extend(paths);
        Ok(rows)
    }

    /// Nothing of the proof is left unread. Returns every query's path, in the order they were opened.
    pub fn finish(self) -> Result<Vec<MerklePath>, VerifierError> {
        require(
            self.stream_offset == self.proof.stream.len(),
            VerifierError::StreamNotConsumed,
        )?;
        require(
            self.opening_offset == self.proof.merkle_openings.len(),
            VerifierError::MerkleNotConsumed,
        )?;
        Ok(self.paths)
    }
}

impl Channel<E> for Transcript<'_> {
    fn next_scalar(&mut self) -> Result<E, VerifierError> {
        let value = self.next()?;
        self.observe(value);
        Ok(value)
    }

    fn next_root(&mut self) -> Result<[E; 2], VerifierError> {
        let halves = [self.next_scalar()?, self.next_scalar()?];
        Digest::from_halves(halves[0], halves[1])?;
        Ok(halves)
    }

    fn sample(&mut self) -> E {
        self.state = compress(self.state, [0, 0, 0, DS_SQUEEZE]);
        E::new(self.state[0], self.state[1], self.state[2])
    }

    fn require_zero(&mut self, value: E, error: VerifierError) -> Result<(), VerifierError> {
        require(value == ZERO, error)
    }

    fn require_nonzero(&mut self, value: E, error: VerifierError) -> Result<(), VerifierError> {
        require(value != ZERO, error)
    }
}

/// returns q(X) := c0 + c1X + c2X^2 + ...
pub fn sumcheck_round_poly<S: Scalar>(
    transcript: &mut impl Channel<S>,
    count: usize,
    claim: S,
    eq_factor: Option<S>,
) -> Result<Vec<S>, VerifierError> {
    let Some(eq_factor) = eq_factor else {
        // `q(0) + q(1) == claim`. The transcript contains c0, c2, c3 ...
        let constant = transcript.next_scalar()?;
        let tail = transcript.next_scalars(count - 2)?;
        return Ok([vec![constant, claim + S::sum(tail.iter().copied())], tail].concat());
    };
    // `(1 + r) q(0) + r q(1) == claim`. The transcript contains c1, c2, c3 ... (r := eq_factor)
    let tail = transcript.next_scalars(count - 1)?;
    Ok([vec![claim + eq_factor * S::sum(tail.iter().copied())], tail].concat())
}

pub fn sumcheck<S: Scalar>(
    transcript: &mut impl Channel<S>,
    claim: S,
    count: usize,
    equalities: &[Option<S>],
) -> Result<(Vec<S>, S), VerifierError> {
    sumcheck_drawn(transcript, claim, count, equalities, false)
}

/// [`sumcheck`], its challenges narrow ([`Channel::sample_narrow`]) when `narrow`.
pub fn sumcheck_drawn<S: Scalar>(
    transcript: &mut impl Channel<S>,
    mut claim: S,
    count: usize,
    equalities: &[Option<S>],
    narrow: bool,
) -> Result<(Vec<S>, S), VerifierError> {
    let mut point = Vec::with_capacity(equalities.len());
    for &equality in equalities {
        let message = sumcheck_round_poly(transcript, count, claim, equality)?;
        let challenge = if narrow {
            transcript.sample_narrow()
        } else {
            transcript.sample()
        };
        point.push(challenge);
        claim = poly_eval(&message, challenge);
    }
    Ok((point, claim))
}

/// `β_1` of the Cantor basis (`β_1² + β_1 = β_0 = 1`, the root with its low bit clear: `crates/leanvm_univariate`'s
/// `domain::beta()[1]`), so `V_2 = {0, 1, β_1, 1 + β_1}` is `GF(4)`: of `x^((2^64 - 1)/3)`, an element of order 3,
/// and it plus one, the one whose low bit is clear.
pub fn cantor_beta1() -> E {
    let g = crate::field::GEN.pow(u64::MAX / 3);
    if g.c0 & 1 == 0 { g } else { g + crate::field::ONE }
}

/// A pair's coordinates at its challenge `z`: `(y_0(z), y_1(z))`, the coordinate functionals of `V_2`
/// (`y_l(ω_i) = i_l` for `i < 4`): `y_1 = z² + z`, `y_0 = z + β_1 y_1`. One squaring and one product by a constant.
pub fn pair_point<S: Scalar>(z: S) -> [S; 2] {
    let y1 = z.square() + z;
    [z + S::constant(cantor_beta1()) * y1, y1]
}

/// A pair's round polynomial `G` of degree `4 · degree` (`degree` the summand's in each variable): the transcript holds
/// its monomial coefficients but `c_3`, which the claim gives. Over `V_2 = GF(4)` the power sum `Σ_x x^e` is 1 when
/// `e > 0` and `3 | e`, else 0, so `Σ_(x ∈ V_2) G(x) = Σ_(e > 0, 3 | e) c_e`.
fn pair_round_poly<S: Scalar>(transcript: &mut impl Channel<S>, degree: usize, claim: S) -> Result<Vec<S>, VerifierError> {
    let top = 4 * degree;
    assert!(top >= 3, "a pair's polynomial reaches x^3");
    let low = transcript.next_scalars(3)?;
    let high = transcript.next_scalars(top - 3)?;
    let mut c3 = claim;
    for (k, &c) in high.iter().enumerate() {
        if (k + 4).is_multiple_of(3) {
            c3 += c;
        }
    }
    Ok([low, vec![c3], high].concat())
}

/// π1-pairs' batching sumcheck (`crates/leanvm_rec/SPEC-POINTS.md`): `vars` variables of a summand of degree `degree`
/// in each, two at a time, low variables first. Pair `j`'s round polynomial is
/// `G_j(X) = Σ_rest f(r_(<2j), y_0(X), y_1(X), rest)`, so that `Σ_(x ∈ V_2) G_j(x)` is the sum over the pair's four
/// corners; one challenge `z_j` a pair, the point's coordinates `(y_0(z_j), y_1(z_j))` ([`pair_point`]). With `vars`
/// odd, the last variable is an ordinary round ([`sumcheck`]'s). Returns the point and the last claim.
pub fn sumcheck_pairs<S: Scalar>(
    transcript: &mut impl Channel<S>,
    mut claim: S,
    degree: usize,
    vars: usize,
) -> Result<(Vec<S>, S), VerifierError> {
    let mut point = Vec::with_capacity(vars);
    for _ in 0..vars / 2 {
        let message = pair_round_poly(transcript, degree, claim)?;
        let z = transcript.sample();
        point.extend(pair_point(z));
        claim = poly_eval(&message, z);
    }
    if vars % 2 == 1 {
        let (last, end) = sumcheck(transcript, claim, degree + 1, &[None])?;
        point.extend(last);
        claim = end;
    }
    Ok((point, claim))
}

/// The bytes of a scalar in calldata: 24 bytes, big-endian.
pub fn scalar_bytes(x: E) -> [u8; 24] {
    let mut bytes = [0; 24];
    for (chunk, limb) in bytes.as_chunks_mut::<8>().0.iter_mut().zip([x.c2, x.c1, x.c0]) {
        *chunk = limb.to_be_bytes();
    }
    bytes
}

/// The bytes of a root half in calldata: 16 bytes, big-endian.
pub fn half_bytes(x: E) -> [u8; 16] {
    assert_eq!(x.c2, 0, "a root half is 128-bit");
    let mut bytes = [0; 16];
    bytes[..8].copy_from_slice(&x.c1.to_be_bytes());
    bytes[8..].copy_from_slice(&x.c0.to_be_bytes());
    bytes
}

/// The challenge a Keccak state gives: its low 192 bits, limb 0 lowest.
pub fn challenge_of(state: &[u8; 32]) -> E {
    let limb = |i: usize| u64::from_be_bytes(state[24 - 8 * i..32 - 8 * i].try_into().unwrap());
    E::new(limb(0), limb(1), limb(2))
}

pub fn keccak256(data: &[u8]) -> [u8; 32] {
    revm::primitives::keccak256(data).0
}

/// The Keccak chain's seed: the hash of the name, the program's IV and the public input.
pub fn keccak_seed(name: &[u8; 16], iv: &[u8; 32], public_input: &[u8; 32]) -> [u8; 32] {
    keccak256(&[&name[..], iv, public_input].concat())
}

/// What a [`KeccakChannel`] does with the identities the verifier requires.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Checks {
    /// Fail on the first that does not hold.
    Enforce,
    /// Hold none to account: collect every value required to be zero, then every one required to be nonzero.
    Collect { zero: Vec<E>, nonzero: Vec<E> },
}

/// The contract's chain, verifier side: the stream as calldata bytes.
pub struct KeccakChannel<'a> {
    data: &'a [u8],
    cursor: usize,
    absorbed: usize,
    state: [u8; 32],
    pub checks: Checks,
}

impl<'a> KeccakChannel<'a> {
    pub fn new(seed: [u8; 32], stream: &'a [u8], checks: Checks) -> Self {
        Self {
            data: stream,
            cursor: 0,
            absorbed: 0,
            state: seed,
            checks,
        }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], VerifierError> {
        let bytes = self
            .data
            .get(self.cursor..self.cursor + N)
            .ok_or(VerifierError::StreamExhausted)?;
        self.cursor += N;
        Ok(bytes.try_into().expect("N bytes"))
    }

    /// Nothing of the stream is left unread.
    pub fn finish(&self) -> Result<(), VerifierError> {
        require(self.cursor == self.data.len(), VerifierError::StreamNotConsumed)
    }
}

impl Channel<E> for KeccakChannel<'_> {
    fn next_scalar(&mut self) -> Result<E, VerifierError> {
        let bytes = self.take::<24>()?;
        let limb = |i: usize| u64::from_be_bytes(bytes[16 - 8 * i..24 - 8 * i].try_into().unwrap());
        Ok(E::new(limb(0), limb(1), limb(2)))
    }

    fn next_root(&mut self) -> Result<[E; 2], VerifierError> {
        let mut half = || -> Result<E, VerifierError> {
            let bytes = self.take::<16>()?;
            let limb = |i: usize| u64::from_be_bytes(bytes[8 - 8 * i..16 - 8 * i].try_into().unwrap());
            Ok(E::new(limb(0), limb(1), 0))
        };
        Ok([half()?, half()?])
    }

    fn sample(&mut self) -> E {
        let input = [&self.state[..], &self.data[self.absorbed..self.cursor]].concat();
        self.absorbed = self.cursor;
        self.state = keccak256(&input);
        challenge_of(&self.state)
    }

    fn sample_narrow(&mut self) -> E {
        narrow(self.sample())
    }

    fn require_zero(&mut self, value: E, error: VerifierError) -> Result<(), VerifierError> {
        match &mut self.checks {
            Checks::Enforce => require(value == ZERO, error),
            Checks::Collect { zero, .. } => {
                zero.push(value);
                Ok(())
            }
        }
    }

    fn require_nonzero(&mut self, value: E, error: VerifierError) -> Result<(), VerifierError> {
        match &mut self.checks {
            Checks::Enforce => require(value != ZERO, error),
            Checks::Collect { nonzero, .. } => {
                nonzero.push(value);
                Ok(())
            }
        }
    }

    fn next_integer(&mut self, bytes: usize) -> Result<E, VerifierError> {
        assert!((1..=8).contains(&bytes));
        let data = self
            .data
            .get(self.cursor..self.cursor + bytes)
            .ok_or(VerifierError::StreamExhausted)?;
        self.cursor += bytes;
        Ok(E::new(data.iter().fold(0u64, |acc, &b| acc << 8 | b as u64), 0, 0))
    }
}

/// The contract's chain, prover side: writes the calldata stream and draws the same challenges.
pub struct KeccakWriter {
    pub stream: Vec<u8>,
    absorbed: usize,
    state: [u8; 32],
}

impl KeccakWriter {
    pub fn new(seed: [u8; 32]) -> Self {
        Self {
            stream: Vec::new(),
            absorbed: 0,
            state: seed,
        }
    }

    pub fn send(&mut self, x: E) {
        self.stream.extend(scalar_bytes(x));
    }

    pub fn send_root(&mut self, halves: [E; 2]) {
        halves.into_iter().for_each(|half| self.stream.extend(half_bytes(half)));
    }

    /// A packed integer of `bytes` bytes, big-endian ([`Channel::next_integer`]).
    pub fn send_integer(&mut self, value: u64, bytes: usize) {
        assert!((1..=8).contains(&bytes) && (bytes == 8 || value >> (8 * bytes) == 0));
        self.stream.extend(&value.to_be_bytes()[8 - bytes..]);
    }

    pub fn sample(&mut self) -> E {
        let input = [&self.state[..], &self.stream[self.absorbed..]].concat();
        self.absorbed = self.stream.len();
        self.state = keccak256(&input);
        challenge_of(&self.state)
    }

    /// [`Channel::sample_narrow`]'s challenge.
    pub fn sample_narrow(&mut self) -> E {
        narrow(self.sample())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn writer_and_channel_agree() {
        let seed = keccak_seed(b"leanVM-flock-gas", &[7; 32], &[9; 32]);
        let mut writer = KeccakWriter::new(seed);
        writer.send(E::new(8, 0, 0));
        writer.send_root([E::new(1, 2, 0), E::new(3, 4, 0)]);
        let a = writer.sample();
        let b = writer.sample();
        writer.send(E::new(5, 6, 7));
        let c = writer.sample();
        let mut channel = KeccakChannel::new(seed, &writer.stream, Checks::Enforce);
        assert_eq!(channel.next_scalar(), Ok(E::new(8, 0, 0)));
        assert_eq!(channel.next_root(), Ok([E::new(1, 2, 0), E::new(3, 4, 0)]));
        assert_eq!((channel.sample(), channel.sample()), (a, b));
        assert_eq!(channel.next_scalar(), Ok(E::new(5, 6, 7)));
        assert_eq!(channel.sample(), c);
        assert_eq!(channel.finish(), Ok(()));
        assert_eq!(writer.stream.len(), 24 + 32 + 24);
    }

    use crate::field::ONE;
    use crate::multilinear::multilinear_eval;

    fn element(seed: &mut u64) -> E {
        let mut next = || {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        };
        E::new(next(), next(), next())
    }

    /// A table's low variable bound to `r`.
    fn fold(table: &[E], r: E) -> Vec<E> {
        table.as_chunks::<2>().0.iter().map(|&[a, b]| a + r * (a + b)).collect()
    }

    /// The monomial coefficients of the polynomial of degree `< xs.len()` through `(xs[j], ys[j])`.
    fn interpolate(xs: &[E], ys: &[E]) -> Vec<E> {
        let n = xs.len();
        let mut out = vec![ZERO; n];
        for j in 0..n {
            // Π_(m ≠ j) (X + x_m), and its value at x_j.
            let mut basis = vec![ONE];
            let mut at = ONE;
            for (m, &x) in xs.iter().enumerate() {
                if m == j {
                    continue;
                }
                let mut next = vec![ZERO; basis.len() + 1];
                for (d, &c) in basis.iter().enumerate() {
                    next[d] += c * x;
                    next[d + 1] += c;
                }
                basis = next;
                at *= xs[j] + x;
            }
            let scale = ys[j] * at.inv();
            for (o, &c) in out.iter_mut().zip(&basis) {
                *o += scale * c;
            }
        }
        out
    }

    /// `Σ_i Π_t tables[t][i]` with each table's low variables bound by `bind`.
    fn sum_bound(tables: &[Vec<E>], bind: impl Fn(&[E]) -> Vec<E>) -> E {
        let bound: Vec<Vec<E>> = tables.iter().map(|t| bind(t)).collect();
        (0..bound[0].len()).map(|i| bound.iter().fold(ONE, |acc, t| acc * t[i])).fold(ZERO, |a, b| a + b)
    }

    /// The honest prover of `Σ_i Π_t tables[t][i]` in [`sumcheck_pairs`]' rounds (`degree` = the tables' count): each
    /// pair's `G` from its values at `4 · degree + 1` points, interpolated, sent but `c_3`; a last single variable as
    /// [`sumcheck`] reads it (`c_0`, then `c_2 …`). Returns the point.
    fn prove_pairs(writer: &mut KeccakWriter, mut tables: Vec<Vec<E>>) -> Vec<E> {
        let degree = tables.len();
        let mut vars = tables[0].len().trailing_zeros() as usize;
        let mut point = Vec::new();
        while vars >= 2 {
            let xs: Vec<E> = (0..=4 * degree as u64).map(|e| E::new(e, 0, 0)).collect();
            let ys: Vec<E> = xs
                .iter()
                .map(|&x| {
                    let [u0, u1] = pair_point(x);
                    sum_bound(&tables, |t| fold(&fold(t, u0), u1))
                })
                .collect();
            let c = interpolate(&xs, &ys);
            assert_eq!(c.len(), 4 * degree + 1);
            for (e, &ce) in c.iter().enumerate() {
                if e != 3 {
                    writer.send(ce);
                }
            }
            let [u0, u1] = pair_point(writer.sample());
            tables = tables.iter().map(|t| fold(&fold(t, u0), u1)).collect();
            point.extend([u0, u1]);
            vars -= 2;
        }
        if vars == 1 {
            let xs: Vec<E> = (0..=degree as u64).map(|e| E::new(e, 0, 0)).collect();
            let ys: Vec<E> = xs.iter().map(|&x| sum_bound(&tables, |t| fold(t, x))).collect();
            let c = interpolate(&xs, &ys);
            for (e, &ce) in c.iter().enumerate() {
                if e != 1 {
                    writer.send(ce);
                }
            }
            point.push(writer.sample());
        }
        point
    }

    /// `β_1` is the Cantor basis's (`β_1² + β_1 = 1`, low bit clear), and a pair's coordinates on `V_2` are its
    /// corners: `(y_0, y_1)(ω_i) = (i_0, i_1)`.
    #[test]
    fn pair_coordinates_are_the_corners_on_v2() {
        let b = cantor_beta1();
        assert_eq!(b * b + b, ONE);
        assert_eq!((b.c0 & 1, b.c1, b.c2), (0, 0, 0));
        for (i, x) in [ZERO, ONE, b, b + ONE].into_iter().enumerate() {
            let bit = |k: usize| E::new((i >> k & 1) as u64, 0, 0);
            assert_eq!(pair_point(x), [bit(0), bit(1)]);
        }
    }

    /// The paired sumcheck on honest product sums of 1 to 3 tables, odd and even variable counts: the verifier reads
    /// exactly the prover's stream (`4 · degree` scalars a pair), ends at the prover's point on the tables' product
    /// there; a wrong initial claim, and each flipped scalar, end on a claim the tables do not give.
    #[test]
    fn pairs_are_complete_and_sound() {
        for (degree, vars) in [(2, 10), (2, 11), (3, 7), (1, 6), (2, 1)] {
            let mut seed = 0x9a12_5eed ^ (degree * 100 + vars) as u64;
            let tables: Vec<Vec<E>> =
                (0..degree).map(|_| (0..1 << vars).map(|_| element(&mut seed)).collect()).collect();
            let claim = sum_bound(&tables, |t| t.to_vec());
            let bytes = keccak_seed(b"sumcheck pairs 1", &[degree as u8; 32], &[vars as u8; 32]);
            let mut writer = KeccakWriter::new(bytes);
            let point = prove_pairs(&mut writer, tables.clone());
            assert_eq!(writer.stream.len(), 24 * ((vars / 2) * 4 * degree + (vars % 2) * degree));
            let product_at = |r: &[E]| tables.iter().fold(ONE, |acc, t| acc * multilinear_eval(t, r).unwrap());
            let run = |stream: &[u8], claim: E| {
                let mut channel = KeccakChannel::new(bytes, stream, Checks::Enforce);
                let out = sumcheck_pairs(&mut channel, claim, degree, vars).unwrap();
                channel.finish().unwrap();
                out
            };
            let (r, last) = run(&writer.stream, claim);
            assert_eq!(r, point, "degree {degree}, {vars} variables");
            assert_eq!(last, product_at(&r), "degree {degree}, {vars} variables: complete");
            let (r, last) = run(&writer.stream, claim + ONE);
            assert_ne!(last, product_at(&r), "a wrong claim");
            for k in 0..writer.stream.len() / 24 {
                let mut stream = writer.stream.clone();
                stream[24 * k + 23] ^= 1;
                let (r, last) = run(&stream, claim);
                assert_ne!(last, product_at(&r), "degree {degree}, {vars} variables: scalar {k} flipped");
            }
        }
    }

    /// What the batching sumcheck costs π2 (`crates/leanvm_rec/SPEC-POINTS.md` §6), recorded: over the batch's 27
    /// variables at degree 2, the paired rounds take as many Keccak-f permutations as the plain ones (a pair's 8 scalars
    /// and the state are 224 bytes, two blocks; a plain round's 2 and the state 80, one), 14 challenges instead of 27,
    /// and these operations.
    #[test]
    fn pairs_cost_what_the_plain_rounds_do_in_permutations() {
        use crate::evm::record::{Node, Recorder, record};
        let measure = |paired: bool| {
            let ((point, last, challenges), graph) = record(|| {
                let mut recorder = Recorder::new();
                let claim = recorder.next_scalar().unwrap();
                let (point, last) = if paired {
                    sumcheck_pairs(&mut recorder, claim, 2, 27).unwrap()
                } else {
                    sumcheck(&mut recorder, claim, 3, &[None; 27]).unwrap()
                };
                (point.len(), last, recorder.cursor)
            });
            let _ = (last, challenges);
            let is_const = |id: u32| matches!(graph.nodes[id as usize], Node::Const(_));
            let (mut perms, mut lows, mut adds, mut muls, mut squares, mut by_const) = (0, 0, 0, 0, 0, 0);
            for node in &graph.nodes {
                match *node {
                    Node::Hash(_, from, to) => perms += (32 + (to - from) as usize) / 136 + 1,
                    Node::Low(_) => lows += 1,
                    Node::Add(..) => adds += 1,
                    Node::Mul(a, b) if is_const(a) || is_const(b) => by_const += 1,
                    Node::Mul(a, b) if a == b => squares += 1,
                    Node::Mul(..) => muls += 1,
                    _ => {}
                }
            }
            (point, perms, lows, adds, muls, squares, by_const)
        };
        let plain = measure(false);
        let pairs = measure(true);
        eprintln!("batch over 27 variables (point, Keccak-f, challenges, adds, products, squares, by constants):");
        eprintln!("  plain rounds  {plain:?}");
        eprintln!("  paired rounds {pairs:?}");
        assert_eq!((plain.0, pairs.0), (27, 27));
        assert_eq!((plain.1, pairs.1), (27, 27), "the same permutations");
        assert_eq!((plain.2, pairs.2), (27, 14), "14 challenges");
    }
}
