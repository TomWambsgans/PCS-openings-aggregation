// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/transcript.rs:
// its `Proof`, `Transcript` (the BLAKE2s chain, used by the reference verifier) and `sumcheck`, the latter two behind a
// `Channel` trait; new here: that trait, and the Keccak-256 chain the contract runs, adapted from this repository's
// `crates/quotient/src/transcript.rs`. MIT OR Apache-2.0; see NOTICE.md.
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
    mut claim: S,
    count: usize,
    equalities: &[Option<S>],
) -> Result<(Vec<S>, S), VerifierError> {
    let mut point = Vec::with_capacity(equalities.len());
    for &equality in equalities {
        let message = sumcheck_round_poly(transcript, count, claim, equality)?;
        let challenge = transcript.sample();
        point.push(challenge);
        claim = poly_eval(&message, challenge);
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
}
