// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6, `FiatShamirState::keccak` (crates/fiat_shamir/src/lib.rs).
// MIT OR Apache-2.0; see NOTICE.md.
//! The reduction's transcript: a Keccak-256 chain, because its verifier is also an EVM contract, where
//! `KECCAK256` is one instruction.
//!
//! The state is a 256-bit word. A challenge is one Keccak-256 of the state and of every scalar sent since
//! the last challenge, each a 256-bit big-endian word (limb 0 lowest, which is how the EVM holds a field
//! element); the digest is the new state, and its low 192 bits the challenge. The protocol fixes how many
//! scalars precede each challenge, so no length or tag is hashed. A commitment rides the stream as the two
//! scalars of [`root_scalars`]; the seed is the Keccak-256 of a label that holds the statement.

use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use primitives::hash::hash as keccak256;

/// A root as the two scalars the stream carries: its 128-bit halves, each read as two little-endian words.
pub fn root_scalars(root: &Hash) -> [F192; 2] {
    fiat_shamir::merkle::hash_to_scalars(root)
}

/// The root two scalars of [`root_scalars`] stand for, if they are two halves (no third limb).
pub fn scalars_root(scalars: &[F192; 2]) -> Result<Hash, TranscriptError> {
    if scalars.iter().any(|s| s.c2 != 0) {
        return Err(TranscriptError::NotARoot);
    }
    let mut root = [0u8; 32];
    for (bytes, word) in
        root.as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip([scalars[0].c0, scalars[0].c1, scalars[1].c0, scalars[1].c1])
    {
        *bytes = word.to_le_bytes();
    }
    Ok(root)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TranscriptError {
    /// The stream ended before the verifier read all it needs.
    Exhausted,
    /// The stream holds more than the verifier reads.
    Trailing,
    /// A commitment's scalars are not two 128-bit halves.
    NotARoot,
}

/// A proof: the scalars, in the order sent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub stream: Vec<F192>,
}

/// The chain itself, shared by both sides.
#[derive(Clone, Debug)]
struct Chain {
    state: [u8; 32],
    pending: Vec<F192>,
}

impl Chain {
    fn new(label: &[u8]) -> Self {
        Self {
            state: keccak256(label),
            pending: Vec::new(),
        }
    }

    fn sample(&mut self) -> F192 {
        let mut input = Vec::with_capacity(32 * (1 + self.pending.len()));
        input.extend_from_slice(&self.state);
        for x in self.pending.drain(..) {
            input.extend_from_slice(&[0u8; 8]);
            for limb in [x.c2, x.c1, x.c0] {
                input.extend_from_slice(&limb.to_be_bytes());
            }
        }
        self.state = keccak256(&input);
        let limb = |i: usize| u64::from_be_bytes(self.state[24 - 8 * i..32 - 8 * i].try_into().unwrap());
        F192::new(limb(0), limb(1), limb(2))
    }
}

/// The prover's side: sends scalars and draws challenges.
pub struct ProverChain {
    chain: Chain,
    stream: Vec<F192>,
}

impl ProverChain {
    pub fn new(label: &[u8]) -> Self {
        Self {
            chain: Chain::new(label),
            stream: Vec::new(),
        }
    }

    pub fn send(&mut self, x: F192) {
        self.chain.pending.push(x);
        self.stream.push(x);
    }

    pub fn send_root(&mut self, root: &Hash) {
        root_scalars(root).into_iter().for_each(|x| self.send(x));
    }

    pub fn sample(&mut self) -> F192 {
        self.chain.sample()
    }

    pub fn into_proof(self) -> Proof {
        Proof { stream: self.stream }
    }
}

/// The verifier's side: reads scalars off a proof and draws the same challenges.
pub struct VerifierChain<'a> {
    chain: Chain,
    stream: &'a [F192],
}

#[allow(clippy::should_implement_trait)]
impl<'a> VerifierChain<'a> {
    pub fn new(label: &[u8], proof: &'a Proof) -> Self {
        Self {
            chain: Chain::new(label),
            stream: &proof.stream,
        }
    }

    pub fn next(&mut self) -> Result<F192, TranscriptError> {
        let (&x, rest) = self.stream.split_first().ok_or(TranscriptError::Exhausted)?;
        self.stream = rest;
        self.chain.pending.push(x);
        Ok(x)
    }

    pub fn next_root(&mut self) -> Result<[F192; 2], TranscriptError> {
        let scalars = [self.next()?, self.next()?];
        scalars_root(&scalars).map(|_| scalars)
    }

    pub fn sample(&mut self) -> F192 {
        self.chain.sample()
    }

    pub fn finish(&self) -> Result<(), TranscriptError> {
        if self.stream.is_empty() {
            Ok(())
        } else {
            Err(TranscriptError::Trailing)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roots_round_trip_and_sides_agree() {
        let root: Hash = std::array::from_fn(|i| (7 * i + 3) as u8);
        assert_eq!(scalars_root(&root_scalars(&root)), Ok(root));
        let mut p = ProverChain::new(b"label");
        p.send_root(&root);
        let a = p.sample();
        p.send(F192::new(1, 2, 3));
        let b = p.sample();
        let proof = p.into_proof();
        let mut v = VerifierChain::new(b"label", &proof);
        assert_eq!(v.next_root(), Ok(root_scalars(&root)));
        assert_eq!(v.sample(), a);
        assert_eq!(v.next(), Ok(F192::new(1, 2, 3)));
        assert_eq!(v.sample(), b);
        assert_eq!(v.finish(), Ok(()));
    }
}
