// Part of this repository. The chain's hashing is leanvm_flock_gas::transcript's `KeccakChannel`. MIT OR Apache-2.0;
// see NOTICE.md.
//! The verifier's combined claims on the point-claim stream.
//!
//! The prover learns each commitment's combined claim (its terms, points and value) by running the verifier's own
//! `reduce` in weighted mode on the stream so far: weighted mode returns the claims, and reads nothing after `ρ`.
//!
//! Since lever 4a (SPEC.md §13), the point-claim stream with Flock has no matrices' reduction after the slices: the
//! batching sumcheck runs its rounds. Weighted mode still reads them there (`flock_min::verify`). [`Replay`] is the
//! contract's Keccak chain on the point-claim stream, but for that one place: at the slices' end it serves the
//! weighted mode's matrices' reduction (`k + 6` rounds of two scalars and a challenge, then `a`, `b`) as zeros and
//! fixed challenges, outside the chain, so that every challenge before and after is the point-claim stream's own.
//! What those reads leave (the matrices' claim) is discarded. The other claims are the same in both modes: the same
//! relations, in the same order, at the same challenges, the ring switch's weight as one term (point mode) or as its
//! 64 twisted terms (weighted mode), which is the same weight.
//!
//! The verifier does not expose its combined claims in point mode (PROVER.md, "Notes for the verifier").

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::transcript::{Channel, Checks, challenge_of, keccak256};

pub struct Replay<'a> {
    data: &'a [u8],
    cursor: usize,
    absorbed: usize,
    state: [u8; 32],
    pub checks: Checks,
    /// Where the inserted reads start, and how many scalars and challenges are left to serve there.
    insert_at: usize,
    scalars_left: usize,
    samples_left: usize,
    active: bool,
}

impl<'a> Replay<'a> {
    /// The chain on `stream`, with `scalars` zeros and `samples` fixed challenges served at byte `insert_at` (none if
    /// both are zero).
    pub fn new(seed: [u8; 32], stream: &'a [u8], insert_at: usize, scalars: usize, samples: usize) -> Self {
        Self {
            data: stream,
            cursor: 0,
            absorbed: 0,
            state: seed,
            checks: Checks::Collect {
                zero: vec![],
                nonzero: vec![],
            },
            insert_at,
            scalars_left: scalars,
            samples_left: samples,
            active: false,
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

    /// The whole stream was read, and every inserted read served.
    pub fn finish(&self) -> Result<(), String> {
        if self.cursor != self.data.len() {
            return Err(format!("the verifier read {} of the stream's {} bytes", self.cursor, self.data.len()));
        }
        if self.scalars_left + self.samples_left > 0 {
            return Err(format!(
                "{} inserted scalars and {} challenges were not read: the weighted mode's stream is not the point mode's \
                 with the matrices' reduction",
                self.scalars_left, self.samples_left
            ));
        }
        Ok(())
    }

    fn inserting(&mut self) -> bool {
        if !self.active && self.cursor == self.insert_at && self.scalars_left > 0 {
            self.active = true;
        }
        self.active && self.scalars_left + self.samples_left > 0
    }
}

impl Channel<E> for Replay<'_> {
    fn next_scalar(&mut self) -> Result<E, VerifierError> {
        if self.inserting() && self.scalars_left > 0 {
            self.scalars_left -= 1;
            return Ok(E::default());
        }
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
        if self.active && self.samples_left > 0 {
            self.samples_left -= 1;
            return E::new(0x9e37_79b9_7f4a_7c15, 0xbf58_476d_1ce4_e5b9, 0x94d0_49bb_1331_11eb + self.samples_left as u64);
        }
        let input = [&self.state[..], &self.data[self.absorbed..self.cursor]].concat();
        self.absorbed = self.cursor;
        self.state = keccak256(&input);
        challenge_of(&self.state)
    }

    fn require_zero(&mut self, value: E, error: VerifierError) -> Result<(), VerifierError> {
        match &mut self.checks {
            Checks::Enforce => (value == E::default()).then_some(()).ok_or(error),
            Checks::Collect { zero, .. } => {
                zero.push(value);
                Ok(())
            }
        }
    }

    fn require_nonzero(&mut self, value: E, error: VerifierError) -> Result<(), VerifierError> {
        match &mut self.checks {
            Checks::Enforce => (value != E::default()).then_some(()).ok_or(error),
            Checks::Collect { nonzero, .. } => {
                nonzero.push(value);
                Ok(())
            }
        }
    }
}
