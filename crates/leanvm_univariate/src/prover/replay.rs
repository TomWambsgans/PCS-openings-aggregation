// Part of this repository. The chain's hashing is leanvm_flock_gas::transcript's `KeccakChannel`. MIT OR Apache-2.0;
// see NOTICE.md.
//! The verifier's combined claims on the point-claim stream.
//!
//! The prover learns each commitment's combined claim (its terms, points and value) by running the verifier's own
//! `reduce` in weighted mode on the stream so far: weighted mode returns the claims, and reads nothing after `ρ`.
//!
//! Since lever 4a (SPEC.md §13), the point-claim stream with Flock has no matrices' reduction after the slices: the
//! batching sumcheck runs its rounds. Weighted mode still reads it there (`flock_min::verify`). [`Replay`] is the
//! contract's Keccak chain on the point-claim stream, but for that one place: at the slices' end it serves the
//! matrices' reduction as an honest prover writes it at fixed challenges ([`challenges`]), outside the chain
//! (`flock::Pending::off_chain`), so that every challenge before and after is the point-claim stream's own. What
//! those reads leave is an honest prover's: the matrices' claim (discarded) and, without the slices (extension B),
//! the slices' combination (which point mode makes the batch's terminal instead). The other claims are the same in
//! both modes: the same relations, in the same order, at the same challenges, the ring switch's weight as one term
//! (point mode) or as its 64 twisted terms (weighted mode), which is the same weight.
//!
//! The verifier does not expose its combined claims in point mode (PROVER.md, "Notes for the verifier").

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::transcript::{Channel, Checks, challenge_of, keccak256};

/// The fixed challenges the inserted reads are served at.
pub fn challenges(count: usize) -> Vec<E> {
    (0..count as u64)
        .map(|k| E::new(0x9e37_79b9_7f4a_7c15 ^ k, 0xbf58_476d_1ce4_e5b9, 0x94d0_49bb_1331_11eb))
        .collect()
}

pub struct Replay<'a> {
    data: &'a [u8],
    cursor: usize,
    absorbed: usize,
    state: [u8; 32],
    pub checks: Checks,
    /// Where the inserted reads start, and the scalars and challenges left to serve there.
    insert_at: usize,
    scalars: std::vec::IntoIter<E>,
    samples: std::vec::IntoIter<E>,
    active: bool,
}

impl<'a> Replay<'a> {
    /// The chain on `stream`, with `scalars` and `samples` served at byte `insert_at` (none if both are empty).
    pub fn new(seed: [u8; 32], stream: &'a [u8], insert_at: usize, scalars: Vec<E>, samples: Vec<E>) -> Self {
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
            scalars: scalars.into_iter(),
            samples: samples.into_iter(),
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
        if self.scalars.len() + self.samples.len() > 0 {
            return Err(format!(
                "{} inserted scalars and {} challenges were not read: the weighted mode's stream is not the point mode's \
                 with the matrices' reduction",
                self.scalars.len(),
                self.samples.len()
            ));
        }
        Ok(())
    }

    fn inserting(&mut self) -> bool {
        if !self.active && self.cursor == self.insert_at && self.scalars.len() > 0 {
            self.active = true;
        }
        self.active && self.scalars.len() + self.samples.len() > 0
    }

    /// Whether the checks collected (zero, then nonzero) all hold.
    pub fn checks_hold(&self) -> bool {
        match &self.checks {
            Checks::Enforce => true,
            Checks::Collect { zero, nonzero } => {
                zero.iter().all(|x| *x == E::default()) && nonzero.iter().all(|x| *x != E::default())
            }
        }
    }
}

impl Channel<E> for Replay<'_> {
    fn next_scalar(&mut self) -> Result<E, VerifierError> {
        if self.inserting()
            && let Some(x) = self.scalars.next()
        {
            return Ok(x);
        }
        let bytes = self.take::<24>()?;
        let limb = |i: usize| u64::from_be_bytes(bytes[16 - 8 * i..24 - 8 * i].try_into().unwrap());
        Ok(E::new(limb(0), limb(1), limb(2)))
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

    fn next_root(&mut self) -> Result<[E; 2], VerifierError> {
        let mut half = || -> Result<E, VerifierError> {
            let bytes = self.take::<16>()?;
            let limb = |i: usize| u64::from_be_bytes(bytes[8 - 8 * i..16 - 8 * i].try_into().unwrap());
            Ok(E::new(limb(0), limb(1), 0))
        };
        Ok([half()?, half()?])
    }

    fn sample(&mut self) -> E {
        if self.active
            && let Some(x) = self.samples.next()
        {
            return x;
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
