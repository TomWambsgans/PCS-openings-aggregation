// Part of this repository. The recording mirrors `leanvm_univariate::contract::record_verifier_with`. MIT OR
// Apache-2.0; see NOTICE.md.
//! `π1`'s Fiat–Shamir shapes (SPEC-REC.md §1.3): the verifier recorded with some of its challenges **derived**
//! instead of hashed, to measure what `π2`'s circuit saves.
//!
//! A [`Derived`] channel wraps the recorder: the challenges it is told to derive are the square of the challenge
//! before them (so a run `c, c², c⁴, …` costs one Keccak-256 and squarings), every other call goes to the recorder.
//! Which challenges may be derived is a soundness question (SPEC-REC.md §5): the zerocheck's eq point (a multilinear
//! in each coordinate, so the power point `(c, c², c⁴, …)` keeps Schwartz–Zippel at degree `2^22`), the bus's tuple
//! weights `α` (each fingerprint multilinear in `α`); not `β` against `α`, nor the ring map's stages.

use std::collections::BTreeSet;

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::evm::record::{Recorder, Sym, record};
use leanvm_flock_gas::scalar::Scalar;
use leanvm_flock_gas::transcript::Channel;
use leanvm_univariate::contract::{Recorded, SetupRoots};
use leanvm_univariate::{Blake2s, Claims, Shape, reduce};

/// The recorder, with the challenges at the indices of `derived` (0-based, in drawing order) the square of the one
/// before.
pub struct Derived {
    pub inner: Recorder,
    derived: BTreeSet<usize>,
    drawn: usize,
    last: Option<Sym>,
    pub hashed: usize,
}

impl Channel<Sym> for Derived {
    fn next_scalar(&mut self) -> Result<Sym, VerifierError> {
        self.inner.next_scalar()
    }

    fn next_root(&mut self) -> Result<[Sym; 2], VerifierError> {
        self.inner.next_root()
    }

    fn sample(&mut self) -> Sym {
        let index = self.drawn;
        self.drawn += 1;
        let value = match (self.derived.contains(&index), self.last) {
            (true, Some(previous)) => previous.square(),
            _ => {
                self.hashed += 1;
                self.inner.sample()
            }
        };
        self.last = Some(value);
        value
    }

    fn require_zero(&mut self, value: Sym, error: VerifierError) -> Result<(), VerifierError> {
        self.inner.require_zero(value, error)
    }

    fn require_nonzero(&mut self, value: Sym, error: VerifierError) -> Result<(), VerifierError> {
        self.inner.require_nonzero(value, error)
    }

    fn next_integer(&mut self, bytes: usize) -> Result<Sym, VerifierError> {
        self.inner.next_integer(bytes)
    }
}

/// The main line's challenge indices `π1-rec` derives: `α_2, α_3, α_4` (from `α_1`), and Flock's zerocheck eq point
/// after its first coordinate (21 of 22). The drawing order is the measured transcript's (SPEC-REC.md §1.2): `α_1`
/// with the counts and `C1`'s root, then 27 draws with no new bytes (`α_2..α_4`, `β`, `γ`, the 22 coordinates).
pub fn pi1_rec_derived(log_n: usize, skip: usize) -> BTreeSet<usize> {
    // leanVM's seven fixed zerocheck coordinates (`flock::N_FIXED_CHALLENGES`, crate-private) are not drawn.
    let coordinates = log_n - skip - 7;
    let mut out: BTreeSet<usize> = [1, 2, 3].into();
    out.extend(7..6 + coordinates);
    out
}

/// The verifier for `shape`, recorded through a [`Derived`] channel.
pub fn record_derived(shape: &Shape, blake2s: Blake2s, mode: Claims, derived: BTreeSet<usize>) -> (Recorded, usize) {
    let ((reduced, stream_len, roots, reads, hashed), graph) = record(|| {
        let mut channel = Derived {
            inner: Recorder::new(),
            derived,
            drawn: 0,
            last: None,
            hashed: 0,
        };
        let words = Recorder::statement();
        let reduced = reduce(shape, words, &mut channel, blake2s, mode).expect("a recorder rejects nothing");
        let inner = channel.inner;
        (
            reduced,
            inner.cursor as usize,
            inner.roots.clone(),
            inner.reads,
            channel.hashed,
        )
    });
    assert_eq!(roots.len(), 2, "two commitments in the stream");
    (
        Recorded {
            shape: *shape,
            roots: SetupRoots::REFERENCE,
            graph,
            reduced,
            stream_len,
            roots_at: [roots[0] as usize, roots[1] as usize],
            reads,
        },
        hashed,
    )
}
