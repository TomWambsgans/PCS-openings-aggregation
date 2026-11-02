// Part of this repository (not vendored). MIT OR Apache-2.0; see NOTICE.md.
// Written for the differential test of the Lean skeleton (`crates/quotient/tests/skel_trace.rs`,
// `formal/QuotientZk/Test/`).
//! A record of every Keccak call, for tests: compiled only with the `trace` feature, which no
//! production build enables. With the feature off, nothing here exists and the hooks in
//! [`crate::hash`] and `fiat_shamir` are compiled out; with it on, they record only between
//! [`start`] and [`stop`] (an atomic flag read otherwise), and never change what they hash.
//!
//! Recorded: [`crate::hash::hash`] (input and digest), [`crate::hash::Hasher::finalize`] (the
//! digest), [`crate::hash::hash_many_from_state`] (and so `hash_many`: the inputs, the zero blocks
//! the shared state stands for, the digests), and from `fiat_shamir` its duplex permutations (input
//! and output), a marker before each `sample`, and each grind's nonce (its tries, batched through
//! `keccak_f_many`, are not recorded one by one).

use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::ThreadId;

use crate::hash::{OUT_LEN, STATE_LANES, zero_prefix_state};

/// One recorded call.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant, reason = "test-only records, kept flat")]
pub enum Event {
    /// Keccak-256 of `input` ([`crate::hash::hash`]); `input` is empty, and `len` its length, when it was
    /// longer than [`Mode::keep`] allows.
    Hash {
        len: usize,
        input: Vec<u8>,
        out: [u8; OUT_LEN],
    },
    /// A streaming Keccak-256 ([`crate::hash::Hasher::finalize`]); its input is not kept.
    Stream { out: [u8; OUT_LEN] },
    /// [`crate::hash::hash_many_from_state`]: `n` inputs of `len` bytes, each after `prefix_blocks` zero
    /// blocks of the rate (`usize::MAX`: a state that is no zero prefix), the inputs and digests kept in
    /// the full mode, only a single digest in the light one.
    Many {
        prefix_blocks: usize,
        len: usize,
        n: usize,
        data: Vec<u8>,
        out: Vec<u8>,
    },
    /// A duplex permutation of `fiat_shamir`.
    Perm {
        input: [u64; STATE_LANES],
        output: [u64; STATE_LANES],
    },
    /// `FiatShamirState::sample` is about to permute.
    Sample,
    /// A grind of `bits` found `nonce`.
    Grind { bits: u32, nonce: u64 },
}

/// One recorded call and whether the thread that started the record made it.
#[derive(Clone, Debug)]
pub struct Record {
    pub main: bool,
    pub event: Event,
}

/// What is kept.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// Every input and digest.
    Full,
    /// Lengths and counts, the inputs of `hash` up to 4 KiB, a batch's digest when it has one.
    Light,
}

impl Mode {
    fn keep(self, len: usize) -> bool {
        self == Mode::Full || len <= 4096
    }
}

static ON: AtomicBool = AtomicBool::new(false);
static STATE: Mutex<Option<(ThreadId, Mode, Vec<Record>)>> = Mutex::new(None);

/// Start recording, from this thread (the "main" one of the records).
pub fn start(mode: Mode) {
    *STATE.lock().unwrap() = Some((std::thread::current().id(), mode, Vec::new()));
    ON.store(true, Ordering::SeqCst);
}

/// Stop recording and take the record.
pub fn stop() -> Vec<Record> {
    ON.store(false, Ordering::SeqCst);
    STATE.lock().unwrap().take().map(|(_, _, log)| log).unwrap_or_default()
}

#[inline]
fn on() -> bool {
    ON.load(Ordering::Relaxed)
}

fn push(make: impl FnOnce(Mode) -> Event) {
    let mut guard = STATE.lock().unwrap();
    if let Some((main, mode, log)) = guard.as_mut() {
        let event = make(*mode);
        log.push(Record {
            main: std::thread::current().id() == *main,
            event,
        });
    }
}

/// Hook of [`crate::hash::hash`].
#[inline]
pub fn hash(data: &[u8], out: &[u8; OUT_LEN]) {
    if on() {
        push(|mode| Event::Hash {
            len: data.len(),
            input: if mode.keep(data.len()) { data.to_vec() } else { vec![] },
            out: *out,
        });
    }
}

/// Hook of [`crate::hash::Hasher::finalize`].
#[inline]
pub fn stream(out: &[u8; OUT_LEN]) {
    if on() {
        push(|_| Event::Stream { out: *out });
    }
}

/// Hook of [`crate::hash::hash_many_from_state`].
#[inline]
pub fn many(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &[u8]) {
    if on() {
        let prefix_blocks = (0..64).find(|&k| zero_prefix_state(k) == *state).unwrap_or(usize::MAX);
        let n = out.len() / OUT_LEN;
        push(|mode| Event::Many {
            prefix_blocks,
            len,
            n,
            data: if mode == Mode::Full { data.to_vec() } else { vec![] },
            out: if mode == Mode::Full || n == 1 {
                out.to_vec()
            } else {
                vec![]
            },
        });
    }
}

/// Hook of `fiat_shamir`'s duplex permutation.
#[inline]
pub fn perm(input: &[u64; STATE_LANES], output: &[u64; STATE_LANES]) {
    if on() {
        push(|_| Event::Perm {
            input: *input,
            output: *output,
        });
    }
}

/// Hook of `fiat_shamir`'s `sample`, before its permutation.
#[inline]
pub fn sample() {
    if on() {
        push(|_| Event::Sample);
    }
}

/// Hook of `fiat_shamir`'s grind, once its nonce is found.
#[inline]
pub fn grind(bits: u32, nonce: u64) {
    if on() {
        push(|_| Event::Grind { bits, nonce });
    }
}
