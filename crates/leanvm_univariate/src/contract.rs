// Part of this repository; the contract's assembly and measurement follow crates/leanvm_flock_gas/src/evm/contract.rs.
// MIT OR Apache-2.0; see NOTICE.md.
//! The verifier as a contract (straight-line code compiled from the recorded verifier, `leanvm_flock_gas::evm`), its
//! calldata, and what a call costs.
//!
//! **Calldata**: selector, the public input (four 64-bit words), then the stream: `C1`'s root, Flock's messages,
//! `C2`'s root, the values at `t` (SPEC.md §8). No announced sizes: the contract is built for one shape, which the
//! transcript's IV binds.
//!
//! **Calls**: one `PCS_OPEN` call per commitment, each with one weighted claim (SPEC.md §8): words `root, layout,
//! k = 1, P`, the `P` points (a length, then the coordinates), the claim's `m` terms (`column | point << 32 |
//! twist << 48`, then the coefficient) and its value; `A0` and `B0` as evaluation claims (`root, layout, 1`, the
//! point, the value). The setup roots are constants in the code (no `SLOAD`).

use leanvm_flock_gas::evm::codegen::{CALLS, Contract, ENTRY, Ending, Entry, MEASURE, VERIFY, Word, compile, word};
use leanvm_flock_gas::evm::machine::{Outcome, PcsOpen, call};
use leanvm_flock_gas::evm::record::{Graph, Recorder, Sym, record};
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::transcript::{Checks, KeccakChannel, keccak_seed};

use crate::claims::{Combined, Commitment};
use crate::verifier::{Blake2s, Claims, Opening, Reduced, Shape, reduce};

/// The transcript's 16-byte name.
pub const NAME: [u8; 16] = *b"leanVM-univar-v1";

/// The layout ids `PCS_OPEN` is called with (they name the stacks of SPEC.md §3).
fn layout_id(commitment: Commitment) -> u64 {
    match commitment {
        Commitment::C1 => 0x5501,
        Commitment::C2 => 0x5502,
        Commitment::Setup => 0x5503,
    }
}
const A0_LAYOUT: u64 = 0x5504;
const B0_LAYOUT: u64 = 0x5505;

/// The setup commitments' roots, constants of the code (the gas does not depend on them).
fn setup_root(k: u64) -> Word {
    Word::Const(word([0x1111 * k, 0x2222, 0x3333]))
}

/// The verifier for one shape, recorded.
pub struct Recorded {
    pub graph: Graph,
    pub reduced: Reduced<Sym>,
    pub stream_len: usize,
    pub roots_at: [usize; 2],
    pub reads: Vec<(&'static str, u32)>,
}

pub fn record_verifier(shape: &Shape, blake2s: Blake2s, mode: Claims) -> Recorded {
    let ((reduced, stream_len, roots, reads), graph) = record(|| {
        let mut recorder = Recorder::new();
        let words = Recorder::statement();
        let reduced = reduce(shape, words, &mut recorder, blake2s, mode).expect("a recorder rejects nothing");
        (reduced, recorder.cursor as usize, recorder.roots.clone(), recorder.reads)
    });
    assert_eq!(roots.len(), 2, "two commitments in the stream");
    Recorded {
        graph,
        reduced,
        stream_len,
        roots_at: [roots[0] as usize, roots[1] as usize],
        reads,
    }
}

fn number(n: u64) -> Word {
    let mut bytes = [0; 32];
    bytes[24..].copy_from_slice(&n.to_be_bytes());
    Word::Const(bytes)
}

fn scalar(sym: Sym) -> Word {
    Word::Node(sym.0)
}

/// A weighted claim's words, after its header: `P`, the points, `m`, the terms, the value.
fn combined_words<T: Copy, W: Clone>(claim: &Combined<T>, word: impl Fn(T) -> W, number: impl Fn(u64) -> W) -> Vec<W> {
    let mut words = vec![number(claim.points.len() as u64)];
    for point in &claim.points {
        words.push(number(point.len() as u64));
        words.extend(point.iter().map(|&x| word(x)));
    }
    words.push(number(claim.terms.len() as u64));
    for &(column, point, twist, coefficient) in &claim.terms {
        words.push(number(column.id() | (point as u64) << 32 | (twist as u64) << 48));
        words.push(word(coefficient));
    }
    words.push(word(claim.value));
    words
}

/// A commitment's call: its header (root, layout, claims), then its claims.
fn opening_words<T: Copy, W: Clone>(
    root: W,
    layout: u64,
    opening: &Opening<T>,
    word: impl Fn(T) -> W + Copy,
    number: impl Fn(u64) -> W + Copy,
) -> Vec<W> {
    match opening {
        Opening::Weighted(claim) => [vec![root, number(layout), number(1)], combined_words(claim, word, number)].concat(),
        Opening::Point { point, value, bit_slice } => {
            let k = 1 + bit_slice.is_some() as u64;
            let mut words = vec![root, number(layout), number(k)];
            words.extend(point.iter().map(|&x| word(x)));
            words.push(word(*value));
            if let Some(claim) = bit_slice {
                words.extend(combined_words(claim, word, number));
            }
            words
        }
    }
}

/// The calls of `PCS_OPEN`, as runs of output words.
pub fn calls(recorded: &Recorded) -> Vec<Vec<Word>> {
    let reduced = &recorded.reduced;
    let mut out = Vec::new();
    for (commitment, opening) in &reduced.openings {
        let root = match commitment {
            Commitment::C1 => Word::Stream(recorded.roots_at[0]),
            Commitment::C2 => Word::Stream(recorded.roots_at[1]),
            Commitment::Setup => setup_root(1),
        };
        out.push(opening_words(root, layout_id(*commitment), opening, scalar, number));
    }
    if let Some(matrices) = &reduced.matrices {
        for (k, (layout, value)) in [(A0_LAYOUT, matrices.a), (B0_LAYOUT, matrices.b)].into_iter().enumerate() {
            let mut words = vec![setup_root(2 + k as u64), number(layout), number(1)];
            words.extend(matrices.point.iter().map(|&x| scalar(x)));
            words.push(scalar(value));
            out.push(words);
        }
    }
    out
}

pub fn compile_verifier(recorded: &Recorded, iv: &[u8; 32], measure: bool) -> Contract {
    let entry = Entry {
        name: NAME,
        iv: *iv,
        stream_len: recorded.stream_len,
        measure,
    };
    let calls = calls(recorded);
    let ending = Ending::PcsOpen(calls.iter().map(Vec::len).collect());
    compile(&recorded.graph, &calls.concat(), &ending, &entry)
}

pub fn calldata(public_words: &[u8; 32], stream: &[u8]) -> Vec<u8> {
    [&VERIFY[..], public_words, stream].concat()
}

/// A stream of the shape's length, its bytes pseudo-random as a proof's are (the contract's gas does not depend on
/// them; the transaction's does, on its zero bytes only).
pub fn sample_stream(len: usize, seed: u64) -> Vec<u8> {
    let mut state = seed | 1;
    (0..len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state >> 24) as u8
        })
        .collect()
}

/// The Rust verifier on the same calldata: the claims, and the values it requires to be zero, then nonzero.
pub fn rust_verifier(
    shape: &Shape,
    iv: &[u8; 32],
    public_words: &[u8; 32],
    stream: &[u8],
    blake2s: Blake2s,
    mode: Claims,
) -> Result<(Reduced<E>, Vec<E>, Vec<E>), leanvm_flock_gas::VerifierError> {
    let seed = keccak_seed(&NAME, iv, public_words);
    let mut channel = KeccakChannel::new(
        seed,
        stream,
        Checks::Collect {
            zero: vec![],
            nonzero: vec![],
        },
    );
    let words: [E; 4] = std::array::from_fn(|k| {
        E::new(
            u64::from_be_bytes(public_words[8 * k..8 * k + 8].try_into().unwrap()),
            0,
            0,
        )
    });
    let reduced = reduce(shape, words, &mut channel, blake2s, mode)?;
    channel.finish()?;
    let Checks::Collect { zero, nonzero } = channel.checks else {
        unreachable!()
    };
    Ok((reduced, zero, nonzero))
}

/// One phase's share of a call.
#[derive(Clone, Debug)]
pub struct PhaseGas {
    pub phase: &'static str,
    pub gas: u64,
}

/// What a verifying call costs.
#[derive(Clone, Debug)]
pub struct GasReport {
    pub calldata_bytes: usize,
    pub calldata_zero_bytes: usize,
    pub stream_bytes: usize,
    pub execution: u64,
    pub phases: Vec<PhaseGas>,
    pub claims: usize,
    pub calls: usize,
    /// Terms of each call's claim, and words written for `PCS_OPEN`.
    pub terms: Vec<(String, usize, usize)>,
    pub pcs_words: usize,
    pub relations: usize,
    pub code_bytes: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    pub hashed_bytes: usize,
    pub checks: usize,
    pub memory_words: usize,
    pub stream_by_phase: Vec<(&'static str, u32)>,
}

impl GasReport {
    pub fn execution_at(&self, c: u64) -> u64 {
        self.execution + c * self.claims as u64
    }

    /// Transaction gas without its 21,000 base: `floor` 40 for EIP-7623 (10 a zero byte), 64 for EIP-7976.
    pub fn transaction(&self, c: u64, floor: u64) -> u64 {
        let nonzero = (self.calldata_bytes - self.calldata_zero_bytes) as u64;
        let zero = self.calldata_zero_bytes as u64;
        let standard = 16 * nonzero + 4 * zero + self.execution_at(c);
        let floor_gas = floor * nonzero + if floor == 64 { 64 } else { floor / 4 } * zero;
        standard.max(floor_gas)
    }

    pub fn calldata_gas(&self) -> u64 {
        let nonzero = (self.calldata_bytes - self.calldata_zero_bytes) as u64;
        16 * nonzero + 4 * self.calldata_zero_bytes as u64
    }
}

/// Measure the verifier for `shape`: build it, run it on sample calldata with every call attested, and check the
/// run's gas against a run at another claim price and the phases against the total.
pub fn measure(shape: &Shape, iv: &[u8; 32], blake2s: Blake2s, mode: Claims) -> GasReport {
    let recorded = record_verifier(shape, blake2s, mode);
    let contract = compile_verifier(&recorded, iv, true);
    let stream = sample_stream(recorded.stream_len, 0x6A5);
    let data = calldata(&[0x5a; 32], &stream);
    assert_eq!(data.len(), contract.calldata_len);
    let all_calls = calls(&recorded);
    let claims: usize = recorded
        .reduced
        .openings
        .iter()
        .map(|(_, opening)| match opening {
            Opening::Weighted(_) => 1,
            Opening::Point { bit_slice, .. } => 1 + bit_slice.is_some() as usize,
        })
        .sum::<usize>()
        + 2 * recorded.reduced.matrices.is_some() as usize;
    let calls_count = all_calls.len();
    let run = |claim_gas: u64| -> Outcome {
        let block = PcsOpen::attesting_all(claim_gas);
        let outcome = call(&contract.code, &[], &data, &block);
        assert_eq!(outcome.output.as_deref(), Some(&word([1, 0, 0])[..]), "the measuring run returns 1");
        assert_eq!(outcome.pcs_calls.len(), calls_count, "one call per commitment");
        outcome
    };
    let outcome = run(0);
    assert_eq!(run(1000).execution, outcome.execution + 1000 * claims as u64);
    let mut phases: Vec<PhaseGas> = Vec::new();
    for (pc, &gas) in outcome.gas_by_pc.iter().enumerate() {
        if gas == 0 {
            continue;
        }
        let phase = contract.phase_of.get(pc).copied().unwrap_or(CALLS);
        match phases.iter_mut().find(|p| p.phase == phase) {
            Some(p) => p.gas += gas,
            None => phases.push(PhaseGas { phase, gas }),
        }
    }
    let total: u64 = phases.iter().map(|p| p.gas).sum();
    assert_eq!(total, outcome.execution, "the instructions' gas is the execution's");
    let measured = phases.iter().find(|p| p.phase == MEASURE).map_or(0, |p| p.gas);
    assert_eq!(measured, contract.checks as u64 + calls_count as u64, "one JUMPDEST a check and a call");
    phases.retain(|p| p.phase != MEASURE);
    phases.sort_by_key(|p| std::cmp::Reverse(p.gas));
    let mut terms: Vec<(String, usize, usize)> = recorded
        .reduced
        .openings
        .iter()
        .zip(&all_calls)
        .map(|((commitment, opening), words)| {
            let terms = match opening {
                Opening::Weighted(claim) => claim.terms.len(),
                Opening::Point { bit_slice, .. } => 1 + bit_slice.as_ref().map_or(0, |c| c.terms.len()),
            };
            (format!("{commitment:?}"), terms, words.len())
        })
        .collect();
    for (name, words) in ["A0", "B0"].iter().zip(&all_calls[recorded.reduced.openings.len()..]) {
        terms.push((name.to_string(), 1, words.len()));
    }
    let _ = ENTRY;
    GasReport {
        calldata_bytes: data.len(),
        calldata_zero_bytes: data.iter().filter(|&&b| b == 0).count(),
        stream_bytes: stream.len(),
        execution: outcome.execution - measured,
        phases,
        claims,
        calls: calls_count,
        pcs_words: all_calls.iter().map(Vec::len).sum(),
        terms,
        relations: recorded.reduced.relations,
        code_bytes: contract.code.len(),
        field_muls: contract.field_muls,
        xors: contract.xors,
        hashes: contract.hashes,
        hashed_bytes: contract.hashed_bytes,
        checks: contract.checks,
        memory_words: contract.memory_words,
        stream_by_phase: recorded.reads.clone(),
    }
}

/// The words `calls` writes, for the Rust verifier's claims on `stream`: what the contract must write.
fn expected_words(reduced: &Reduced<E>, recorded: &Recorded, stream: &[u8]) -> Vec<[u8; 32]> {
    use leanvm_flock_gas::evm::machine::element_word;
    let number = |n: u64| {
        let mut bytes = [0u8; 32];
        bytes[24..].copy_from_slice(&n.to_be_bytes());
        bytes
    };
    let root = |at: usize| -> [u8; 32] { stream[at..at + 32].try_into().unwrap() };
    let constant = |k: u64| word([0x1111 * k, 0x2222, 0x3333]);
    let mut out = Vec::new();
    for (commitment, opening) in &reduced.openings {
        let r = match commitment {
            Commitment::C1 => root(recorded.roots_at[0]),
            Commitment::C2 => root(recorded.roots_at[1]),
            Commitment::Setup => constant(1),
        };
        out.extend(opening_words(r, layout_id(*commitment), opening, element_word, number));
    }
    if let Some(matrices) = &reduced.matrices {
        for (k, (layout, value)) in [(A0_LAYOUT, matrices.a), (B0_LAYOUT, matrices.b)].into_iter().enumerate() {
            out.extend([constant(2 + k as u64), number(layout), number(1)]);
            out.extend(matrices.point.iter().map(|&x| element_word(x)));
            out.push(element_word(value));
        }
    }
    out
}

/// The contract, built to return what it would hand `PCS_OPEN` and every value it checks, against the Rust verifier
/// on the same calldata: word for word.
pub fn parity(shape: &Shape, iv: &[u8; 32], public_words: &[u8; 32], stream: &[u8], blake2s: Blake2s, mode: Claims) {
    let recorded = record_verifier(shape, blake2s, mode);
    let entry = Entry {
        name: NAME,
        iv: *iv,
        stream_len: recorded.stream_len,
        measure: true,
    };
    let checks = recorded.graph.zero.iter().chain(&recorded.graph.nonzero);
    let outputs: Vec<Word> = calls(&recorded)
        .concat()
        .into_iter()
        .chain(checks.map(|&(id, _)| Word::Node(id)))
        .collect();
    let contract = compile(&recorded.graph, &outputs, &Ending::Return, &entry);
    let (reduced, zero, nonzero) =
        rust_verifier(shape, iv, public_words, stream, blake2s, mode).expect("the stream's length");
    let mut expected = expected_words(&reduced, &recorded, stream);
    expected.extend(zero.iter().chain(&nonzero).map(|&x| leanvm_flock_gas::evm::machine::element_word(x)));
    let outcome = call(&contract.code, &[], &calldata(public_words, stream), &PcsOpen::default());
    let output = outcome.output.expect("the measuring build does not revert");
    assert_eq!(output.len(), 32 * expected.len(), "words returned");
    for (k, (got, want)) in output.chunks(32).zip(&expected).enumerate() {
        assert_eq!(got, &want[..], "word {k}");
    }
}
