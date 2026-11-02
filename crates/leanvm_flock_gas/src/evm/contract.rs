// Part of this repository; the contract's assembly follows this repository's crates/evm/src/quotient.rs. MIT OR
// Apache-2.0; see NOTICE.md.
//! The leanVM verifier as a contract, its calldata, and what a call costs.
//!
//! **ABI.** `verify(bytes32 publicInput, bytes proof)`, selector [`VERIFY`], arguments packed: calldata is the
//! selector, the public input as its four 64-bit words (leanVM's little-endian words of the 32 bytes, each written
//! big-endian, word 0 first), then the proof's stream: leanVM's PIOP stream in the transcript's encoding (24 bytes a
//! scalar, 16 a root's half), with the bytecode's value after the bus's final counts, the matrices' reduction after
//! the lincheck (if it has one) and the stack's batching sumcheck at the end. The contract is built for one shape
//! (the announced sizes, which it checks), as this repository's is for one circuit size.
//!
//! **Calls.** One `PCS_OPEN` call per commitment, each with its one claim: the stack (root in calldata), the
//! stacked bytecode, and, when the lincheck's terminal is left to them, `A0` and `B0`; the three fixed commitments
//! are in storage slots 0, 1, 2 (one cold `SLOAD` each), as this repository keeps its circuit's.

use crate::evm::codegen::{CALLS, Contract, Ending, Entry, MEASURE, VERIFY, Word, compile, word};
use crate::evm::machine::{Outcome, PcsOpen, call, element_word};
use crate::evm::record::{Graph, Recorder, Sym, record};
use crate::field::E;
use crate::transcript::{Checks, KeccakChannel, keccak_seed, scalar_bytes};
use crate::{Claim, LincheckTerminal, Reduced, Shape, VerifierError, reduce};

/// The transcript's 16-byte name.
pub const NAME: [u8; 16] = *b"leanVM-42422001K";

/// The `PCS_OPEN` layout ids: the stack of `2^n` words, the stacked bytecode, `A0`, `B0`.
pub fn stack_layout(stack_log: usize) -> u64 {
    256 + stack_log as u64
}
pub const BYTECODE_LAYOUT: u64 = 2 * 256 + 23;
pub const A0_LAYOUT: u64 = 3 * 256 + 28;
pub const B0_LAYOUT: u64 = 4 * 256 + 28;

/// The fixed commitments' storage slots.
pub const BYTECODE_SLOT: u8 = 0;
pub const A0_SLOT: u8 = 1;
pub const B0_SLOT: u8 = 2;

/// The verifier for one shape, recorded.
pub struct Recorded {
    pub graph: Graph,
    pub reduced: Reduced<Sym>,
    /// Bytes of stream it reads, and where the stack's root starts in it.
    pub stream_len: usize,
    pub root_at: usize,
}

pub fn record_verifier(shape: &Shape, lincheck: LincheckTerminal) -> Recorded {
    let ((reduced, stream_len, root_at), graph) = record(|| {
        let mut recorder = Recorder::new();
        let words = Recorder::statement();
        let reduced = reduce(shape, words, &mut recorder, lincheck).expect("a recorder rejects nothing");
        assert_eq!(recorder.roots.len(), 1, "one commitment in the stream");
        (reduced, recorder.cursor as usize, recorder.roots[0] as usize)
    });
    Recorded {
        graph,
        reduced,
        stream_len,
        root_at,
    }
}

fn number(n: u64) -> Word {
    let mut bytes = [0; 32];
    bytes[24..].copy_from_slice(&n.to_be_bytes());
    Word::Const(bytes)
}

fn claim_words(claim: &Claim<Sym>) -> Vec<Word> {
    claim
        .point
        .iter()
        .chain([&claim.value])
        .map(|sym| Word::Node(sym.0))
        .collect()
}

/// The calls of `PCS_OPEN`, as runs of output words.
fn calls(recorded: &Recorded) -> Vec<Vec<Word>> {
    let reduced = &recorded.reduced;
    let header = |root: Word, layout: u64| vec![root, number(layout), number(1)];
    let mut calls = vec![
        [
            header(Word::Stream(recorded.root_at), stack_layout(reduced.layout_stack_log)),
            claim_words(&reduced.stack),
        ]
        .concat(),
        [
            header(Word::Stored(BYTECODE_SLOT), BYTECODE_LAYOUT),
            claim_words(&reduced.bytecode),
        ]
        .concat(),
    ];
    if let Some([a, b]) = &reduced.matrices {
        calls.push([header(Word::Stored(A0_SLOT), A0_LAYOUT), claim_words(a)].concat());
        calls.push([header(Word::Stored(B0_SLOT), B0_LAYOUT), claim_words(b)].concat());
    }
    calls
}

/// How the contract ends.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// The verifier: `PCS_OPEN` checks the claims, and it returns the word 1.
    Verify,
    /// For tests: it returns the claims, then every value it requires to be zero, then every one to be nonzero.
    Return,
}

pub fn compile_verifier(recorded: &Recorded, iv: &[u8; 32], mode: Mode, measure: bool) -> Contract {
    let entry = Entry {
        name: NAME,
        iv: *iv,
        stream_len: recorded.stream_len,
        measure,
    };
    let calls = calls(recorded);
    match mode {
        Mode::Verify => {
            let ending = Ending::PcsOpen(calls.iter().map(Vec::len).collect());
            compile(&recorded.graph, &calls.concat(), &ending, &entry)
        }
        Mode::Return => {
            let checks = recorded.graph.zero.iter().chain(&recorded.graph.nonzero);
            let outputs: Vec<Word> = calls
                .concat()
                .into_iter()
                .chain(checks.map(|&(id, _)| Word::Node(id)))
                .collect();
            compile(&recorded.graph, &outputs, &Ending::Return, &entry)
        }
    }
}

/// The public input as calldata carries it: its four little-endian 64-bit words, each big-endian, word 0 first.
pub fn public_input_calldata(public_input: &[u8; 32]) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (out, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(crate::public_words(public_input)) {
        *out = word.to_be_bytes();
    }
    bytes
}

pub fn calldata(public_input: &[u8; 32], stream: &[u8]) -> Vec<u8> {
    [&VERIFY[..], &public_input_calldata(public_input), stream].concat()
}

/// A stream of the shape's length whose announced sizes are the shape's and whose other bytes are pseudo-random,
/// as a proof's are (the contract's gas does not depend on them; the transaction's does, on its zero bytes only).
pub fn sample_stream(shape: &Shape, recorded: &Recorded, seed: u64) -> Vec<u8> {
    let mut state = seed | 1;
    let mut stream: Vec<u8> = (0..recorded.stream_len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state >> 24) as u8
        })
        .collect();
    for (i, value) in shape.announced().into_iter().enumerate() {
        stream[24 * i..24 * i + 24].copy_from_slice(&scalar_bytes(value));
    }
    // The root's halves are 16 bytes each, so any bytes are a root.
    stream
}

/// The Rust verifier on the same calldata: the claims, and the values it requires to be zero, then nonzero.
pub fn rust_verifier(
    shape: &Shape,
    iv: &[u8; 32],
    public_input: &[u8; 32],
    stream: &[u8],
    lincheck: LincheckTerminal,
) -> Result<(Reduced<E>, Vec<E>, Vec<E>), VerifierError> {
    let seed = keccak_seed(&NAME, iv, &public_input_calldata(public_input));
    let mut channel = KeccakChannel::new(
        seed,
        stream,
        Checks::Collect {
            zero: vec![],
            nonzero: vec![],
        },
    );
    let words = crate::public_words(public_input).map(|w| E::new(w, 0, 0));
    let reduced = reduce(shape, words, &mut channel, lincheck)?;
    channel.finish()?;
    let Checks::Collect { zero, nonzero } = channel.checks else {
        unreachable!()
    };
    Ok((reduced, zero, nonzero))
}

/// The words a contract in [`Mode::Return`] returns for these claims and checks.
pub fn expected_return(reduced: &Reduced<E>, root: [u8; 32], zero: &[E], nonzero: &[E]) -> Vec<u8> {
    let number = |n: u64| {
        let mut bytes = [0u8; 32];
        bytes[24..].copy_from_slice(&n.to_be_bytes());
        bytes
    };
    let claim = |claim: &Claim<E>| -> Vec<[u8; 32]> {
        claim
            .point
            .iter()
            .chain([&claim.value])
            .map(|&x| element_word(x))
            .collect()
    };
    let mut words = vec![root, number(stack_layout(reduced.layout_stack_log)), number(1)];
    words.extend(claim(&reduced.stack));
    words.extend([[0; 32], number(BYTECODE_LAYOUT), number(1)]);
    words.extend(claim(&reduced.bytecode));
    if let Some([a, b]) = &reduced.matrices {
        words.extend([[0; 32], number(A0_LAYOUT), number(1)]);
        words.extend(claim(a));
        words.extend([[0; 32], number(B0_LAYOUT), number(1)]);
        words.extend(claim(b));
    }
    words.extend(zero.iter().chain(nonzero).map(|&x| element_word(x)));
    words.concat()
}

/// The fixed commitments, as stored: any three words (the gas does not depend on them).
pub fn fixed_roots() -> Vec<(u8, [u8; 32])> {
    [BYTECODE_SLOT, A0_SLOT, B0_SLOT]
        .into_iter()
        .map(|slot| (slot, word([0x1111 * (slot as u64 + 1), 0x2222, 0x3333])))
        .collect()
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
    /// The stream's scalars: 24-byte ones, and roots.
    pub stream_bytes: usize,
    /// Execution gas at a claim price of 0, of a valid proof (the measuring build's `JUMPDEST`s subtracted).
    pub execution: u64,
    pub phases: Vec<PhaseGas>,
    pub claims: usize,
    pub calls: usize,
    pub code_bytes: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    pub hashed_bytes: usize,
    pub checks: usize,
    pub memory_words: usize,
}

impl GasReport {
    /// The execution at a claim price of `c`.
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

    /// The calldata's gas at the standard rate.
    pub fn calldata_gas(&self) -> u64 {
        let nonzero = (self.calldata_bytes - self.calldata_zero_bytes) as u64;
        16 * nonzero + 4 * self.calldata_zero_bytes as u64
    }
}

/// Measure the verifier for `shape`: build it, run it on a sample proof's calldata with every claim attested, and
/// check the run's gas against a run at another claim price and the phases against the total.
pub fn measure(shape: &Shape, iv: &[u8; 32], lincheck: LincheckTerminal) -> GasReport {
    let recorded = record_verifier(shape, lincheck);
    let contract = compile_verifier(&recorded, iv, Mode::Verify, true);
    let stream = sample_stream(shape, &recorded, 0x6A5);
    let data = calldata(&[0x5a; 32], &stream);
    assert_eq!(data.len(), contract.calldata_len);
    let claims = 2 + 2 * recorded.reduced.matrices.is_some() as usize;
    let run = |claim_gas: u64| -> Outcome {
        let block = PcsOpen::attesting_all(claim_gas);
        let outcome = call(&contract.code, &fixed_roots(), &data, &block);
        assert_eq!(outcome.output.as_deref(), Some(&word([1, 0, 0])[..]), "the measuring run returns 1");
        assert_eq!(outcome.pcs_calls.len(), claims, "one call per commitment");
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
    assert_eq!(measured, contract.checks as u64 + claims as u64, "one JUMPDEST a check and a call");
    phases.retain(|p| p.phase != MEASURE);
    phases.sort_by_key(|p| std::cmp::Reverse(p.gas));
    GasReport {
        calldata_bytes: data.len(),
        calldata_zero_bytes: data.iter().filter(|&&b| b == 0).count(),
        stream_bytes: stream.len(),
        execution: outcome.execution - measured,
        phases,
        claims,
        calls: claims,
        code_bytes: contract.code.len(),
        field_muls: contract.field_muls,
        xors: contract.xors,
        hashes: contract.hashes,
        hashed_bytes: contract.hashed_bytes,
        checks: contract.checks,
        memory_words: contract.memory_words,
    }
}

/// Check the contract against the Rust verifier on `stream`: the claims it writes and every value it checks.
pub fn parity(shape: &Shape, iv: &[u8; 32], public_input: &[u8; 32], stream: &[u8], lincheck: LincheckTerminal) {
    let recorded = record_verifier(shape, lincheck);
    let contract = compile_verifier(&recorded, iv, Mode::Return, true);
    let (reduced, zero, nonzero) =
        rust_verifier(shape, iv, public_input, stream, lincheck).expect("the stream has the shape's length");
    let mut root = [0u8; 32];
    root.copy_from_slice(&stream[recorded.root_at..recorded.root_at + 32]);
    let mut expected = expected_return(&reduced, root, &zero, &nonzero);
    // The fixed commitments' words are read from storage.
    let roots = fixed_roots();
    let calls = calls(&recorded);
    let mut at = 0;
    for run in &calls {
        if let Word::Stored(slot) = run[0] {
            let stored = roots.iter().find(|(s, _)| *s == slot).expect("a slot").1;
            expected[32 * at..32 * at + 32].copy_from_slice(&stored);
        }
        at += run.len();
    }
    let outcome = call(
        &contract.code,
        &roots,
        &calldata(public_input, stream),
        &PcsOpen::default(),
    );
    let output = outcome.output.expect("the measuring build does not revert");
    assert_eq!(output.len(), expected.len());
    for (k, (got, want)) in output.chunks(32).zip(expected.chunks(32)).enumerate() {
        assert_eq!(got, want, "word {k}");
    }
}
