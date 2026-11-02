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

use evm_link::creation_code;
use revm::primitives::Address;

use crate::evm::codegen::{
    CALLS, Contract, Deployable, ENTRY, Ending, Entry, MEASURE, VERIFY, Word, compile, compile_deployable,
    compile_deployable_like, word,
};
use crate::evm::machine::{Chain, Outcome, PcsOpen, VERIFIER, call, element_word, transaction_gas};
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
    /// The stream's bytes, by the phase that reads them.
    pub reads: Vec<(&'static str, u32)>,
}

pub fn record_verifier(shape: &Shape, lincheck: LincheckTerminal) -> Recorded {
    let ((reduced, stream_len, root_at, reads), graph) = record(|| {
        let mut recorder = Recorder::new();
        let words = Recorder::statement();
        let reduced = reduce(shape, words, &mut recorder, lincheck).expect("a recorder rejects nothing");
        assert_eq!(recorder.roots.len(), 1, "one commitment in the stream");
        (
            reduced,
            recorder.cursor as usize,
            recorder.roots[0] as usize,
            recorder.reads,
        )
    });
    Recorded {
        graph,
        reduced,
        stream_len,
        root_at,
        reads,
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
    let (outputs, ending, entry) = ends(recorded, iv, mode, measure);
    compile(&recorded.graph, &outputs, &ending, &entry)
}

/// The same verifier as contracts of at most `limit` bytes of code each ([`compile_deployable`]): one if it fits,
/// else a driver and the parts it calls.
pub fn compile_deployable_verifier(
    recorded: &Recorded,
    iv: &[u8; 32],
    mode: Mode,
    measure: bool,
    limit: usize,
) -> Deployable {
    let (outputs, ending, entry) = ends(recorded, iv, mode, measure);
    compile_deployable(&recorded.graph, &outputs, &ending, &entry, limit)
}

/// The measuring build of `like` (a non-measuring build of the same mode): the same cuts, so its gas is `like`'s and
/// one a check.
pub fn compile_measuring_like(recorded: &Recorded, iv: &[u8; 32], mode: Mode, like: &Deployable) -> Deployable {
    let (outputs, ending, entry) = ends(recorded, iv, mode, true);
    compile_deployable_like(&recorded.graph, &outputs, &ending, &entry, like)
}

/// What the contract writes, how it ends, and how it is entered.
fn ends(recorded: &Recorded, iv: &[u8; 32], mode: Mode, measure: bool) -> (Vec<Word>, Ending, Entry) {
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
            (calls.concat(), ending, entry)
        }
        Mode::Return => {
            let checks = recorded.graph.zero.iter().chain(&recorded.graph.nonzero);
            let outputs: Vec<Word> = calls
                .concat()
                .into_iter()
                .chain(checks.map(|&(id, _)| Word::Node(id)))
                .collect();
            (outputs, Ending::Return, entry)
        }
    }
}

/// The contracts of a [`Deployable`] deployed, each by a transaction: the parts (no constructor), then the driver,
/// calling them at their addresses, its constructor storing the fixed commitments.
pub struct Deployed {
    pub chain: Chain,
    /// The driver's address: where a verifying call is sent.
    pub address: Address,
    /// Each contract: its address, code bytes, init code, the deployment's execution gas, and its code's tags (the
    /// driver last).
    pub contracts: Vec<DeployedContract>,
}

pub struct DeployedContract {
    pub address: Address,
    pub code_bytes: usize,
    pub init_code: Vec<u8>,
    pub execution: u64,
    pub tags: Vec<&'static str>,
}

impl DeployedContract {
    /// The deployment's transaction gas, without its 21,000 base, under a calldata floor of `floor` a byte.
    pub fn transaction(&self, floor: u64) -> u64 {
        transaction_gas(&self.init_code, self.execution, floor) - 21_000
    }
}

/// Deploy `deployable` on a fresh chain, its driver storing `roots` (slot, word).
pub fn deploy(deployable: &Deployable, roots: &[(u8, [u8; 32])]) -> Deployed {
    let mut chain = Chain::default();
    let mut contracts = Vec::new();
    let linked = &deployable.linked;
    for part in &linked.parts {
        let init_code = creation_code(&part.code.code, &[]);
        let (address, execution) = chain.deploy(&init_code);
        let address = address.expect("a part deploys");
        assert_eq!(chain.code(address), part.code.code);
        contracts.push(DeployedContract {
            address,
            code_bytes: part.code.code.len(),
            init_code,
            execution,
            tags: part.code.tags.clone(),
        });
    }
    let addresses: Vec<[u8; 20]> = contracts.iter().map(|c| c.address.into_array()).collect();
    let code = linked.driver_code(&addresses);
    let slots: Vec<u8> = roots.iter().map(|&(slot, _)| slot).collect();
    let mut init_code = creation_code(&code, &slots);
    roots.iter().for_each(|(_, word)| init_code.extend(word));
    let (address, execution) = chain.deploy(&init_code);
    let address = address.expect("the driver deploys");
    assert_eq!(chain.code(address), code);
    for &(slot, word) in roots {
        assert_eq!(chain.storage(address, slot), word);
    }
    contracts.push(DeployedContract {
        address,
        code_bytes: code.len(),
        init_code,
        execution,
        tags: linked.driver.code.tags.clone(),
    });
    Deployed {
        chain,
        address,
        contracts,
    }
}

impl Deployed {
    /// Each instruction's gas of `outcome`, summed by phase.
    fn phases(&self, outcome: &Outcome) -> Vec<PhaseGas> {
        let mut phases: Vec<PhaseGas> = Vec::new();
        for (address, gas_by_pc) in &outcome.gas_by_code {
            let tags = &self
                .contracts
                .iter()
                .find(|c| c.address == *address)
                .expect("a contract of the deployment")
                .tags;
            for (pc, &gas) in gas_by_pc.iter().enumerate() {
                if gas == 0 {
                    continue;
                }
                let phase = tags.get(pc).copied().unwrap_or(CALLS);
                match phases.iter_mut().find(|p| p.phase == phase) {
                    Some(p) => p.gas += gas,
                    None => phases.push(PhaseGas { phase, gas }),
                }
            }
        }
        phases
    }
}

/// The public input as calldata carries it: its four little-endian 64-bit words, each big-endian, word 0 first.
pub fn public_input_calldata(public_input: &[u8; 32]) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (out, word) in bytes
        .as_chunks_mut::<8>()
        .0
        .iter_mut()
        .zip(crate::public_words(public_input))
    {
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

/// The claims, and the values the verifier requires to be zero, then nonzero.
pub type Verdict = (Reduced<E>, Vec<E>, Vec<E>);

/// The Rust verifier on the same calldata: the claims, and the values it requires to be zero, then nonzero.
pub fn rust_verifier(
    shape: &Shape,
    iv: &[u8; 32],
    public_input: &[u8; 32],
    stream: &[u8],
    lincheck: LincheckTerminal,
) -> Result<Verdict, VerifierError> {
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

/// The breakdown's categories: what each phase is.
pub fn category(phase: &str) -> &'static str {
    match phase {
        "transcript (Keccak-256 chain)" => "transcript hashing (Keccak-256)",
        "calldata reads" => "calldata reads (CALLDATALOAD, first use)",
        "bus GKR: sumcheck rounds"
        | "table sumcheck: rounds"
        | "flock zerocheck: rounds"
        | "flock lincheck: rounds"
        | "flock matrices: sumcheck rounds"
        | "stack batch: sumcheck rounds" => "sumcheck rounds (all sumchecks)",
        "bus GKR: layers" => "GKR layer checks (bus)",
        "flock zerocheck: skip round"
        | "flock matrices: reduction to A0, B0 claims"
        | "flock lincheck: terminal walk of the BLAKE2s circuit" => "Flock checks (skip round, lincheck terminal)",
        "ring switch: map, coefficients, target" | "stack batch: ring-switch weight at the point" => {
            "ring switching (map, target, weight at the point)"
        }
        "bus leaves: fingerprints, selectors, padding"
        | "table sumcheck: terminal (constraints, bus forms)"
        | "public input binding"
        | "stack batch: eq / selector weights at the point" => {
            "public polynomials (eq, selectors, padding, index, bus forms)"
        }
        "PCS_OPEN: claims written, calls, replies checked" | "PCS_OPEN: fixed commitments read (cold SLOAD)" => {
            "PCS_OPEN calls (c = 0) and fixed roots (cold SLOAD)"
        }
        _ => "entry, announced sizes",
    }
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
    /// The stack's variables, the claims batched on it, the depth of the bus's GKR.
    pub stack_log: usize,
    pub stack_claims: usize,
    pub bus_depth: usize,
    /// The stream's bytes, by the phase that reads them.
    pub stream_by_phase: Vec<(&'static str, u32)>,
}

impl GasReport {
    /// The execution at a claim price of `c`.
    pub fn execution_at(&self, c: u64) -> u64 {
        self.execution + c * self.claims as u64
    }

    /// Transaction gas without its 21,000 base: `floor` 40 for EIP-7623 (10 a zero byte), 64 for EIP-7976.
    pub fn transaction(&self, c: u64, floor: u64) -> u64 {
        self.transaction_for(self.execution_at(c), floor)
    }

    /// The same calldata's transaction with this execution.
    pub fn transaction_for(&self, execution: u64, floor: u64) -> u64 {
        let nonzero = (self.calldata_bytes - self.calldata_zero_bytes) as u64;
        let zero = self.calldata_zero_bytes as u64;
        let standard = 16 * nonzero + 4 * zero + execution;
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
    let mut chain = Chain::default();
    chain.install(VERIFIER, &contract.code);
    fixed_roots()
        .into_iter()
        .for_each(|(slot, word)| chain.store(VERIFIER, slot, word));
    let installed = Deployed {
        chain,
        address: VERIFIER,
        contracts: vec![DeployedContract {
            address: VERIFIER,
            code_bytes: contract.code.len(),
            init_code: Vec::new(),
            execution: 0,
            tags: contract.phase_of.clone(),
        }],
    };
    let counts = Counts {
        calldata_len: contract.calldata_len,
        code_bytes: contract.code.len(),
        field_muls: contract.field_muls,
        xors: contract.xors,
        hashes: contract.hashes,
        hashed_bytes: contract.hashed_bytes,
        checks: contract.checks,
        memory_words: contract.memory_words,
    };
    measure_run(shape, &recorded, &installed, &counts, 0)
}

/// What a measuring run reports besides its gas.
struct Counts {
    calldata_len: usize,
    code_bytes: usize,
    field_muls: usize,
    xors: usize,
    hashes: usize,
    hashed_bytes: usize,
    checks: usize,
    memory_words: usize,
}

/// Run the measuring build `installed` (calling `parts` other contracts) on a sample proof's calldata with every claim
/// attested; check the run's gas against a run at another claim price, and the phases against the total.
fn measure_run(shape: &Shape, recorded: &Recorded, installed: &Deployed, counts: &Counts, parts: usize) -> GasReport {
    let stream = sample_stream(shape, recorded, 0x6A5);
    let data = calldata(&[0x5a; 32], &stream);
    assert_eq!(data.len(), counts.calldata_len);
    let claims = 2 + 2 * recorded.reduced.matrices.is_some() as usize;
    let run = |claim_gas: u64| -> Outcome {
        let block = PcsOpen::attesting_all(claim_gas);
        let outcome = installed.chain.call(installed.address, &data, &block);
        assert_eq!(
            outcome.output.as_deref(),
            Some(&word([1, 0, 0])[..]),
            "the measuring run returns 1"
        );
        assert_eq!(outcome.pcs_calls.len(), claims, "one call per commitment");
        outcome
    };
    let outcome = run(0);
    assert_eq!(run(1000).execution, outcome.execution + 1000 * claims as u64);
    let mut phases = installed.phases(&outcome);
    let total: u64 = phases.iter().map(|p| p.gas).sum();
    assert_eq!(total, outcome.execution, "the instructions' gas is the execution's");
    let measured = phases.iter().find(|p| p.phase == MEASURE).map_or(0, |p| p.gas);
    // The driver checks the word the last part returns, as the contract checks each call of `PCS_OPEN`.
    let returned = (parts > 0) as usize;
    assert_eq!(
        measured,
        (counts.checks + claims + parts + returned) as u64,
        "one JUMPDEST a check, a call of PCS_OPEN, a call of a part and the last part's word"
    );
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
        code_bytes: counts.code_bytes,
        field_muls: counts.field_muls,
        xors: counts.xors,
        hashes: counts.hashes,
        hashed_bytes: counts.hashed_bytes,
        checks: counts.checks,
        memory_words: counts.memory_words,
        stack_log: recorded.reduced.layout_stack_log,
        stack_claims: recorded.reduced.stack_claims,
        bus_depth: recorded.reduced.bus_depth,
        stream_by_phase: recorded.reads.clone(),
    }
}

/// Where a measuring build's parts are installed: `0x7a..` and the part's number.
fn part_address(k: usize) -> Address {
    let mut bytes = [0u8; 20];
    bytes[0] = 0x7a;
    bytes[18..].copy_from_slice(&(k as u16).to_be_bytes());
    Address::from(bytes)
}

/// `deployable` installed rather than deployed (a measuring build may pass EIP-170's limit by its `JUMPDEST`s): the
/// driver at [`VERIFIER`], storing `roots`, its parts at addresses of their own.
pub fn install(deployable: &Deployable, roots: &[(u8, [u8; 32])]) -> Deployed {
    let mut chain = Chain::default();
    let linked = &deployable.linked;
    let mut contracts = Vec::new();
    for (k, part) in linked.parts.iter().enumerate() {
        chain.install(part_address(k), &part.code.code);
        contracts.push(DeployedContract {
            address: part_address(k),
            code_bytes: part.code.code.len(),
            init_code: Vec::new(),
            execution: 0,
            tags: part.code.tags.clone(),
        });
    }
    let addresses: Vec<[u8; 20]> = (0..linked.parts.len()).map(|k| part_address(k).into_array()).collect();
    let code = linked.driver_code(&addresses);
    chain.install(VERIFIER, &code);
    roots.iter().for_each(|&(slot, word)| chain.store(VERIFIER, slot, word));
    contracts.push(DeployedContract {
        address: VERIFIER,
        code_bytes: code.len(),
        init_code: Vec::new(),
        execution: 0,
        tags: linked.driver.code.tags.clone(),
    });
    Deployed {
        chain,
        address: VERIFIER,
        contracts,
    }
}

/// One contract of the deployable verifier.
#[derive(Clone, Debug)]
pub struct ContractStats {
    pub code_bytes: usize,
    pub init_bytes: usize,
    /// Its deployment's execution gas, and transaction gas (without the 21,000 base) under EIP-7623.
    pub deployment_execution: u64,
    pub deployment_tx: u64,
    pub memory_words: usize,
    /// The program's items it runs, the values it reads from earlier contracts and keeps for later ones, and the stack
    /// words it starts and ends with.
    pub items: std::ops::Range<usize>,
    pub imports: usize,
    pub exports: usize,
    pub stack_in: usize,
    pub stack_out: usize,
}

/// What the deployable verifier costs, and its deployment.
#[derive(Clone, Debug)]
pub struct DeployableReport {
    /// A verifying call, as [`measure`] reports the one contract's (`code_bytes`: every contract's).
    pub report: GasReport,
    /// The one straight-line contract's execution and code, measured the same way.
    pub straight: u64,
    pub straight_code: usize,
    /// The driver first, then the parts in the order it calls them.
    pub contracts: Vec<ContractStats>,
    /// Words of the driver's values region.
    pub values: usize,
}

/// Measure the deployable verifier for `shape`, of contracts of at most `limit` bytes: deploy it, each contract by a
/// transaction; run its measuring build (cut at the same places) as [`measure`] runs the one contract.
pub fn measure_deployable(shape: &Shape, iv: &[u8; 32], lincheck: LincheckTerminal, limit: usize) -> DeployableReport {
    let recorded = record_verifier(shape, lincheck);
    let real = compile_deployable_verifier(&recorded, iv, Mode::Verify, false, limit);
    let deployed = deploy(&real, &fixed_roots());
    let measuring = compile_measuring_like(&recorded, iv, Mode::Verify, &real);
    assert_eq!(measuring.linked.starts(), real.linked.starts());
    let installed = install(&measuring, &fixed_roots());
    let linked = &real.linked;
    let counts = Counts {
        calldata_len: real.calldata_len,
        code_bytes: linked.code_bytes(),
        field_muls: real.field_muls,
        xors: real.xors,
        hashes: real.hashes,
        hashed_bytes: real.hashed_bytes,
        checks: real.checks,
        memory_words: linked.driver.code.memory_words,
    };
    let report = measure_run(shape, &recorded, &installed, &counts, linked.parts.len());
    let straight = measure(shape, iv, lincheck);
    // `deploy` deploys the parts first and the driver last.
    let deployments = |k: usize| &deployed.contracts[(k + linked.parts.len()) % deployed.contracts.len()];
    let contracts = [&linked.driver]
        .into_iter()
        .chain(&linked.parts)
        .enumerate()
        .map(|(k, part)| {
            let deployment = deployments(k);
            ContractStats {
                code_bytes: part.code.code.len(),
                init_bytes: deployment.init_code.len(),
                deployment_execution: deployment.execution,
                deployment_tx: deployment.transaction(40),
                memory_words: part.code.memory_words,
                items: part.items.clone(),
                imports: part.imports,
                exports: part.exports,
                stack_in: part.stack_in,
                stack_out: part.stack_out,
            }
        })
        .collect();
    DeployableReport {
        report,
        straight: straight.execution,
        straight_code: straight.code_bytes,
        contracts,
        values: linked.values,
    }
}

/// What a contract in [`Mode::Return`] returns on `stream`, by the Rust verifier.
fn expected_words(
    shape: &Shape,
    iv: &[u8; 32],
    public_input: &[u8; 32],
    stream: &[u8],
    lincheck: LincheckTerminal,
    recorded: &Recorded,
) -> Vec<u8> {
    let (reduced, zero, nonzero) =
        rust_verifier(shape, iv, public_input, stream, lincheck).expect("the stream has the shape's length");
    let mut root = [0u8; 32];
    root.copy_from_slice(&stream[recorded.root_at..recorded.root_at + 32]);
    let mut expected = expected_return(&reduced, root, &zero, &nonzero);
    // The fixed commitments' words are read from storage.
    let roots = fixed_roots();
    let calls = calls(recorded);
    let mut at = 0;
    for run in &calls {
        if let Word::Stored(slot) = run[0] {
            let stored = roots.iter().find(|(s, _)| *s == slot).expect("a slot").1;
            expected[32 * at..32 * at + 32].copy_from_slice(&stored);
        }
        at += run.len();
    }
    expected
}

fn assert_words(output: &[u8], expected: &[u8]) {
    assert_eq!(output.len(), expected.len());
    for (k, (got, want)) in output.chunks(32).zip(expected.chunks(32)).enumerate() {
        assert_eq!(got, want, "word {k}");
    }
}

/// Check the contract against the Rust verifier on `stream`: the claims it writes and every value it checks.
pub fn parity(shape: &Shape, iv: &[u8; 32], public_input: &[u8; 32], stream: &[u8], lincheck: LincheckTerminal) {
    let recorded = record_verifier(shape, lincheck);
    let contract = compile_verifier(&recorded, iv, Mode::Return, true);
    let expected = expected_words(shape, iv, public_input, stream, lincheck, &recorded);
    let outcome = call(
        &contract.code,
        &fixed_roots(),
        &calldata(public_input, stream),
        &PcsOpen::default(),
    );
    assert_words(&outcome.output.expect("the measuring build does not revert"), &expected);
}

/// The deployable verifier, of contracts of at most `limit` bytes, deployed, on `stream`:
///
/// - returning, it returns what the Rust verifier computes, word for word: the claims, and every value it checks;
/// - verifying with every check enforced, it reverts exactly when the Rust verifier rejects, and, when the block
///   attests every call, it calls `PCS_OPEN` with exactly the inputs the one contract does (in its measuring build,
///   which runs to the end), and returns 1.
///
/// Returns how many contracts it is.
pub fn parity_deployable(
    shape: &Shape,
    iv: &[u8; 32],
    public_input: &[u8; 32],
    stream: &[u8],
    lincheck: LincheckTerminal,
    limit: usize,
) -> usize {
    let recorded = record_verifier(shape, lincheck);
    let data = calldata(public_input, stream);
    // Returning every checked value, whatever it is: the measuring build, cut where the real one is.
    let returning = compile_deployable_verifier(&recorded, iv, Mode::Return, false, limit);
    let installed = install(
        &compile_measuring_like(&recorded, iv, Mode::Return, &returning),
        &fixed_roots(),
    );
    let output = installed
        .chain
        .call(installed.address, &data, &PcsOpen::default())
        .output;
    let expected = expected_words(shape, iv, public_input, stream, lincheck, &recorded);
    assert_words(&output.expect("a measuring build does not revert"), &expected);

    let verifying = compile_deployable_verifier(&recorded, iv, Mode::Verify, false, limit);
    let deployed = deploy(&verifying, &fixed_roots());
    let attest = PcsOpen::attesting_all(0);
    let enforced = deployed.chain.call(deployed.address, &data, &attest);
    let accepts = {
        let seed = keccak_seed(&NAME, iv, &public_input_calldata(public_input));
        let mut channel = KeccakChannel::new(seed, stream, Checks::Enforce);
        let words = crate::public_words(public_input).map(|w| E::new(w, 0, 0));
        reduce(shape, words, &mut channel, lincheck)
            .and_then(|_| channel.finish())
            .is_ok()
    };
    assert_eq!(
        enforced.output.is_some(),
        accepts,
        "reverts exactly when the Rust verifier rejects"
    );
    let one = compile_verifier(&recorded, iv, Mode::Verify, true);
    let straight = call(&one.code, &fixed_roots(), &data, &attest);
    let measuring = install(
        &compile_measuring_like(&recorded, iv, Mode::Verify, &verifying),
        &fixed_roots(),
    );
    let linked = measuring.chain.call(measuring.address, &data, &attest);
    assert_eq!(linked.output, straight.output);
    assert_eq!(linked.output.as_deref(), Some(&word([1, 0, 0])[..]));
    assert_eq!(linked.pcs_calls, straight.pcs_calls, "the same calls of PCS_OPEN");
    1 + verifying.linked.parts.len()
}

/// What a part of a verifier costs measured alone: the same compilation and run, of a graph `f` records on a fresh
/// transcript (its outputs kept live by returning them), less the entry checks and the returned words.
#[derive(Clone, Debug)]
pub struct FragmentGas {
    /// Execution of the part itself: its arithmetic, its transcript hashing and its calldata reads.
    pub execution: u64,
    pub phases: Vec<PhaseGas>,
    pub stream_bytes: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    pub memory_words: usize,
}

pub fn measure_fragment(f: impl FnOnce(&mut Recorder) -> Vec<Sym>) -> FragmentGas {
    let ((outputs, stream_len), graph) = record(|| {
        let mut recorder = Recorder::new();
        let outputs = f(&mut recorder);
        (outputs, recorder.cursor as usize)
    });
    let entry = Entry {
        name: NAME,
        iv: [0x77; 32],
        stream_len,
        measure: true,
    };
    let words: Vec<Word> = outputs.iter().map(|sym| Word::Node(sym.0)).collect();
    let contract = compile(&graph, &words, &Ending::Return, &entry);
    let mut state = 0x9E37_79B9u64;
    let stream: Vec<u8> = (0..stream_len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state >> 24) as u8
        })
        .collect();
    let outcome = call(
        &contract.code,
        &[],
        &calldata(&[0x5a; 32], &stream),
        &PcsOpen::default(),
    );
    assert!(outcome.output.is_some(), "the measuring build returns");
    let mut phases: Vec<PhaseGas> = Vec::new();
    for (pc, &gas) in outcome.gas_by_pc.iter().enumerate() {
        let phase = contract.phase_of.get(pc).copied().unwrap_or(CALLS);
        if gas == 0 || [MEASURE, CALLS, ENTRY].contains(&phase) {
            continue;
        }
        match phases.iter_mut().find(|p| p.phase == phase) {
            Some(p) => p.gas += gas,
            None => phases.push(PhaseGas { phase, gas }),
        }
    }
    phases.sort_by_key(|p| std::cmp::Reverse(p.gas));
    FragmentGas {
        execution: phases.iter().map(|p| p.gas).sum(),
        phases,
        stream_bytes: stream_len,
        field_muls: contract.field_muls,
        xors: contract.xors,
        hashes: contract.hashes,
        memory_words: contract.memory_words,
    }
}
