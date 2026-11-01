//! Adversarial tests of the verifier contract and of its calls of `PCS_OPEN`, none of which needs a proof: the
//! contract's claims are compared with the Rust verifier's on random and tampered calldata, degenerate proofs are
//! built from the transcript, the bytecode is walked for its stack, jumps and gas, and the calls are answered by
//! precompiles other than the mock.

use std::collections::BTreeMap;

use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use primitives::test_rng::Rng;
use quotient::protocol::{VerifyError, label, verify};
use quotient::statement::Statement;
use quotient::transcript::{Proof, ProverChain, TranscriptError, root_scalars, scalars_root};
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Cfg, Context, ContextTr, LocalContextTr, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{EthPrecompiles, ExecuteEvm, MainBuilder, MainContext, PrecompileProvider};
use revm::interpreter::interpreter_types::{InterpreterTypes, StackTr};
use revm::interpreter::{CallInput, Gas, InputsImpl, InstructionContext, InstructionResult, InterpreterResult, gas};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, U256};
use revm::state::{AccountInfo, Bytecode};

use crate::machine::{FIELD_MUL, FIELD_MUL_GAS, LOG_ROWS, PCS_OPEN, PcsOpen, call, root_word};
use crate::quotient::{calldata, claims_contract, contract, decode, openings};

const CALLDATA_LEN: usize = 64 + 64 + 5 * 24;

/// Calldata as the statement and proof it stands for: the inverse of [`calldata`].
fn parse(data: &[u8]) -> (Statement, Proof) {
    assert_eq!(data.len(), CALLDATA_LEN);
    let word = |at: usize| u64::from_be_bytes(data[at..at + 8].try_into().unwrap());
    let mut stream = vec![];
    for i in 0..4 {
        let at = 64 + 16 * i;
        stream.push(F192::new(word(at + 8), word(at), 0));
    }
    for i in 0..5 {
        let at = 128 + 24 * i;
        stream.push(F192::new(word(at + 16), word(at + 8), word(at)));
    }
    let statement = Statement {
        y: data[..32].try_into().unwrap(),
        root: data[32..64].try_into().unwrap(),
    };
    (statement, Proof { stream })
}

fn random_bytes<const N: usize>(rng: &mut Rng) -> [u8; N] {
    std::array::from_fn(|_| rng.next_u8())
}

fn random_calldata(rng: &mut Rng) -> Vec<u8> {
    (0..CALLDATA_LEN).map(|_| rng.next_u8()).collect()
}

/// Calldata the Rust verifier rejects as degenerate: the copy identity's denominator `d · d' + w_m` is zero, which
/// the prover controls through `next`, sent after `t`.
fn degenerate(index_root: &Hash, log_rows: usize, rng: &mut Rng) -> Vec<u8> {
    let statement = Statement {
        y: random_bytes(rng),
        root: random_bytes(rng),
    };
    let mut chain = ProverChain::new(&label(index_root, &statement));
    chain.send_root(&random_bytes(rng));
    let (alpha, beta) = (chain.sample(), chain.sample());
    let _gamma = chain.sample();
    chain.send_root(&random_bytes(rng));
    let t = chain.sample();
    let a: [F192; 4] = std::array::from_fn(|_| rng.ext());
    a.iter().for_each(|&x| chain.send(x));
    let m = log_rows + 2;
    let mut w = vec![t];
    for k in 0..m + 1 {
        w.push(w[k] * w[k] + w[k]);
    }
    let x = a[0] + t * a[1] + w[1] * (a[2] + t * a[3]);
    let d = alpha + x + beta * t;
    let next = (w[m] * d.inv() + alpha + x) * beta.inv();
    chain.send(next);
    calldata(&statement, &chain.into_proof())
}

/// The block holding the openings of the claims the Rust verifier leaves on `data`, if it leaves any.
fn block_for(index_root: &Hash, data: &[u8], log_rows: usize) -> PcsOpen {
    let (statement, proof) = parse(data);
    let mut block = PcsOpen::default();
    if let Ok((roots, claims)) = verify(index_root, &statement, &proof, log_rows) {
        for (root, id, claims) in openings(index_root, &roots, &claims, log_rows) {
            block.register(&root, id, &claims);
        }
    }
    block
}

/// The verifiers on one calldata, each check one assertion: the claims contract returns what `verify` leaves; the
/// contract succeeds, returning nothing, against the openings of those claims exactly when `verify` accepts, and
/// fails against `other`'s, a block for other claims.
fn agree(index_root: &Hash, log_rows: usize, codes: &(Vec<u8>, Vec<u8>), data: &[u8], other: &PcsOpen) -> bool {
    let (statement, proof) = parse(data);
    let expected = verify(index_root, &statement, &proof, log_rows);
    assert_ne!(
        expected.as_ref().err(),
        Some(&VerifyError::Transcript(TranscriptError::NotARoot))
    );
    let returned = call(&codes.0, data, &PcsOpen::default()).output;
    assert_eq!(
        returned.as_deref().and_then(|output| decode(output, log_rows)),
        expected.clone().ok(),
        "claims contract, {data:02x?}"
    );
    let own = call(&codes.1, data, &block_for(index_root, data, log_rows)).output;
    assert_eq!(own, expected.is_ok().then(Vec::new), "contract, {data:02x?}");
    assert_eq!(
        call(&codes.1, data, other).output,
        None,
        "foreign openings, {data:02x?}"
    );
    expected.is_ok()
}

fn codes(index_root: &Hash, log_rows: usize) -> (Vec<u8>, Vec<u8>) {
    (
        claims_contract(index_root, log_rows).code,
        contract(index_root, log_rows).code,
    )
}

/// Random calldata, at every size of circuit `PCS_OPEN` knows, with random and extreme index roots.
#[test]
fn random_calldata_agrees() {
    let mut rng = Rng::new(0xADD);
    for log_rows in LOG_ROWS {
        for index_root in [[0; 32], [0xff; 32], random_bytes(&mut rng)] {
            let codes = codes(&index_root, log_rows);
            let mut extremes: Vec<Vec<u8>> = [0u8, 0xff, 0x80, 0x01].iter().map(|&b| vec![b; CALLDATA_LEN]).collect();
            // Roots of all ones, scalars of all zeros, and the reverse.
            let mut mixed = vec![0xff; 128];
            mixed.resize(CALLDATA_LEN, 0);
            extremes.push(mixed.iter().map(|b| !b).collect());
            extremes.push(mixed);
            let other = block_for(&index_root, &random_calldata(&mut rng), log_rows);
            let samples = extremes.into_iter().chain((0..200).map(|_| random_calldata(&mut rng)));
            for data in samples {
                assert!(agree(&index_root, log_rows, &codes, &data, &other));
            }
        }
    }
}

/// Every single-bit change of a calldata, at the smallest and the largest circuit: the verifiers agree, and the
/// openings of the original's claims never pass the changed calldata.
#[test]
fn bit_flips_agree() {
    let mut rng = Rng::new(0xF11);
    for log_rows in [*LOG_ROWS.start(), *LOG_ROWS.end()] {
        let index_root = random_bytes(&mut rng);
        let codes = codes(&index_root, log_rows);
        let base = random_calldata(&mut rng);
        let honest = block_for(&index_root, &base, log_rows);
        assert_eq!(call(&codes.1, &base, &honest).output, Some(vec![]));
        for bit in 0..8 * CALLDATA_LEN {
            let mut data = base.clone();
            data[bit / 8] ^= 1 << (bit % 8);
            assert!(agree(&index_root, log_rows, &codes, &data, &honest), "bit {bit}");
        }
    }
}

/// The one rejection a prover can reach without grinding a hash: both contracts revert where the Rust verifier
/// finds a zero denominator, the calling one even when `PCS_OPEN` attests everything; one bit off, all accept.
/// No other test reaches the contract's nonzero check: with it compiled out (`ISZERO` and its jump replaced by a
/// `POP`), every other test of the crate passes.
#[test]
fn degenerate_proofs_revert() {
    let mut rng = Rng::new(0xDE6);
    for log_rows in [13, 17, 22] {
        let index_root = random_bytes(&mut rng);
        let codes = codes(&index_root, log_rows);
        let other = PcsOpen::default();
        for _ in 0..8 {
            let data = degenerate(&index_root, log_rows, &mut rng);
            let (statement, proof) = parse(&data);
            assert_eq!(
                verify(&index_root, &statement, &proof, log_rows).err(),
                Some(VerifyError::Degenerate)
            );
            assert!(!agree(&index_root, log_rows, &codes, &data, &other));
            assert_eq!(call_with(&codes.1, &data, Reply::Attest).output, None);
            let mut near = data.clone();
            near[CALLDATA_LEN - 1] ^= 1;
            assert!(agree(&index_root, log_rows, &codes, &near, &other));
            assert_eq!(call_with(&codes.1, &near, Reply::Attest).output, Some(vec![]));
        }
    }
}

/// Calldata of any other length reverts, whatever it holds and whatever `PCS_OPEN` says.
#[test]
fn other_lengths_revert() {
    let mut rng = Rng::new(0x1E2);
    let index_root = random_bytes(&mut rng);
    let codes = codes(&index_root, 22);
    let full = random_calldata(&mut rng);
    for len in (0..=CALLDATA_LEN + 64).filter(|&len| len != CALLDATA_LEN) {
        let mut data = full.clone();
        data.resize(len, 0);
        assert_eq!(call(&codes.0, &data, &PcsOpen::default()).output, None, "{len}");
        assert_eq!(call_with(&codes.1, &data, Reply::Attest).output, None, "{len}");
    }
    // Zero bytes past the end are not the same calldata: the size is checked, not the bytes read.
    let mut long = full.clone();
    long.extend([0; 8]);
    assert_eq!(call_with(&codes.1, &long, Reply::Attest).output, None);
}

/// A commitment's word in calldata is the word `PCS_OPEN` reads for its root, and roots and words correspond one
/// to one.
#[test]
fn root_words_are_the_calldata_words() {
    let mut rng = Rng::new(0x5007);
    for _ in 0..1000 {
        let data = random_calldata(&mut rng);
        let (_, proof) = parse(&data);
        assert_eq!(calldata(&parse(&data).0, &proof), data);
        for (i, at) in [(0, 64), (2, 96)] {
            let root = scalars_root(&[proof.stream[i], proof.stream[i + 1]]).unwrap();
            assert_eq!(root_word(&root)[..], data[at..at + 32]);
            assert_eq!(root_scalars(&root), [proof.stream[i], proof.stream[i + 1]]);
        }
    }
}

/// `calldata` drops a commitment scalar's third limb unchecked: a proof the Rust verifier rejects (`NotARoot`)
/// becomes calldata the contract accepts, that of the proof without the limb.
#[test]
fn calldata_of_a_proof_that_is_not_a_root() {
    let mut rng = Rng::new(0x2007);
    let index_root = random_bytes(&mut rng);
    let codes = codes(&index_root, 22);
    let data = random_calldata(&mut rng);
    let (statement, mut proof) = parse(&data);
    proof.stream[0].c2 = 1;
    assert_eq!(
        verify(&index_root, &statement, &proof, 22).err(),
        Some(VerifyError::Transcript(TranscriptError::NotARoot))
    );
    assert_eq!(calldata(&statement, &proof), data);
    let block = block_for(&index_root, &data, 22);
    assert_eq!(
        call(&codes.1, &calldata(&statement, &proof), &block).output,
        Some(vec![])
    );
}

/// How `PCS_OPEN` answers, in place of the mock's lookup.
#[derive(Clone, Copy, Debug)]
enum Reply {
    /// The word 1, to everything.
    Attest,
    /// The word 0: "no", in an ABI that answers every call.
    Zero,
    /// A revert carrying the word 1.
    RevertOne,
    /// Two words.
    Long,
    /// Nothing.
    Nothing,
    /// No precompile at the address: an empty account.
    Absent,
}

struct Rogue {
    eth: EthPrecompiles,
    reply: Reply,
    warm: bool,
    inputs: Vec<Vec<u8>>,
}

impl<CTX: ContextTr> PrecompileProvider<CTX> for Rogue {
    type Output = InterpreterResult;

    fn set_spec(&mut self, spec: <CTX::Cfg as Cfg>::Spec) -> bool {
        let changed = <EthPrecompiles as PrecompileProvider<CTX>>::set_spec(&mut self.eth, spec);
        changed | !std::mem::replace(&mut self.warm, true)
    }

    fn run(
        &mut self,
        context: &mut CTX,
        address: &Address,
        inputs: &InputsImpl,
        is_static: bool,
        gas_limit: u64,
    ) -> Result<Option<InterpreterResult>, String> {
        if *address != PCS_OPEN || matches!(self.reply, Reply::Absent) {
            return self.eth.run(context, address, inputs, is_static, gas_limit);
        }
        let input = match &inputs.input {
            CallInput::SharedBuffer(range) => context
                .local()
                .shared_memory_buffer_slice(range.clone())
                .map_or_else(Vec::new, |slice| slice.to_vec()),
            CallInput::Bytes(bytes) => bytes.to_vec(),
        };
        self.inputs.push(input);
        let one = U256::from(1).to_be_bytes_vec();
        let (result, output) = match self.reply {
            Reply::Attest => (InstructionResult::Return, one),
            Reply::Zero => (InstructionResult::Return, vec![0; 32]),
            Reply::RevertOne => (InstructionResult::Revert, one),
            Reply::Long => (InstructionResult::Return, [one.clone(), one].concat()),
            Reply::Nothing | Reply::Absent => (InstructionResult::Return, vec![]),
        };
        Ok(Some(InterpreterResult {
            result,
            gas: Gas::new(gas_limit),
            output: output.into(),
        }))
    }

    fn warm_addresses(&self) -> Box<impl Iterator<Item = Address>> {
        let pcs = (!matches!(self.reply, Reply::Absent)).then_some(PCS_OPEN);
        Box::new(self.eth.warm_addresses().chain(pcs))
    }

    fn contains(&self, address: &Address) -> bool {
        (*address == PCS_OPEN && !matches!(self.reply, Reply::Absent)) || self.eth.contains(address)
    }
}

/// `machine::field_mul`, which is private there.
fn field_mul<W: InterpreterTypes, H: ?Sized>(context: InstructionContext<'_, H, W>) {
    gas!(context.interpreter, FIELD_MUL_GAS);
    let Some(([a], b)) = context.interpreter.stack.popn_top() else {
        context.interpreter.halt(InstructionResult::StackUnderflow);
        return;
    };
    let element = |w: U256| {
        let [c0, c1, c2, _] = w.into_limbs();
        F192::new(c0, c1, c2)
    };
    let product = element(a) * element(*b);
    *b = U256::from_limbs([product.c0, product.c1, product.c2, 0]);
}

struct Called {
    output: Option<Vec<u8>>,
    inputs: Vec<Vec<u8>>,
}

/// [`call`], with `PCS_OPEN` answering as `reply` says.
fn call_with(code: &[u8], data: &[u8], reply: Reply) -> Called {
    let (contract, caller) = (Address::with_last_byte(0xc0), Address::with_last_byte(0xca));
    let mut db = CacheDB::new(EmptyDB::default());
    db.insert_account_info(
        contract,
        AccountInfo::from_bytecode(Bytecode::new_legacy(Bytes::copy_from_slice(code))),
    );
    let mut evm = Context::mainnet()
        .with_db(db)
        .modify_cfg_chained(|cfg| cfg.spec = SpecId::CANCUN)
        .build_mainnet()
        .with_precompiles(Rogue {
            eth: EthPrecompiles::default(),
            reply,
            warm: false,
            inputs: vec![],
        });
    evm.instruction.insert_instruction(FIELD_MUL, field_mul);
    let tx = TxEnv::builder()
        .caller(caller)
        .kind(TxKind::Call(contract))
        .data(Bytes::copy_from_slice(data))
        .gas_limit(10_000_000)
        .build()
        .expect("a transaction");
    let result = evm.transact_one(tx).expect("a valid transaction");
    let output = match result {
        ExecutionResult::Success {
            output: Output::Call(output),
            ..
        } => Some(output.to_vec()),
        _ => None,
    };
    Called {
        output,
        inputs: std::mem::take(&mut evm.precompiles.inputs),
    }
}

/// The contract tests only that a call returned data: any reply but none passes it, the word 0 and a reverted
/// call too. Against the ABI (`machine`), whose precompile returns the word 1 or nothing, that is enough; against
/// anything else at the address, it accepts every proof.
#[test]
fn any_returned_data_passes() {
    let mut rng = Rng::new(0x0DA7A);
    let index_root = random_bytes(&mut rng);
    let code = contract(&index_root, 22).code;
    let data = random_calldata(&mut rng);
    for (reply, passes) in [
        (Reply::Attest, true),
        (Reply::Zero, true),
        (Reply::RevertOne, true),
        (Reply::Long, true),
        (Reply::Nothing, false),
        (Reply::Absent, false),
    ] {
        let called = call_with(&code, &data, reply);
        assert_eq!(called.output.is_some(), passes, "{reply:?}");
        let calls = match reply {
            Reply::Nothing => 1,
            Reply::Absent => 0,
            _ => 3,
        };
        assert_eq!(called.inputs.len(), calls, "{reply:?}");
    }
}

/// The three inputs the contract sends are, byte for byte, those the mock is given for the Rust verifier's claims,
/// in order: no more calls, no other bytes.
#[test]
fn inputs_are_the_rust_openings() {
    let mut rng = Rng::new(0x1A9);
    for log_rows in LOG_ROWS {
        let index_root = random_bytes(&mut rng);
        let code = contract(&index_root, log_rows).code;
        for _ in 0..20 {
            let data = random_calldata(&mut rng);
            let (statement, proof) = parse(&data);
            let (roots, claims) = verify(&index_root, &statement, &proof, log_rows).expect("a reduction");
            let expected: Vec<Vec<u8>> = openings(&index_root, &roots, &claims, log_rows)
                .iter()
                .map(|(root, id, claims)| crate::machine::pcs_open_input(root, *id, claims))
                .collect();
            let called = call_with(&code, &data, Reply::Attest);
            assert_eq!(called.output, Some(vec![]));
            assert_eq!(called.inputs, expected);
        }
    }
}

/// What a walk of the straight-line path finds.
#[derive(Debug, Default)]
struct Walk {
    /// Execution gas by opcode, its dynamic part (words copied or hashed, memory) included.
    gas: BTreeMap<&'static str, u64>,
    max_stack: usize,
    memory_words: u64,
    /// `(offset, size)` of each `STATICCALL`'s input.
    calls: Vec<(u64, u64)>,
    fail: Vec<u64>,
    end: usize,
}

fn memory_cost(words: u64) -> u64 {
    3 * words + words * words / 512
}

/// Walk `code` from its start to its `STOP` or `RETURN`, no jump taken, pricing each instruction as Cancun (and
/// Prague, Osaka) does with `PCS_OPEN` warm and free. Offsets and sizes must be pushed constants.
fn walk(code: &[u8]) -> Walk {
    let mut walk = Walk::default();
    let mut stack: Vec<Option<u64>> = vec![];
    let mut pc = 0;
    let pop = |stack: &mut Vec<Option<u64>>| stack.pop().expect("no underflow");
    let expand = |walk: &mut Walk, offset: Option<u64>, size: Option<u64>| -> u64 {
        let size = size.expect("a constant size");
        if size == 0 {
            return 0;
        }
        let words = (offset.expect("a constant offset") + size).div_ceil(32);
        if words <= walk.memory_words {
            return 0;
        }
        let cost = memory_cost(words) - memory_cost(walk.memory_words);
        walk.memory_words = words;
        cost
    };
    loop {
        let op = code[pc];
        let (name, cost): (&'static str, u64) = match op {
            0x5f => {
                stack.push(Some(0));
                ("PUSH", 2)
            }
            0x60..=0x7f => {
                let n = (op - 0x5f) as usize;
                let bytes = &code[pc + 1..pc + 1 + n];
                let value = (n <= 8).then(|| bytes.iter().fold(0u64, |acc, &b| acc << 8 | b as u64));
                stack.push(value);
                pc += n;
                ("PUSH", 3)
            }
            0x80 => {
                let top = *stack.last().unwrap();
                stack.push(top);
                ("DUP", 3)
            }
            0x81 => {
                let second = stack[stack.len() - 2];
                stack.push(second);
                ("DUP", 3)
            }
            0x90 => {
                let len = stack.len();
                stack.swap(len - 1, len - 2);
                ("SWAP", 3)
            }
            FIELD_MUL => {
                pop(&mut stack);
                pop(&mut stack);
                stack.push(None);
                ("FIELD_MUL", FIELD_MUL_GAS)
            }
            0x16..=0x18 | 0x1b | 0x1c => {
                pop(&mut stack);
                pop(&mut stack);
                stack.push(None);
                ("logic", 3)
            }
            0x15 | 0x35 => {
                pop(&mut stack);
                stack.push(None);
                (if op == 0x15 { "ISZERO" } else { "CALLDATALOAD" }, 3)
            }
            0x36 | 0x3d | 0x5a => {
                stack.push(None);
                ("env", 2)
            }
            0x50 => {
                pop(&mut stack);
                ("POP", 2)
            }
            0x51 => {
                let offset = pop(&mut stack);
                let cost = 3 + expand(&mut walk, offset, Some(32));
                stack.push(None);
                ("MLOAD", cost)
            }
            0x52 => {
                let offset = pop(&mut stack);
                pop(&mut stack);
                ("MSTORE", 3 + expand(&mut walk, offset, Some(32)))
            }
            0x20 => {
                let (offset, size) = (pop(&mut stack), pop(&mut stack));
                let cost = 30 + 6 * size.unwrap().div_ceil(32) + expand(&mut walk, offset, size);
                stack.push(None);
                ("KECCAK256", cost)
            }
            0x37 | 0x39 => {
                let (dest, _, size) = (pop(&mut stack), pop(&mut stack), pop(&mut stack));
                let cost = 3 + 3 * size.unwrap().div_ceil(32) + expand(&mut walk, dest, size);
                (if op == 0x37 { "CALLDATACOPY" } else { "CODECOPY" }, cost)
            }
            0x57 => {
                let dest = pop(&mut stack).expect("a pushed destination");
                pop(&mut stack);
                walk.fail.push(dest);
                ("JUMPI", 10)
            }
            0xfa => {
                pop(&mut stack);
                let address = pop(&mut stack);
                assert_eq!(address, Some(0x12));
                let (offset, size) = (pop(&mut stack), pop(&mut stack));
                let (ret_offset, ret_size) = (pop(&mut stack), pop(&mut stack));
                assert_eq!((ret_offset, ret_size), (Some(0), Some(0)));
                walk.calls.push((offset.unwrap(), size.unwrap()));
                let cost = 100 + expand(&mut walk, offset, size);
                stack.push(None);
                ("STATICCALL", cost)
            }
            0x00 => {
                walk.end = pc;
                return walk;
            }
            0xf3 => {
                let (offset, size) = (pop(&mut stack), pop(&mut stack));
                let cost = expand(&mut walk, offset, size);
                *walk.gas.entry("RETURN").or_default() += cost;
                walk.end = pc;
                return walk;
            }
            _ => panic!("opcode {op:#04x} at {pc}"),
        };
        *walk.gas.entry(name).or_default() += cost;
        walk.max_stack = walk.max_stack.max(stack.len());
        pc += 1;
    }
}

/// Where instructions start, as a jump's analysis finds them.
fn boundaries(code: &[u8]) -> Vec<bool> {
    let mut starts = vec![false; code.len()];
    let mut pc = 0;
    while pc < code.len() {
        starts[pc] = true;
        pc += 1 + if (0x60..=0x7f).contains(&code[pc]) {
            (code[pc] - 0x5f) as usize
        } else {
            0
        };
    }
    starts
}

/// The code's straight line: a stack far from its limit, every jump to the one revert, deployable size, and the
/// gas revm charges (`machine::call`) equal to an independent pricing of each instruction. Prints both
/// contracts' gas by opcode: `cargo test --release -p evm -- --nocapture gas_by_opcode`.
#[test]
fn gas_by_opcode() {
    let mut rng = Rng::new(0x6A5);
    for log_rows in LOG_ROWS {
        let index_root = random_bytes(&mut rng);
        let returning = claims_contract(&index_root, log_rows);
        let calling = contract(&index_root, log_rows);
        let data = random_calldata(&mut rng);
        let block = block_for(&index_root, &data, log_rows);
        let mut totals = vec![];
        for (name, compiled, block) in [
            ("returning", &returning, PcsOpen::default()),
            ("calling", &calling, block),
        ] {
            let code = &compiled.code;
            let walk = walk(code);
            assert!(walk.max_stack <= 1024);
            assert_eq!(walk.memory_words as usize, compiled.memory_words);
            let starts = boundaries(code);
            let revert = *walk.fail.first().unwrap();
            assert!(walk.fail.iter().all(|&at| at == revert));
            assert!(starts[revert as usize] && code[revert as usize] == 0x5b);
            assert_eq!(&code[revert as usize..revert as usize + 4], &[0x5b, 0x5f, 0x5f, 0xfd]);
            assert_eq!(revert as usize, walk.end + 1);
            let outcome = call(code, &data, &block);
            assert!(outcome.output.is_some());
            let total: u64 = walk.gas.values().sum();
            assert_eq!(total, outcome.execution, "{name}, 2^{log_rows} rows");
            totals.push(total);
            if log_rows == 22 {
                println!(
                    "{name}: {} bytes of code (EIP-170: 24576), stack at most {}, memory {} words, gas {total}",
                    code.len(),
                    walk.max_stack,
                    walk.memory_words
                );
                println!("  {:?}", walk.gas);
                println!("  calls (offset, size): {:?}", walk.calls);
            }
            assert!(code.len() <= 24_576, "{name}: {} bytes", code.len());
        }
        // The calls read the region back to back to its end, each `3 + k (v + 1)` words: the witness table's claim
        // in `m + 1` variables, the wiring table's in `m`, the quotient table's two in `m + 6`.
        let m = log_rows as u64 + 2;
        let calls = walk(&calling.code).calls;
        let sizes: Vec<u64> = calls.iter().map(|&(_, size)| size / 32).collect();
        assert_eq!(sizes, [3 + (m + 2), 3 + (m + 1), 3 + 2 * (m + 7)]);
        assert!(calls.windows(2).all(|pair| pair[0].0 + pair[0].1 == pair[1].0));
        assert_eq!(calls[2].0 + calls[2].1, 32 * calling.memory_words as u64);
        if log_rows == 22 {
            println!("difference: {}", totals[1] - totals[0]);
        }
    }
}

/// A call `PCS_OPEN` cannot pay for fails, returning nothing, and the contract reverts.
#[test]
fn out_of_gas_in_the_call_reverts() {
    let mut rng = Rng::new(0x006);
    let index_root = random_bytes(&mut rng);
    let code = contract(&index_root, 22).code;
    let data = random_calldata(&mut rng);
    let mut block = block_for(&index_root, &data, 22);
    block.claim_gas = 4_000_000;
    assert_eq!(call(&code, &data, &block).output, None);
    block.claim_gas = 1_000_000;
    assert_eq!(call(&code, &data, &block).output, Some(vec![]));
}
