// Adapted from this repository's crates/evm/src/machine.rs (itself adapted from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6): revm with `FIELD_MUL`
// and a mock `PCS_OPEN`, the same opcode, address, call encoding and transaction gas, and a `Chain` that deploys
// contracts and keeps them across transactions; here the mock takes any layout id, code may also be installed rather
// than deployed (it may pass EIP-170's limit), and an inspector gives every instruction's gas, in every contract a
// call runs. MIT OR Apache-2.0; see NOTICE.md.
//! revm with `FIELD_MUL`, a mock of the precompile `PCS_OPEN`, and per-instruction gas.
//!
//! `PCS_OPEN`'s input is this repository's (`crates/evm/src/machine.rs`): `3 + k (v + 1)` words, the commitment's
//! root word, the layout's id, `k`, then each claim's `v` coordinates and its value, a field element being the low
//! 192 bits of its word. It returns the word 1 if the block's openings hold exactly these claims on that commitment
//! under that layout. A call carries every claim on its commitment. Gas: `call_gas` a call and `claim_gas` a claim.
//!
//! The mock has two modes. The **byte-string** mode (no layouts registered) attests an input if it is one of the
//! registered inputs, byte for byte: what `crates/leanvm_univariate`'s vectors use. The **decoding** mode
//! (`crates/leanvm_rec/REVIEW-REC.md`, M1) is a registry keyed by the layout word: an input attests only if it
//! decodes under the ABI ([`decode`]: the root word `s_0 · 2^128 + s_1` of [`root_word`], a layout word the registry
//! knows, which fixes `v`, `k ≥ 1`, the exact length, every element's top 64 bits zero) into a registered opening
//! (the root as the opening has it, the layout word, the claims). A call in another format then fails its test.

use std::collections::{HashMap, HashSet};

use crate::field::E;
use revm::bytecode::Bytecode;
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Cfg, Context, ContextTr, LocalContextTr, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{EthPrecompiles, ExecuteCommitEvm, MainBuilder, MainContext, PrecompileProvider};
use revm::inspector::{InspectCommitEvm, Inspector};
use revm::interpreter::interpreter_types::{InputsTr, InterpreterTypes, Jumps, StackTr};
use revm::interpreter::{
    CallInput, CallInputs, CallOutcome, Gas, InputsImpl, InstructionContext, InstructionResult, Interpreter,
    InterpreterResult, gas,
};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, U256};
use revm::state::AccountInfo;

/// The opcode of `FIELD_MUL`, unassigned on mainnet.
pub const FIELD_MUL: u8 = 0x0c;
pub const FIELD_MUL_GAS: u64 = 10;

/// The address of `PCS_OPEN`: the first no mainnet precompile takes (Prague's last is `0x11`).
pub const PCS_OPEN: Address = Address::with_last_byte(0x12);

/// Where the contract is installed, and who calls it.
pub const VERIFIER: Address = Address::with_last_byte(0xc0);
pub const CALLER: Address = Address::with_last_byte(0xca);
/// Who deploys contracts.
pub const DEPLOYER: Address = Address::with_last_byte(0xde);

fn element(word: U256) -> E {
    let [c0, c1, c2, _] = word.into_limbs();
    E::new(c0, c1, c2)
}

/// Pops two words and pushes the product of their low 192 bits as elements of `GF(2^192)`.
fn field_mul<W: InterpreterTypes, H: ?Sized>(context: InstructionContext<'_, H, W>) {
    gas!(context.interpreter, FIELD_MUL_GAS);
    let Some(([a], b)) = context.interpreter.stack.popn_top() else {
        context.interpreter.halt(InstructionResult::StackUnderflow);
        return;
    };
    let product = element(a) * element(*b);
    *b = U256::from_limbs([product.c0, product.c1, product.c2, 0]);
}

/// A field element as `PCS_OPEN` reads it: limb 0 lowest, the top 64 bits zero.
pub fn element_word(x: E) -> [u8; 32] {
    U256::from_limbs([x.c0, x.c1, x.c2, 0]).to_be_bytes()
}

/// `PCS_OPEN`'s root word (`crates/evm/src/machine.rs`): `s_0 · 2^128 + s_1`, `s_h` the little-endian number of the
/// root's bytes `16 h .. 16 h + 16`, that is each 16-byte half reversed. Its own inverse.
pub fn root_word(root: &[u8; 32]) -> [u8; 32] {
    let mut out = *root;
    out[..16].reverse();
    out[16..].reverse();
    out
}

/// The root a root word names ([`root_word`] is an involution).
pub fn root_of_word(word: &[u8; 32]) -> [u8; 32] {
    root_word(word)
}

/// A `PCS_OPEN` call, decoded: the commitment's root (as its opening has it), the layout word, the claims.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opening {
    pub root: [u8; 32],
    pub layout: [u8; 32],
    pub claims: Vec<(Vec<E>, E)>,
}

impl Opening {
    /// The input that names this opening: [`decode`]'s inverse.
    pub fn input(&self) -> Vec<u8> {
        let mut out = root_word(&self.root).to_vec();
        out.extend(self.layout);
        out.extend(U256::from(self.claims.len()).to_be_bytes::<32>());
        for (point, value) in &self.claims {
            for &x in point.iter().chain([value]) {
                out.extend(element_word(x));
            }
        }
        out
    }
}

/// Decode `input` under the ABI, the table's variables `vars(layout word)` (`None`: a layout the precompile does not
/// know). `None` unless the input is exactly `3 + k (v + 1)` words with `1 ≤ k`, and every element's top 64 bits are
/// zero.
pub fn decode(input: &[u8], vars: impl Fn(&[u8; 32]) -> Option<usize>) -> Option<Opening> {
    let word = |k: usize| -> Option<[u8; 32]> { input.get(32 * k..32 * k + 32)?.try_into().ok() };
    let (root, layout, count) = (word(0)?, word(1)?, word(2)?);
    let v = vars(&layout)?;
    if count[..24].iter().any(|&b| b != 0) {
        return None;
    }
    let k = u64::from_be_bytes(count[24..].try_into().ok()?) as usize;
    if k == 0 || input.len() != 32 * (3 + k * (v + 1)) {
        return None;
    }
    let element = |w: [u8; 32]| -> Option<E> {
        if w[..8].iter().any(|&b| b != 0) {
            return None;
        }
        let [c0, c1, c2, _] = U256::from_be_bytes(w).into_limbs();
        Some(E::new(c0, c1, c2))
    };
    let mut claims = Vec::with_capacity(k);
    for c in 0..k {
        let at = 3 + c * (v + 1);
        let point = (0..v).map(|j| element(word(at + j)?)).collect::<Option<Vec<E>>>()?;
        claims.push((point, element(word(at + v)?)?));
    }
    Some(Opening {
        root: root_of_word(&root),
        layout,
        claims,
    })
}

/// A mock of `PCS_OPEN`: the openings standing for a block's, each as the one input that names it, and its prices.
#[derive(Clone, Debug, Default)]
pub struct PcsOpen {
    attested: HashSet<Vec<u8>>,
    /// The decoding mode's registry: the layouts the precompile knows (layout word → the table's variables), and the
    /// block's openings, decoded.
    layouts: HashMap<[u8; 32], usize>,
    openings: Vec<Opening>,
    /// Attest every call: a measuring run, whose claims are not those of a valid proof.
    pub attest_all: bool,
    pub call_gas: u64,
    pub claim_gas: u64,
}

impl PcsOpen {
    /// A block that attests every call, at `claim_gas` a claim: a measuring run.
    pub fn attesting_all(claim_gas: u64) -> Self {
        Self {
            attest_all: true,
            claim_gas,
            ..Self::default()
        }
    }

    pub fn register(&mut self, input: Vec<u8>) {
        assert!(self.layouts.is_empty(), "the decoding mode registers openings, not inputs");
        self.attested.insert(input);
    }

    /// The decoding mode: a precompile that knows these layouts (layout word, the table's variables).
    pub fn decoding(layouts: impl IntoIterator<Item = ([u8; 32], usize)>) -> Self {
        let layouts: HashMap<[u8; 32], usize> = layouts.into_iter().collect();
        assert!(!layouts.is_empty(), "a registry of at least one layout");
        Self {
            layouts,
            ..Self::default()
        }
    }

    /// An opening of the block (decoding mode): its root, layout word and claims, which must be of a known layout.
    pub fn register_opening(&mut self, opening: Opening) {
        let v = self.layouts.get(&opening.layout).expect("a layout the precompile knows");
        assert!(!opening.claims.is_empty() && opening.claims.iter().all(|(p, _)| p.len() == *v));
        self.openings.push(opening);
    }

    /// `input` decoded as this precompile does (decoding mode).
    pub fn decode(&self, input: &[u8]) -> Option<Opening> {
        decode(input, |w| self.layouts.get(w).copied())
    }

    /// What a call with `input` costs, and whether it attests.
    fn run(&self, input: &[u8]) -> (u64, bool) {
        let claims = input
            .get(64..96)
            .map_or(0, |k| U256::from_be_slice(k).saturating_to::<u64>());
        let gas = self.claim_gas.saturating_mul(claims).saturating_add(self.call_gas);
        let attested = if self.layouts.is_empty() {
            self.attest_all || self.attested.contains(input)
        } else {
            // A known layout and a well-formed input, even in a measuring run.
            self.decode(input)
                .is_some_and(|o| self.attest_all || self.openings.contains(&o))
        };
        (gas, attested)
    }
}

/// Mainnet's precompiles and `PCS_OPEN`, which keeps the inputs it was called with.
struct Precompiles<'a> {
    eth: EthPrecompiles,
    pcs_open: &'a PcsOpen,
    calls: Vec<Vec<u8>>,
    warm: bool,
}

impl<CTX: ContextTr> PrecompileProvider<CTX> for Precompiles<'_> {
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
        if *address != PCS_OPEN {
            return self.eth.run(context, address, inputs, is_static, gas_limit);
        }
        let input = match &inputs.input {
            CallInput::SharedBuffer(range) => context
                .local()
                .shared_memory_buffer_slice(range.clone())
                .map_or_else(Vec::new, |slice| slice.to_vec()),
            CallInput::Bytes(bytes) => bytes.to_vec(),
        };
        let (cost, attested) = self.pcs_open.run(&input);
        self.calls.push(input);
        let mut result = InterpreterResult {
            result: InstructionResult::Return,
            gas: Gas::new(gas_limit),
            output: Bytes::new(),
        };
        if !result.gas.record_cost(cost) {
            result.result = InstructionResult::PrecompileOOG;
        } else if attested {
            result.output = Bytes::from(U256::from(1).to_be_bytes_vec());
        }
        Ok(Some(result))
    }

    fn warm_addresses(&self) -> Box<impl Iterator<Item = Address>> {
        Box::new(self.eth.warm_addresses().chain([PCS_OPEN]))
    }

    fn contains(&self, address: &Address) -> bool {
        *address == PCS_OPEN || self.eth.contains(address)
    }
}

/// A call frame being run: whose code, and its last instruction started (its pc and the gas left then).
struct FrameGas {
    code: Address,
    last: Option<(usize, u64)>,
    /// The gas left after its last instruction ran (for the one that ends it).
    end: u64,
    /// Gas its finished calls' frames spent since its last instruction started, which that instruction's drop holds.
    children: u64,
    /// Gas attributed to its instructions and to its calls' frames.
    total: u64,
}

impl FrameGas {
    fn new(code: Address) -> Self {
        Self {
            code,
            last: None,
            end: 0,
            children: 0,
            total: 0,
        }
    }
}

/// The gas of each instruction, by the code it is in and its program counter: what its frame's gas left drops by
/// between the start of the instruction and the start of the next, less what the frames of its calls spent (a call
/// of a precompile runs no instructions: its gas is the call's).
#[derive(Default)]
struct GasByPc {
    sizes: Vec<(Address, usize)>,
    gas: Vec<(Address, Vec<u64>)>,
    frames: Vec<FrameGas>,
}

impl GasByPc {
    fn charge(&mut self, code: Address, pc: usize, gas: u64) {
        let at = match self.gas.iter().position(|(address, _)| *address == code) {
            Some(at) => at,
            None => {
                let size = self
                    .sizes
                    .iter()
                    .find(|(address, _)| *address == code)
                    .map_or(0, |s| s.1);
                self.gas.push((code, vec![0; size + 1]));
                self.gas.len() - 1
            }
        };
        let counts = &mut self.gas[at].1;
        if counts.len() <= pc {
            counts.resize(pc + 1, 0);
        }
        counts[pc] += gas;
    }

    /// The frame on top ended: its last instruction's gas, and its total to its caller's.
    fn finish(&mut self) {
        let frame = self.frames.pop().expect("a frame");
        let mut total = frame.total;
        if let Some((pc, before)) = frame.last {
            let gas = before - frame.end - frame.children;
            self.charge(frame.code, pc, gas);
            total += gas + frame.children;
        }
        if let Some(caller) = self.frames.last_mut() {
            caller.children += total;
        }
    }
}

impl<CTX, INTR: InterpreterTypes> Inspector<CTX, INTR> for GasByPc {
    fn step(&mut self, interp: &mut Interpreter<INTR>, _context: &mut CTX) {
        let (pc, left) = (interp.bytecode.pc(), interp.gas.remaining());
        let code = interp
            .input
            .bytecode_address()
            .copied()
            .unwrap_or_else(|| interp.input.target_address());
        if self.frames.is_empty() {
            self.frames.push(FrameGas::new(code));
        }
        let frame = self.frames.last_mut().expect("a frame");
        frame.code = code;
        let previous = frame.last.replace((pc, left));
        let children = std::mem::take(&mut frame.children);
        if let Some((last, before)) = previous {
            let gas = before - left - children;
            frame.total += gas + children;
            self.charge(code, last, gas);
        }
    }

    fn step_end(&mut self, interp: &mut Interpreter<INTR>, _context: &mut CTX) {
        if let Some(frame) = self.frames.last_mut() {
            frame.end = interp.gas.remaining();
        }
    }

    fn call(&mut self, _context: &mut CTX, inputs: &mut CallInputs) -> Option<CallOutcome> {
        self.frames.push(FrameGas::new(inputs.bytecode_address));
        None
    }

    fn call_end(&mut self, _context: &mut CTX, _inputs: &CallInputs, _outcome: &mut CallOutcome) {
        self.finish();
    }
}

/// What a call did.
#[derive(Debug)]
pub struct Outcome {
    /// What it returned, or `None` if it reverted or halted.
    pub output: Option<Vec<u8>>,
    /// The gas of its execution, its calls of `PCS_OPEN` included: the transaction's without its base cost and its
    /// calldata.
    pub execution: u64,
    /// Each instruction's gas, by program counter, of the code called.
    pub gas_by_pc: Vec<u64>,
    /// The same, of every code that ran, by its address.
    pub gas_by_code: Vec<(Address, Vec<u64>)>,
    /// The inputs `PCS_OPEN` was called with, in order.
    pub pcs_calls: Vec<Vec<u8>>,
}

/// A transaction's gas: its base cost, then the larger of its calldata at the standard rate plus `execution`, and
/// of its calldata at the floor rate, `floor` gas a nonzero byte. EIP-7623 has a floor of 40, and 10 for a zero
/// byte; EIP-7976 has 64 for every byte.
pub fn transaction_gas(calldata: &[u8], execution: u64, floor: u64) -> u64 {
    let zeros = calldata.iter().filter(|&&byte| byte == 0).count() as u64;
    let nonzeros = calldata.len() as u64 - zeros;
    let floor_gas = floor * nonzeros + if floor == 64 { 64 } else { floor / 4 } * zeros;
    21_000 + (16 * nonzeros + 4 * zeros + execution).max(floor_gas)
}

/// Call `code`, installed at [`VERIFIER`] with storage `storage` (slot, word), with `calldata`, from [`CALLER`], in a
/// block whose openings are `pcs_open`'s; the transaction starts cold (EIP-2929).
pub fn call(code: &[u8], storage: &[(u8, [u8; 32])], calldata: &[u8], pcs_open: &PcsOpen) -> Outcome {
    let mut chain = Chain::default();
    chain.install(VERIFIER, code);
    for &(slot, word) in storage {
        chain.store(VERIFIER, slot, word);
    }
    chain.call(VERIFIER, calldata, pcs_open)
}

/// The accounts transactions run on, kept across them.
#[derive(Clone, Default)]
pub struct Chain {
    db: CacheDB<EmptyDB>,
}

/// A transaction's output (a creation's: the code), its execution gas (a creation's includes its 32,000, its init
/// code's 2 a word and its code's deposit, 200 a byte), and the address it created.
type Run = (Option<Vec<u8>>, u64, Option<Address>);

impl Chain {
    /// Put `code` at `address`, as if deployed.
    pub fn install(&mut self, address: Address, code: &[u8]) {
        let account = AccountInfo::default().with_code(Bytecode::new_raw(Bytes::copy_from_slice(code)));
        self.db.insert_account_info(address, account);
    }

    pub fn store(&mut self, address: Address, slot: u8, word: [u8; 32]) {
        self.db
            .insert_account_storage(address, U256::from(slot), U256::from_be_bytes(word))
            .expect("an account");
    }

    /// The code at `address`.
    pub fn code(&self, address: Address) -> Vec<u8> {
        let account = self.db.cache.accounts.get(&address);
        let code = account.and_then(|account| account.info.code.as_ref());
        code.map_or_else(Vec::new, |code| code.original_byte_slice().to_vec())
    }

    /// The word in storage slot `slot` of the account at `address`.
    pub fn storage(&self, address: Address, slot: u8) -> [u8; 32] {
        let account = self.db.cache.accounts.get(&address);
        let word = account.and_then(|account| account.storage.get(&U256::from(slot)).copied());
        word.unwrap_or_default().to_be_bytes()
    }

    /// Deploy `init_code` by a transaction from [`DEPLOYER`] (EIP-170's and EIP-3860's limits enforced): the address,
    /// unless the creation failed, and the transaction's execution gas.
    pub fn deploy(&mut self, init_code: &[u8]) -> (Option<Address>, u64) {
        let (_, execution, created) = self.transact(DEPLOYER, TxKind::Create, init_code, &PcsOpen::default(), None);
        (created, execution)
    }

    /// Call `to` with `calldata`, from [`CALLER`], in a block whose openings are `pcs_open`'s, leaving the chain as
    /// it was; each instruction's gas, by code.
    pub fn call(&self, to: Address, calldata: &[u8], pcs_open: &PcsOpen) -> Outcome {
        let mut chain = self.clone();
        let mut inspector = GasByPc::default();
        for (address, account) in &chain.db.cache.accounts {
            let size = account
                .info
                .code
                .as_ref()
                .map_or(0, |code| code.original_byte_slice().len());
            inspector.sizes.push((*address, size));
        }
        let mut calls = Vec::new();
        let (output, execution, _) = chain.transact(
            CALLER,
            TxKind::Call(to),
            calldata,
            pcs_open,
            Some((&mut inspector, &mut calls)),
        );
        while !inspector.frames.is_empty() {
            inspector.finish();
        }
        let gas_by_pc = inspector
            .gas
            .iter()
            .find(|(address, _)| *address == to)
            .map_or_else(Vec::new, |(_, gas)| gas.clone());
        Outcome {
            output,
            execution,
            gas_by_pc,
            gas_by_code: inspector.gas,
            pcs_calls: calls,
        }
    }

    fn transact(
        &mut self,
        from: Address,
        to: TxKind,
        data: &[u8],
        pcs_open: &PcsOpen,
        inspect: Option<(&mut GasByPc, &mut Vec<Vec<u8>>)>,
    ) -> Run {
        let nonce = self
            .db
            .cache
            .accounts
            .get(&from)
            .map_or(0, |account| account.info.nonce);
        self.db.insert_account_info(
            from,
            AccountInfo::from_balance(U256::from(10u64.pow(18))).with_nonce(nonce),
        );
        let tx = TxEnv::builder()
            .caller(from)
            .nonce(nonce)
            .kind(to)
            .data(Bytes::copy_from_slice(data))
            .gas_limit(100_000_000)
            .build()
            .expect("a transaction");
        let precompiles = Precompiles {
            eth: EthPrecompiles::default(),
            pcs_open,
            calls: Vec::new(),
            warm: false,
        };
        // Cancun has no calldata floor, so the gas it reports separates into calldata and execution.
        let context = Context::mainnet()
            .with_db(&mut self.db)
            .modify_cfg_chained(|cfg| cfg.spec = SpecId::CANCUN)
            .modify_block_chained(|block| block.gas_limit = u64::MAX);
        let result = match inspect {
            Some((inspector, calls)) => {
                let mut evm = context
                    .build_mainnet_with_inspector(std::mem::take(inspector))
                    .with_precompiles(precompiles);
                evm.instruction.insert_instruction(FIELD_MUL, field_mul);
                let result = evm.inspect_tx_commit(tx).expect("a valid transaction");
                *inspector = std::mem::take(&mut evm.inspector);
                *calls = std::mem::take(&mut evm.precompiles.calls);
                result
            }
            None => {
                let mut evm = context.build_mainnet().with_precompiles(precompiles);
                evm.instruction.insert_instruction(FIELD_MUL, field_mul);
                evm.transact_commit(tx).expect("a valid transaction")
            }
        };
        let execution = result.gas_used() - transaction_gas(data, 0, 0);
        match result {
            ExecutionResult::Success {
                output: Output::Call(output),
                ..
            } => (Some(output.to_vec()), execution, None),
            ExecutionResult::Success {
                output: Output::Create(output, created),
                ..
            } => (Some(output.to_vec()), execution, created),
            _ => (None, execution, None),
        }
    }
}
