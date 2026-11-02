// Adapted from this repository's crates/evm/src/machine.rs (itself adapted from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6): revm with `FIELD_MUL`
// and a mock `PCS_OPEN`, the same opcode, address, call encoding and transaction gas; here the mock takes any layout
// id, the code is installed rather than deployed (it may pass EIP-170's limit), and an inspector gives every
// instruction's gas. MIT OR Apache-2.0; see NOTICE.md.
//! revm with `FIELD_MUL`, a mock of the precompile `PCS_OPEN`, and per-instruction gas.
//!
//! `PCS_OPEN`'s input is this repository's (`crates/evm/src/machine.rs`): `3 + k (v + 1)` words, the commitment's
//! root word, the layout's id, `k`, then each claim's `v` coordinates and its value, a field element being the low
//! 192 bits of its word. It returns the word 1 if the block's openings hold exactly these claims on that commitment
//! under that layout. A call carries every claim on its commitment. Gas: `call_gas` a call and `claim_gas` a claim.

use std::collections::HashSet;

use crate::field::E;
use revm::bytecode::Bytecode;
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Cfg, Context, ContextTr, LocalContextTr, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{EthPrecompiles, MainBuilder, MainContext, PrecompileProvider};
use revm::inspector::{InspectEvm, Inspector};
use revm::interpreter::interpreter_types::{InterpreterTypes, Jumps, StackTr};
use revm::interpreter::{
    CallInput, Gas, InputsImpl, InstructionContext, InstructionResult, Interpreter, InterpreterResult, gas,
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

/// A mock of `PCS_OPEN`: the openings standing for a block's, each as the one input that names it, and its prices.
#[derive(Clone, Debug, Default)]
pub struct PcsOpen {
    attested: HashSet<Vec<u8>>,
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
        self.attested.insert(input);
    }

    /// What a call with `input` costs, and whether it attests.
    fn run(&self, input: &[u8]) -> (u64, bool) {
        let claims = input
            .get(64..96)
            .map_or(0, |k| U256::from_be_slice(k).saturating_to::<u64>());
        let gas = self.claim_gas.saturating_mul(claims).saturating_add(self.call_gas);
        (gas, self.attest_all || self.attested.contains(input))
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

/// The gas of each instruction, by its program counter: what the gas left drops by between the start of the
/// instruction and the start of the next (a call's included).
#[derive(Default)]
struct GasByPc {
    gas: Vec<u64>,
    last: Option<(usize, u64)>,
    end: u64,
}

impl<CTX, INTR: InterpreterTypes> Inspector<CTX, INTR> for GasByPc {
    fn step(&mut self, interp: &mut Interpreter<INTR>, _context: &mut CTX) {
        let (pc, left) = (interp.bytecode.pc(), interp.gas.remaining());
        if let Some((last, before)) = self.last {
            self.gas[last] += before - left;
        }
        self.last = Some((pc, left));
    }

    fn step_end(&mut self, interp: &mut Interpreter<INTR>, _context: &mut CTX) {
        self.end = interp.gas.remaining();
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
    /// Each instruction's gas, by program counter.
    pub gas_by_pc: Vec<u64>,
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
    let mut db = CacheDB::<EmptyDB>::default();
    let account = AccountInfo::default().with_code(Bytecode::new_raw(Bytes::copy_from_slice(code)));
    db.insert_account_info(VERIFIER, account);
    for &(slot, word) in storage {
        db.insert_account_storage(VERIFIER, U256::from(slot), U256::from_be_bytes(word))
            .expect("an account");
    }
    db.insert_account_info(CALLER, AccountInfo::from_balance(U256::from(10u64.pow(18))));
    // Cancun has no calldata floor, so the gas it reports separates into calldata and execution.
    let mut evm = Context::mainnet()
        .with_db(&mut db)
        .modify_cfg_chained(|cfg| cfg.spec = SpecId::CANCUN)
        .modify_block_chained(|block| block.gas_limit = u64::MAX)
        .build_mainnet_with_inspector(GasByPc {
            gas: vec![0; code.len() + 1],
            ..GasByPc::default()
        })
        .with_precompiles(Precompiles {
            eth: EthPrecompiles::default(),
            pcs_open,
            calls: Vec::new(),
            warm: false,
        });
    evm.instruction.insert_instruction(FIELD_MUL, field_mul);
    let tx = TxEnv::builder()
        .caller(CALLER)
        .kind(TxKind::Call(VERIFIER))
        .data(Bytes::copy_from_slice(calldata))
        .gas_limit(100_000_000)
        .build()
        .expect("a transaction");
    let result = evm.inspect_one_tx(tx).expect("a valid transaction");
    let execution = result.gas_used() - transaction_gas(calldata, 0, 0);
    let output = match result {
        ExecutionResult::Success {
            output: Output::Call(output),
            ..
        } => Some(output.to_vec()),
        _ => None,
    };
    let mut inspector = std::mem::take(&mut evm.inspector);
    if let Some((last, before)) = inspector.last {
        inspector.gas[last] += before - inspector.end;
    }
    Outcome {
        output,
        execution,
        gas_by_pc: inspector.gas,
        pcs_calls: std::mem::take(&mut evm.precompiles.calls),
    }
}
