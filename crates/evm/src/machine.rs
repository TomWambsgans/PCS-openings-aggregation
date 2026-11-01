// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/machine.rs. MIT OR Apache-2.0; see NOTICE.md.
//! revm with `FIELD_MUL`.

use primitives::field::F192;
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Context, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{ExecuteEvm, MainBuilder, MainContext};
use revm::interpreter::interpreter_types::{InterpreterTypes, StackTr};
use revm::interpreter::{InstructionContext, InstructionResult, gas};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, U256};
use revm::state::{AccountInfo, Bytecode};

/// The opcode of `FIELD_MUL`, unassigned on mainnet.
pub const FIELD_MUL: u8 = 0x0c;
pub const FIELD_MUL_GAS: u64 = 10;

fn element(word: U256) -> F192 {
    let [c0, c1, c2, _] = word.into_limbs();
    F192::new(c0, c1, c2)
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

/// What a call did.
#[derive(Debug)]
pub struct Outcome {
    /// What it returned, or `None` if it reverted or halted.
    pub output: Option<Vec<u8>>,
    /// The gas of the contract's execution: the transaction's without its base cost and its calldata.
    pub execution: u64,
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

/// Call a contract holding `code` with `calldata`, in one transaction.
pub fn call(code: &[u8], calldata: &[u8]) -> Outcome {
    let (contract, caller) = (Address::with_last_byte(0xc0), Address::with_last_byte(0xca));
    let mut db = CacheDB::new(EmptyDB::default());
    db.insert_account_info(
        contract,
        AccountInfo::from_bytecode(Bytecode::new_legacy(Bytes::copy_from_slice(code))),
    );
    // Cancun has no calldata floor, so the gas it reports separates into calldata and execution.
    let mut evm = Context::mainnet()
        .with_db(db)
        .modify_cfg_chained(|cfg| cfg.spec = SpecId::CANCUN)
        .build_mainnet();
    evm.instruction.insert_instruction(FIELD_MUL, field_mul);
    let tx = TxEnv::builder()
        .caller(caller)
        .kind(TxKind::Call(contract))
        .data(Bytes::copy_from_slice(calldata))
        .gas_limit(10_000_000)
        .build()
        .expect("a transaction");
    let result = evm.transact_one(tx).expect("a valid transaction");
    let execution = result.gas_used() - transaction_gas(calldata, 0, 0);
    let output = match result {
        ExecutionResult::Success {
            output: Output::Call(output),
            ..
        } => Some(output.to_vec()),
        _ => None,
    };
    Outcome { output, execution }
}
