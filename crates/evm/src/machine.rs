// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/machine.rs; the mock `PCS_OPEN` is new here. MIT OR Apache-2.0; see NOTICE.md.
//! revm with `FIELD_MUL`, and with a mock of the precompile `PCS_OPEN`.
//!
//! # `PCS_OPEN`
//!
//! The precompile at [`PCS_OPEN`] attests that claims on one commitment are those of an opening the block's
//! builder aggregated: the openings travel beside the transactions, and the precompile only looks a call up
//! among them. A call carries **every** claim on its commitment, as one opening does: an opening is of one
//! random combination of its claims, and that alone binds them to one table, leanVM's WHIR taking no
//! out-of-domain sample at its first commitment (two openings of one root could be of two tables).
//!
//! **Input**: `3 + k (v + 1)` words of 32 bytes, nothing more:
//!
//! 1. the commitment: its Merkle root `r` as the word `s_0 · 2^128 + s_1`, `s_h` the little-endian number of
//!    bytes `16 h .. 16 h + 16` of `r` (the two scalars of [`quotient::transcript::root_scalars`]);
//! 2. the layout's id ([`layout_id`]), which fixes `v`, the table's variables, and which lane of the WHIR stack
//!    holds which block of the table;
//! 3. `k ≥ 1`, the number of claims;
//! 4. each claim: its point's `v` coordinates, then its value. A field element of `GF(2^192)` is the low 192
//!    bits of its word, limb 0 lowest, and its top 64 bits are zero.
//!
//! **Output**: the word 1 if one of the block's openings is of exactly these claims, in this order, on the table
//! committed as this root under this layout, and nothing otherwise. A call fails only for lack of gas. A contract
//! tests `RETURNDATASIZE`, which a failed call and an address without the precompile also leave zero.
//!
//! **Why this encoding.** Every word is one the contract already holds as an EVM word, so marshalling a call is
//! an `MSTORE` a word: a field element as `XOR` and `FIELD_MUL` work on it, a root as the calldata carries it and
//! the transcript absorbs it (the raw root would take some forty instructions per root to reverse the bytes of
//! its halves, which a native precompile does for free). Words of fixed width, with no offsets and no length
//! but `k`, leave one way to parse an input, whose length the layout and `k` fix; with the top bits zero, a
//! list of claims has one encoding, and a call is a lookup of its bytes. The layout is named, not sent: the
//! protocol fixes it, and its lanes would be up to 64 more words.
//!
//! **Gas**: [`PcsOpen::call_gas`] a call plus [`PcsOpen::claim_gas`] a claim (`k` as the input's third word says,
//! read before anything is checked; none if the input is shorter), both zero by default, so that what the calls
//! cost the contract is measured apart. No gas a byte of input: the caller paid for writing it to memory, and a
//! claim's price stands for its share of the block's aggregated proof.

use std::collections::HashSet;

use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use quotient::opening::{Claim, Layout};
use quotient::protocol::{quotient_layout, wiring_layout, witness_layout};
use quotient::transcript::root_scalars;
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Cfg, Context, ContextTr, LocalContextTr, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{EthPrecompiles, ExecuteEvm, MainBuilder, MainContext, PrecompileProvider};
use revm::interpreter::interpreter_types::{InterpreterTypes, StackTr};
use revm::interpreter::{CallInput, Gas, InputsImpl, InstructionContext, InstructionResult, InterpreterResult, gas};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, U256};
use revm::state::{AccountInfo, Bytecode};

/// The opcode of `FIELD_MUL`, unassigned on mainnet.
pub const FIELD_MUL: u8 = 0x0c;
pub const FIELD_MUL_GAS: u64 = 10;

/// The address of `PCS_OPEN`: the first no mainnet precompile takes (Prague's last is `0x11`).
pub const PCS_OPEN: Address = Address::with_last_byte(0x12);

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

/// A field element as `PCS_OPEN` reads it: limb 0 lowest, the top 64 bits zero.
pub fn element_word(x: F192) -> [u8; 32] {
    U256::from_limbs([x.c0, x.c1, x.c2, 0]).to_be_bytes()
}

/// A root as `PCS_OPEN` reads it: `s_0 · 2^128 + s_1`, its two scalars as the transcript carries them.
pub fn root_word(root: &Hash) -> [u8; 32] {
    let [s0, s1] = root_scalars(root);
    U256::from_limbs([s1.c0, s1.c1, s0.c0, s0.c1]).to_be_bytes()
}

/// The tables of the membership protocol (`quotient::protocol`), as `PCS_OPEN` names their layouts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableId {
    Witness = 1,
    Wiring = 2,
    Quotient = 3,
}

/// The rows, `2^log_rows`, for which `PCS_OPEN` knows the protocol's layouts: where each of its three tables is
/// a stack leanVM's WHIR commits, of `2^15` to `2^28` words in at most 64 lanes, and the two secret ones have
/// hidden layouts (`quotient::protocol::MIN_LOG_ROWS`, `crates/quotient/HIDING.md`).
pub const LOG_ROWS: std::ops::RangeInclusive<usize> = quotient::protocol::MIN_LOG_ROWS..=22;

/// The id of the layout of `table` for a circuit of `2^log_rows` rows: `256 · table + log_rows`.
pub fn layout_id(table: TableId, log_rows: usize) -> u64 {
    assert!(LOG_ROWS.contains(&log_rows), "no layout for 2^{log_rows} rows");
    256 * table as u64 + log_rows as u64
}

/// The layout an id names, if `PCS_OPEN` knows it.
pub fn layout(id: U256) -> Option<Layout> {
    let id = u64::try_from(id).ok()?;
    let log_rows = (id % 256) as usize;
    let table = match id / 256 {
        1 => witness_layout,
        2 => wiring_layout,
        3 => quotient_layout,
        _ => return None,
    };
    LOG_ROWS.contains(&log_rows).then(|| table(log_rows))
}

/// The input of `PCS_OPEN` for `claims` on the table committed as `root`, under layout `id`.
pub fn pcs_open_input(root: &Hash, id: u64, claims: &[Claim]) -> Vec<u8> {
    let vars = layout(U256::from(id)).expect("a layout PCS_OPEN knows").vars;
    assert!(!claims.is_empty() && claims.iter().all(|claim| claim.point.len() == vars));
    let mut input = root_word(root).to_vec();
    input.extend(U256::from(id).to_be_bytes::<32>());
    input.extend(U256::from(claims.len()).to_be_bytes::<32>());
    for claim in claims {
        for &x in claim.point.iter().chain([&claim.value]) {
            input.extend(element_word(x));
        }
    }
    input
}

/// A mock of `PCS_OPEN`: the openings standing for a block's, each as the one input that names it, and its
/// prices. It checks nothing else: an input it holds is well formed, being made by [`pcs_open_input`].
#[derive(Clone, Debug, Default)]
pub struct PcsOpen {
    attested: HashSet<Vec<u8>>,
    /// Gas a call costs.
    pub call_gas: u64,
    /// Gas a claim costs.
    pub claim_gas: u64,
}

impl PcsOpen {
    /// Take an opening of `claims`, all together, on the table committed as `root`, under layout `id`, to be in
    /// the block.
    pub fn register(&mut self, root: &Hash, id: u64, claims: &[Claim]) {
        self.attested.insert(pcs_open_input(root, id, claims));
    }

    /// What a call with `input` costs, and whether it attests.
    fn run(&self, input: &[u8]) -> (u64, bool) {
        let claims = input
            .get(64..96)
            .map_or(0, |k| U256::from_be_slice(k).saturating_to::<u64>());
        let gas = self.claim_gas.saturating_mul(claims).saturating_add(self.call_gas);
        (gas, self.attested.contains(input))
    }
}

/// Mainnet's precompiles and `PCS_OPEN`.
struct Precompiles<'a> {
    eth: EthPrecompiles,
    pcs_open: &'a PcsOpen,
    /// Whether the journal has been told the addresses, `PCS_OPEN`'s among them, which makes it warm.
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

/// What a call did.
#[derive(Debug)]
pub struct Outcome {
    /// What it returned, or `None` if it reverted or halted.
    pub output: Option<Vec<u8>>,
    /// The gas of the contract's execution, its calls of `PCS_OPEN` included: the transaction's without its base
    /// cost and its calldata.
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

/// Call a contract holding `code` with `calldata`, in one transaction of a block whose openings are `pcs_open`'s.
pub fn call(code: &[u8], calldata: &[u8], pcs_open: &PcsOpen) -> Outcome {
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
        .build_mainnet()
        .with_precompiles(Precompiles {
            eth: EthPrecompiles::default(),
            pcs_open,
            warm: false,
        });
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Every layout `PCS_OPEN` knows is a stack leanVM's WHIR commits; ids outside the table name none.
    #[test]
    fn layouts_are_known_by_id() {
        for log_rows in LOG_ROWS {
            for table in [TableId::Witness, TableId::Wiring, TableId::Quotient] {
                let layout = layout(U256::from(layout_id(table, log_rows))).expect("a layout");
                assert!((15..=28).contains(&layout.log_n) && layout.lanes() <= 64);
            }
        }
        for id in [0u64, 12, 256 + 12, 256 + 23, 4 * 256 + 22, 1 << 40] {
            assert_eq!(layout(U256::from(id)), None, "{id}");
        }
        assert_eq!(layout(U256::MAX), None);
    }

    /// The root's word is its two scalars, the high one first.
    #[test]
    fn root_word_is_its_scalars() {
        let root: Hash = std::array::from_fn(|i| i as u8 + 1);
        let word = root_word(&root);
        let mut halves = [root[..16].to_vec(), root[16..].to_vec()];
        halves.iter_mut().for_each(|half| half.reverse());
        assert_eq!(word.to_vec(), halves.concat());
    }
}
