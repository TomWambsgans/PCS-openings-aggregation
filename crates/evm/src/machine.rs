// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/machine.rs; new here: the mock `PCS_OPEN`, and the `Chain` that deploys contracts and keeps
// their storage across transactions. MIT OR Apache-2.0; see NOTICE.md.
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
//! committed as this root under this layout, and nothing otherwise, an input of another length included. Such an
//! opening is one [`quotient::opening::verify`] accepts for the layout the id names: its transcript's IV hashes
//! that layout's prefix ([`quotient::opening::prefix`]: the label, the version, the layout's hash, its size, WHIR's
//! rate) then these claims, words 4 onwards as field elements, and its proof's first two scalars are the root's,
//! word 1's two halves (`formal/WhirBridge`, `family_sound`). The ids name distinct prefixes. A call
//! fails only for lack of gas. A contract takes a call to attest only if it succeeded and returned exactly 32 bytes,
//! the word 1: a failed call and an address without the precompile return nothing, and anything else (the word 0,
//! a revert with data, more words) is not an attestation either.
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
//! claim's price stands for its share of the block's aggregated proof. A real precompile's price should depend on
//! the table the layout names, not on `k` alone: the tables are of `2^15` to `2^28` words, and what a claim adds to
//! the block's aggregated proof (and to its builder's work) grows with the table's size.

use std::collections::HashSet;

use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use quotient::opening::{Claim, Layout};
use quotient::protocol::{quotient_layout, wiring_layout, witness_layout};
use quotient::transcript::root_scalars;
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Cfg, Context, ContextTr, LocalContextTr, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::handler::{EthPrecompiles, ExecuteCommitEvm, MainBuilder, MainContext, PrecompileProvider};
use revm::interpreter::interpreter_types::{InterpreterTypes, StackTr};
use revm::interpreter::{CallInput, Gas, InputsImpl, InstructionContext, InstructionResult, InterpreterResult, gas};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, U256};
use revm::state::AccountInfo;

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

/// The rows of the layouts a `PCS_OPEN` taking tables past WHIR's `2^28` words would know
/// ([`PcsOpen::large_tables`]): every size the reduction takes (`quotient::protocol::reduction_supported`).
pub const LARGE_LOG_ROWS: std::ops::RangeInclusive<usize> =
    quotient::protocol::MIN_LOG_ROWS..=quotient::protocol::MAX_REDUCTION_LOG_ROWS;

/// The id of the layout of `table` for a circuit of `2^log_rows` rows: `256 · table + log_rows`.
pub fn layout_id(table: TableId, log_rows: usize) -> u64 {
    assert!(LARGE_LOG_ROWS.contains(&log_rows), "no layout for 2^{log_rows} rows");
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

/// [`layout`] for a `PCS_OPEN` that also takes the larger tables, to [`LARGE_LOG_ROWS`].
pub fn layout_large(id: U256) -> Option<Layout> {
    let id = u64::try_from(id).ok()?;
    let log_rows = (id % 256) as usize;
    let table = match id / 256 {
        1 => witness_layout,
        2 => wiring_layout,
        3 => quotient_layout,
        _ => return None,
    };
    LARGE_LOG_ROWS.contains(&log_rows).then(|| table(log_rows))
}

/// The input of `PCS_OPEN` for `claims` on the table committed as `root`, under layout `id`.
pub fn pcs_open_input(root: &Hash, id: u64, claims: &[Claim]) -> Vec<u8> {
    let vars = layout_large(U256::from(id)).expect("a layout PCS_OPEN knows").vars;
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
/// prices. It parses an input only as far as its length, `3 + k (v + 1)` words for the layout it names: an input it
/// holds is well formed, being made by [`pcs_open_input`].
#[derive(Clone, Debug, Default)]
pub struct PcsOpen {
    attested: HashSet<Vec<u8>>,
    /// Gas a call costs.
    pub call_gas: u64,
    /// Gas a claim costs.
    pub claim_gas: u64,
    /// Whether it also takes the layouts past WHIR's `2^28` words ([`layout_large`]): the assumption a circuit
    /// above `2^22` rows, such as SLH-DSA's (`crates/slh_dsa`), needs. Off, it knows [`layout`]'s only.
    pub large_tables: bool,
}

impl PcsOpen {
    /// A `PCS_OPEN` that also takes the tables past WHIR's `2^28` words ([`PcsOpen::large_tables`]).
    pub fn large() -> Self {
        Self {
            large_tables: true,
            ..Self::default()
        }
    }

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
        (gas, Self::well_sized(input, self.large_tables) && self.attested.contains(input))
    }

    /// Whether `input` is `3 + k (v + 1)` words, `k ≥ 1` its third word and `v` the variables of the layout its
    /// second names.
    fn well_sized(input: &[u8], large_tables: bool) -> bool {
        let word = |i: usize| input.get(32 * i..32 * i + 32).map(U256::from_be_slice);
        let (Some(id), Some(k)) = (word(1), word(2)) else {
            return false;
        };
        let known = if large_tables { layout_large(id) } else { layout(id) };
        let (Some(layout), Ok(k)) = (known, u64::try_from(k)) else {
            return false;
        };
        let words = (layout.vars as u64 + 1)
            .checked_mul(k)
            .and_then(|claims| claims.checked_add(3));
        k >= 1 && words.and_then(|words| words.checked_mul(32)) == Some(input.len() as u64)
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

/// What a transaction did.
#[derive(Debug)]
pub struct Outcome {
    /// What it returned (a creation: the code it deployed), or `None` if it reverted or halted.
    pub output: Option<Vec<u8>>,
    /// The gas of its execution, its calls of `PCS_OPEN` included: the transaction's without its base cost and its
    /// calldata. A creation's includes its 32,000, its init code's 2 a word and its code's deposit, 200 a byte.
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

/// Who deploys contracts.
pub const DEPLOYER: Address = Address::with_last_byte(0xde);
/// Who calls them, unless said otherwise.
pub const CALLER: Address = Address::with_last_byte(0xca);

/// The accounts transactions run on: the senders' and the contracts deployed.
#[derive(Clone, Default)]
pub struct Chain {
    db: CacheDB<EmptyDB>,
}

impl Chain {
    /// The accounts, for an EVM of another kind.
    #[cfg(test)]
    pub(crate) fn db(&self) -> CacheDB<EmptyDB> {
        self.db.clone()
    }

    /// Run a transaction from `from`, sending `value` wei, in a block whose openings are `pcs_open`'s, and keep
    /// what it changes; and the address of the contract it created, if any. Each transaction starts cold
    /// (EIP-2929): its first `SLOAD` of a slot costs 2,100.
    pub(crate) fn run(
        &mut self,
        from: Address,
        to: TxKind,
        data: &[u8],
        value: U256,
        pcs_open: &PcsOpen,
    ) -> (Outcome, Option<Address>) {
        // Senders have funds for the value; gas is free.
        let nonce = self
            .db
            .cache
            .accounts
            .get(&from)
            .map_or(0, |account| account.info.nonce);
        let balance = U256::from(10u64.pow(18));
        self.db
            .insert_account_info(from, AccountInfo::from_balance(balance).with_nonce(nonce));
        // Cancun has no calldata floor, so the gas it reports separates into calldata and execution.
        let mut evm = Context::mainnet()
            .with_db(&mut self.db)
            .modify_cfg_chained(|cfg| cfg.spec = SpecId::CANCUN)
            .build_mainnet()
            .with_precompiles(Precompiles {
                eth: EthPrecompiles::default(),
                pcs_open,
                warm: false,
            });
        evm.instruction.insert_instruction(FIELD_MUL, field_mul);
        let tx = TxEnv::builder()
            .caller(from)
            .nonce(nonce)
            .kind(to)
            .value(value)
            .data(Bytes::copy_from_slice(data))
            .gas_limit(10_000_000)
            .build()
            .expect("a transaction");
        let result = evm.transact_commit(tx).expect("a valid transaction");
        let execution = result.gas_used() - transaction_gas(data, 0, 0);
        let (output, created) = match result {
            ExecutionResult::Success {
                output: Output::Call(output),
                ..
            } => (Some(output.to_vec()), None),
            ExecutionResult::Success {
                output: Output::Create(output, created),
                ..
            } => (Some(output.to_vec()), created),
            _ => (None, None),
        };
        (Outcome { output, execution }, created)
    }

    /// Deploy a contract by a transaction of `init_code` from [`DEPLOYER`]: its address, unless the creation
    /// failed, and the transaction's outcome.
    pub fn deploy(&mut self, init_code: &[u8]) -> (Option<Address>, Outcome) {
        let (outcome, created) = self.run(DEPLOYER, TxKind::Create, init_code, U256::ZERO, &PcsOpen::default());
        (created, outcome)
    }

    /// Send `calldata` and `value` wei from `from` to `to`, in a transaction of a block whose openings are
    /// `pcs_open`'s, and keep what it changes.
    pub fn transact(
        &mut self,
        from: Address,
        to: Address,
        calldata: &[u8],
        value: U256,
        pcs_open: &PcsOpen,
    ) -> Outcome {
        self.run(from, TxKind::Call(to), calldata, value, pcs_open).0
    }

    /// The same from [`CALLER`] with no value, leaving the chain as it was.
    pub fn call(&self, to: Address, calldata: &[u8], pcs_open: &PcsOpen) -> Outcome {
        self.clone().transact(CALLER, to, calldata, U256::ZERO, pcs_open)
    }

    /// The code of the account at `address`.
    pub fn code(&self, address: Address) -> Vec<u8> {
        let account = self.db.cache.accounts.get(&address);
        let code = account.and_then(|account| account.info.code.as_ref());
        code.map_or_else(Vec::new, |code| code.original_byte_slice().to_vec())
    }

    /// The word in storage slot `slot` of the account at `address`.
    pub fn storage(&self, address: Address, slot: U256) -> U256 {
        let account = self.db.cache.accounts.get(&address);
        account
            .and_then(|account| account.storage.get(&slot).copied())
            .unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every layout `PCS_OPEN` knows is a stack leanVM's WHIR commits, and the ids name distinct openings'
    /// prefixes (`quotient::opening::prefix`); ids outside the table name none.
    #[test]
    fn layouts_are_known_by_id() {
        let mut prefixes = HashSet::new();
        for log_rows in LOG_ROWS {
            for table in [TableId::Witness, TableId::Wiring, TableId::Quotient] {
                let layout = layout(U256::from(layout_id(table, log_rows))).expect("a layout");
                assert!((15..=28).contains(&layout.log_n) && layout.lanes() <= 64);
                assert!(
                    prefixes.insert(quotient::opening::prefix(&layout)),
                    "{table:?}, 2^{log_rows} rows"
                );
            }
        }
        for id in [0u64, 12, 256 + 12, 256 + 23, 4 * 256 + 22, 1 << 40] {
            assert_eq!(layout(U256::from(id)), None, "{id}");
        }
        assert_eq!(layout(U256::MAX), None);
    }

    /// An input attests only at its length, `3 + k (v + 1)` words: one word or byte more or fewer, `k` of 0 or
    /// one more claim than the words hold, an unknown layout, do not.
    #[test]
    fn inputs_of_another_length_do_not_attest() {
        let (root, id) = ([3; 32], layout_id(TableId::Wiring, 20));
        let vars = layout(U256::from(id)).expect("a layout").vars;
        let claims = [Claim {
            point: vec![F192::ONE; vars],
            value: F192::ZERO,
        }];
        let input = pcs_open_input(&root, id, &claims);
        let mut block = PcsOpen::default();
        block.register(&root, id, &claims);
        assert!(block.run(&input).1);
        for len in [
            0,
            31,
            64,
            96,
            input.len() - 32,
            input.len() - 1,
            input.len() + 1,
            input.len() + 32,
        ] {
            let mut other = input.clone();
            other.resize(len, 0);
            assert!(!PcsOpen::well_sized(&other, false), "{len}");
            assert!(!block.run(&other).1, "{len}");
        }
        for (at, byte) in [(95, 0), (95, 2), (62, 9), (40, 1)] {
            let mut other = input.clone();
            other[at] = byte;
            assert!(!PcsOpen::well_sized(&other, false), "{at} {byte}");
        }
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
