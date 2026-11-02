// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/quotient.rs; new here: the calls of `PCS_OPEN`, the selector, the index root in storage, its
// deployment and `setIndexRoot`. MIT OR Apache-2.0; see NOTICE.md.
//! The membership verifier (`quotient::protocol::reduce`) as a contract, its ABI, and its deployment.
//!
//! The contract ([`contract`]) has `PCS_OPEN` ([`crate::machine`]) check the four claims a proof leaves, in three
//! calls ([`openings`]), and returns the word 1; without the calls ([`claims_contract`]), it returns the commitments'
//! four scalars, three claims as a point then a value, and the value of the claim at the fixed point. Its code
//! depends on the circuit's size alone: the circuit's commitment (the index root) is in storage, where it can be
//! changed (the README's "Forward compatibility").
//!
//! # ABI
//!
//! **`verify(bytes32 y, bytes32 root, bytes proof)`**, selector [`VERIFY`] (`0xde12c640`), its arguments
//! **packed**, not ABI-encoded: calldata is exactly 252 bytes,
//!
//! | bytes      | what                                                                                      |
//! |------------|-------------------------------------------------------------------------------------------|
//! | `0..4`     | `0xde12c640`                                                                              |
//! | `4..36`    | `y`                                                                                       |
//! | `36..68`   | `root`                                                                                    |
//! | `68..100`  | the witness table's commitment: its two 16-byte scalars, each big-endian, the first first |
//! | `100..132` | the quotient table's commitment, likewise                                                 |
//! | `132..252` | the proof's five scalars, 24 bytes each, big-endian                                       |
//!
//! `proof` is bytes `68..252`, 184 bytes, as [`calldata`] writes them. The contract reverts on calldata of another
//! length or selector, on value, and on a proof the verifier rejects or whose claims `PCS_OPEN` does not attest
//! (each call must succeed and return exactly the word 1); otherwise it returns [`VERIFIED`], the word 1, as
//! `abi.encode(true)`, which no account without code returns. It writes nothing, so a `STATICCALL` will do. A
//! Solidity caller holding `proof` as `bytes calldata` (184 bytes) writes
//!
//! ```solidity
//! (bool ok, bytes memory ret) = verifier.staticcall(abi.encodePacked(bytes4(0xde12c640), y, root, proof));
//! require(ok && ret.length == 32 && abi.decode(ret, (bool)));
//! ```
//!
//! Declaring `verify(bytes32,bytes32,bytes) returns (bool)` in an interface and calling it would ABI-encode `proof`
//! (with an offset, a length and padding: 324 bytes of calldata), and revert.
//!
//! **`setIndexRoot(bytes32 indexRoot)`**, selector [`SET_INDEX_ROOT`] (`0xcdaf736c`), ABI-encoded (36 bytes): from
//! the owner, with no value, it stores `indexRoot` in slot 0 and returns nothing; otherwise it reverts. The owner is
//! fixed at deployment, and can make the contract accept proofs for any circuit: an owner of 0 fixes the root for
//! good (no one signs for the zero address). The README's trustless upgrade, which anyone could call to move the
//! root to the same circuit committed for another version of `PCS_OPEN`, proving it by two openings that agree at a
//! Fiat-Shamir point (Schwartz-Zippel), is left for when `PCS_OPEN` has versions.
//!
//! **Deployment**: `constructor(bytes32 indexRoot, address owner)`. The init code ([`init_code`]) is the creation
//! code, then the two arguments ABI-encoded (64 bytes); it stores `indexRoot`, the Merkle root of the circuit's
//! index table as its 32 bytes, in slot 0, writes `owner` into the code, and reverts on value or on arguments of
//! another length.

use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use quotient::opening::Claim;
use quotient::protocol::{Claims, Reduced, label, reduce, sum_point};
use quotient::statement::Statement;
use quotient::transcript::{Proof, TranscriptError, scalars_root};
use revm::primitives::{Address, U256};

use crate::codegen::{COMMITMENT, Ending, Entry, Word, compile, creation_code};
pub use crate::codegen::{Contract, SET_INDEX_ROOT, VERIFY};
use crate::contract::Recorder;
use crate::machine::{TableId, element_word, layout_id, root_word};
use crate::record::{Graph, Sym, record};

/// What the contract returns on a proof it accepts: the word 1, `abi.encode(true)`.
pub const VERIFIED: [u8; 32] = {
    let mut word = [0; 32];
    word[31] = 1;
    word
};

/// The contract verifying proofs against the circuit of `2^log_rows` rows whose commitment the deployment stores
/// ([`init_code`]): it reverts unless `PCS_OPEN` attests the claims a proof leaves, in the three calls of
/// [`openings`] (one per commitment: the witness table's claim, the wiring table's against the stored root, and
/// the quotient table's two together), and returns [`VERIFIED`].
pub fn contract(log_rows: usize) -> Contract {
    build(log_rows, &entry(true, None), true)
}

/// The same verifier, returning the commitments and the claims ([`decode`]) instead of calling `PCS_OPEN`.
pub fn claims_contract(log_rows: usize) -> Contract {
    build(log_rows, &entry(true, None), false)
}

/// The init code deploying `contract` (either of the two above) for the circuit committed as `index_root`, owned
/// by `owner`: its creation code, then the constructor's two arguments.
pub fn init_code(contract: &Contract, index_root: &Hash, owner: Address) -> Vec<u8> {
    assert!(contract.owner_at.is_some(), "a contract reading its root from storage");
    [&creation_code(contract)[..], index_root, owner.into_word().as_slice()].concat()
}

/// How the contract is entered: with the selector or not, and with the circuit's commitment in storage or else
/// in the code (`index_root`).
fn entry(selector: bool, index_root: Option<&Hash>) -> Entry {
    let some_root = [0xa5; 32];
    let zero = Statement {
        y: [0; 32],
        root: [0; 32],
    };
    let label = label(&some_root, &zero);
    assert!(
        label.len() == 112 && label[16..48] == some_root,
        "the label is a name, the root and the statement"
    );
    Entry {
        selector,
        name: label[..16].try_into().expect("a 16-byte name"),
        index_root: index_root.copied(),
    }
}

fn build(log_rows: usize, entry: &Entry, pcs_open: bool) -> Contract {
    let Recorded {
        graph,
        outputs,
        ending,
        inputs,
    } = recorded(log_rows, entry, pcs_open);
    compile(&graph, &outputs, &ending, entry, inputs)
}

/// What a contract is compiled from: the graph the recorder leaves, the words the contract writes (the calls'
/// inputs, or the claims it returns), how it ends, and how many scalars of the proof it reads.
pub(crate) struct Recorded {
    pub(crate) graph: Graph,
    pub(crate) outputs: Vec<Word>,
    pub(crate) ending: Ending,
    pub(crate) inputs: usize,
}

/// What [`contract`] is compiled from (`formal/Implementation` is about this graph).
pub(crate) fn deployed(log_rows: usize) -> Recorded {
    recorded(log_rows, &entry(true, None), true)
}

fn recorded(log_rows: usize, entry: &Entry, pcs_open: bool) -> Recorded {
    let ((reduced, read), graph) = record(|| {
        let mut recorder = Recorder::new();
        let reduced = reduce(&mut recorder, log_rows).unwrap_or_else(|_| unreachable!("a recorder rejects nothing"));
        (reduced, recorder.read)
    });
    let Reduced {
        roots,
        witness,
        wiring,
        quotient,
        sum,
    } = reduced;
    let node = |sym: &Sym| Word::Node(sym.0);
    let claim = |(point, value): &(Vec<Sym>, Sym)| point.iter().chain([value]).map(node).collect::<Vec<_>>();
    let (outputs, ending) = if pcs_open {
        let number = |n: u64| Word::Const(U256::from(n).to_be_bytes());
        let header =
            |root: Word, table: TableId, claims: u64| vec![root, number(layout_id(table, log_rows)), number(claims)];
        let index_root = entry
            .index_root
            .map_or(Word::StoredRoot, |root| Word::Const(root_word(&root)));
        let calls = [
            [header(Word::Calldata(COMMITMENT), TableId::Witness, 1), claim(&witness)].concat(),
            [header(index_root, TableId::Wiring, 1), claim(&wiring)].concat(),
            [
                header(Word::Calldata(COMMITMENT + 32), TableId::Quotient, 2),
                claim(&quotient),
                sum_point(log_rows)
                    .into_iter()
                    .map(|x| Word::Const(element_word(x)))
                    .collect(),
                vec![node(&sum)],
            ]
            .concat(),
        ];
        (calls.concat(), Ending::PcsOpen(calls.iter().map(Vec::len).collect()))
    } else {
        let mut outputs: Vec<Word> = roots.iter().flatten().map(node).collect();
        for pair in [&witness, &wiring, &quotient] {
            outputs.extend(claim(pair));
        }
        outputs.push(node(&sum));
        (outputs, Ending::Return)
    };
    Recorded {
        graph,
        outputs,
        ending,
        inputs: read as usize,
    }
}

/// The calls of `PCS_OPEN` that [`contract`] makes, as a root, a layout id and the claims opened together: those of
/// the commitments and the claims a proof leaves ([`quotient::protocol::verify`]), as
/// [`quotient::protocol::verify_openings`] opens them.
pub fn openings(
    index_root: &Hash,
    roots: &[Hash; 2],
    claims: &Claims,
    log_rows: usize,
) -> [(Hash, u64, Vec<Claim>); 3] {
    [
        (
            roots[0],
            layout_id(TableId::Witness, log_rows),
            vec![claims.witness.clone()],
        ),
        (
            *index_root,
            layout_id(TableId::Wiring, log_rows),
            vec![claims.wiring.clone()],
        ),
        (
            roots[1],
            layout_id(TableId::Quotient, log_rows),
            vec![claims.quotient.clone(), claims.sum.clone()],
        ),
    ]
}

/// The calldata of `setIndexRoot(index_root)`.
pub fn set_index_root_calldata(index_root: &Hash) -> Vec<u8> {
    [&SET_INDEX_ROOT[..], index_root].concat()
}

/// A statement and its proof as calldata verifying them: the selector, then the arguments packed. A commitment's
/// two scalars are 128-bit, and calldata has room for no more: a proof with a larger one, which the Rust verifier
/// rejects, has no calldata (`NotARoot`). A proof of another length has calldata of another length, which the
/// contract rejects as the Rust verifier does.
pub fn calldata(statement: &Statement, proof: &Proof) -> Result<Vec<u8>, TranscriptError> {
    let mut data = [&VERIFY[..], &statement.y, &statement.root].concat();
    for (i, scalar) in proof.stream.iter().enumerate() {
        let limbs = if i < 4 {
            if scalar.c2 != 0 {
                return Err(TranscriptError::NotARoot);
            }
            vec![scalar.c1, scalar.c0]
        } else {
            vec![scalar.c2, scalar.c1, scalar.c0]
        };
        limbs.iter().for_each(|limb| data.extend(limb.to_be_bytes()));
    }
    Ok(data)
}

/// What [`claims_contract`] returned: the two commitments and the four claims.
pub fn decode(output: &[u8], log_rows: usize) -> Option<([Hash; 2], Claims)> {
    let words: Vec<F192> = output
        .as_chunks::<32>()
        .0
        .iter()
        .map(|word| {
            let limb = |i: usize| u64::from_be_bytes(word[24 - 8 * i..32 - 8 * i].try_into().unwrap());
            (limb(3) == 0).then(|| F192::new(limb(0), limb(1), limb(2)))
        })
        .collect::<Option<_>>()?;
    let m = log_rows + 2;
    let mut rest = &words[..];
    let mut take = |n: usize| {
        let (head, tail) = rest.split_at_checked(n)?;
        rest = tail;
        Some(head)
    };
    let roots = take(4)?;
    let mut claim = |vars: usize| {
        let (value, point) = take(vars + 1)?.split_last()?;
        Some(Claim {
            point: point.to_vec(),
            value: *value,
        })
    };
    let (witness, wiring, quotient) = (claim(m + 1)?, claim(m)?, claim(m + 6)?);
    let sum = Claim {
        point: sum_point(log_rows),
        value: *take(1)?.first()?,
    };
    rest.is_empty().then_some(())?;
    Some((
        [
            scalars_root(&[roots[0], roots[1]]).ok()?,
            scalars_root(&[roots[2], roots[3]]).ok()?,
        ],
        Claims {
            witness,
            wiring,
            quotient,
            sum,
        },
    ))
}

#[cfg(test)]
mod tests {
    use std::sync::LazyLock;

    use super::*;
    use crate::codegen::INDEX_ROOT_SLOT;
    use crate::machine::{CALLER, Chain, DEPLOYER, PcsOpen, transaction_gas};
    use primitives::test_rng::Rng;
    use quotient::circuit::{LOG_ROWS, membership, membership_inputs};
    use quotient::opening::commit;
    use quotient::protocol::{Index, prove_with_seed, verify};
    use quotient::statement::{DEPTH, Secret};
    use revm::primitives::TxKind;

    /// Who may change the circuit's commitment.
    const OWNER: Address = Address::with_last_byte(0x0e);

    fn proof(rng: &mut Rng) -> (Hash, Statement, Proof) {
        let mut bytes = || std::array::from_fn(|_| rng.next_u64() as u8);
        let secret = Secret {
            x: bytes(),
            siblings: std::array::from_fn::<_, DEPTH, _>(|_| bytes()),
            directions: 0x5A3C_96F0,
        };
        let statement = secret.statement();
        let circuit = membership();
        let cells = circuit.cells(&membership_inputs(&secret));
        let index = Index::new(&circuit);
        let index_root = commit(&index.table).root;
        // The proof's seed from the test generator, so that the tests repeat: `prove` draws a fresh one.
        let seed = std::array::from_fn(|_| rng.next_u64() as u8);
        let proved = prove_with_seed(&circuit, &index, &index_root, &statement, &cells, &seed);
        (index_root, statement, proved.proof)
    }

    /// The tests' proof, made once for all of them: a full-size proof takes some 10 GB.
    static HONEST: LazyLock<(Hash, Statement, Proof)> = LazyLock::new(|| proof(&mut Rng::new(0xE8)));

    /// A chain holding `contract`, deployed for the circuit committed as `index_root` and owned by [`OWNER`].
    fn deployed(contract: &Contract, index_root: &Hash) -> (Chain, Address) {
        let mut chain = Chain::default();
        let (address, _) = chain.deploy(&init_code(contract, index_root, OWNER));
        (chain, address.expect("a deployment"))
    }

    /// A block whose openings are of the claims the Rust verifier leaves, if it leaves any.
    fn block_for(index_root: &Hash, statement: &Statement, proof: &Proof) -> PcsOpen {
        let mut block = PcsOpen::default();
        if let Ok((roots, claims)) = verify(index_root, statement, proof, LOG_ROWS) {
            for (root, id, claims) in openings(index_root, &roots, &claims, LOG_ROWS) {
                block.register(&root, id, &claims);
            }
        }
        block
    }

    /// Change scalar `at` of a proof (a commitment's within its 128 bits), or change it back.
    fn tamper(proof: &mut Proof, at: usize) {
        proof.stream[at] += if at < 4 { F192::new(1, 2, 0) } else { F192::new(1, 2, 3) };
    }

    /// The contract without its calls and the Rust verifier leave the same commitments and claims, on an honest
    /// proof and on tampered ones, and the contract reverts on calldata of another length.
    #[test]
    fn contract_is_the_verifier() {
        let (index_root, statement, mut proof) = HONEST.clone();
        let (chain, address) = deployed(&claims_contract(LOG_ROWS), &index_root);
        let returned = |statement: &Statement, proof: &Proof| {
            let output = chain
                .call(address, &calldata(statement, proof).unwrap(), &PcsOpen::default())
                .output;
            output.as_deref().and_then(|output| decode(output, LOG_ROWS))
        };
        let expected = verify(&index_root, &statement, &proof, LOG_ROWS).expect("a reduction");
        assert_eq!(returned(&statement, &proof), Some(expected));

        for at in 0..proof.stream.len() {
            tamper(&mut proof, at);
            assert_eq!(
                returned(&statement, &proof),
                verify(&index_root, &statement, &proof, LOG_ROWS).ok(),
                "{at}"
            );
            tamper(&mut proof, at);
        }
        let mut other = statement;
        other.y[5] ^= 4;
        assert_eq!(
            returned(&other, &proof),
            verify(&index_root, &other, &proof, LOG_ROWS).ok()
        );

        let mut long = calldata(&statement, &proof).unwrap();
        long.push(0);
        let none = PcsOpen::default();
        assert!(chain.call(address, &long, &none).output.is_none());
        assert!(chain.call(address, &long[..long.len() - 2], &none).output.is_none());
    }

    /// The contract succeeds, returning the word 1, exactly when the block holds an opening of each commitment's
    /// claims, all together, under its layout: those the Rust verifier leaves, on the honest proof and on
    /// tampered ones, which leave other claims than the honest proof's.
    #[test]
    fn contract_has_pcs_open_check_the_claims() {
        let (index_root, statement, proof) = HONEST.clone();
        let (chain, address) = deployed(&contract(LOG_ROWS), &index_root);
        let succeeds = |statement: &Statement, proof: &Proof, block: &PcsOpen| {
            let output = chain.call(address, &calldata(statement, proof).unwrap(), block).output;
            assert!(output.as_ref().is_none_or(|output| *output == VERIFIED));
            output.is_some()
        };
        let honest = block_for(&index_root, &statement, &proof);
        assert!(succeeds(&statement, &proof, &honest));

        // Openings missing, or of the claims otherwise than the contract asks.
        let (roots, claims) = verify(&index_root, &statement, &proof, LOG_ROWS).expect("a reduction");
        let calls = openings(&index_root, &roots, &claims, LOG_ROWS);
        let block_of = |calls: &[(Hash, u64, Vec<Claim>)]| {
            let mut block = PcsOpen::default();
            calls
                .iter()
                .for_each(|(root, id, claims)| block.register(root, *id, claims));
            block
        };
        assert!(!succeeds(&statement, &proof, &PcsOpen::default()));
        for missing in 0..3 {
            let mut some = calls.to_vec();
            some.remove(missing);
            assert!(!succeeds(&statement, &proof, &block_of(&some)), "{missing}");
        }
        let (root, id, pair) = calls[2].clone();
        let apart = [(root, id, vec![pair[0].clone()]), (root, id, vec![pair[1].clone()])];
        let swapped = [(root, id, vec![pair[1].clone(), pair[0].clone()])];
        for quotient in [&apart[..], &swapped[..]] {
            let block = block_of(&[&calls[..2], quotient].concat());
            assert!(!succeeds(&statement, &proof, &block));
        }
        // The wiring claim under another layout of as many variables: the witness table's for half the rows.
        let (root, _, wiring) = calls[1].clone();
        let elsewhere = (root, layout_id(TableId::Witness, LOG_ROWS - 1), wiring);
        let block = block_of(&[calls[0].clone(), elsewhere, calls[2].clone()]);
        assert!(!succeeds(&statement, &proof, &block));

        // A tampered proof or statement fails against the honest claims, and agrees with the Rust verifier against
        // its own.
        let mut tampered = proof.clone();
        for at in 0..proof.stream.len() {
            tamper(&mut tampered, at);
            assert!(!succeeds(&statement, &tampered, &honest), "{at}");
            let own = block_for(&index_root, &statement, &tampered);
            let verifies = verify(&index_root, &statement, &tampered, LOG_ROWS).is_ok();
            assert_eq!(succeeds(&statement, &tampered, &own), verifies, "{at}");
            tamper(&mut tampered, at);
        }
        let mut other = statement;
        other.root[17] ^= 0x20;
        assert!(!succeeds(&other, &proof, &honest));
        assert!(succeeds(&other, &proof, &block_for(&index_root, &other, &proof)));

        let mut long = calldata(&statement, &proof).unwrap();
        long.push(0);
        assert!(chain.call(address, &long, &honest).output.is_none());
    }

    /// A call of the verifier is the selector [`VERIFY`] then the arguments packed, with no value: where it
    /// succeeds, another selector, the arguments without one or ABI-encoded, and value revert.
    #[test]
    fn contract_checks_its_selector() {
        let (index_root, statement, proof) = HONEST.clone();
        let (mut chain, address) = deployed(&contract(LOG_ROWS), &index_root);
        let honest = block_for(&index_root, &statement, &proof);
        let data = calldata(&statement, &proof).unwrap();
        assert_eq!(data[..4], [0xde, 0x12, 0xc6, 0x40]);
        assert_eq!(data.len(), 252);
        let succeeds = |data: &[u8]| {
            let output = chain.call(address, data, &honest).output;
            assert!(output.as_ref().is_none_or(|output| *output == VERIFIED));
            output.is_some()
        };
        assert!(succeeds(&data));

        for byte in 0..4 {
            for bit in [0x01, 0x80] {
                let mut other = data.clone();
                other[byte] ^= bit;
                assert!(!succeeds(&other), "{byte} {bit}");
            }
        }
        let mut other = data.clone();
        other[..4].copy_from_slice(&SET_INDEX_ROOT);
        assert!(!succeeds(&other));
        // The arguments alone (the calldata of the contract without a selector), and nothing at all.
        assert!(!succeeds(&data[4..]));
        assert!(!succeeds(&[]));
        // `proof` ABI-encoded, as a call through a Solidity interface would: its offset, its length, padding.
        let word = |n: u64| U256::from(n).to_be_bytes::<32>();
        let encoded = [&data[..68], &word(96), &word(184), &data[68..], &[0; 8]].concat();
        assert_eq!(encoded.len(), 324);
        assert!(!succeeds(&encoded));

        // Value is refused; the same transaction without succeeds, and changes nothing.
        assert!(
            chain
                .transact(CALLER, address, &data, U256::from(1), &honest)
                .output
                .is_none()
        );
        let slot = U256::from(INDEX_ROOT_SLOT);
        assert_eq!(
            chain.transact(CALLER, address, &data, U256::ZERO, &honest).output,
            Some(VERIFIED.to_vec())
        );
        assert_eq!(chain.storage(address, slot).to_be_bytes::<32>(), index_root);
    }

    /// The circuit's commitment is the root in storage, for the transcript and for the wiring table's opening
    /// alike: the one the deployment stores, then the one `setIndexRoot` stores, from the owner only.
    #[test]
    fn contract_reads_the_index_root_from_storage() {
        let (index_root, statement, proof) = HONEST.clone();
        let contract = contract(LOG_ROWS);
        let (mut chain, address) = deployed(&contract, &index_root);
        let stored = |chain: &Chain| chain.storage(address, U256::from(INDEX_ROOT_SLOT)).to_be_bytes::<32>();
        assert_eq!(stored(&chain), index_root);
        // The code deployed is the contract's, its owner written in.
        let mut code = contract.code.clone();
        let at = contract.owner_at.expect("an owner");
        code[at..at + 32].copy_from_slice(OWNER.into_word().as_slice());
        assert_eq!(chain.code(address), code);

        // Against another root, the proof leaves other claims, which the contract asks for when it holds that
        // root: the claims contract returns those the Rust verifier leaves, and the contract has `PCS_OPEN` check
        // them, the wiring table's against that root.
        let data = calldata(&statement, &proof).unwrap();
        let mut other_root = index_root;
        other_root[9] ^= 1;
        let expected = verify(&other_root, &statement, &proof, LOG_ROWS).expect("a reduction");
        let (returning, at) = deployed(&claims_contract(LOG_ROWS), &other_root);
        let output = returning.call(at, &data, &PcsOpen::default()).output;
        assert_eq!(output.and_then(|output| decode(&output, LOG_ROWS)), Some(expected));
        let (honest, other) = (
            block_for(&index_root, &statement, &proof),
            block_for(&other_root, &statement, &proof),
        );
        let succeeds = |chain: &Chain, block: &PcsOpen| chain.call(address, &data, block).output.is_some();
        assert!(succeeds(&chain, &honest));
        assert!(!succeeds(&chain, &other));
        let (elsewhere, at) = deployed(&contract, &other_root);
        assert!(elsewhere.call(at, &data, &other).output.is_some());
        assert!(elsewhere.call(at, &data, &honest).output.is_none());

        // `setIndexRoot` reverts, leaving the root, from anyone but the owner, with value, or on calldata of
        // another length or selector.
        let none = PcsOpen::default();
        let set = set_index_root_calldata(&other_root);
        let mut wrong = set.clone();
        wrong[3] ^= 1;
        for (from, data, value) in [
            (CALLER, &set[..], 0u64),
            (DEPLOYER, &set[..], 0),
            (OWNER, &set[..], 1),
            (OWNER, &set[..35], 0),
            (OWNER, &[&set[..], &[0]].concat()[..], 0),
            (OWNER, &wrong[..], 0),
            (OWNER, &data[..], 0),
        ] {
            let outcome = chain.transact(from, address, data, U256::from(value), &none);
            assert!(outcome.output.is_none(), "{from} {}", data.len());
            assert_eq!(stored(&chain), index_root);
        }
        // From the owner, it moves the contract to the other circuit, and back.
        let outcome = chain.transact(OWNER, address, &set, U256::ZERO, &none);
        assert_eq!(outcome.output, Some(vec![]));
        assert_eq!(stored(&chain), other_root);
        assert!(!succeeds(&chain, &honest));
        assert!(succeeds(&chain, &other));
        let back = set_index_root_calldata(&index_root);
        assert_eq!(
            chain.transact(OWNER, address, &back, U256::ZERO, &none).output,
            Some(vec![])
        );
        assert_eq!(stored(&chain), index_root);
        assert!(succeeds(&chain, &honest));
    }

    /// The init code deploys the contract with exactly its two arguments and no value, and reverts otherwise.
    #[test]
    fn deployment_takes_its_arguments() {
        let contract = contract(LOG_ROWS);
        let index_root = [0xa7; 32];
        let init = init_code(&contract, &index_root, OWNER);
        let mut chain = Chain::default();
        let short = &init[..init.len() - 1];
        let long = [&init[..], &[0]].concat();
        let no_owner = &init[..init.len() - 32];
        for init in [short, &long[..], no_owner, &init[..init.len() - 64]] {
            assert_eq!(chain.deploy(init).0, None, "{}", init.len());
        }
        let paid = chain.run(DEPLOYER, TxKind::Create, &init, U256::from(1), &PcsOpen::default());
        assert_eq!(paid.1, None);

        let (address, outcome) = chain.deploy(&init);
        let address = address.expect("a deployment");
        assert_eq!(outcome.output.as_deref(), Some(&chain.code(address)[..]));
        assert_eq!(
            chain.storage(address, U256::from(INDEX_ROOT_SLOT)).to_be_bytes::<32>(),
            index_root
        );
        assert!(contract.code.len() <= 24_576, "EIP-170");
    }

    /// `n` with a comma every three digits.
    fn grouped(n: u64) -> String {
        let digits = n.to_string();
        let mut out = String::new();
        for (i, digit) in digits.chars().enumerate() {
            if i > 0 && (digits.len() - i).is_multiple_of(3) {
                out.push(',');
            }
            out.push(digit);
        }
        out
    }

    /// What a call costs: `cargo test --release -p evm -- --ignored --nocapture gas_report`.
    #[test]
    #[ignore]
    fn gas_report() {
        let (index_root, statement, proof) = proof(&mut Rng::new(0x6A6));
        let data = calldata(&statement, &proof).unwrap();
        let mut block = block_for(&index_root, &statement, &proof);
        let none = PcsOpen::default();
        let deploy = |contract: &Contract| {
            let init = match contract.owner_at {
                Some(_) => init_code(contract, &index_root, OWNER),
                None => creation_code(contract),
            };
            let mut chain = Chain::default();
            let (address, outcome) = chain.deploy(&init);
            (chain, address.expect("a deployment"), init, outcome)
        };
        let tx = |calldata: &[u8], execution: u64, floor: u64| transaction_gas(calldata, execution, floor);
        let with_base = |gas: u64| format!("{} ({})", grouped(gas), grouped(gas - 21_000));

        let contract = contract(LOG_ROWS);
        let zeros = data.iter().filter(|&&byte| byte == 0).count();
        println!(
            "calldata   : {} bytes, {zeros} of them zero: selector 4, statement 64, commitments 64, proof scalars 120",
            data.len()
        );
        println!("FIELD_MUL  : {}", contract.field_muls);
        println!("KECCAK256  : {}", contract.hashes);
        println!("PCS_OPEN   : 3 calls for the 4 claims: witness 1, wiring 1, quotient 2 together");
        println!("SLOAD      : 1, cold (2,100 gas): the index root, for the transcript's seed and the wiring call");
        println!(
            "code       : {} bytes (EIP-170 limit 24,576), the same for every circuit of 2^{LOG_ROWS} rows",
            grouped(contract.code.len() as u64)
        );
        println!("memory     : {} words", contract.memory_words);

        // The contract built up, one thing at a time.
        let honest = block.clone();
        let in_code = |selector| entry(selector, Some(&index_root));
        let steps = [
            (
                "the verifier, returning the claims (root in code, no selector)",
                build(LOG_ROWS, &in_code(false), false),
                &data[4..],
                &none,
            ),
            (
                "+ PCS_OPEN: 3 calls at 0 gas, each reply checked; word 1 out",
                build(LOG_ROWS, &in_code(false), true),
                &data[4..],
                &honest,
            ),
            (
                "+ selector, and no value",
                build(LOG_ROWS, &in_code(true), true),
                &data[..],
                &honest,
            ),
            (
                "+ index root from storage: cold SLOAD, halves reversed",
                contract,
                &data[..],
                &honest,
            ),
        ];
        println!();
        println!(
            "The contract built up, PCS_OPEN at 0 gas; transaction gas without its 21,000 base, and the zero bytes"
        );
        println!("of calldata from which EIP-7976's floor (64 a byte) binds:");
        println!(
            "{:<58} {:>6} {:>9} {:>7} {:>10} {:>7} {:>10} {:>7} {:>6}",
            "", "bytes", "execution", "added", "EIP-7623", "added", "EIP-7976", "added", "floor"
        );
        let mut last: Option<(u64, u64, u64)> = None;
        for (name, contract, data, block) in &steps {
            let (chain, address, _, _) = deploy(contract);
            let outcome = chain.call(address, data, block);
            assert!(outcome.output.is_some(), "{name}");
            let gas = (
                outcome.execution,
                tx(data, outcome.execution, 40) - 21_000,
                tx(data, outcome.execution, 64) - 21_000,
            );
            let added =
                |now: u64, then: Option<u64>| then.map_or(String::new(), |then| format!("+{}", grouped(now - then)));
            // The floor, 64 n, passes 16 n - 12 z + execution when z > (execution - 48 n) / 12.
            let n = data.len() as u64;
            let floor = outcome.execution.checked_sub(48 * n).map_or(0, |over| over / 12 + 1);
            println!(
                "{name:<58} {:>6} {:>9} {:>7} {:>10} {:>7} {:>10} {:>7} {:>6}",
                n,
                grouped(gas.0),
                added(gas.0, last.map(|l| l.0)),
                grouped(gas.1),
                added(gas.1, last.map(|l| l.1)),
                grouped(gas.2),
                added(gas.2, last.map(|l| l.2)),
                floor,
            );
            last = Some(gas);
        }

        let [.., (_, contract, _, _)] = &steps;
        let (chain, address, init, deployment) = deploy(contract);
        let at_zero = chain.call(address, &data, &block);
        assert_eq!(at_zero.output, Some(VERIFIED.to_vec()));
        println!();
        println!("PCS_OPEN at 0 gas a call and c a claim; transaction gas, and (without its 21,000 base):");
        println!(
            "{:>8} {:>10} {:>24} {:>24}",
            "c", "execution", "EIP-7623 (40/byte)", "EIP-7976 (64/byte)"
        );
        for claim_gas in [0, 2_000, 5_000, 20_000] {
            block.claim_gas = claim_gas;
            let outcome = chain.call(address, &data, &block);
            assert_eq!(outcome.output, Some(VERIFIED.to_vec()));
            assert_eq!(outcome.execution, at_zero.execution + 4 * claim_gas);
            println!(
                "{:>8} {:>10} {:>24} {:>24}",
                grouped(claim_gas),
                grouped(outcome.execution),
                with_base(tx(&data, outcome.execution, 40)),
                with_base(tx(&data, outcome.execution, 64)),
            );
        }

        // A creation's execution holds its 32,000, its init code's 2 a word, the constructor's and the deposit.
        let size = contract.code.len() as u64;
        let words = (init.len() as u64).div_ceil(32);
        let constructor = deployment.execution - 32_000 - 2 * words - 200 * size;
        let calldata = tx(&init, 0, 0) - 21_000;
        let zeros = init.iter().filter(|&&byte| byte == 0).count();
        println!();
        println!(
            "Deployment: init code {} bytes ({} creation code, {} code, 64 of arguments; {zeros} zero)",
            grouped(init.len() as u64),
            init.len() - contract.code.len() - 64,
            grouped(size)
        );
        println!(
            "  21,000 + 32,000 creation + {} calldata + {} init code ({words} words) + {} constructor + {} code deposit \
             ({} bytes) = {}",
            grouped(calldata),
            2 * words,
            grouped(constructor),
            grouped(200 * size),
            grouped(size),
            grouped(tx(&init, deployment.execution, 0)),
        );
        println!(
            "  EIP-7623: {}; EIP-7976: {}",
            with_base(tx(&init, deployment.execution, 40)),
            with_base(tx(&init, deployment.execution, 64))
        );

        let mut chain = chain;
        let mut other_root = index_root;
        other_root[0] ^= 1;
        let set = set_index_root_calldata(&other_root);
        let upgrade = chain.transact(OWNER, address, &set, U256::ZERO, &none);
        assert_eq!(upgrade.output, Some(vec![]));
        println!(
            "setIndexRoot by the owner: execution {}, transaction {} under either floor",
            grouped(upgrade.execution),
            grouped(tx(&set, upgrade.execution, 64)),
        );
    }
}
