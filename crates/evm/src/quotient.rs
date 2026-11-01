// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/quotient.rs; the calls of `PCS_OPEN` are new here. MIT OR Apache-2.0; see NOTICE.md.
//! The membership verifier (`quotient::protocol::reduce`) as a contract, and its calldata and return value.
//!
//! Calldata is `y`, `root`, the two commitments (the witness table's, then the quotient table's), each as its two
//! 16-byte scalars, then the proof's five scalars, 24 bytes each. The contract ([`contract`]) has `PCS_OPEN`
//! ([`crate::machine`]) check the four claims a proof leaves, in three calls ([`openings`]), and returns nothing;
//! without the calls ([`claims_contract`]), it returns the commitments' four scalars, three claims as a point then
//! a value, and the value of the claim at the fixed point.

use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use quotient::opening::Claim;
use quotient::protocol::{Claims, Reduced, label, reduce, sum_point};
use quotient::statement::Statement;
use quotient::transcript::{Proof, scalars_root};
use revm::primitives::U256;

use crate::codegen::{COMMITMENT, Contract, Ending, SCALAR_BYTES, Word, compile};
use crate::contract::Recorder;
use crate::machine::{TableId, element_word, layout_id, root_word};
use crate::record::{Sym, record};

/// Where calldata holds the proof's scalars: after the statement and the two commitments.
const SCALARS: usize = COMMITMENT + 64;

/// The contract verifying proofs against the circuit of `2^log_rows` rows committed as `index_root`: it reverts
/// unless `PCS_OPEN` attests the claims a proof leaves, in the three calls of [`openings`] (one per commitment: the
/// witness table's claim, the wiring table's against `index_root`, which the code holds, and the quotient table's
/// two together), and returns nothing.
pub fn contract(index_root: &Hash, log_rows: usize) -> Contract {
    build(index_root, log_rows, true)
}

/// The same verifier, returning the commitments and the claims ([`decode`]) instead of calling `PCS_OPEN`.
pub fn claims_contract(index_root: &Hash, log_rows: usize) -> Contract {
    build(index_root, log_rows, false)
}

fn build(index_root: &Hash, log_rows: usize, pcs_open: bool) -> Contract {
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
        let calls = [
            [header(Word::Calldata(COMMITMENT), TableId::Witness, 1), claim(&witness)].concat(),
            [
                header(Word::Const(root_word(index_root)), TableId::Wiring, 1),
                claim(&wiring),
            ]
            .concat(),
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
    let label = label(
        index_root,
        &Statement {
            y: [0; 32],
            root: [0; 32],
        },
    );
    let prefix = label[..label.len() - 64].try_into().expect("a 48-byte prefix");
    compile(
        &graph,
        &outputs,
        &ending,
        prefix,
        SCALARS,
        SCALARS + SCALAR_BYTES * read as usize,
    )
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

/// A statement and its proof as the contract's calldata.
pub fn calldata(statement: &Statement, proof: &Proof) -> Vec<u8> {
    let mut data = [statement.y, statement.root].concat();
    for (i, scalar) in proof.stream.iter().enumerate() {
        // A commitment's two scalars are 128-bit.
        let limbs = if i < 4 {
            vec![scalar.c1, scalar.c0]
        } else {
            vec![scalar.c2, scalar.c1, scalar.c0]
        };
        limbs.iter().for_each(|limb| data.extend(limb.to_be_bytes()));
    }
    data
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
    use crate::machine::{PcsOpen, call, transaction_gas};
    use primitives::field::F64;
    use primitives::test_rng::Rng;
    use quotient::circuit::{LOG_ROWS, membership, membership_inputs};
    use quotient::opening::commit;
    use quotient::protocol::{Index, prove, verify};
    use quotient::statement::{DEPTH, Secret};

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
        let masks = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));
        let index = Index::new(&circuit);
        let index_root = commit(&index.table).root;
        let seed = std::array::from_fn(|_| rng.next_u64() as u8);
        let proved = prove(&circuit, &index, &index_root, &statement, &cells, &masks, &seed);
        (index_root, statement, proved.proof)
    }

    /// The tests' proof, made once for all of them: a full-size proof takes some 10 GB.
    static HONEST: LazyLock<(Hash, Statement, Proof)> = LazyLock::new(|| proof(&mut Rng::new(0xE8)));

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
        let code = claims_contract(&index_root, LOG_ROWS).code;
        let returned = |statement: &Statement, proof: &Proof| {
            let output = call(&code, &calldata(statement, proof), &PcsOpen::default()).output;
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

        let mut long = calldata(&statement, &proof);
        long.push(0);
        assert!(call(&code, &long, &PcsOpen::default()).output.is_none());
        assert!(
            call(&code, &long[..long.len() - 2], &PcsOpen::default())
                .output
                .is_none()
        );
    }

    /// The contract succeeds, returning nothing, exactly when the block holds an opening of each commitment's
    /// claims, all together, under its layout: those the Rust verifier leaves, on the honest proof and on
    /// tampered ones, which leave other claims than the honest proof's.
    #[test]
    fn contract_has_pcs_open_check_the_claims() {
        let (index_root, statement, proof) = HONEST.clone();
        let code = contract(&index_root, LOG_ROWS).code;
        let succeeds = |statement: &Statement, proof: &Proof, block: &PcsOpen| {
            let output = call(&code, &calldata(statement, proof), block).output;
            assert!(output.as_ref().is_none_or(Vec::is_empty));
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

        let mut long = calldata(&statement, &proof);
        long.push(0);
        assert!(call(&code, &long, &honest).output.is_none());
    }

    /// What a call costs: `cargo test --release -p evm -- --ignored --nocapture gas_report`.
    #[test]
    #[ignore]
    fn gas_report() {
        let (index_root, statement, proof) = proof(&mut Rng::new(0x6A6));
        let data = calldata(&statement, &proof);
        let returning = claims_contract(&index_root, LOG_ROWS);
        let returned = call(&returning.code, &data, &PcsOpen::default());
        assert!(returned.output.is_some());
        let contract = contract(&index_root, LOG_ROWS);
        let mut block = block_for(&index_root, &statement, &proof);
        let at_zero = call(&contract.code, &data, &block);
        assert_eq!(at_zero.output, Some(vec![]));

        println!("calldata             : {} bytes", data.len());
        println!("FIELD_MUL            : {}", contract.field_muls);
        println!("KECCAK256            : {}", contract.hashes);
        println!("PCS_OPEN             : 3 calls for the 4 claims: witness 1, wiring 1, quotient 2 together");
        println!(
            "code                 : {} bytes calling PCS_OPEN, {} returning the claims",
            contract.code.len(),
            returning.code.len()
        );
        println!(
            "memory               : {} words calling PCS_OPEN, {} returning the claims",
            contract.memory_words, returning.memory_words
        );
        println!("execution, returning the claims : {} gas", returned.execution);
        println!(
            "execution, PCS_OPEN at 0 gas    : {} gas, {} more (marshalling the inputs, and the calls)",
            at_zero.execution,
            at_zero.execution - returned.execution
        );
        println!();
        println!("PCS_OPEN at 0 gas a call and c a claim; transaction gas (without its 21,000 base):");
        println!(
            "{:>8} {:>10} {:>20} {:>20}",
            "c", "execution", "EIP-7623 (40/byte)", "EIP-7976 (64/byte)"
        );
        for claim_gas in [0, 2_000, 5_000, 20_000] {
            block.claim_gas = claim_gas;
            let outcome = call(&contract.code, &data, &block);
            assert_eq!(outcome.output, Some(vec![]));
            assert_eq!(outcome.execution, at_zero.execution + 4 * claim_gas);
            let total = |floor| {
                let gas = transaction_gas(&data, outcome.execution, floor);
                format!("{gas} ({})", gas - 21_000)
            };
            println!(
                "{claim_gas:>8} {:>10} {:>20} {:>20}",
                outcome.execution,
                total(40),
                total(64)
            );
        }
    }
}
