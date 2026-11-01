// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/quotient.rs. MIT OR Apache-2.0; see NOTICE.md.
//! The membership verifier (`quotient::protocol::reduce`) as a contract, and its calldata and return value.
//!
//! Calldata is `y`, `root`, the two commitments (the witness table's, then the quotient table's), each as its two
//! 16-byte scalars, then the proof's five scalars, 24 bytes each. The contract returns the commitments' four
//! scalars, three claims as a point then a value, and the value of the claim at the fixed point.

use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use quotient::opening::Claim;
use quotient::protocol::{Claims, Reduced, label, reduce, sum_point};
use quotient::statement::Statement;
use quotient::transcript::{Proof, scalars_root};

use crate::codegen::{COMMITMENT, Contract, SCALAR_BYTES, compile};
use crate::contract::Recorder;
use crate::record::record;

/// Where calldata holds the proof's scalars: after the statement and the two commitments.
const SCALARS: usize = COMMITMENT + 64;

/// The contract verifying proofs against the circuit of `2^log_rows` rows committed as `index_root`.
pub fn contract(index_root: &Hash, log_rows: usize) -> Contract {
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
    let mut outputs: Vec<u32> = roots.iter().flatten().map(|sym| sym.0).collect();
    for (point, value) in [witness, wiring, quotient] {
        outputs.extend(point.iter().chain([&value]).map(|sym| sym.0));
    }
    outputs.push(sum.0);
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
        prefix,
        SCALARS,
        SCALARS + SCALAR_BYTES * read as usize,
    )
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

/// What the contract returned: the two commitments and the four claims.
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
    use super::*;
    use crate::machine::{call, transaction_gas};
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
        let proved = prove(&circuit, &index, &index_root, &statement, &cells, &masks);
        (index_root, statement, proved.proof)
    }

    /// The contract and the Rust verifier leave the same commitments and claims, on an honest proof and on
    /// tampered ones, and the contract reverts on calldata of another length.
    #[test]
    fn contract_is_the_verifier() {
        let mut rng = Rng::new(0xE8);
        let (index_root, statement, mut proof) = proof(&mut rng);
        let code = contract(&index_root, LOG_ROWS).code;
        let returned = |statement: &Statement, proof: &Proof| {
            let output = call(&code, &calldata(statement, proof)).output;
            output.as_deref().and_then(|output| decode(output, LOG_ROWS))
        };
        let expected = verify(&index_root, &statement, &proof, LOG_ROWS).expect("a reduction");
        assert_eq!(returned(&statement, &proof), Some(expected));

        for at in 0..proof.stream.len() {
            let change = if at < 4 { F192::new(1, 2, 0) } else { F192::new(1, 2, 3) };
            proof.stream[at] += change;
            assert_eq!(
                returned(&statement, &proof),
                verify(&index_root, &statement, &proof, LOG_ROWS).ok(),
                "{at}"
            );
            proof.stream[at] += change;
        }
        let mut other = statement;
        other.y[5] ^= 4;
        assert_eq!(
            returned(&other, &proof),
            verify(&index_root, &other, &proof, LOG_ROWS).ok()
        );

        let mut long = calldata(&statement, &proof);
        long.push(0);
        assert!(call(&code, &long).output.is_none());
        assert!(call(&code, &long[..long.len() - 2]).output.is_none());
    }

    /// What a call costs: `cargo test --release -p evm -- --ignored --nocapture gas_report`.
    #[test]
    #[ignore]
    fn gas_report() {
        let (index_root, statement, proof) = proof(&mut Rng::new(0x6A6));
        let contract = contract(&index_root, LOG_ROWS);
        let data = calldata(&statement, &proof);
        let outcome = call(&contract.code, &data);
        assert!(outcome.output.is_some());
        println!("code                 : {} bytes", contract.code.len());
        println!("calldata             : {} bytes", data.len());
        println!("FIELD_MUL            : {}", contract.field_muls);
        println!("KECCAK256            : {}", contract.hashes);
        println!("memory               : {} words", contract.memory_words);
        println!("execution            : {} gas", outcome.execution);
        for (name, floor) in [("EIP-7623", 40), ("EIP-7976", 64)] {
            let gas = transaction_gas(&data, outcome.execution, floor);
            println!("transaction, {name}: {gas} gas, {} without its base cost", gas - 21_000);
        }
    }
}
