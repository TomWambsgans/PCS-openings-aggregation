// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The SLH-DSA-SHAKE-128s verifier contract: the quotient argument's contract at the circuit's `2^29` rows, in
//! the inverse-hint mode, the circuit's commitment in its code. It is the verifier's PIOP part: what it computes
//! from the calldata are the commitments and four claims, which it hands to `PCS_OPEN` (mocked, at 0 gas).
//!
//! What is not real here: no prover takes 2^29 rows (leanVM's WHIR commits at most 2^28 words; the tables here
//! are 2^32), so the transcript is random scalars with the hint that fits them, and the circuit's commitment a
//! stand-in for the root of its wiring table. The contract's code and gas do not depend on either: it is
//! straight-line, the same for every circuit of 2^29 rows, its commitment a constant in its code.

use evm::machine::{Chain, PcsOpen, transaction_gas};
use evm::quotient::{VERIFIED, calldata, claims_contract_in, contract_in, creation_code, decode, openings};
use fips205::{Shake128s, SigningKey, VerifyingKey};
use primitives::field::F192;
use primitives::test_rng::Rng;
use quotient::protocol::{Inverse, hint, verify_reduction_in};
use quotient::statement::Statement;
use quotient::transcript::Proof;
use slh_dsa::{MSG_BYTES, SHAKE_128S_LOG_ROWS, statement};

/// A real key's statement: the public key and a message.
fn real_statement(rng: &mut Rng) -> Statement {
    let mut bytes16 = || -> [u8; 16] { std::array::from_fn(|_| rng.next_u64() as u8) };
    let sk = SigningKey::<Shake128s>::slh_keygen_internal(&bytes16(), &bytes16(), &bytes16());
    let vk: &VerifyingKey<Shake128s> = sk.as_ref();
    let pk: [u8; 32] = vk.to_bytes().as_slice().try_into().unwrap();
    let msg: [u8; MSG_BYTES] = [bytes16(), bytes16()].concat().try_into().unwrap();
    statement(&pk, &msg)
}

/// Nine scalars (two commitments, five values) and the hint that fits them.
fn transcript(rng: &mut Rng, index_root: &[u8; 32], statement: &Statement, mode: Inverse) -> Proof {
    let mut stream: Vec<F192> = (0..4).map(|_| F192::new(rng.next_u64(), rng.next_u64(), 0)).collect();
    stream.extend((0..5).map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64())));
    let mut proof = Proof { stream };
    if mode == Inverse::Hint {
        let h = hint(index_root, statement, &proof, SHAKE_128S_LOG_ROWS).expect("a nonzero product");
        proof.stream.push(h);
    }
    proof
}

fn deployed(init: &[u8]) -> (Chain, revm::primitives::Address) {
    let mut chain = Chain::default();
    let (address, _) = chain.deploy(init);
    (chain, address.expect("a deployment"))
}

#[test]
fn slh_dsa_contract() {
    let log_rows = SHAKE_128S_LOG_ROWS;
    let mut rng = Rng::new(0x5_1D5C);
    let index_root: [u8; 32] = std::array::from_fn(|i| 0xA0 ^ i as u8);
    let (claims_chain, claims_at) = deployed(&creation_code(&claims_contract_in(log_rows, Inverse::Hint, Some(&index_root))));
    let contract = contract_in(log_rows, Inverse::Hint, Some(&index_root));
    let (chain, at) = deployed(&creation_code(&contract));
    println!("SLH-DSA-SHAKE-128s verifier (2^{log_rows} rows, hint, root in code): {} bytes of code, {} FIELD_MUL", contract.code.len(), contract.field_muls);

    let mut gas = vec![];
    for _ in 0..4 {
        let statement = real_statement(&mut rng);
        let proof = transcript(&mut rng, &index_root, &statement, Inverse::Hint);
        let data = calldata(&statement, &proof).unwrap();
        assert_eq!(data.len(), 276);
        let (roots, claims) = verify_reduction_in(&index_root, &statement, &proof, log_rows, Inverse::Hint).expect("a reduction");

        // The contract computes the Rust verifier's commitments and claims.
        let returned = claims_chain.call(claims_at, &data, &PcsOpen::default()).output;
        assert_eq!(returned.as_deref().and_then(|out| decode(out, log_rows)), Some((roots, claims.clone())));

        // With the claims attested by a PCS_OPEN taking the 2^32-word tables, it verifies.
        let mut block = PcsOpen::large();
        for (root, id, claims) in openings(&index_root, &roots, &claims, log_rows) {
            block.register(&root, id, &claims);
        }
        let outcome = chain.call(at, &data, &block);
        assert_eq!(outcome.output, Some(VERIFIED.to_vec()));
        gas.push((outcome.execution, transaction_gas(&data, outcome.execution, 40) - 21_000, transaction_gas(&data, outcome.execution, 64) - 21_000));

        // Not with today's PCS_OPEN (WHIR's 2^28 words), not with any claim unattested, nor with a wrong hint or
        // another statement.
        let mut small = PcsOpen::default();
        for (root, id, claims) in openings(&index_root, &roots, &claims, log_rows) {
            small.register(&root, id, &claims);
        }
        assert_eq!(chain.call(at, &data, &small).output, None);
        assert_eq!(chain.call(at, &data, &PcsOpen::large()).output, None);
        for byte in [252, 263, 275] {
            let mut bad = data.clone();
            bad[byte] ^= 0x10;
            assert_eq!(chain.call(at, &bad, &block).output, None, "hint byte {byte}");
        }
        for byte in [4, 40, 60] {
            let mut bad = data.clone();
            bad[byte] ^= 0x01;
            assert_eq!(chain.call(at, &bad, &block).output, None, "statement byte {byte}");
        }
    }
    println!("gas (execution, EIP-7623 and EIP-7976 transaction without the 21,000 base): {gas:?}");
    let (exec, tx) = (gas[0].0, gas[0].1);
    assert!(gas.iter().all(|g| g.0 == exec), "straight-line: the same execution for every proof");
    assert!(tx < 17_500, "{tx}");

    // The same at the circuit's commitment in storage, and in compute mode, for comparison.
    let owner = revm::primitives::Address::with_last_byte(0x0e);
    let stored = contract_in(log_rows, Inverse::Hint, None);
    let mut storage_chain = Chain::default();
    let (stored_at, _) = evm::quotient::deploy(&mut storage_chain, &stored, &index_root, owner);
    let compute = contract_in(log_rows, Inverse::Compute, Some(&index_root));
    let (compute_chain, compute_at) = deployed(&creation_code(&compute));
    let statement = real_statement(&mut rng);
    for (name, chain, at, mode) in [
        ("hint, root in storage", &storage_chain, stored_at.unwrap(), Inverse::Hint),
        ("compute, root in code", &compute_chain, compute_at, Inverse::Compute),
    ] {
        let proof = transcript(&mut rng, &index_root, &statement, mode);
        let data = calldata(&statement, &proof).unwrap();
        let (roots, claims) = verify_reduction_in(&index_root, &statement, &proof, log_rows, mode).unwrap();
        let mut block = PcsOpen::large();
        for (root, id, claims) in openings(&index_root, &roots, &claims, log_rows) {
            block.register(&root, id, &claims);
        }
        let outcome = chain.call(at, &data, &block);
        assert_eq!(outcome.output, Some(VERIFIED.to_vec()), "{name}");
        println!("{name}: execution {}, transaction {} ({} bytes)", outcome.execution, transaction_gas(&data, outcome.execution, 40) - 21_000, data.len());
    }
}
