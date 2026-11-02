// Part of this repository (written by an adversarial review of c004698: the opening transcript in the form F2
// proves, and `PCS_OPEN`'s documented link to it). MIT OR Apache-2.0; see NOTICE.md.
//! `PCS_OPEN`'s input, read as its documentation says a real precompile reads it, is what `opening::verify` takes.
//!
//! The mock attests an input by looking its bytes up; `machine.rs` says such an input names an opening that
//! `quotient::opening::verify` accepts, for the layout the id names, with the IV hashing that layout's prefix then
//! "words 4 onwards as field elements", and the proof's first two scalars "word 1's two halves". Here a reference
//! precompile parses an input by that text alone (byte order included) and runs `opening::verify` on the real
//! openings of a real proof at `2^17` rows, whose three calls the deployed contract makes (it succeeds against a
//! block holding exactly those three inputs). The IV is also recomputed from the input's raw bytes, and every
//! one-byte change of an input (two flips a byte) is rejected by the reference precompile against each of the three
//! openings.
//!
//! `cargo test --release -p evm --test review_pcs_open`.

use std::collections::HashMap;

use evm::machine::{Chain, PcsOpen, layout, pcs_open_input};
use evm::quotient::{VERIFIED, calldata, contract, init_code, openings};
use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use quotient::circuit::{Builder, Circuit, Src, public_words};
use quotient::opening::{self, Claim, Layout};
use quotient::protocol::{self, Index, Randomness, prove_with_randomness};
use quotient::statement::{Statement, pair};
use revm::primitives::{Address, U256};

const LOG_ROWS: usize = 17;

/// The protocol tests' toy circuit (`protocol::tests::toy`): `root` is a Keccak-256 of `y`, at `2^17` rows.
fn toy() -> Circuit {
    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
    b.finish(LOG_ROWS, &public_words(&x, &digest))
}

/// What a real `PCS_OPEN` would read from `input`, by `machine.rs`'s text: `3 + k (v + 1)` words; word 1 the root
/// as `s_0 · 2^128 + s_1`, `s_h` the little-endian number of the root's bytes `16 h .. 16 h + 16`; word 2 a known
/// layout's id; word 3 `k ≥ 1`; then each claim's `v` coordinates and value, a field element the low 192 bits of
/// its word, limb 0 lowest, the top 64 bits zero.
fn parse(input: &[u8]) -> Option<(Layout, Hash, Vec<Claim>)> {
    if !input.len().is_multiple_of(32) || input.len() < 96 {
        return None;
    }
    let words: Vec<&[u8]> = input.as_chunks::<32>().0.iter().map(|w| &w[..]).collect();
    let layout = layout(U256::from_be_slice(words[1]))?;
    let k = u64::try_from(U256::from_be_slice(words[2])).ok()? as usize;
    let v = layout.vars;
    if k == 0 || words.len() != 3 + k.checked_mul(v + 1)? {
        return None;
    }
    let mut root = [0u8; 32];
    for h in 0..2 {
        let mut half = words[0][16 * h..16 * h + 16].to_vec();
        half.reverse();
        root[16 * h..16 * h + 16].copy_from_slice(&half);
    }
    let element = |word: &[u8]| -> Option<F192> {
        let limb = |i: usize| u64::from_be_bytes(word[24 - 8 * i..32 - 8 * i].try_into().unwrap());
        (limb(3) == 0).then(|| F192::new(limb(0), limb(1), limb(2)))
    };
    let mut claims = vec![];
    for c in 0..k {
        let xs = words[3 + c * (v + 1)..3 + (c + 1) * (v + 1)]
            .iter()
            .map(|w| element(w))
            .collect::<Option<Vec<F192>>>()?;
        let (value, point) = xs.split_last()?;
        claims.push(Claim {
            point: point.to_vec(),
            value: *value,
        });
    }
    Some((layout, root, claims))
}

#[test]
fn pcs_open_inputs_are_what_opening_verify_reads() {
    let circuit = toy();
    let index = Index::new(&circuit);
    let index_committed = opening::commit(&index.table);
    let index_root = index_committed.root;
    let x = [0x6B; 32];
    let statement = Statement {
        y: x,
        root: pair(&x, &x),
    };
    let inputs: Vec<bool> = (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect();
    let cells = circuit.cells(&inputs);
    let randomness = Randomness::derive(&[0x33; 32], &index_root, &statement, &cells);
    let proved = prove_with_randomness(&circuit, &index, &index_root, &statement, &cells, &randomness);
    let proof = proved.proof.clone();
    let (roots, claims) = (proved.roots, proved.claims.clone());
    let opened = protocol::open(proved.tables, &claims, &index, &index_committed);
    assert_eq!(
        protocol::verify_openings(LOG_ROWS, &index_root, &roots, &claims, &opened),
        Ok(())
    );

    // The three calls, and the real opening each stands for (by root: the witness, the index, the quotient).
    let calls = openings(&index_root, &roots, &claims, LOG_ROWS);
    let by_root: HashMap<Hash, &fiat_shamir::transcript::Proof> = [
        (roots[0], &opened.witness),
        (index_root, &opened.wiring),
        (roots[1], &opened.quotient),
    ]
    .into_iter()
    .collect();
    let mut block = PcsOpen::default();
    let mut inputs = vec![];
    for (root, id, call_claims) in &calls {
        block.register(root, *id, call_claims);
        inputs.push((pcs_open_input(root, *id, call_claims), *root));
    }

    // The deployed contract's calls are these three inputs: it succeeds against a block holding exactly them.
    let owner = Address::with_last_byte(0x0e);
    let built = contract(LOG_ROWS);
    let mut chain = Chain::default();
    let (address, _) = chain.deploy(&init_code(&built, &index_root, owner));
    let address = address.expect("a deployment");
    let data = calldata(&statement, &proof).expect("calldata");
    assert_eq!(
        chain.call(address, &data, &block).output.as_deref(),
        Some(&VERIFIED[..])
    );
    for missing in 0..3 {
        let mut fewer = PcsOpen::default();
        for (k, (root, id, call_claims)) in calls.iter().enumerate() {
            if k != missing {
                fewer.register(root, *id, call_claims);
            }
        }
        assert_eq!(chain.call(address, &data, &fewer).output, None, "{missing}");
    }

    // Each input, read by the reference precompile: the layout, root and claims of a real opening it accepts.
    let wires: Vec<_> = [&opened.witness, &opened.wiring, &opened.quotient]
        .into_iter()
        .map(opening::wire_proof)
        .collect();
    for ((input, root), (_, id, call_claims)) in inputs.iter().zip(&calls) {
        let (layout, parsed_root, parsed_claims) = parse(input).expect("a well-formed input");
        assert_eq!(&parsed_root, root);
        assert_eq!(&parsed_claims, call_claims);
        assert_eq!(Some(&layout), evm::machine::layout(U256::from(*id)).as_ref());
        let opening_proof = by_root[root];
        let wire = opening::wire_proof(opening_proof);
        assert_eq!(
            opening::verify(&layout, &parsed_root, &parsed_claims, &wire),
            Ok(()),
            "id {id}"
        );

        // The IV from the raw bytes: the prefix, then each claim word's low 24 bytes reversed (limb 0 first,
        // little-endian), which is `opening::iv`'s.
        let mut iv_bytes = opening::prefix(&layout).to_vec();
        for word in input[96..].as_chunks::<32>().0 {
            assert_eq!(word[..8], [0; 8]);
            iv_bytes.extend(word[8..].iter().rev());
        }
        assert_eq!(primitives::hash::hash(&iv_bytes), opening::iv(&layout, &parsed_claims));
        // The proof's first two scalars are word 1's halves: the high half first, each read as two limbs.
        let limb = |at: usize| u64::from_be_bytes(input[at..at + 8].try_into().unwrap());
        assert_eq!(
            opening_proof.stream[..2],
            [F192::new(limb(8), limb(0), 0), F192::new(limb(24), limb(16), 0)]
        );

        // Every one-byte change of the input is rejected: it does not parse, or the opening does not verify.
        let mut verified = 0;
        for at in 0..input.len() {
            for flip in [0x01u8, 0x80] {
                let mut other = input.clone();
                other[at] ^= flip;
                // Against every opening the block holds, not only the one of its root.
                let accepted = parse(&other).is_some_and(|(layout, root, claims)| {
                    verified += 1;
                    wires
                        .iter()
                        .any(|w| opening::verify(&layout, &root, &claims, w).is_ok())
                });
                assert!(!accepted, "id {id}: byte {at} ^ {flip:#x}");
            }
        }
        // All but the changes of the id, of `k` and of a claim word's top 64 bits parse, and were verified.
        let claim_words = (input.len() - 96) / 32;
        assert_eq!(verified, 2 * (32 + 24 * claim_words), "id {id}");
    }
}
