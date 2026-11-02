//! Adversarial review of the lean prover (commit 411866f) at the protocol level: whole proofs and openings on
//! the toy circuit at several sizes, seeds, honest and broken witnesses, fingerprinted:
//! `cargo test -p quotient --release protocol::adversarial -- --nocapture` prints one `DIGEST` line per case.
//! With the pool size set (`LEANVM_NUM_THREADS`), the lines must not change either.
//!
//! The review compared these lines with those of commit d940553 (whose prover kept every codeword and wrote the
//! weight out): the lean prover made the same proofs. The hidden layouts (201a5d1) then changed the proofs on
//! purpose, so the lines were pinned to the prover of f6e68a5 (hidden layouts, lean prover): a regression pin
//! of this prover's own outputs, not a comparison with an independent one. They moved once more, on purpose,
//! when the openings' transcripts took leanVM's shape (`opening::iv`: the IV hashes a prefix binding the layout
//! and a version, then the claims; the root is the proof's first two scalars): the reduction's proofs are
//! unchanged, every opening changed. (Before re-pinning, the old pins were reproduced with the new
//! `prove_with_randomness` and the old seed: the API change alone moved nothing.)

use super::*;
use crate::circuit::{Builder, Src, public_words};
use primitives::test_rng::Rng;

/// The fingerprint [`digest`] computes, written out here so that the old prover could be fingerprinted by the
/// same code: every scalar, row word and digest of the proof and its openings, each list after its length.
fn fingerprint(proof: &Proof, openings: [&fiat_shamir::transcript::Proof; 3]) -> String {
    let mut bytes = vec![];
    let scalars = |bytes: &mut Vec<u8>, xs: &[F192]| {
        bytes.extend_from_slice(&(xs.len() as u64).to_le_bytes());
        for x in xs {
            for limb in [x.c0, x.c1, x.c2] {
                bytes.extend_from_slice(&limb.to_le_bytes());
            }
        }
    };
    scalars(&mut bytes, &proof.stream);
    for opening in openings {
        scalars(&mut bytes, &opening.stream);
        bytes.extend_from_slice(&(opening.merkle.len() as u64).to_le_bytes());
        for paths in &opening.merkle {
            bytes.extend_from_slice(&(paths.leaf_data.len() as u64).to_le_bytes());
            for row in &paths.leaf_data {
                bytes.extend_from_slice(&(row.len() as u64).to_le_bytes());
                row.iter().for_each(|w| bytes.extend_from_slice(&w.0.to_le_bytes()));
            }
            bytes.extend_from_slice(&(paths.sibling_hashes.len() as u64).to_le_bytes());
            paths.sibling_hashes.iter().for_each(|h| bytes.extend_from_slice(h));
        }
    }
    primitives::hash::hash(&bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// `prove`'s buffer reuse on a tiny table, for Miri (`cargo +nightly miri test --target
/// x86_64-unknown-linux-gnu -p quotient miri_`): the loop's values buffer becomes the quotient table's stack
/// (`Table::new_in`), and `q`'s `F192` allocation, reinterpreted as words (`into_words`), the commitment's
/// encoding scratch (`commit_in`), whose root is `commit`'s; the allocation is freed as words.
#[test]
fn miri_buffer_reuse() {
    let layout = opening::Layout::new(9, 7, 8, &[(2, 1 << 7), (0, 50), (3, 16)]);
    let placed = layout.placed();
    let mut values = Vec::with_capacity(placed.max(40));
    values.resize(40, F64(9));
    let fill = |l: usize, b: usize, out: &mut [F64]| {
        out.iter_mut()
            .enumerate()
            .for_each(|(i, w)| *w = F64((l * 977 + b * 31 + i) as u64))
    };
    let table = Table::new_in(layout.clone(), values, fill);
    assert_eq!(table.stack, Table::new(layout, fill).stack);
    let mut q: Vec<F192> = Vec::with_capacity(12usize.max(placed.div_ceil(3)));
    q.resize(12, F192::ONE);
    let scratch = into_words(q);
    assert_eq!(scratch.len(), 36);
    assert!(scratch[..3] == [F64(1), F64(0), F64(0)]);
    let committed = opening::commit_in(&table, scratch);
    assert_eq!(committed.root, opening::commit(&table).root);
    // A scratch too small to hold the stack is grown, not overrun.
    let small = into_words(vec![F192::ZERO; 2]);
    assert_eq!(opening::commit_in(&table, small).root, committed.root);
}

fn toy(log_rows: usize) -> Circuit {
    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
    b.finish(log_rows, &public_words(&x, &digest))
}

/// One case: prove and open, return `(fits, fingerprint)`.
fn case(circuit: &Circuit, index: &Index, index_committed: &Committed, seed: u64, broken: bool) -> (bool, String) {
    let mut rng = Rng::new(seed);
    let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let statement = Statement {
        y: x,
        root: crate::statement::pair(&x, &x),
    };
    let inputs: Vec<bool> = (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect();
    let mut cells = circuit.cells(&inputs);
    if broken {
        // A witness that is not one: one cell flipped somewhere past the public rows.
        let at = 1 << 12 | (rng.next_u64() as usize % (cells.len() >> 13)) << 12;
        cells[at] = F64(cells[at].0 ^ 1);
    }
    let masks: [[F64; 3]; 4] = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));
    // The tables' padding seed (an input since the hidden layouts), drawn after what d940553's case drew.
    let padding: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let randomness = Randomness { masks, padding };
    let proved = prove_with_randomness(circuit, index, &index_committed.root, &statement, &cells, &randomness);
    let fits = proved.fits;
    let openings = open(proved.tables, &proved.claims, index, index_committed);
    let fp = fingerprint(&proved.proof, [&openings.witness, &openings.wiring, &openings.quotient]);
    // The pinned `digest` is the same fingerprint.
    let d: String = digest(&proved.proof, &openings)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    assert_eq!(d, fp);
    (fits, fp)
}

/// What the prover makes on these cases, its masks and padding given (`prove_with_randomness`): `(log_rows, seed,
/// broken, fits, fingerprint)`. Re-pinned when the hidden layouts changed the proofs (the review pinned
/// d940553's here), then when the openings' transcripts took leanVM's shape, then when the hidden layouts took
/// the gadget (`HIDING.md`, condition (R) for every challenge).
const PINNED: &[(usize, u64, bool, bool, &str)] = &[
    (
        17,
        0,
        false,
        true,
        "c348f6ff3f48a9cacecf36db855e61c38f1f88ddcaa2fe46b8c6ae13a1f8537c",
    ),
    (
        17,
        0,
        true,
        false,
        "a9f256706a3c313b71ab51df93db399df3fd4d32d0bfb42fe1bc5a7bfae072c5",
    ),
    (
        17,
        1,
        false,
        true,
        "0fb7c2b490b631a81e156e27014858784f99fdbc19e6e49ada97302247deb866",
    ),
    (
        17,
        1,
        true,
        false,
        "77b408a724d999973fab7dc94f835feb018ddaff07ed57e57e0be68e66d866dc",
    ),
    (
        17,
        2,
        false,
        true,
        "d85efa618d8cd13bec725d45edc0b9c0202fe3ce03f5f406be19caeeaf967d49",
    ),
    (
        17,
        2,
        true,
        false,
        "142458636abb16a8af715e48d355499c3bc1832cab7750179a3ac6e55978db7a",
    ),
    (
        17,
        3,
        false,
        true,
        "de78c0ba9aa972d78da505df1dd929432d2566c0ed4ee32b4ca325b4ed85dba1",
    ),
    (
        17,
        3,
        true,
        false,
        "b2f69ac212f7da1afc91ed3c301d37abcb3b3b03e1be12df3d0bea140ab151be",
    ),
    (
        18,
        0,
        false,
        true,
        "eca14c901b2fb938b2efacc1cc1042c7d218edf4fd51e8e4b284edb9a0f65785",
    ),
    (
        18,
        0,
        true,
        false,
        "d605103d0e1e4fb4a4a80d0a0443eedf127a15d04a32e76142498f4d846d7829",
    ),
    (
        18,
        1,
        false,
        true,
        "e3ee6351e566e45a6352b161bdc915b6f2fde1326ae5907540b63f2d86b58e66",
    ),
    (
        18,
        1,
        true,
        false,
        "b380bfdf60b235886c9ee0812fc8a62dcead232100fae2c0c5821f5491219e35",
    ),
    (
        18,
        2,
        false,
        true,
        "00e0e809155bfba6ede57b6f94e3d809b11b24e1e6c88a4a1e62df1e37a17780",
    ),
    (
        18,
        2,
        true,
        false,
        "7d95380fe095187721aec777f35cab18836b3a274ed8ba1b0a5c26d009678758",
    ),
    (
        19,
        0,
        false,
        true,
        "07d1e9c34066e6055b9405ffc0b39c19d83a225b4140405b73f54d6998bbbe1c",
    ),
    (
        19,
        0,
        true,
        false,
        "5ac7af5604a019fe667f71fb8978c3c7474eb4dab8ed8e6418baa4740a286fd2",
    ),
    (
        19,
        1,
        false,
        true,
        "0f8f8a80b4bc980d510fedc0c4338e40fae23ac33767896403e381a1ae5aae6b",
    ),
    (
        19,
        1,
        true,
        false,
        "bd1243b0565cfa29711840a54a5b22bedfb3395789d3d19c1fca015ab52e78cd",
    ),
];

/// The prover makes the pinned proofs and openings on the toy circuit at 2^17..2^19 rows, honest and broken
/// witnesses alike (a broken one leaves quotients that do not fit, so false claims).
#[test]
fn protocol_digests_are_pinned() {
    let mut circuit = None;
    let mut moved = vec![];
    for &(log_rows, seed, broken, pinned_fits, pinned) in PINNED {
        if circuit.as_ref().is_none_or(|(lr, _, _, _)| *lr != log_rows) {
            let c = toy(log_rows);
            let index = Index::new(&c);
            let index_committed = opening::commit(&index.table);
            circuit = Some((log_rows, c, index, index_committed));
        }
        let (_, c, index, index_committed) = circuit.as_ref().unwrap();
        let (fits, fp) = case(c, index, index_committed, 0xD1 + seed, broken);
        println!("DIGEST log_rows={log_rows} seed={seed} broken={broken} fits={fits} {fp}");
        if (fits, fp.as_str()) != (pinned_fits, pinned) {
            moved.push(format!(
                "log_rows={log_rows} seed={seed} broken={broken}: fits={fits} {fp}"
            ));
        }
    }
    assert!(moved.is_empty(), "cases that moved: {moved:#?}");
}
