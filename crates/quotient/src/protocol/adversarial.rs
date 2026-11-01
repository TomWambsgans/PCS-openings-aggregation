//! Adversarial review of the lean prover (commit 411866f) at the protocol level: whole proofs and openings on
//! the toy circuit at several sizes, seeds, honest and broken witnesses, fingerprinted:
//! `cargo test -p quotient --release protocol::adversarial -- --nocapture` prints one `DIGEST` line per case.
//! With the pool size set (`LEANVM_NUM_THREADS`), the lines must not change either.
//!
//! The review compared these lines with those of commit d940553 (whose prover kept every codeword and wrote the
//! weight out): the lean prover made the same proofs. The hidden layouts (201a5d1) then changed the proofs on
//! purpose, so the lines are now pinned to the prover of f6e68a5 (hidden layouts, lean prover): a regression pin
//! of this prover's own outputs, not a comparison with an independent one.

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
    let pad: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let proved = prove(circuit, index, &index_committed.root, &statement, &cells, &masks, &pad);
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

/// What the prover of f6e68a5 (hidden layouts, lean prover) makes on these cases: `(log_rows, seed, broken,
/// fits, fingerprint)`. Re-pinned when the hidden layouts changed the proofs: the review pinned d940553's here.
const PINNED: &[(usize, u64, bool, bool, &str)] = &[
    (
        17,
        0,
        false,
        true,
        "6fcabeeb779165ded777ab034faa57b6e7f73068f58d2a4138b574bf9d1f70f3",
    ),
    (
        17,
        0,
        true,
        false,
        "a4bd85c7b31ad81287bf3a64265a43051d984f06455b577d8e37450d37b438ea",
    ),
    (
        17,
        1,
        false,
        true,
        "80841d13558e779109229bac0138c0aa9271018f57e7596265604021161e0b13",
    ),
    (
        17,
        1,
        true,
        false,
        "91bd5422a929d827f442146a1958c523a4f755ebed816b8cebc560895425861e",
    ),
    (
        17,
        2,
        false,
        true,
        "8e9b10446a0554e8f08db396866f9139a0c39cd2250d83a6aa900066526ae8d2",
    ),
    (
        17,
        2,
        true,
        false,
        "bdd730e0c94197226b0f36358a334d79d8ea4a1c6d1ad03c30ab28cc914d1162",
    ),
    (
        17,
        3,
        false,
        true,
        "2c5941bec0b0c3579de40716cf64565bf30294c37f8f1c717ae5a99413140ad5",
    ),
    (
        17,
        3,
        true,
        false,
        "2af4c894f5bb4bff3209bfcb69900ef1f452f0ed09a197111ddf0861a215fd31",
    ),
    (
        18,
        0,
        false,
        true,
        "2b2a82cb7d6cc3d8aa97ba5bdc76d4ba22108f938805129f0d5f2954bca620e9",
    ),
    (
        18,
        0,
        true,
        false,
        "3fb90077573b38362a851c09049e51921cf586f8a8c020a95d87c1f35e721f6d",
    ),
    (
        18,
        1,
        false,
        true,
        "83a65598483079ab52ab3ae29656279e85641fd5f87bc6fa6830375f20c451e8",
    ),
    (
        18,
        1,
        true,
        false,
        "46b679a7e3acf8e7e83ea8f38034a9c819354e5872c4f3bf24517e841618927b",
    ),
    (
        18,
        2,
        false,
        true,
        "84ee1e10ce01bba783422179eaad7cd7ebf8f525e99ad17b268e522a535c6894",
    ),
    (
        18,
        2,
        true,
        false,
        "81dd4042010c4ffba0c88f96fafe3e5ed5f28e1b01fabac1261202bef66b5cd6",
    ),
    (
        19,
        0,
        false,
        true,
        "9a0cfffbff1c32c29014bd08506da276d7257a5ba8f68561bf08736d64fbb76a",
    ),
    (
        19,
        0,
        true,
        false,
        "2958f14c9804813a3e525f79a8733b962647c767a7a489d7474d4d4e8ceb23f1",
    ),
    (
        19,
        1,
        false,
        true,
        "8b3d2abb4ffa4d507c7670586f56e14e294a4680bed1d64a0c527aa6ceefd562",
    ),
    (
        19,
        1,
        true,
        false,
        "859284bf8f7a18ee1332a56e4144b10e49e9ee18d7d78128e46e22a22cde3b0b",
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
