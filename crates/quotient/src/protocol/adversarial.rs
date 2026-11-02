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
        "49449f954f7fd96e2a181d39fcaddc10ebaf0b801a7c42f911a54f62ba0d0ea5",
    ),
    (
        17,
        0,
        true,
        false,
        "65097e41d5c92e24364cebf96e965588157bc36770500b0d2aa09c8270e174ee",
    ),
    (
        17,
        1,
        false,
        true,
        "e12e2368801bde4d36fedadf29ef7df06bc889aedeffdbaac31e68922fb88f8c",
    ),
    (
        17,
        1,
        true,
        false,
        "2720532a556f91df79b425ae75672c89397f67b8d95dc20d5197b5ac7c415958",
    ),
    (
        17,
        2,
        false,
        true,
        "f717cce8bfe5eb3a261c094136c25aec0074da2f7596b9ac611874fe41970800",
    ),
    (
        17,
        2,
        true,
        false,
        "6f949904bfd2e518421d0a3ad67445fbd534a4761ebf073c5f90a3dbe57cd28d",
    ),
    (
        17,
        3,
        false,
        true,
        "f97ffc51688b890296fc59892ac26ec8ef6c28f23aea9e50e5af6f78e76ff349",
    ),
    (
        17,
        3,
        true,
        false,
        "a1b24996f57748f1f7bf17d529276204c0644398ed04b8905345e2e64c93073b",
    ),
    (
        18,
        0,
        false,
        true,
        "be3154a192e978692eb1a4335900b012acfc34f75abd69d5166af451fb877091",
    ),
    (
        18,
        0,
        true,
        false,
        "77509ce5f02d0e19b9041cb7ded42d78bb5d895bbc666f1806e99ba21f6953f4",
    ),
    (
        18,
        1,
        false,
        true,
        "f045769618e8f02105109727d44a63b38c487c12ec940e6cc5e372ccb079b7a9",
    ),
    (
        18,
        1,
        true,
        false,
        "79967f59d19e03ef3900ce7436b9df0b154731f18a2cfbfb36f5d2b1b7b1aed7",
    ),
    (
        18,
        2,
        false,
        true,
        "c8af7d67afed687f6e0945a6daa4e5813ddd4880ce7acd91002245140c14f7e3",
    ),
    (
        18,
        2,
        true,
        false,
        "211578f6f8a40f9cb50947fed21cb8960237ccd6e762036f5b355aaefcd51351",
    ),
    (
        19,
        0,
        false,
        true,
        "ff907e29c72be980d1f9bf8ef02bac3280eb83b020dd311101875079b499d423",
    ),
    (
        19,
        0,
        true,
        false,
        "6f9f966e5c3811c71fc80bcce31bb2ef9d278a38aea714d6427299f838716ffc",
    ),
    (
        19,
        1,
        false,
        true,
        "c7f6d4db02d0556ca9114a57c5e9fd0b1680314a040ef5f9804497cb4bfe3551",
    ),
    (
        19,
        1,
        true,
        false,
        "0aa8fc28a12280a64da4f7968cf2798a239cc2d81c4dd8ec693515050816941b",
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
