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
/// d940553's here), then when the openings' transcripts took leanVM's shape.
const PINNED: &[(usize, u64, bool, bool, &str)] = &[
    (
        17,
        0,
        false,
        true,
        "f0b5c6ae598499dd429c406fd094de19d923aa3d9a750cb11d33d76499e984a3",
    ),
    (
        17,
        0,
        true,
        false,
        "e5ac471eb9577bbd75aafd8448806e9367a2f3a73865243844d30d436ff6013d",
    ),
    (
        17,
        1,
        false,
        true,
        "0186523831d71fa8fa0577827ba6edc75fdf85aee7325302fc2ecfa1beb753be",
    ),
    (
        17,
        1,
        true,
        false,
        "867858f9d4eef117be44c5caf8eda77e45d6edee92853e9cce6d3d9112c1ea60",
    ),
    (
        17,
        2,
        false,
        true,
        "4f41f631eede19fcfb3e117801ceba9fa5f7711c552120e8cdfb21d304bfbdf6",
    ),
    (
        17,
        2,
        true,
        false,
        "fb5209f201835062d7b3d41b5e62ccce9fe4a6ca5a0036ce1f38cb37e26be76d",
    ),
    (
        17,
        3,
        false,
        true,
        "8f8d14b92de096ca53df280cca3e77a0612fbe469791921f2fc5e70a0d274d92",
    ),
    (
        17,
        3,
        true,
        false,
        "1144d0f134e8d6fba2023270a684f266467b2808193a2c1d6f3e025af4ab87f8",
    ),
    (
        18,
        0,
        false,
        true,
        "ec566bfff0bd591137966e4dedfb485b1457513d62a5cc9153a0005b81a16e53",
    ),
    (
        18,
        0,
        true,
        false,
        "d14cd20d62512a98b48532005072b8018e37d5bef56e517e2b544464e7cacea6",
    ),
    (
        18,
        1,
        false,
        true,
        "29fdf3dd480201be013c809dfad4069b8f3f5e0172c5aa609f2b8618b3fd4b70",
    ),
    (
        18,
        1,
        true,
        false,
        "df850d6ea50874f20e665413dd8d101e1f195b76cf551c4e0f04d7207806d88d",
    ),
    (
        18,
        2,
        false,
        true,
        "e76030adefa23f32b87b77bad2cf2ad291cf868220f4dfcdb010dbc4fa150270",
    ),
    (
        18,
        2,
        true,
        false,
        "37f67867075a76b268335c1769572d562a72e22db34cdcae8f65124ff9256e8f",
    ),
    (
        19,
        0,
        false,
        true,
        "ab50ca3a38b7be6c8ea8118625c42c4a4189c9dab589794067ca510fe4d4785b",
    ),
    (
        19,
        0,
        true,
        false,
        "a9596fa66c10896e3aa742fd881ad1a6ae14a904dcf67953fb03fb1daa6db2e3",
    ),
    (
        19,
        1,
        false,
        true,
        "04d5ae663babe88ba92b962c90ca9899f61749d698f61463876255ce021664d5",
    ),
    (
        19,
        1,
        true,
        false,
        "8f11316f42be2b34eb3050e954128ad4e38888a8d57e42cd0f22ffa1ee5f3afb",
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
