//! Adversarial review of the lean prover (commit 411866f) at the protocol level: whole proofs and openings on
//! the toy circuit at several sizes, seeds, honest and broken witnesses, fingerprinted so that the same test
//! run on commit d940553 (whose prover kept every codeword and wrote the weight out) can be compared line for
//! line: `cargo test -p quotient --release protocol::adversarial -- --nocapture` prints one `DIGEST` line per
//! case. With the pool size set (`LEANVM_NUM_THREADS`), the lines must not change either.

use super::*;
use crate::circuit::{Builder, Src, public_words};
use primitives::test_rng::Rng;

/// The fingerprint [`digest`] computes, written out here so that the old prover can be fingerprinted by the
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
    let proved = prove(circuit, index, &index_committed.root, &statement, &cells, &masks);
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

/// What commit d940553's prover makes on these cases (the same test, run there): `(log_rows, seed, broken,
/// fits, fingerprint)`.
const OLD: &[(usize, u64, bool, bool, &str)] = &[
    (
        17,
        0,
        false,
        true,
        "579356c562bc94ba4f5d06097838a263b8118c00e5d47a514d4f4fe6fb81d94e",
    ),
    (
        17,
        0,
        true,
        false,
        "651baecf6f3f9f67ff4384aee7926bbb661194e8f067665fd741623a740047c4",
    ),
    (
        17,
        1,
        false,
        true,
        "7637c64354fd85ecc0fbf5589058cdd4092efc2186344984db131c20be6f138f",
    ),
    (
        17,
        1,
        true,
        false,
        "17e31b0023e025f56fd42d496246c834adadba99a5cdefa2073f94fffe361670",
    ),
    (
        17,
        2,
        false,
        true,
        "acc40da7224db402dd4c91ce9280f0ce55964774b18cd0ffbd4496e0ef4835c2",
    ),
    (
        17,
        2,
        true,
        false,
        "8e5d708b1fc6d8a82878cc7dcedeee4d63b53a5878e07e7800bf650b97f17ce7",
    ),
    (
        17,
        3,
        false,
        true,
        "8311aa9c0cfd698f19487b25b904ef1c4fa3b33711dfebcbc70efb3ff3dea066",
    ),
    (
        17,
        3,
        true,
        false,
        "e25d077c97bbda7bb7b62128740188afe5f453272e53f6f52932ce1c66852180",
    ),
    (
        18,
        0,
        false,
        true,
        "5b5827029e45f9456c7f7cecf098424eb599c7cc961e0a270664b99dd09f45c6",
    ),
    (
        18,
        0,
        true,
        false,
        "46dd5bb505b424a81155b99b8058258a749c28b09a484dd281b3f6c668951ab5",
    ),
    (
        18,
        1,
        false,
        true,
        "81e8901ffc5cb8ffe364a3ac16dc6851154a88cb2391d782c90ee0993ecef6a9",
    ),
    (
        18,
        1,
        true,
        false,
        "0ec479a6721cfef6b83f48b6006ed57278289873cc17c3517bdffabedf03ab21",
    ),
    (
        18,
        2,
        false,
        true,
        "3f746eb6d69db3670bdac51357f0328f49e6c3c70d456ae1ae96e99de840eed9",
    ),
    (
        18,
        2,
        true,
        false,
        "b1d162d50cf51cd03d7743ec55d0199630388c1d79ed1213c4cd61bfcb39f32a",
    ),
    (
        19,
        0,
        false,
        true,
        "1019ae12ec9a808b1d39da695cb9c6a20e0f95bca65d0b4b7643bb04f9d5cbdb",
    ),
    (
        19,
        0,
        true,
        false,
        "b2c4a9f2b4c66811805323556a113572ed19b8a16e6a7df93f75c075ffbaee86",
    ),
    (
        19,
        1,
        false,
        true,
        "eeb88adcf81aceb16fe604a96050a50d1c74b8b4f4c4760e6df89895348dc330",
    ),
    (
        19,
        1,
        true,
        false,
        "f36ab8f457d3b480da33772d09fc3bc730e67870506c098a8361d971a1281dc3",
    ),
];

/// The lean prover makes the old prover's proofs and openings on the toy circuit at 2^17..2^19 rows, honest
/// and broken witnesses alike (a broken one leaves quotients that do not fit, so false claims).
#[test]
fn protocol_digests_are_the_old_provers() {
    let mut circuit = None;
    for &(log_rows, seed, broken, old_fits, old) in OLD {
        if circuit.as_ref().is_none_or(|(lr, _, _, _)| *lr != log_rows) {
            let c = toy(log_rows);
            let index = Index::new(&c);
            let index_committed = opening::commit(&index.table);
            circuit = Some((log_rows, c, index, index_committed));
        }
        let (_, c, index, index_committed) = circuit.as_ref().unwrap();
        let (fits, fp) = case(c, index, index_committed, 0xD1 + seed, broken);
        println!("DIGEST log_rows={log_rows} seed={seed} broken={broken} fits={fits} {fp}");
        assert_eq!(
            (fits, fp.as_str()),
            (old_fits, old),
            "log_rows={log_rows} seed={seed} broken={broken}"
        );
    }
}
