// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! A test vector for `formal/WhirBridge`: an opening of two claims on a stacked table (the layout of
//! `opening::tests`, lanes out of order and a gap, `placed` short of the stack), written in the form leanerVM
//! mumbai's Lean verifier reads: the scalar stream, then one full Merkle path per query (the pruned batches
//! expanded, as `Transcript::finish` returns them). `formal/WhirBridge/Test/Check.lean` runs the Lean mirror of
//! `opening::verify` on it. The opening has leanVM's transcript shape (`opening::iv`: the IV `keccak256(prefix ‖
//! claims)`, a zero public digest, the root as the stream's first two scalars), which `variantProg` and
//! `famSeed` model; the vector's `prefix` line is `pre`, byte by byte.
//!
//! `cargo test -p quotient --test whir_bridge_vector -- --ignored` writes `target/whir_bridge_vector.txt`
//! (or `$WHIR_BRIDGE_VECTOR`).

use primitives::field::{F64, F192};
use primitives::test_rng::Rng;
use quotient::opening::{self, Claim, Layout, Table};
use verifier::{Digest, E, Transcript};

fn words(bytes: &[u8; 32]) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().expect("8 bytes")))
}

fn line(tag: &str, values: impl IntoIterator<Item = u64>) -> String {
    let mut s = tag.to_string();
    for v in values {
        s.push(' ');
        s.push_str(&v.to_string());
    }
    s.push('\n');
    s
}

fn limbs(x: &F192) -> [u64; 3] {
    [x.c0, x.c1, x.c2]
}

#[test]
#[ignore = "writes the vector `formal/WhirBridge` checks; run with --ignored"]
fn whir_bridge_vector() {
    let mut rng = Rng::new(0x0E);
    let (vars, log_chunk, log_n) = (18, 14, 16);
    let layout = Layout::new(vars, log_chunk, log_n, &[(3, 1 << 14), (0, 3000), (9, 1 << 13)]);
    let table = Table::new(layout, |l, _, lane| {
        for (i, w) in lane.iter_mut().enumerate() {
            *w = F64(((l << 32 | i) as u64 + 1)
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .rotate_left(17));
        }
    });
    let committed = opening::commit(&table);
    let claims: Vec<Claim> = (0..2)
        .map(|_| {
            let point = rng.ext_vec(vars);
            let value = table.eval(&point);
            Claim { point, value }
        })
        .collect();
    let proof = opening::open(&table, &committed, &claims);
    let wire = opening::wire_proof(&proof);
    assert_eq!(opening::verify(&table.layout, &committed.root, &claims, &wire), Ok(()));

    // Replay the opening (`opening::verify`'s transcript and calls, nothing checked) for every query's full path:
    // the IV `keccak256(prefix ‖ claims)`, a zero public digest, the root as the first two scalars.
    let mut bytes = opening::prefix(&table.layout).to_vec();
    for claim in &claims {
        for x in claim.point.iter().chain([&claim.value]) {
            for limb in limbs(x) {
                bytes.extend_from_slice(&limb.to_le_bytes());
            }
        }
    }
    let iv = primitives::hash::hash(&bytes);
    assert_eq!(iv, opening::iv(&table.layout, &claims));
    let mut transcript = Transcript::new(&wire, Digest(iv), Digest([0; 32]), false);
    let halves = transcript.next_scalars(2).expect("the root's two scalars");
    assert_eq!(Digest::from_halves(halves[0], halves[1]), Ok(Digest(committed.root)));
    let _lambda = transcript.sample();
    let zero = E::new(0, 0, 0);
    verifier::whir::verify_whir(
        &mut transcript,
        log_n,
        table.layout.placed() as u64,
        opening::LOG_INV_RATE,
        zero,
        Digest(committed.root),
        &|_| zero,
    )
    .expect("the replay walks the proof");
    let paths = transcript.finish().expect("the replay reads the whole proof");

    let layout = &table.layout;
    let mut out = line(
        "layout",
        [layout.vars as u64, layout.log_n as u64, layout.lanes() as u64]
            .into_iter()
            .chain((0..layout.lanes()).map(|l| layout.block(l) as u64)),
    );
    out += &line("root", words(&committed.root));
    // The IV's prefix, byte by byte (`opening::prefix`, `pre` of `famSeed`).
    out += &line("prefix", opening::prefix(layout).iter().map(|&b| b as u64));
    for claim in &claims {
        out += &line("claim", claim.point.iter().chain([&claim.value]).flat_map(limbs));
    }
    out += &line("stream", proof.stream.iter().flat_map(limbs));
    for path in &paths {
        out += &line(
            "open",
            [path.leaf.len() as u64]
                .into_iter()
                .chain(path.leaf.iter().map(|k| k.0))
                .chain(path.siblings.iter().flat_map(words)),
        );
    }
    let file = std::env::var("WHIR_BRIDGE_VECTOR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/whir_bridge_vector.txt").to_string());
    std::fs::write(&file, out).expect("the vector is written");
    eprintln!("{} paths, {} stream scalars: {file}", paths.len(), proof.stream.len());
}
