// Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (F0a/F2/F4 review): not part of
// the protocol's tests.
//! Differential vectors for `formal/Review/F2Differential.lean`: an opening of the **deployed wiring layout at
//! `2^22` rows** (`wiring_layout(22)`: public, `24` variables, `64` lanes, the index table of
//! `circuit::membership()`), which `formal/WhirBridge/Test/Check.lean` never runs (its public vector is a toy
//! layout), and the verdict of the Rust `opening::verify` on generic tamperings of it, which the Lean
//! `openingVerifyWithHash` must match where the Rust accepts (`Rust accepts ⇒ Lean accepts` is the direction the
//! soundness theorem needs) and should match elsewhere.
//!
//!   cargo test -p quotient --release --test review_f0f2f4 -- --ignored --nocapture
//!
//! writes `$REVIEW_VECTOR` (default `target/review_f0f2f4_vector.txt`).

use primitives::field::F192;
use primitives::test_rng::Rng;
use quotient::circuit::membership;
use quotient::opening::{self, Claim, Layout};
use quotient::protocol::{Index, wiring_layout};
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

/// `whir_bridge_vector.rs`'s `vector`: the honest opening as the Lean verifier reads it (stream, full paths).
fn vector(
    name: &str,
    head: String,
    layout: &Layout,
    root: &[u8; 32],
    claims: &[Claim],
    proof: &fiat_shamir::transcript::Proof,
) -> String {
    let wire = opening::wire_proof(proof);
    assert_eq!(opening::verify(layout, root, claims, &wire), Ok(()));
    let iv = opening::iv(layout, claims);
    let mut transcript = Transcript::new(&wire, Digest(iv), Digest(opening::PUBLIC_DIGEST), false);
    let halves = transcript.next_scalars(2).expect("the root's two scalars");
    assert_eq!(Digest::from_halves(halves[0], halves[1]), Ok(Digest(*root)));
    let _lambda = transcript.sample();
    let zero = E::new(0, 0, 0);
    verifier::whir::verify_whir(
        &mut transcript,
        layout.log_n,
        layout.placed() as u64,
        opening::LOG_INV_RATE,
        zero,
        Digest(*root),
        &|_| zero,
    )
    .expect("the replay walks the proof");
    let paths = transcript.finish().expect("the replay reads the whole proof");
    let mut out = format!("vector {name}\n") + &head;
    out += &line("prefix", opening::prefix(layout).iter().map(|&b| b as u64));
    out += &line("root", words(root));
    for claim in claims {
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
    eprintln!("{name}: {} paths, {} stream scalars", paths.len(), proof.stream.len());
    out
}

#[test]
#[ignore = "review experiment; run with --ignored"]
fn review_vectors() {
    let log_rows = 22;
    let circuit = membership();
    assert_eq!(circuit.log_rows, log_rows);
    let index = Index::new(&circuit);
    let layout = wiring_layout(log_rows);
    assert_eq!(index.table.layout, layout);
    let committed = opening::commit(&index.table);
    let mut rng = Rng::new(0xF0F2F4);
    let point = rng.ext_vec(layout.vars);
    let claims = vec![Claim {
        value: index.table.eval(&point),
        point,
    }];
    let proof = opening::open(&index.table, &committed, &claims);
    let m = layout.vars;
    let head = line("new", [m, m, m, 0, 1 << m].map(|n| n as u64));
    let mut out = vector("wiring22", head, &layout, &committed.root, &claims, &proof);

    // Generic tamperings, each with the Rust verdict; the Lean side applies the same edit.
    let wire = opening::wire_proof(&proof);
    let rust = |claims: &[Claim], stream: Option<Vec<E>>| -> bool {
        let mut w = wire.clone();
        if let Some(s) = stream {
            w.stream = s;
        }
        opening::verify(&layout, &committed.root, claims, &w).is_ok()
    };
    let mut verdict = |name: &str, ok: bool| {
        eprintln!("variant {name}: rust accepts = {ok}");
        out += &line(&format!("variant {name}"), [ok as u64]);
    };
    verdict("honest", rust(&claims, None));
    verdict("dupclaim", rust(&[claims[0].clone(), claims[0].clone()], None));
    verdict("noclaims", rust(&[], None));
    let mut long = claims[0].clone();
    long.point.push(F192::ZERO);
    verdict("longpoint", rust(&[long], None));
    let mut s = wire.stream.clone();
    s.push(E::new(0, 0, 0));
    verdict("trailing", rust(&claims, Some(s)));
    let mut s = wire.stream.clone();
    s[0] = E::new(s[0].c0, s[0].c1, 1);
    verdict("rootc2", rust(&claims, Some(s)));
    let mut s = wire.stream.clone();
    s.swap(0, 1);
    verdict("swaproot", rust(&claims, Some(s)));
    let mut s = wire.stream.clone();
    s.pop();
    verdict("truncated", rust(&claims, Some(s)));
    out += "end\n";

    let file = std::env::var("REVIEW_VECTOR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/review_f0f2f4_vector.txt").to_string());
    std::fs::write(&file, out).expect("the vectors are written");
    eprintln!("{file}");
}
