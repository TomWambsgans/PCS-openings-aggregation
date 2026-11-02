// Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The deployed openings are made as
// `review_f2f3.rs`'s `deployed_opening` makes them (this repository, commit 4d5dd40).
//! The test vectors for `formal/WhirBridge`, in the form leanerVM mumbai's Lean verifier reads (the scalar stream,
//! then one full Merkle path per query: the pruned batches expanded, as `Transcript::finish` returns them):
//!
//! * `public`: an opening of two claims on a public layout (the layout of `opening::tests`, lanes out of order and
//!   a gap, `placed` short of the stack);
//! * `witness` and `quotient`: openings of the deployed witness and quotient layouts at `2^17` rows (hidden,
//!   `40` and `63` lanes; one and two claims), by the real prover, every entry the layout holds pseudo-random;
//! * `layoutprefix`: the 76-byte prefix (`opening::prefix`, `pre` of `famSeed`) of each of the 18 layouts the
//!   protocol opens, `2^17` to `2^22` rows.
//!
//! Each vector names its layout by the constructor's arguments (`new` or `hidden`), which
//! `formal/WhirBridge/Test/Check.lean` rebuilds with the Lean `Layout.new` / `Layout.hidden`, and carries its
//! `prefix` line, which Check.lean recomputes (the layout's id is Keccak-256 of every field). The openings have
//! leanVM's transcript shape (`opening::iv`: the IV `keccak256(prefix ‖ claims)`, a zero public digest, the root as
//! the stream's first two scalars).
//!
//! Regenerate and check, from the repository root (one command each; also after a change of the layouts):
//!
//!   cargo test -p quotient --release --test whir_bridge_vector -- --ignored
//!   (cd formal/WhirBridge && lake env lean --run Test/Check.lean ../../target/whir_bridge_vector.txt)
//!
//! The first writes `target/whir_bridge_vector.txt` (or `$WHIR_BRIDGE_VECTOR`).

use primitives::field::{F64, F192};
use primitives::test_rng::Rng;
use quotient::opening::{self, Claim, Layout, Table};
use quotient::protocol::{MAX_LOG_ROWS, MIN_LOG_ROWS, quotient_layout, wiring_layout, witness_layout};
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

fn pseudo(i: usize) -> F64 {
    F64(((i as u64) + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(17))
}

/// A vector: its head (the layout's constructor), the prefix, the root, the claims, the stream and one full
/// path per query (the replay of `opening::verify`'s transcript and calls, nothing checked).
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
    let mut bytes = opening::prefix(layout).to_vec();
    for claim in claims {
        for x in claim.point.iter().chain([&claim.value]) {
            for limb in limbs(x) {
                bytes.extend_from_slice(&limb.to_le_bytes());
            }
        }
    }
    let iv = primitives::hash::hash(&bytes);
    assert_eq!(iv, opening::iv(layout, claims));
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
    out + "end\n"
}

/// `hidden vars log_chunk log_n random log_piece` then the chunks, as `Layout::hidden_with` takes them.
fn hidden_head(vars: usize, log_chunk: usize, log_n: usize, chunks: &[(usize, usize)], random: usize) -> String {
    line(
        "hidden",
        [vars, log_chunk, log_n, random, opening::LOG_PIECE]
            .into_iter()
            .chain(chunks.iter().flat_map(|&(c, l)| [c, l]))
            .map(|n| n as u64),
    )
}

/// A deployed opening (`review_f2f3.rs`, `deployed_opening`): a table of `layout`, every entry the layout holds
/// pseudo-random, `claims` claims at random points, committed and opened by the real prover.
fn deployed(name: &str, head: String, layout: Layout, claims: usize, seed: u64) -> String {
    let table = Table::hidden(layout.clone(), &[seed as u8; 32], |start, out| {
        out.iter_mut().enumerate().for_each(|(k, o)| *o = pseudo(start + k));
    });
    let mut rng = Rng::new(seed);
    let claims: Vec<Claim> = (0..claims)
        .map(|_| {
            let point = rng.ext_vec(layout.vars);
            Claim {
                value: table.eval(&point),
                point,
            }
        })
        .collect();
    let committed = opening::commit(&table);
    let proof = opening::open(&table, &committed, &claims);
    vector(name, head, &layout, &committed.root, &claims, &proof)
}

#[test]
#[ignore = "writes the vectors `formal/WhirBridge` checks; run with --ignored"]
fn whir_bridge_vector() {
    // A public layout: two claims, lanes out of order and a gap.
    let mut rng = Rng::new(0x0E);
    let (vars, log_chunk, log_n) = (18, 14, 16);
    let chunks = [(3, 1 << 14), (0, 3000), (9, 1 << 13)];
    let layout = Layout::new(vars, log_chunk, log_n, &chunks);
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
    let head = line(
        "new",
        [vars, log_chunk, log_n]
            .into_iter()
            .chain(chunks.iter().flat_map(|&(c, l)| [c, l]))
            .map(|n| n as u64),
    );
    let mut out = vector("public", head, &table.layout, &committed.root, &claims, &proof);

    // The deployed witness and quotient openings at `2^17` rows (`protocol.rs:116-129`, `m = 19`).
    let m = MIN_LOG_ROWS + 2;
    let witness_chunks = [(0, 1 << m), (1, 16)];
    let head = hidden_head(
        m + 1,
        m,
        m + 1,
        &witness_chunks,
        quotient::protocol::WITNESS_RANDOM_LANES,
    );
    assert_eq!(
        Layout::hidden(
            m + 1,
            m,
            m + 1,
            &witness_chunks,
            quotient::protocol::WITNESS_RANDOM_LANES
        ),
        witness_layout(MIN_LOG_ROWS)
    );
    out += &deployed("witness", head, witness_layout(MIN_LOG_ROWS), 1, 0xF2);
    let q = quotient_layout(MIN_LOG_ROWS);
    // `quotient_chunks` is private to the crate: the head carries the chunks the Lean `quotientChunks` builds,
    // checked here against the layout they make.
    let n = 1usize << m;
    let mut quotient_chunks = vec![];
    for e in 0..3 {
        quotient_chunks.push((16 * e, n));
        quotient_chunks.extend((0..3).map(|digit| (16 * e + 4 + digit, n)));
        quotient_chunks.push((16 * e + 7, 9216 + 64));
    }
    quotient_chunks.push((8, n));
    quotient_chunks.push((9, 3 * n / 4 + 64));
    assert_eq!(
        Layout::hidden(
            m + 6,
            m,
            m + 4,
            &quotient_chunks,
            quotient::protocol::QUOTIENT_RANDOM_LANES
        ),
        q
    );
    let head = hidden_head(
        m + 6,
        m,
        m + 4,
        &quotient_chunks,
        quotient::protocol::QUOTIENT_RANDOM_LANES,
    );
    out += &deployed("quotient", head, q, 2, 0xF3);

    // The prefixes of the 18 layouts the protocol opens.
    for log_rows in MIN_LOG_ROWS..=MAX_LOG_ROWS {
        for (code, layout) in [
            (0, witness_layout(log_rows)),
            (1, wiring_layout(log_rows)),
            (2, quotient_layout(log_rows)),
        ] {
            let pre = opening::prefix(&layout);
            assert_eq!(pre[28..60], opening::layout_id(&layout));
            out += &line(
                "layoutprefix",
                [code, log_rows as u64].into_iter().chain(pre.iter().map(|&b| b as u64)),
            );
        }
    }

    let file = std::env::var("WHIR_BRIDGE_VECTOR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/whir_bridge_vector.txt").to_string());
    std::fs::write(&file, out).expect("the vectors are written");
    eprintln!("{file}");
}

/// The prefix (`pre` of `famSeed`) of every layout the protocol opens, as hex, with the layout's id:
/// `cargo test -p quotient --release --test whir_bridge_vector -- --ignored --nocapture opening_prefixes`.
#[test]
#[ignore = "prints every layout's prefix; run with --ignored --nocapture"]
fn opening_prefixes() {
    let hex = |bytes: &[u8]| bytes.iter().map(|b| format!("{b:02x}")).collect::<String>();
    for log_rows in MIN_LOG_ROWS..=MAX_LOG_ROWS {
        for (name, layout) in [
            ("witness", witness_layout(log_rows)),
            ("wiring", wiring_layout(log_rows)),
            ("quotient", quotient_layout(log_rows)),
        ] {
            let pre = opening::prefix(&layout);
            assert_eq!(pre[28..60], opening::layout_id(&layout));
            println!(
                "{name:<8} 2^{log_rows} rows: log_n {}, {} lanes, id {}\n  pre {}",
                layout.log_n,
                layout.lanes(),
                hex(&pre[28..60]),
                hex(&pre)
            );
        }
    }
}
