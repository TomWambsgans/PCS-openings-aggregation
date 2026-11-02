// Part of this repository (written by an adversarial review of `formal/WhirBridge` (F2) and
// `formal/QuotientSecurity/Hiding` (F3)). MIT OR Apache-2.0; see NOTICE.md.
//! What the two Lean layers are about, checked against the deployed Rust.
//!
//! (The F2 finding below is fixed: `formal/WhirBridge` now mirrors every field of `Layout` and both branches of
//! `verify`'s weight, builds the protocol's layouts with `Layout.hidden`, and `whir_bridge_vector.rs` writes deployed
//! witness and quotient openings that `Test/Check.lean` accepts. `bridge_layouts` here is the bridge before the fix.)
//!
//! * F2: the bridge's `WhirBridge.Layout` is `Layout::new`'s public layout, and its `witnessLayout` /
//!   `quotientLayout` (`formal/WhirBridge/WhirBridge/Sound.lean:171-196`) are the pre-hiding layouts. The
//!   deployed witness and quotient openings use `Layout::hidden` (`protocol.rs:116-129`): a proof of the deployed
//!   witness opening is rejected by the check the bridge transcribes.
//! * F3: the facts `formal/QuotientSecurity/Hiding` takes from the design (the random lanes its (S) patterns
//!   name, the lane counts behind `64(L-3)`, the overflow lane's room) hold of `Layout::hidden` at every
//!   supported size; the padding the Lean theorems draw uniformly is a function of 32 bytes.
//!
//! `cargo test --release -p quotient --test review_f2f3`; with `REVIEW_F2_VECTOR=<file>`,
//! `f2_deployed_openings_are_not_the_bridge_check` also
//! writes the deployed witness opening in the form `formal/WhirBridge/Test/Check.lean` reads, laid out as the
//! bridge's `witnessLayout 17`:
//! `cd formal/WhirBridge && lake env lean --run Test/Check.lean <file>` prints `honest proof accepted: false`;
//! with `REVIEW_F2_HIDDEN_VECTOR=<file>`, the same proof with the deployed layout, which
//! `lake env lean --run ../Review/HiddenWeight.lean <file>` (the hidden branch of `verify`'s closure in Lean,
//! with mumbai's `verifyWhir`) accepts. `REVIEW_F2_Q_VECTOR` and `REVIEW_F2_Q_HIDDEN_VECTOR` do the same for a
//! deployed quotient opening (two claims, `quotient_layout(17)`).

use primitives::field::{F64, F192};
use primitives::test_rng::Rng;
use quotient::opening::{self, Claim, LOG_PIECE, Lane, Layout, Table};
use quotient::protocol::{MAX_LOG_ROWS, MIN_LOG_ROWS, quotient_layout, wiring_layout, witness_layout};
use verifier::{Digest, E, Transcript};

/// `WhirBridge.quotientChunks` (`Sound.lean:185-190`), transcribed: `Q_SPILL = 9216 + 64`, the gate quotient's
/// tail `64`.
fn bridge_quotient_chunks(m: usize) -> Vec<(usize, usize)> {
    let n = 1usize << m;
    let mut chunks = vec![];
    for e in 0..3 {
        chunks.push((16 * e, n));
        chunks.extend((0..3).map(|digit| (16 * e + 4 + digit, n)));
        chunks.push((16 * e + 7, 9216 + 64));
    }
    chunks.push((8, n));
    chunks.push((9, 3 * n / 4 + 64));
    chunks
}

/// The bridge's `witnessLayout`, `wiringLayout`, `quotientLayout` (`Sound.lean:171-196`): all `Layout.new`.
fn bridge_layouts(log_rows: usize) -> (Layout, Layout, Layout) {
    let m = log_rows + 2;
    (
        Layout::new(m + 1, m, m + 1, &[(0, 1 << m), (1, 16)]),
        Layout::new(m, m, m, &[(0, 1 << m)]),
        Layout::new(m + 6, m, m + 4, &bridge_quotient_chunks(m)),
    )
}

fn random_lanes(layout: &Layout) -> Vec<usize> {
    (0..layout.lanes())
        .filter(|&l| layout.lane(l) == Lane::Random)
        .collect()
}

/// F2: the bridge's wiring layout is the deployed one; its witness and quotient layouts are not (33 and 59
/// block lanes against the deployed 40 and 63 hidden lanes). The stacks' sizes agree, so the certified codes
/// and list bounds (which depend on `log_n` only) are the right ones; the table meaning is not.
#[test]
fn f2_bridge_layouts_are_the_pre_hiding_ones() {
    for log_rows in MIN_LOG_ROWS..=MAX_LOG_ROWS {
        let (w, wi, q) = bridge_layouts(log_rows);
        assert_eq!(wiring_layout(log_rows), wi);
        let (dw, dq) = (witness_layout(log_rows), quotient_layout(log_rows));
        assert_eq!((w.log_n, q.log_n), (dw.log_n, dq.log_n));
        assert_eq!((w.lanes(), q.lanes()), (33, 59));
        assert_eq!((dw.lanes(), dq.lanes()), (40, 63));
        assert_ne!(dw, w);
        assert_ne!(dq, q);
        assert_eq!((w.log_piece(), dw.log_piece()), (None, Some(LOG_PIECE)));
        assert_eq!((q.log_piece(), dq.log_piece()), (None, Some(LOG_PIECE)));
    }
}

fn pseudo(i: usize) -> F64 {
    F64(((i as u64) + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(17))
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

fn words(bytes: &[u8; 32]) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().expect("8 bytes")))
}

fn limbs(x: &F192) -> [u64; 3] {
    [x.c0, x.c1, x.c2]
}

/// A deployed opening: a table of `layout` (every entry the layout holds pseudo-random), `claims` claims at random
/// points, committed and opened by the real prover, accepted by `opening::verify` with `layout`.
fn deployed_opening(
    layout: &Layout,
    claims: usize,
    seed: u64,
) -> (
    opening::Committed,
    Vec<Claim>,
    fiat_shamir::transcript::Proof,
    verifier::Proof,
) {
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
    let wire = opening::wire_proof(&proof);
    assert_eq!(opening::verify(layout, &committed.root, &claims, &wire), Ok(()));
    (committed, claims, proof, wire)
}

/// The vector of `whir_bridge_vector.rs` past its layout line: the root, the claims, the stream and one full
/// path per query (the replay of `opening::verify`'s calls, nothing checked).
fn vector_body(
    layout: &Layout,
    root: &[u8; 32],
    claims: &[Claim],
    proof: &fiat_shamir::transcript::Proof,
    wire: &verifier::Proof,
) -> String {
    let mut bytes = root.to_vec();
    for claim in claims {
        for x in claim.point.iter().chain([&claim.value]) {
            for limb in limbs(x) {
                bytes.extend_from_slice(&limb.to_le_bytes());
            }
        }
    }
    let iv = primitives::hash::hash(b"pcs-quotient-opening");
    let statement = primitives::hash::hash(&bytes);
    let mut transcript = Transcript::new(wire, Digest(iv), Digest(statement), false);
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
    let mut body = line("root", words(root));
    for claim in claims {
        body += &line("claim", claim.point.iter().chain([&claim.value]).flat_map(limbs));
    }
    body += &line("stream", proof.stream.iter().flat_map(limbs));
    for path in &paths {
        body += &line(
            "open",
            [path.leaf.len() as u64]
                .into_iter()
                .chain(path.leaf.iter().map(|k| k.0))
                .chain(path.siblings.iter().flat_map(words)),
        );
    }
    body
}

/// The head `formal/Review/HiddenWeight.lean` reads: the deployed layout, lane `l` coded `2b` (block `b`), `1`
/// (overflow), `3` (random), then the overflow lane's pieces.
fn hidden_head(layout: &Layout) -> String {
    let code = |l: usize| match layout.lane(l) {
        Lane::Block(b) => 2 * b as u64,
        Lane::Overflow => 1,
        Lane::Random => 3,
    };
    line(
        "hidden",
        [
            layout.vars as u64,
            layout.log_n as u64,
            LOG_PIECE as u64,
            layout.share().expect("a share lane") as u64,
            layout.lanes() as u64,
        ]
        .into_iter()
        .chain((0..layout.lanes()).map(code)),
    ) + &line("pieces", layout.pieces().iter().map(|&p| p as u64))
}

/// The head `formal/WhirBridge/Test/Check.lean` reads: a public layout's blocks.
fn plain_head(layout: &Layout) -> String {
    line(
        "layout",
        [layout.vars as u64, layout.log_n as u64, layout.lanes() as u64]
            .into_iter()
            .chain((0..layout.lanes()).map(|l| layout.block(l) as u64)),
    )
}

/// F2: a deployed witness opening and a deployed quotient opening (the real prover, `witness_layout(17)` and
/// `quotient_layout(17)`) are accepted by `opening::verify` with the deployed layouts and rejected by the same
/// function with the bridge's `witnessLayout 17` / `quotientLayout 17`, which is what `WhirBridge.openingCheck`
/// transcribes (`Test/Check.lean` runs the Lean check on the witness vector: rejected). So the bridge's
/// `openingCheck_eq`, `holds_iff`, `variant_sound_table` and `family_sound` are about another check than the one
/// `protocol::verify_openings` runs on the witness and quotient roots.
#[test]
fn f2_deployed_openings_are_not_the_bridge_check() {
    let log_rows = MIN_LOG_ROWS;
    let (bridge_w, _, bridge_q) = bridge_layouts(log_rows);
    let cases = [
        (
            witness_layout(log_rows),
            bridge_w,
            1,
            "REVIEW_F2_VECTOR",
            "REVIEW_F2_HIDDEN_VECTOR",
        ),
        (
            quotient_layout(log_rows),
            bridge_q,
            2,
            "REVIEW_F2_Q_VECTOR",
            "REVIEW_F2_Q_HIDDEN_VECTOR",
        ),
    ];
    for (k, (layout, bridge, claims, plain, hidden)) in cases.into_iter().enumerate() {
        let (committed, claims, proof, wire) = deployed_opening(&layout, claims, 0xF2 + k as u64);
        assert!(opening::verify(&bridge, &committed.root, &claims, &wire).is_err());
        let (plain, hidden) = (std::env::var(plain), std::env::var(hidden));
        if plain.is_err() && hidden.is_err() {
            continue;
        }
        let body = vector_body(&layout, &committed.root, &claims, &proof, &wire);
        if let Ok(file) = plain {
            std::fs::write(&file, plain_head(&bridge) + &body).expect("the vector is written");
        }
        if let Ok(file) = hidden {
            std::fs::write(&file, hidden_head(&layout) + &body).expect("the vector is written");
        }
    }
}

/// F3: what the Lean hiding layer takes from the design, at every supported size. The random lanes named by
/// `witness_lane_pattern` (`1, 7, 13, 25`) and `quotient_lane_pattern` (`1, 21, 11, 41`) are random lanes other
/// than the share; the lane counts behind `unopened_row_le`'s `64(L - 3)` are 40 and 63 (2368 and 3840 bits);
/// the overflow and share lanes are `L - 2` and `L - 1`; the overflow lane holds `33` and `167` pieces.
#[test]
fn f3_design_facts_hold_at_every_size() {
    for log_rows in MIN_LOG_ROWS..=MAX_LOG_ROWS {
        for (layout, lanes, random, pattern, pieces) in [
            (
                witness_layout(log_rows),
                40,
                vec![1, 7, 13, 19, 25, 31, 39],
                [1, 7, 13, 25],
                33,
            ),
            (
                quotient_layout(log_rows),
                63,
                vec![1, 11, 21, 31, 41, 51, 62],
                [1, 21, 11, 41],
                167,
            ),
        ] {
            assert_eq!(layout.lanes(), lanes);
            assert_eq!(random_lanes(&layout), random);
            assert_eq!((layout.overflow(), layout.share()), (Some(lanes - 2), Some(lanes - 1)));
            for l in pattern {
                assert_eq!(layout.lane(l), Lane::Random);
                assert_ne!(layout.share(), Some(l));
            }
            assert_eq!(layout.pieces().len(), pieces);
            assert!(pieces < 1 << (layout.log_lane() - LOG_PIECE));
            assert_eq!(64 * (lanes - 3), if lanes == 40 { 2368 } else { 3840 });
        }
    }
}

/// F3: the Lean theorems draw the padding uniformly from `ι → Y → K` (`hidden_view_evalDistEq`,
/// `hidden_prEvent_le_bound`, `unopened_row_le`: `$ᵗ (ι → Y → K)`). The prover's padding is ChaCha12 keyed by
/// Keccak-256 of a 32-byte seed (`opening.rs:347-354`, `protocol.rs:145-148`): one seed, one stack. At `2^17`
/// rows the witness stack's padding is 130,816 words (8.4 Mbit) drawn from the seed's 256 bits, and every
/// opened row is a function of the seed and the table, so an unbounded observer can test every seed. The
/// hiding the deployed prover gets is computational (ChaCha12 as a PRG), not the statistical closeness the Lean
/// theorems state for uniform padding.
#[test]
fn f3_padding_is_a_function_of_32_bytes() {
    let layout = witness_layout(MIN_LOG_ROWS);
    let entries = |start: usize, out: &mut [F64]| {
        out.iter_mut().enumerate().for_each(|(k, o)| *o = pseudo(start + k));
    };
    let a = Table::hidden(layout.clone(), &[9; 32], entries);
    let b = Table::hidden(layout.clone(), &[9; 32], entries);
    assert_eq!(a.stack, b.stack);
    let (lane, piece) = (1usize << layout.log_lane(), 1usize << LOG_PIECE);
    let held = layout.pieces().len();
    let padding = layout.lanes() * piece + random_lanes(&layout).len() * (lane - piece) + (lane - (held + 1) * piece);
    assert_eq!(padding, 130_816);
}
