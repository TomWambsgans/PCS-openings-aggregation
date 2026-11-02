// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The WHIR parameters `formal/WhirBridge/WhirBridge/LargeParams.lean` decides at the stack sizes `2^24 ..= 2^28`
//! (rate `1/2`), against the Rust:
//!
//! * the prover's configuration (`pcs::whir::config_for_rate`, the per-level eta search of `whir_config.rs`): the
//!   folds, rate exponents, queries, grinding bits, out-of-domain samples and residual, level by level;
//! * the verifier's tabulated query counts (`WHIR_QUERIES` of `crates/verifier/src/whir.rs`, read from its source:
//!   the table is private) and its ladder rule;
//! * the Lean `largeLadder` (decided equal to leanerVM mumbai's `Whir.ladder`, `ladder_large`), its certified
//!   level-0 lists `largeList` (`listHi_large`) and the opening's query count `largeQueries` (`largeQueries_eq`),
//!   copied below.
//!
//! With `--nocapture` it also prints each level's slack `eta` from the code's search and the level-0 Johnson list it
//! implies, `1 / (2 eta sqrt(rho))`, next to leanerVM's certified list (the code's search omits the fold group's
//! row-union factor `2^(l-1)`, so its lists are smaller; `review/whir_params.py`).
//!
//!   cargo test --release -p quotient --test whir_large_params -- --nocapture
//!   cargo test --release -p quotient --test whir_large_params -- --ignored --nocapture large_public_openings

use pcs::whir_config::WhirSecurityConfig;
use primitives::field::{F64, F192};
use primitives::test_rng::Rng;
use quotient::opening::{self, Claim, Layout, Table};

/// A ladder: per level `(fold, log_inv_rate, queries)`.
type Ladder = &'static [(usize, usize, usize)];

/// `largeLadder` (`LargeParams.lean`).
const LEAN_LADDERS: [(usize, Ladder); 5] = [
    (24, &[(6, 1, 224), (4, 4, 56), (4, 7, 32), (4, 10, 23), (4, 13, 17)]),
    (25, &[(6, 1, 224), (4, 4, 56), (4, 7, 32), (4, 10, 23), (4, 13, 17)]),
    (26, &[(6, 1, 224), (4, 4, 56), (4, 7, 32), (4, 10, 23), (4, 13, 18)]),
    (27, &[(6, 1, 225), (4, 4, 56), (4, 7, 32), (4, 10, 23), (4, 13, 18)]),
    (
        28,
        &[
            (6, 1, 225),
            (4, 4, 56),
            (4, 7, 32),
            (4, 10, 23),
            (4, 13, 18),
            (4, 16, 14),
        ],
    ),
];

/// `residual_large`: the variables left after the folds.
const LEAN_RESIDUAL: [usize; 5] = [2, 3, 4, 5, 2];

/// `largeList` (`listHi_large`): leanerVM's certified level-0 lists.
const LEAN_LIST: [usize; 5] = [9952, 7908, 6296, 4473, 3564];

/// `largeQueries` (`largeQueries_eq`): the opening's queries to the two oracles.
const LEAN_QO: [usize; 5] = [7183, 7546, 7928, 8318, 9018];

/// `QUERY_GRINDING_BITS` (`grinding_large`).
const LEAN_GRINDING: usize = 17;

/// Row `log_inv_rate - 1`, entry `log_n - 15` of `WHIR_QUERIES`, parsed from the verifier's source.
fn verifier_queries(log_inv_rate: usize, log_n: usize) -> Vec<usize> {
    let source = include_str!("../../verifier/src/whir.rs");
    let start = source.find("const WHIR_QUERIES").expect("WHIR_QUERIES in whir.rs");
    let row = source[start..].lines().nth(log_inv_rate).expect("a row per rate");
    let entries: Vec<Vec<usize>> = row
        .split("&[")
        .skip(1)
        .map(|e| {
            e.split(']')
                .next()
                .expect("an entry")
                .split(',')
                .map(|x| x.trim().parse().expect("a count"))
                .collect()
        })
        .collect();
    assert_eq!(entries.len(), 14, "14 stack sizes, 15 to 28");
    entries[log_n - 15].clone()
}

/// The verifier's ladder (`derive_config`, `whir.rs:34-60`): folds and rate exponents.
fn verifier_ladder(log_n: usize, log_inv_rate: usize) -> (Vec<usize>, Vec<usize>) {
    let (mut folds, mut rates, mut remaining) = (vec![6], vec![log_inv_rate], log_n - 6);
    while remaining > 5 {
        let reduction = if folds.len() == 1 { 3 } else { 1 };
        rates.push(rates[rates.len() - 1] + folds[folds.len() - 1] - reduction);
        let fold = remaining.min(4);
        remaining -= fold;
        folds.push(fold);
    }
    (folds, rates)
}

fn reduced_rate(log_inv_rate: usize, log_msg_cols: usize) -> f64 {
    ((log_msg_cols as f64).exp2() - 1.0) / ((log_msg_cols + log_inv_rate) as f64).exp2()
}

#[test]
fn whir_large_params_match_lean() {
    for (i, &(log_n, ladder)) in LEAN_LADDERS.iter().enumerate() {
        let folds: Vec<usize> = ladder.iter().map(|l| l.0).collect();
        let rates: Vec<usize> = ladder.iter().map(|l| l.1).collect();
        let queries: Vec<usize> = ladder.iter().map(|l| l.2).collect();

        // The prover's derived configuration.
        let cfg = pcs::whir::config_for_rate(log_n, 1).expect("a supported shape");
        let shapes = cfg.level_shapes(log_n);
        assert_eq!(shapes.ks, folds, "folds at log_n = {log_n}");
        assert_eq!(cfg.log_inv_rates, rates, "rates at log_n = {log_n}");
        assert_eq!(cfg.queries, queries, "queries at log_n = {log_n}");
        assert_eq!(
            cfg.grinding_bits,
            vec![LEAN_GRINDING; ladder.len()],
            "grinding at log_n = {log_n}"
        );
        let mut ood = vec![1; ladder.len()];
        ood[0] = 0;
        assert_eq!(
            cfg.ood_samples, ood,
            "out-of-domain samples at log_n = {log_n} (none at level 0)"
        );
        assert_eq!(shapes.yr_log_n, LEAN_RESIDUAL[i], "residual at log_n = {log_n}");

        // The verifier's table and ladder.
        assert_eq!(verifier_queries(1, log_n), queries, "WHIR_QUERIES at log_n = {log_n}");
        assert_eq!(
            verifier_ladder(log_n, 1),
            (folds.clone(), rates.clone()),
            "ladder at log_n = {log_n}"
        );

        // The code's own slack search, against the certified list.
        let sec = WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + pcs::LOG_PACKING, 1)
            .expect("a supported shape");
        let l0 = &sec.levels[0];
        let code_list = 1.0 / (2.0 * l0.eta * reduced_rate(l0.log_inv_rate, l0.log_msg_cols).sqrt());
        println!(
            "log_n = {log_n}: folds {folds:?}, rates {rates:?}, queries {queries:?}, grinding {LEAN_GRINDING}, \
             residual {}; level-0 list: code's search {:.1} (2^{:.2}, eta {:.6e}), certified {} (2^{:.2}); \
             QO {}",
            LEAN_RESIDUAL[i],
            code_list,
            code_list.log2(),
            l0.eta,
            LEAN_LIST[i],
            (LEAN_LIST[i] as f64).log2(),
            LEAN_QO[i],
        );
        for (j, level) in sec.levels.iter().enumerate() {
            let list = 1.0 / (2.0 * level.eta * reduced_rate(level.log_inv_rate, level.log_msg_cols).sqrt());
            println!(
                "   L{j}: msg 2^{} rate 1/2^{} fold {} queries {} ood {} eta {:.6e} list {:.1}",
                level.log_msg_cols, level.log_inv_rate, level.k, level.queries, level.ood_samples, level.eta, list
            );
        }
        assert!(
            code_list < LEAN_LIST[i] as f64,
            "the code's list is below the certified one"
        );
    }
}

/// A public layout of `(table, height)` chunks in a `2^log_n` stack, as a PIOP's: chunks of two lanes
/// (`log_chunk = log_lane + 1`) of a table of `log_n + 1` variables, `29` full ones (chunk `7` left out), then
/// one of a lane and five entries (two lanes), one of a third of a lane and one of a single entry (a lane each),
/// out of order: `62` lanes, `placed` short of the stack.
fn public_chunks(log_n: usize) -> (usize, usize, Vec<(usize, usize)>) {
    let log_lane = log_n - 6;
    let mut chunks: Vec<(usize, usize)> = (0..30).filter(|&c| c != 7).map(|c| (c, 2 << log_lane)).collect();
    chunks.extend([(40, (1 << log_lane) + 5), (33, (1 << log_lane) / 3), (7, 1)]);
    (log_n + 1, log_lane + 1, chunks)
}

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

/// The vector `formal/WhirBridge/Test/CheckLarge.lean` reads (as `whir_bridge_vector.rs` writes them, this
/// repository): the layout's constructor, the prefix, the root, the claims, the stream and one full path per query
/// (the replay of `opening::verify`'s transcript, nothing checked).
fn vector(
    name: &str,
    head: String,
    layout: &Layout,
    root: &[u8; 32],
    claims: &[Claim],
    proof: &fiat_shamir::transcript::Proof,
) -> String {
    let wire = &opening::wire_proof(proof);
    use verifier::{Digest, E, Transcript};
    let mut transcript = Transcript::new(
        wire,
        Digest(opening::iv(layout, claims)),
        Digest(opening::PUBLIC_DIGEST),
        false,
    );
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
    out + "end\n"
}

/// Public openings at `2^24 ..= 2^MAX` words (`WHIR_LARGE_MAX`, default 26; the prover's memory grows with the
/// stack): on the PIOP-like layout of `public_chunks`, the prover's proof of two claims verifies and a changed value
/// is rejected; each opening is written (`target/whir_large_vector.txt`, or `$WHIR_LARGE_VECTOR`) for
/// `formal/WhirBridge/Test/CheckLarge.lean`, which runs the Lean verifier on it.
#[test]
#[ignore = "heavy: commits and opens stacks of 2^24 words and more"]
fn large_public_openings() {
    let max: usize = std::env::var("WHIR_LARGE_MAX")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(26);
    let path = std::env::var("WHIR_LARGE_VECTOR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/whir_large_vector.txt").to_string());
    let mut out = String::new();
    let mut rng = Rng::new(0x1a7e);
    for log_n in 24..=max {
        let (vars, log_chunk, chunks) = public_chunks(log_n);
        let layout = Layout::new(vars, log_chunk, log_n, &chunks);
        let start = std::time::Instant::now();
        let log_lane = layout.log_lane();
        let table = Table::new(layout.clone(), |_, b, out: &mut [F64]| {
            for (k, x) in out.iter_mut().enumerate() {
                *x = F64((((b << log_lane) + k) as u64 + 1)
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
        let proved = start.elapsed();
        let root = committed.root;
        drop(table);
        let start = std::time::Instant::now();
        assert_eq!(
            opening::verify(&layout, &root, &claims, &wire),
            Ok(()),
            "log_n = {log_n}"
        );
        let verified = start.elapsed();
        let mut bad = claims.clone();
        bad[1].value += F192::ONE;
        assert!(
            opening::verify(&layout, &root, &bad, &wire).is_err(),
            "log_n = {log_n}: a wrong value"
        );
        let head = line(
            "new",
            [vars, log_chunk, log_n]
                .into_iter()
                .chain(chunks.iter().flat_map(|&(c, l)| [c, l]))
                .map(|n| n as u64),
        );
        out += &vector(&format!("public{log_n}"), head, &layout, &root, &claims, &proof);
        println!(
            "log_n = {log_n}: {} chunks, {} lanes, placed {} of 2^{log_n}; committed and opened in {:.1} s, \
             verified in {:.1} ms; a wrong value rejected",
            chunks.len(),
            layout.lanes(),
            layout.placed(),
            proved.as_secs_f64(),
            verified.as_secs_f64() * 1e3
        );
    }
    std::fs::write(&path, out).expect("write the vectors");
    println!("wrote {path}");
}
