// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π1-rec's graph as Lean data (`formal/RecGraph`, `leanvm_rec::lean`).
//!
//! - `graph_lean_is_current`: the checked-in `formal/RecGraph/RecGraph/Emitted.lean` is what `lean::render` writes for
//!   π1-rec's recorded verifier now; `UPDATE_LEAN=1` rewrites it.
//! - `lean_vectors` (ignored): `REC_VECTORS_OUT=<path>` writes the vectors of `formal/RecGraph`'s differential runner:
//!   the real 1,000-signature proof (`crates/leanvm_univariate/tests/vectors/main_line_rec.txt`), its stream with one
//!   byte flipped at several places, the real stream under other public inputs, and pseudo-random streams
//!   (`REC_VECTOR_COUNT` of them, default 16), each with the evaluated graph's `PCS_OPEN` inputs and checks and the Rust
//!   verifier's on `E`.
//!
//! `cargo test --release -p leanvm_rec --test lean_graph`

#[path = "../../leanvm_univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_rec::lean::{recorded, render, vector};
use leanvm_univariate::contract::sample_stream;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn graph_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../formal/RecGraph/RecGraph/Emitted.lean")
}

/// The checked-in Lean graph is π1-rec's recorded verifier: `UPDATE_LEAN=1` rewrites it.
#[test]
fn graph_lean_is_current() {
    let rendered = deep(|| render(&recorded()));
    let path = graph_path();
    if std::env::var_os("UPDATE_LEAN").is_some() {
        std::fs::write(&path, &rendered).expect("the Lean graph written");
        return;
    }
    let current = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(
        current == rendered,
        "{} is stale: run `UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_graph graph_lean_is_current`",
        path.display()
    );
}

/// The runner's vectors (`REC_VECTORS_OUT`).
#[test]
#[ignore]
fn lean_vectors() {
    let Ok(path) = std::env::var("REC_VECTORS_OUT") else {
        eprintln!("REC_VECTORS_OUT unset: nothing written");
        return;
    };
    let count: u64 = std::env::var("REC_VECTOR_COUNT").map_or(16, |n| n.parse().expect("a count"));
    let text = deep(move || {
        let recorded = recorded();
        let file = format!(
            "{}/../leanvm_univariate/tests/vectors/main_line_rec.txt",
            env!("CARGO_MANIFEST_DIR")
        );
        let real = vectors::read(&std::fs::read_to_string(&file).expect("the committed vector"));
        assert_eq!(real.config, "main_line_rec");
        let stream = real.calldata[4 + 32..].to_vec();
        let mut out = String::from(
            "# formal/RecGraph's differential vectors (crates/leanvm_rec/tests/lean_graph.rs): pi1-rec's graph at the reference shape\n",
        );
        out.push_str(&vector("real", &recorded, &real.public, &stream));
        let len = stream.len();
        // One byte flipped: in a row count, in C1's root, in Flock's messages, in the middle, at the end.
        for at in [3, 24, 30, 200, len / 2, len - 1] {
            let mut mutated = stream.clone();
            mutated[at] ^= 1;
            out.push_str(&vector(&format!("flip{at}"), &recorded, &real.public, &mutated));
        }
        // The real stream under other public inputs.
        for k in 0..2u8 {
            let mut public = real.public;
            public[(7 + 8 * k as usize) % 32] ^= 0x80;
            out.push_str(&vector(&format!("public{k}"), &recorded, &public, &stream));
        }
        // Pseudo-random streams and public inputs.
        for seed in 0..count {
            let random = sample_stream(len, 0x5ec0 + seed);
            let public: [u8; 32] = sample_stream(32, 0x9b1c + seed).try_into().expect("32 bytes");
            out.push_str(&vector(&format!("random{seed}"), &recorded, &public, &random));
        }
        out
    });
    std::fs::write(path, text).expect("the vectors written");
}
