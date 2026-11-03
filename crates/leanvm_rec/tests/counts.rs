// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Milestone R1 (SPEC-REC.md §1): the inner verifier's graph on real proofs, and its counts.
//!
//! - `the_graph_is_the_verifier_on_real_proofs`: the recorded graph, evaluated on each committed real proof
//!   (`crates/leanvm_univariate/tests/vectors/`, 1,000 signatures, π1-rec's `main_line_rec` among them), writes exactly
//!   the `PCS_OPEN` inputs the contract wrote, and its checks hold: the evaluator is the witness generator's core.
//! - `pi1_rec_is_record_derived`: π1-rec in code (`FLOCK_REC`, `FsShape::Rec`) records exactly the graph
//!   [`leanvm_rec::fs::record_derived`] states, with 80 Keccak-256 calls and 107 Keccak-f permutations.
//! - `count_report` (ignored): the table of SPEC-REC.md §1, over the inner verifier's variants.
//!
//! `cargo test --release -p leanvm_rec --test counts -- --include-ignored --nocapture`

#[path = "../../leanvm_univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_flock_gas::evm::record::Node;
use leanvm_flock_gas::flock_min::{Slices, Variant};
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_flock_gas::transcript::{FsShape, keccak_seed};
use leanvm_rec::count::{Counts, count, shared};
use leanvm_rec::eval::{call_inputs, checks, evaluate};
use leanvm_rec::{REFERENCE, permutations};
use leanvm_univariate::contract::{NAME, Recorded, SetupRoots, calls, contract_iv, record_verifier};
use leanvm_univariate::{Blake2s, Claims, FLOCK_LEANVM_SKIP, FLOCK_MAIN, FLOCK_REC};

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

const STREAM_AT: usize = 4 + 32;

fn vector(name: &str) -> vectors::Vector {
    let path = format!(
        "{}/../leanvm_univariate/tests/vectors/{name}.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    vectors::read(&std::fs::read_to_string(&path).expect("a committed vector"))
}

#[test]
fn the_graph_is_the_verifier_on_real_proofs() {
    deep(|| {
        for name in ["main_line", "main_line_rec", "leanvm_skip", "omitted", "ext_b"] {
            let v = vector(name);
            let blake2s = vectors::blake2s_of(&v.config);
            let recorded = record_verifier(&v.shape, blake2s, Claims::Point);
            let stream = &v.calldata[STREAM_AT..];
            assert_eq!(stream.len(), recorded.stream_len);
            let seed = keccak_seed(
                &NAME,
                &contract_iv(&v.shape, &PROGRAM_IV, &SetupRoots::REFERENCE),
                &v.public,
            );
            let values = evaluate(&recorded.graph, seed, &v.public, stream);
            let inputs = call_inputs(&recorded, &values, stream);
            assert_eq!(
                inputs, v.calls,
                "{name}: the evaluated graph writes the recorded PCS_OPEN inputs"
            );
            let (zero, nonzero) = checks(&recorded.graph, &values);
            assert!(
                zero.iter().all(|x| *x == Default::default()),
                "{name}: every zero check holds"
            );
            assert!(
                nonzero.iter().all(|x| *x != Default::default()),
                "{name}: every nonzero check holds"
            );
            // A flipped byte of the stream changes some call's input or breaks a check.
            let mut mutated = stream.to_vec();
            mutated[stream.len() / 2] ^= 1;
            let values = evaluate(&recorded.graph, seed, &v.public, &mutated);
            let (zero, _) = checks(&recorded.graph, &values);
            let broken =
                call_inputs(&recorded, &values, &mutated) != v.calls || zero.iter().any(|x| *x != Default::default());
            assert!(broken, "{name}: a mutated stream is caught");
            println!(
                "{name}: {} nodes evaluated, {} calls equal to the vector's, {} zero and {} nonzero checks hold",
                values.len(),
                inputs.len(),
                recorded.graph.zero.len(),
                recorded.graph.nonzero.len()
            );
        }
    });
}

/// π1-rec in code records the graph `fs::record_derived` states (SPEC-REC.md §1.4, R2 step 1): the main line's
/// verifier with `α_2..α_4` and Flock's zerocheck coordinates 2..22 the squares of the ones before, through the
/// [`leanvm_rec::fs::Derived`] channel, against `reduce` with `FsShape::Rec` on the plain recorder. Node for node, with
/// the same phases, checks, ring kernels, `PCS_OPEN` words, stream and reads; at skip 3 (`FLOCK_REC`) and skip 6.
#[test]
fn pi1_rec_is_record_derived() {
    deep(|| {
        for (skip, hashes, perms) in [(3, 80, 107), (6, 77, 114)] {
            let main = Variant {
                skip,
                slices: Slices::Tower,
                fs: FsShape::Main,
            };
            let rec = Variant { fs: FsShape::Rec, ..main };
            if skip == 3 {
                assert_eq!((main, rec), (FLOCK_MAIN, FLOCK_REC), "the main line and pi1-rec");
            }
            let derived = leanvm_rec::fs::pi1_rec_derived(32, skip);
            let (stated, hashed) =
                leanvm_rec::fs::record_derived(&REFERENCE, Blake2s::Flock(main), Claims::Point, derived.clone());
            let real = record_verifier(&REFERENCE, Blake2s::Flock(rec), Claims::Point);
            let (a, b) = (&stated.graph, &real.graph);
            assert_eq!(a.nodes.len(), b.nodes.len(), "skip {skip}: the node count");
            if let Some(i) = (0..a.nodes.len()).find(|&i| a.nodes[i] != b.nodes[i]) {
                panic!("skip {skip}: node {i} differs: stated {:?}, real {:?}", a.nodes[i], b.nodes[i]);
            }
            assert_eq!(a.phases, b.phases, "skip {skip}: every node's phase");
            assert_eq!(a.zero, b.zero, "skip {skip}: the zero checks");
            assert_eq!(a.nonzero, b.nonzero, "skip {skip}: the nonzero checks");
            assert_eq!(a.kernels, b.kernels, "skip {skip}: the ring kernels");
            assert_eq!(
                format!("{:?}", calls(&stated)),
                format!("{:?}", calls(&real)),
                "skip {skip}: the PCS_OPEN calls' words"
            );
            assert_eq!(stated.stream_len, real.stream_len, "skip {skip}: the stream");
            assert_eq!(stated.roots_at, real.roots_at, "skip {skip}: the roots' offsets");
            assert_eq!(stated.reads, real.reads, "skip {skip}: the reads by phase");
            // The main line's stream and claims are pi1-rec's.
            let line = record_verifier(&REFERENCE, Blake2s::Flock(main), Claims::Point);
            assert_eq!(line.stream_len, real.stream_len, "skip {skip}: the main line's stream length");
            assert_eq!(line.roots_at, real.roots_at, "skip {skip}: the main line's roots");
            let counts = count(&real);
            assert_eq!(counts.challenges, hashed, "skip {skip}: one challenge node a hashed draw");
            assert_eq!(counts.hash_lengths.len(), hashes, "skip {skip}: Keccak-256 calls, seed included");
            assert_eq!(counts.permutations, perms, "skip {skip}: Keccak-f permutations");
            let main_counts = count(&line);
            println!(
                "skip {skip}: pi1-rec in code = record_derived ({} nodes; {} derived): {} Keccak-256 calls, {} Keccak-f \
                 (main line {}, {}); squares {} (main line {})",
                b.nodes.len(),
                derived.len(),
                counts.hash_lengths.len(),
                counts.permutations,
                main_counts.hash_lengths.len(),
                main_counts.permutations,
                counts.total_ops.squares,
                main_counts.total_ops.squares,
            );
        }
    });
}

struct Config {
    name: String,
    blake2s: Blake2s,
}

fn configs() -> Vec<Config> {
    let mut out = vec![
        Config {
            name: "main line (skip 3, tower)".into(),
            blake2s: Blake2s::Flock(FLOCK_MAIN),
        },
        Config {
            name: "leanVM skip (skip 6, weighted)".into(),
            blake2s: Blake2s::Flock(FLOCK_LEANVM_SKIP),
        },
    ];
    for skip in [6, 5, 4] {
        out.push(Config {
            name: format!("skip {skip}, tower"),
            blake2s: Blake2s::Flock(Variant {
                skip,
                slices: Slices::Tower,
                fs: FsShape::Main,
            }),
        });
    }
    out.push(Config {
        name: "BLAKE2s omitted (scale)".into(),
        blake2s: Blake2s::Omitted,
    });
    out
}

fn print_counts(name: &str, recorded: &Recorded, c: &Counts) {
    let graph = &recorded.graph;
    println!("\n### {name}");
    println!(
        "nodes {} (live {}), constants {}, statement words {}",
        c.nodes, c.live, c.consts, c.statement
    );
    println!(
        "stream {} B (hashed {} B); live reads: {} scalars, {} root halves, {} integers; {} live reads never hashed",
        c.stream_bytes, c.hashed_stream_bytes, c.scalars, c.halves, c.integers, c.unhashed_live_reads
    );
    let by: Vec<String> = c
        .hashes_by_permutations()
        .iter()
        .map(|(p, n)| format!("{n} of {p} perm"))
        .collect();
    let bytes: usize = c.hash_lengths.iter().sum();
    println!(
        "Keccak-256 calls {} ({} B hashed, longest {} B): {} Keccak-f permutations [{}]; challenges {}",
        c.hash_lengths.len(),
        bytes,
        c.hash_lengths.iter().max().unwrap_or(&0),
        c.permutations,
        by.join(", "),
        c.challenges
    );
    let o = &c.ops;
    println!(
        "graph ops: products {} (x*y {}, squares {}), linear {} (adds {}, +const {}, *const {})",
        o.products(),
        o.muls,
        o.squares,
        o.linear(),
        o.adds,
        o.add_const,
        o.mul_const
    );
    let k = &c.kernel_ops;
    println!(
        "ring kernels {}: products {} (x*y {}, squares {}), linear {} (adds {}, +const {}, *const {})",
        c.kernels,
        k.products(),
        k.muls,
        k.squares,
        k.linear(),
        k.adds,
        k.add_const,
        k.mul_const
    );
    let t = &c.total_ops;
    println!(
        "TOTAL E ops (kernels expanded): products {} (x*y {}, squares {}), linear {} (adds {}, +const {}, *const {})",
        t.products(),
        t.muls,
        t.squares,
        t.linear(),
        t.adds,
        t.add_const,
        t.mul_const
    );
    println!(
        "bit fields {}, zero checks {}, nonzero checks {}",
        c.bits, c.zero_checks, c.nonzero_checks
    );
    println!(
        "claims {}: distinct points {}, coordinates {} in all, {} distinct non-constant",
        c.claims.len(),
        c.distinct_points(),
        c.coordinates(),
        c.distinct_coordinates(graph)
    );
    for claim in &c.claims {
        let consts = claim
            .point
            .iter()
            .filter(|&&id| matches!(graph.nodes[id as usize], Node::Const(_)))
            .count();
        let (prefix, anywhere) = shared(&c.claims[0].point, &claim.point);
        println!(
            "  {}: {} coordinates ({} constant), shares a prefix of {} with {}'s point ({} of its coordinates anywhere in it)",
            claim.name,
            claim.point.len(),
            consts,
            prefix,
            c.claims[0].name,
            anywhere
        );
    }
    if c.claims.len() > 3 {
        let (prefix, anywhere) = shared(&c.claims[3].point, &c.claims[0].point);
        println!(
            "  {}'s point in {}'s: prefix {}, anywhere {}",
            c.claims[0].name, c.claims[3].name, prefix, anywhere
        );
    }
    // The packings pi2 needs: every live read and every challenge between bytes and E.
    let pack_bits = 192 * c.scalars + 128 * c.halves + 32 * c.integers + 192 * c.challenges;
    println!(
        "packings: {} reads + {} challenges = {} E cells from {} bits; {} stream bits + {} state bits absorbed",
        c.scalars + c.halves + c.integers,
        c.challenges,
        c.scalars + c.halves + c.integers + c.challenges,
        pack_bits,
        8 * c.hashed_stream_bytes,
        256 * (c.hash_lengths.len() - 1)
    );
}

#[test]
#[ignore]
fn count_report() {
    deep(|| {
        println!("## pi1's verifier graph at the reference shape (1,000 signatures), Claims::Point");
        println!("Keccak-256 of the seed: {} perm (80 B)", permutations(80));
        for config in configs() {
            let recorded = record_verifier(&REFERENCE, config.blake2s, Claims::Point);
            let counts = count(&recorded);
            print_counts(&config.name, &recorded, &counts);
        }
        // pi1-rec: the main line with alpha_2..4 and Flock's zerocheck eq point derived as squares (SPEC-REC.md §1.3).
        for (name, skip) in [
            ("pi1-rec: main line, alpha and the zerocheck point derived", 3),
            ("pi1-rec at skip 6, tower", 6),
        ] {
            let blake2s = Blake2s::Flock(Variant {
                skip,
                slices: Slices::Tower,
                fs: FsShape::Main,
            });
            let (recorded, hashed) = leanvm_rec::fs::record_derived(
                &REFERENCE,
                blake2s,
                Claims::Point,
                leanvm_rec::fs::pi1_rec_derived(32, skip),
            );
            let counts = count(&recorded);
            print_counts(name, &recorded, &counts);
            let derived = leanvm_rec::fs::pi1_rec_derived(32, skip).len();
            assert_eq!(counts.challenges, hashed, "one challenge node a hashed draw");
            println!("  (challenges hashed: {hashed}; derived as squares: {derived})");
        }
        // Weighted mode (extension W) for comparison: no batching sumcheck; its claims are not ABI point claims.
        let recorded = record_verifier(&REFERENCE, Blake2s::Flock(FLOCK_MAIN), Claims::Weighted);
        let counts = count(&recorded);
        print_counts(
            "main line, Claims::Weighted (not the ABI; for scale)",
            &recorded,
            &counts,
        );
    });
}

/// The transcript's shape: the challenges' hashes in order, run-length encoded by the stream bytes each absorbs
/// (besides the 32-byte state), and the stream's bytes by the phase that reads them.
#[test]
#[ignore]
fn transcript_shape() {
    deep(|| {
        for config in configs().into_iter().take(2) {
            let recorded = record_verifier(&REFERENCE, config.blake2s, Claims::Point);
            let graph = &recorded.graph;
            println!("\n### {}: the challenges in order", config.name);
            let mut runs: Vec<(u32, usize)> = Vec::new();
            for node in &graph.nodes {
                if let Node::Hash(_, from, to) = *node {
                    match runs.last_mut() {
                        Some((bytes, n)) if *bytes == to - from => *n += 1,
                        _ => runs.push((to - from, 1)),
                    }
                }
            }
            let line: Vec<String> = runs.iter().map(|(b, n)| format!("{n}x{b}B")).collect();
            println!("  {}", line.join(" "));
            for (phase, bytes) in &recorded.reads {
                println!("  read {bytes:>5} B  [{phase}]");
            }
        }
    });
}
