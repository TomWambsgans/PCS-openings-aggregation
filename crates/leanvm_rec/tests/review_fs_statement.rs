// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Review (REVIEW-REC.md, attacks 4 and 6): π1's side of π2's statement.
//!
//! - `review_fs_graph_is_the_rust_verifier_on_random_streams`: the recorded π1-rec graph, evaluated
//!   (`eval::evaluate`), is π1-rec's Rust verifier (`rust_verifier_with`, `Checks::Collect`) on random streams and
//!   random public inputs, not only on the real proof: every opening's point and value, the matrices' claims and the
//!   13 zero checks, one for one. So the graph's control flow does not depend on the stream.
//! - `review_fs_stream_layout_and_checks`: every stream byte is read by exactly one input node; the reads never hashed
//!   are exactly the batch's five end values, each a `PCS_OPEN` element; the 13 zero checks are the six counts' two
//!   range checks and the batching sumcheck's terminal; the counts are the first 24 bytes, hashed with `C1`'s root.
//! - `review_fs_circuit_is_the_graph_on_a_random_stream` (ignored, about a minute, D32v): π2's circuit compiled on a
//!   random stream (out-of-range row counts among them), a random public input and a random IV: every digest and every
//!   live element's limbs are `eval::evaluate`'s on that stream (the counts' 4-byte big-endian bit fields included),
//!   the out-of-range counts make their zero ports fail and only those, and the IV reaches the circuit through `κ`
//!   alone (`σ` unchanged under another IV).
//!
//! `cargo test --release -p leanvm_rec --test review_fs_statement -- --include-ignored --nocapture --test-threads 1`

#[path = "../../leanvm_univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::evm::codegen::Word;
use leanvm_flock_gas::evm::record::Node;
use leanvm_flock_gas::field::K;
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_flock_gas::transcript::keccak_seed;
use leanvm_rec::circuit::compile::{Inputs, Layout, pi2};
use leanvm_rec::circuit::spec::{CallWord, Failure, Source};
use leanvm_rec::eval::{Value, checks, evaluate};
use leanvm_univariate::contract::{NAME, SetupRoots, calls, record_verifier, rust_verifier_with};
use leanvm_univariate::{Claims, Opening};

const STREAM_AT: usize = 4 + 32;

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn vector(name: &str) -> vectors::Vector {
    let path = format!(
        "{}/../leanvm_univariate/tests/vectors/{name}.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    vectors::read(&std::fs::read_to_string(&path).expect("a committed vector"))
}

fn next(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn random_bytes(len: usize, seed: &mut u64) -> Vec<u8> {
    (0..len).map(|_| (next(seed) >> 24) as u8).collect()
}

/// Random 32 bytes.
fn random32(seed: &mut u64) -> [u8; 32] {
    random_bytes(32, seed).try_into().expect("32 bytes")
}

#[test]
fn review_fs_graph_is_the_rust_verifier_on_random_streams() {
    deep(|| {
        let v = vector("main_line_rec");
        let blake2s = vectors::blake2s_of(&v.config);
        let recorded = record_verifier(&v.shape, blake2s, Claims::Point);
        let iv = recorded.iv(&PROGRAM_IV);
        let real = v.calldata[STREAM_AT..].to_vec();
        assert_eq!(real.len(), recorded.stream_len);
        let mut seed = 0x5eed_f00d_1234_9876u64;
        let mut cases: Vec<([u8; 32], Vec<u8>)> = vec![(v.public, real.clone())];
        for _ in 0..3 {
            cases.push((random32(&mut seed), random_bytes(real.len(), &mut seed)));
        }
        // The real proof with its tail (after the first 1,000 bytes) randomised, and with in-range counts kept.
        let mut tail = real.clone();
        let fresh = random_bytes(real.len() - 1000, &mut seed);
        tail[1000..].copy_from_slice(&fresh);
        cases.push((v.public, tail));
        for (case, (public, stream)) in cases.iter().enumerate() {
            let values = evaluate(&recorded.graph, keccak_seed(&NAME, &iv, public), public, stream);
            let e = |id: u32| values[id as usize].e();
            let (reduced, zero, nonzero) = rust_verifier_with(
                &v.shape,
                &PROGRAM_IV,
                &SetupRoots::REFERENCE,
                public,
                stream,
                blake2s,
                Claims::Point,
            )
            .expect("the stream's length");
            let (graph_zero, graph_nonzero) = checks(&recorded.graph, &values);
            assert_eq!(graph_zero, zero, "case {case}: the zero checks, one for one");
            assert_eq!(graph_nonzero, nonzero, "case {case}: the nonzero checks");
            assert_eq!(recorded.reduced.openings.len(), reduced.openings.len());
            let mut words = 0;
            for ((c_sym, o_sym), (c_e, o_e)) in recorded.reduced.openings.iter().zip(&reduced.openings) {
                assert_eq!(c_sym, c_e, "case {case}: the openings' order");
                let (
                    Opening::Point {
                        point: ps,
                        value: vs,
                        bit_slice: bs,
                    },
                    Opening::Point {
                        point: pe,
                        value: ve,
                        bit_slice: be,
                    },
                ) = (o_sym, o_e)
                else {
                    panic!("point claims")
                };
                assert!(bs.is_none() && be.is_none());
                assert_eq!(ps.len(), pe.len());
                for (s, x) in ps.iter().zip(pe) {
                    assert_eq!(e(s.0), *x, "case {case}: a coordinate of {c_sym:?}");
                }
                assert_eq!(e(vs.0), *ve, "case {case}: the value of {c_sym:?}");
                words += ps.len() + 1;
            }
            let (ms, me) = (
                recorded.reduced.matrices.as_ref().expect("A0, B0"),
                reduced.matrices.as_ref().expect("A0, B0"),
            );
            assert_eq!(ms.point.len(), me.point.len());
            for (s, x) in ms.point.iter().zip(&me.point) {
                assert_eq!(e(s.0), *x, "case {case}: a coordinate of A0, B0");
            }
            assert_eq!((e(ms.a.0), e(ms.b.0)), (me.a, me.b), "case {case}: a, b");
            let held = zero.iter().filter(|x| **x == Default::default()).count();
            println!(
                "case {case}: the graph is the Rust verifier ({} opening words, {} matrix coordinates, {} zero checks, {held} hold)",
                words,
                me.point.len(),
                zero.len()
            );
        }
    });
}

#[test]
fn review_fs_stream_layout_and_checks() {
    deep(|| {
        let v = vector("main_line_rec");
        let blake2s = vectors::blake2s_of(&v.config);
        let recorded = record_verifier(&v.shape, blake2s, Claims::Point);
        let g = &recorded.graph;
        let len = recorded.stream_len;

        // The 13 zero checks: two range checks per row count, then the batching sumcheck's terminal.
        let errors: Vec<VerifierError> = g.zero.iter().map(|&(_, e)| e).collect();
        println!("zero checks: {errors:?}; nonzero: {}", g.nonzero.len());
        assert_eq!(errors.len(), 13);
        assert!(errors[..12].iter().all(|&e| e == VerifierError::TableRows));
        assert_eq!(errors[12], VerifierError::StackBatchTerminal);
        assert!(g.nonzero.is_empty());

        // Every stream byte is read by exactly one input node.
        let mut cover = vec![0u32; len];
        let mut inputs: Vec<(u32, (usize, usize))> = Vec::new();
        for (id, node) in g.nodes.iter().enumerate() {
            if let Node::Input { offset, len } = *node {
                inputs.push((id as u32, (offset as usize, len as usize)));
                for c in &mut cover[offset as usize..offset as usize + len as usize] {
                    *c += 1;
                }
            }
        }
        assert!(cover.iter().all(|&c| c == 1), "every byte read once");
        // The counts: six 4-byte integers at bytes 0..24, then C1's root.
        let counts: Vec<(usize, usize)> = inputs.iter().filter(|(_, (_, l))| *l == 4).map(|&(_, r)| r).collect();
        assert_eq!(counts, (0..6).map(|k| (4 * k, 4)).collect::<Vec<_>>());
        assert_eq!(recorded.roots_at[0], 24);

        // Hashed bytes: every hash's run (each hash is live, as a later state or a challenge reads it).
        let mut hashed = vec![false; len];
        let mut runs = Vec::new();
        for node in &g.nodes {
            if let Node::Hash(_, from, to) = *node {
                hashed[from as usize..to as usize].fill(true);
                runs.push((from, to));
            }
        }
        assert_eq!(
            runs[0],
            (0, 56),
            "the counts and C1's root, absorbed by α's first challenge"
        );
        let never: Vec<(u32, (usize, usize))> = inputs
            .iter()
            .copied()
            .filter(|&(_, (o, l))| {
                let h = hashed[o..o + l].iter().filter(|&&b| b).count();
                assert!(h == 0 || h == l, "a read partly hashed at {o}");
                h == 0
            })
            .collect();
        println!(
            "reads never hashed: {:?}",
            never.iter().map(|(_, r)| *r).collect::<Vec<_>>()
        );
        assert_eq!(never.len(), 5, "the batch's five end values");
        assert!(never.iter().all(|&(_, (o, l))| l == 24 && o >= len - 120));
        // Each is an element of a PCS_OPEN call (a claim's value).
        let call_nodes: Vec<u32> = calls(&recorded)
            .concat()
            .iter()
            .filter_map(|w| match w {
                Word::Node(id) => Some(*id),
                _ => None,
            })
            .collect();
        for &(id, _) in &never {
            assert!(call_nodes.contains(&id), "a never-hashed read is a call's element");
        }
        // The statement's four words are read by the graph (the public lines of Q_W).
        let live = leanvm_rec::count::live(g, leanvm_rec::count::outputs(&recorded));
        for k in 0..4u8 {
            let id = g
                .nodes
                .iter()
                .position(|n| *n == Node::Statement(k))
                .expect("a statement word");
            println!("statement word {k}: node {id}, live {}", live[id]);
        }
        println!(
            "stream: {len} bytes, {} inputs, {} hashed, {} hashes",
            inputs.len(),
            hashed.iter().filter(|&&b| b).count(),
            runs.len()
        );
    });
}

#[test]
#[ignore]
fn review_fs_circuit_is_the_graph_on_a_random_stream() {
    deep(|| {
        let layout = match std::env::var("REVIEW_LAYOUT").as_deref() {
            Ok("d16v") => Layout::D16v,
            _ => Layout::D32v,
        };
        let v = vector("main_line_rec");
        let blake2s = vectors::blake2s_of(&v.config);
        let recorded = record_verifier(&v.shape, blake2s, Claims::Point);
        let heights = v.shape.heights();
        let mut seed = 0x0bad_c0de_5eed_0001u64;
        let mut stream = random_bytes(recorded.stream_len, &mut seed);
        // Counts: 0 at 2^(r+1) (a bit above r), 1 at 2^r + 1 (bit r and a low bit), 2 at exactly 2^r, the others below.
        let mut counts: Vec<u32> = heights.iter().map(|&r| (next(&mut seed) as u32) % (1 << r)).collect();
        counts[0] = 1 << (heights[0] + 1);
        counts[1] = (1 << heights[1]) + 1;
        counts[2] = 1 << heights[2];
        for (k, c) in counts.iter().enumerate() {
            stream[4 * k..4 * k + 4].copy_from_slice(&c.to_be_bytes());
        }
        let public = random32(&mut seed);
        // A random program IV, so a random contract IV (REVIEW-REC L2: the compiler derives it from `recorded`).
        let program_iv = random32(&mut seed);
        let c = pi2(
            &recorded,
            layout,
            &Inputs {
                program_iv,
                public,
                stream: &stream,
            },
        );
        let iv = c.pi1_iv;
        assert_eq!(iv, recorded.iv(&program_iv));
        let values = evaluate(&c.expanded, keccak_seed(&NAME, &iv, &public), &public, &stream);
        for (&id, digest) in &c.digests {
            let mut bytes = [0u8; 32];
            for (i, &d) in digest.iter().enumerate() {
                bytes[i / 8] |= (c.finished.words[d as usize].0 as u8) << (i % 8);
            }
            assert_eq!(Value::State(bytes), values[id as usize], "digest of node {id}");
        }
        let mut bit_fields = 0;
        for (&id, limbs) in &c.limbs {
            let x = values[id as usize].e();
            let words = limbs.map(|l| c.finished.words[l as usize]);
            assert_eq!(
                words,
                [K(x.c0), K(x.c1), K(x.c2)],
                "the limbs of node {id} ({:?})",
                c.expanded.nodes[id as usize]
            );
            bit_fields += matches!(c.expanded.nodes[id as usize], Node::Bits(..)) as usize;
        }
        println!(
            "{layout:?}, random stream: {} digests and {} elements ({bit_fields} bit fields) are the graph's",
            c.digests.len(),
            c.limbs.len()
        );
        // The range checks' values in the circuit: count 0 fails its high-bits check (2^(r+1)), count 1 its
        // "bit r, then no low bit" check (2^r + 1); count 2 (2^r) and the others hold both.
        let expected = [
            true, false, false, true, false, false, false, false, false, false, false, false,
        ];
        for (k, &(id, _)) in recorded.graph.zero[..12].iter().enumerate() {
            let limbs = c.limbs[&c.map[id as usize]].map(|l| c.finished.words[l as usize]);
            assert_eq!(
                limbs != [K(0); 3],
                expected[k],
                "count {}'s check {}: {limbs:?}",
                k / 2,
                k % 2
            );
        }
        // Every root and element a call of π1 takes is a port's (the statement once, 2 roots, 51 elements, 13 zeros).
        let circuit = &c.finished.circuit;
        let mut by_source = [0usize; 4];
        let (mut roots, mut elements) = (std::collections::BTreeSet::new(), std::collections::BTreeSet::new());
        for p in &circuit.ports {
            match p.source {
                Source::Statement => by_source[0] += 1,
                Source::Root(i) => {
                    by_source[1] += 1;
                    roots.insert(i);
                }
                Source::Element(i) => {
                    by_source[2] += 1;
                    elements.insert(i);
                }
                Source::Zero => by_source[3] += 1,
            }
        }
        println!("ports (statement, roots, elements, zeros): {by_source:?}");
        assert_eq!(by_source, [1, 2, 51, 13]);
        assert_eq!((roots.len(), elements.len()), (2, 51), "each once");
        for w in circuit.calls.iter().flatten() {
            match *w {
                CallWord::Root(i) => assert!(roots.contains(&i), "root {i} of a call is a port's"),
                CallWord::Element(i) => assert!(elements.contains(&i), "element {i} of a call is a port's"),
                CallWord::Const(_) => {}
            }
        }
        // So the circuit rejects at a zero port, the first one that fails: count 0's high bits.
        match circuit.check(&c.finished.witness, &c.public) {
            Err(Failure::Public { port, .. }) => {
                assert_eq!(circuit.ports[port as usize].source, Source::Zero);
                let first_zero = circuit
                    .ports
                    .iter()
                    .position(|p| p.source == Source::Zero)
                    .expect("zero ports");
                println!("rejected at port {port} (the first zero port is {first_zero})");
                assert_eq!(
                    port as usize, first_zero,
                    "count 0's high-bits check is the first zero port"
                );
            }
            other => panic!("expected a zero port to fail: {other:?}"),
        }
        // The IV is a constant of the setup: another IV changes κ, not σ.
        let (sigma, kappa) = (circuit.sigma.clone(), circuit.kappa.clone());
        drop(c);
        let other = pi2(
            &recorded,
            layout,
            &Inputs {
                program_iv: [0x77; 32],
                public,
                stream: &stream,
            },
        );
        assert_eq!(other.finished.circuit.sigma, sigma, "σ does not depend on the IV");
        assert_ne!(other.finished.circuit.kappa, kappa, "κ holds the IV's bits");
        let first: std::collections::BTreeSet<(u32, u64)> = kappa.iter().map(|&(i, k)| (i, k.0)).collect();
        let differ = other
            .finished
            .circuit
            .kappa
            .iter()
            .filter(|&&(i, k)| !first.contains(&(i, k.0)))
            .count();
        println!("another IV: σ the same, κ differs ({differ} entries not in the first κ)");
    });
}
