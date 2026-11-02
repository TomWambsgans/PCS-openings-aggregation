// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
// The Rust half of the differential test of the Lean skeleton `QuotientZk.Deployed.skel`
// (`formal/QuotientZk/Deployed/Skeleton.lean`) against the prover; the Lean half is
// `formal/QuotientZk/Test/SkelTrace.lean` (executable `skeltrace`, `formal/lakefile.toml`).
//! The skeleton against the prover, operation by operation.
//!
//! The prover is run with every Keccak call recorded (`primitives::trace`, feature `skel-trace`, which turns on
//! test-only hooks in `primitives::hash` and `fiat_shamir`: no production build has them). The record is turned
//! into the skeleton's operations in the skeleton's order where the prover's is not fixed (a Merkle tree, built by
//! parallel tasks, is its leaves in order, then each level left to right), and grinding into its nonce: the
//! prover's tokens. The Lean driver runs `skel` on the same data (the statement, the shape this file derives from
//! WHIR's configuration, the secret tables' leaf digests, and the prover's messages, cut here from the prover's own
//! transcript at its draws) with Keccak-256 and Keccak-f[1600] as the oracle, and writes its operations and its
//! proof. This file then aligns the two token lists, explains each difference or fails, and compares the proofs.
//!
//! What is compared byte for byte: every Fiat–Shamir input (the reduction's chain, every duplex permutation and
//! draw, the seeds, the IVs), every tree (its size, its root, so every node), the grinding nonces, the streams, the
//! opened positions and the Merkle siblings. What is checked of the skeleton's shape: the messages' grammar
//! (`grammar`: what the skeleton reads after each draw) against the prover's scalars between its draws, at every
//! size; and `deployedShape` against the shape derived from the configuration at `2^22`.
//!
//! How to run (the `2^17` comparison; `SKEL_TRACE_DIR` defaults to `target/skel_trace`):
//!
//! ```text
//! cargo test --release -p quotient --features skel-trace --test skel_trace -- --nocapture
//! # copy $SKEL_TRACE_DIR/input_17.bin to the Lean side, then (formal/, after `lake build skeltrace`):
//! ulimit -s unlimited; .lake/build/bin/skeltrace input_17.bin lean_trace_17.txt lean_proof_17.txt > lean_out_17.txt
//! # copy the three outputs back to $SKEL_TRACE_DIR and run the test again: it now compares
//! cargo test --release -p quotient --features skel-trace --test skel_trace -- --nocapture
//! # 2^22 (heavy, a few GiB): the prover's structure against the derived shape, which the first run checks
//! # against `deployedShape`
//! cargo test --release -p quotient --features skel-trace --test skel_trace -- --ignored --nocapture
//! ```

#![cfg(feature = "skel-trace")]

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use fiat_shamir::merkle::{Hash, hash_to_scalars};
use fiat_shamir::transcript::Proof as WhirProof;
use pcs::whir::config_for_rate;
use primitives::field::{F64, F192};
use primitives::hash::{RATE, hash as keccak256};
use primitives::test_rng::Rng;
use primitives::trace::{self, Event, Mode, Record};
use quotient::circuit::{Builder, Circuit, Src, membership, membership_inputs, public_words};
use quotient::opening::{self, LOG_INV_RATE, Layout, PREFIX_LEN, layout_id, prefix};
use quotient::protocol::{Index, open, prove_with_seed, quotient_layout, wiring_layout, witness_layout};
use quotient::statement::{DEPTH, Secret, Statement, pair};

// ---------------------------------------------------------------------------------------------------------------
// Formatting

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(2 * bytes.len());
    for &b in bytes {
        s.push(DIGITS[(b >> 4) as usize] as char);
        s.push(DIGITS[(b & 15) as usize] as char);
    }
    s
}

fn hex_state(x: &[u64; 25]) -> String {
    x.iter().map(|w| format!("{w:016x}")).collect()
}

fn hex_limbs(x: &F192) -> String {
    format!("{:016x} {:016x} {:016x}", x.c0, x.c1, x.c2)
}

fn words_bytes(words: &[F64]) -> Vec<u8> {
    words.iter().flat_map(|w| w.0.to_le_bytes()).collect()
}

fn out_dir() -> PathBuf {
    let dir = std::env::var("SKEL_TRACE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target/skel_trace"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

// ---------------------------------------------------------------------------------------------------------------
// The shape: what `OpenShape` holds, derived from WHIR's configuration

/// An opening's shape, the fields of the skeleton's `OpenShape` (but the IV prefix and the rows).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Shape {
    log_n: usize,
    depth0: usize,
    depth1: usize,
    ood0: usize,
    levels: Vec<(usize, usize, usize)>,
    queries: Vec<usize>,
    last_folds: usize,
    residual: usize,
}

impl Shape {
    /// The derivation, from `recursive_prover`: level 0's codeword has `2^(n1 + rate_0)` leaves (`n1 = log_n -
    /// initial_k`); the first commitment, after the lane rounds, `2^(n1 - k_0 + rate_1)`; the level after fold
    /// `j` has `n_{j+2} = n1 - k_0 - .. - k_j` variables, a commitment of `2^(n_{j+2} - k_{j+1} + rate_{j+2})`
    /// leaves and an out-of-domain point of `n_{j+2}` coordinates; the residual is what the last fold leaves. Also
    /// what the skeleton fixes and the configuration must agree with: six lane rounds, one out-of-domain sample
    /// at every level but the first, 17 grinding bits at every level.
    fn derive(log_n: usize) -> (Shape, Vec<String>) {
        let c = config_for_rate(log_n, LOG_INV_RATE).expect("a supported size");
        let mut problems = vec![];
        let r = c.level_steps;
        if c.initial_k != 6 {
            problems.push(format!("initial_k = {} (the skeleton: 6 lane rounds)", c.initial_k));
        }
        if c.grinding_bits.iter().any(|&b| b != 17) {
            problems.push(format!("grinding bits {:?} (the skeleton: 17)", c.grinding_bits));
        }
        if c.ood_samples[0] != 0 || c.ood_samples[1..].iter().any(|&s| s != 1) {
            problems.push(format!(
                "OOD samples {:?} (the skeleton: one a level, none at level 0)",
                c.ood_samples
            ));
        }
        let n1 = log_n - c.initial_k;
        let mut n = n1;
        let mut levels = vec![];
        for j in 0..r - 1 {
            n -= c.level_ks[j];
            levels.push((c.level_ks[j], n - c.level_ks[j + 1] + c.log_inv_rates[j + 2], n));
        }
        let shape = Shape {
            log_n,
            depth0: n1 + c.log_inv_rates[0],
            depth1: n1 - c.level_ks[0] + c.log_inv_rates[1],
            ood0: n1,
            levels,
            queries: c.queries.clone(),
            last_folds: c.level_ks[r - 1],
            residual: n - c.level_ks[r - 1],
        };
        (shape, problems)
    }

    /// The depths of the trees an opening commits, level 0 first.
    fn depths(&self) -> Vec<usize> {
        [self.depth0, self.depth1]
            .into_iter()
            .chain(self.levels.iter().map(|l| l.1))
            .collect()
    }

    /// The Lean driver's `shapeLine`, without the IV prefix.
    fn line(&self, secret: &str) -> String {
        let levels: Vec<String> = self.levels.iter().map(|(a, b, c)| format!("{a},{b},{c}")).collect();
        let queries: Vec<String> = self.queries.iter().map(|q| q.to_string()).collect();
        format!(
            "secret={secret} depth0={} depth1={} ood0={} levels={} queries={} lastFolds={} residual={}",
            self.depth0,
            self.depth1,
            self.ood0,
            levels.join(";"),
            queries.join(","),
            self.last_folds,
            self.residual
        )
    }
}

const NAMES: [&str; 3] = ["witness", "wiring", "quotient"];
/// The skeleton's tables: the witness table `0`, the quotient table `1`, the wiring table public.
const SECRET: [&str; 3] = ["0", "none", "1"];

fn layouts(log_rows: usize) -> [Layout; 3] {
    [
        witness_layout(log_rows),
        wiring_layout(log_rows),
        quotient_layout(log_rows),
    ]
}

// ---------------------------------------------------------------------------------------------------------------
// The grammar: what the skeleton reads after each draw of an opening

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Slot {
    /// `sendK k`: `k` scalars sent and absorbed.
    S(usize),
    /// `commitNext`: a commitment's rows (its root absorbed).
    R,
    /// A multiproof's opened rows (not absorbed).
    O,
    /// Grinding: a nonce absorbed.
    G,
}

/// The skeleton's `opening`, read for what it absorbs and reads: before its first draw (the root of level 0),
/// and after each draw. Transcribed from `Skeleton.lean` (`opening`, `rounds`, `ood`, `queryPhase`, `middle`).
struct Grammar {
    pre: Vec<Slot>,
    msgs: Vec<Vec<Slot>>,
}

impl Grammar {
    fn draw(&mut self) {
        self.msgs.push(vec![]);
    }

    fn slot(&mut self, s: Slot) {
        match self.msgs.last_mut() {
            Some(m) => m.push(s),
            None => self.pre.push(s),
        }
    }

    fn rounds(&mut self, k: usize) {
        for _ in 0..k {
            self.draw();
            self.slot(Slot::S(2));
        }
    }

    fn ood(&mut self, m: usize) {
        for _ in 0..m {
            self.draw();
        }
        self.slot(Slot::S(3));
    }

    /// `queryPhase` on a tree of depth `b`: grind, the positions' draws (`192 / b` a draw), `λ`, the opened rows,
    /// the intro message.
    fn query(&mut self, b: usize, q: usize) {
        self.slot(Slot::G);
        let per = 192 / b.max(1);
        for _ in 0..q.div_ceil(per) {
            self.draw();
        }
        self.draw();
        self.slot(Slot::O);
        self.slot(Slot::S(2));
    }

    fn of(sh: &Shape) -> Grammar {
        let mut g = Grammar {
            pre: vec![],
            msgs: vec![],
        };
        let depths = sh.depths();
        g.slot(Slot::R);
        g.draw();
        g.slot(Slot::S(2));
        g.rounds(6);
        g.slot(Slot::R);
        g.ood(sh.ood0);
        g.query(depths[0], sh.queries[0]);
        for (j, &(folds, _, ood)) in sh.levels.iter().enumerate() {
            g.rounds(folds);
            g.slot(Slot::R);
            g.ood(ood);
            g.query(depths[j + 1], sh.queries[j + 1]);
        }
        g.rounds(sh.last_folds);
        g.slot(Slot::S(1 << sh.residual));
        g.query(depths[sh.levels.len() + 1], *sh.queries.last().unwrap());
        g.rounds(sh.residual - 1);
        g.draw();
        g
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The prover, recorded

struct Run {
    log_rows: usize,
    statement: Statement,
    index_root: Hash,
    stream: Vec<F192>,
    roots: [Hash; 2],
    openings: [WhirProof; 3],
    layouts: [Layout; 3],
    records: Vec<Record>,
}

/// A small circuit of the membership statement's shape (`protocol.rs`'s tests), in `2^log_rows` rows.
fn toy(log_rows: usize) -> Circuit {
    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
    b.finish(log_rows, &public_words(&x, &digest))
}

/// One record at a time: the recorder is global, and the tests of this file run on parallel threads.
static RECORDER: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn run_prover(log_rows: usize, mode: Mode) -> Run {
    let _one = RECORDER.lock().unwrap_or_else(|e| e.into_inner());
    let mut rng = Rng::new(0x5CE1 + log_rows as u64);
    // The deployed circuit at 2^22, the small one below.
    let (circuit, statement, inputs) = if log_rows < 22 {
        let circuit = toy(log_rows);
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
        let statement = Statement {
            y: x,
            root: pair(&x, &x),
        };
        let inputs: Vec<bool> = (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect();
        (circuit, statement, inputs)
    } else {
        let circuit = membership();
        let secret = Secret {
            x: std::array::from_fn(|_| rng.next_u8()),
            siblings: std::array::from_fn::<_, DEPTH, _>(|_| std::array::from_fn(|_| rng.next_u8())),
            directions: rng.next_u32(),
        };
        (circuit, secret.statement(), membership_inputs(&secret))
    };
    assert_eq!(circuit.log_rows, log_rows);
    let cells = circuit.cells(&inputs);
    let index = Index::new(&circuit);
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    // The index commitment is in the record: the skeleton builds the wiring table's tree too.
    trace::start(mode);
    let index_committed = opening::commit(&index.table);
    let proved = prove_with_seed(&circuit, &index, &index_committed.root, &statement, &cells, &seed);
    let stream = proved.proof.stream.clone();
    let roots = proved.roots;
    let openings = open(proved.tables, &proved.claims, &index, &index_committed);
    let records = trace::stop();
    Run {
        log_rows,
        statement,
        index_root: index_committed.root,
        stream,
        roots,
        openings: [openings.witness, openings.wiring, openings.quotient],
        layouts: layouts(log_rows),
        records,
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Trees

struct Tree {
    root: Hash,
    n_leaves: usize,
    /// Level 0's digests and images (full mode).
    leaves: Vec<Hash>,
    images: Vec<Vec<u8>>,
    /// The record that finished it.
    last: usize,
    /// A leaf's image: its length, and the zero blocks before the bytes hashed.
    leaf_len: usize,
    prefix_blocks: usize,
}

fn is_node(prefix_blocks: usize, len: usize) -> bool {
    prefix_blocks == 0 && len == 64
}

/// The trees of a full record: every node digest climbed down from each root (a digest no node takes as a child).
fn trees_full(records: &[Record]) -> Vec<Tree> {
    let mut nodes: HashMap<Hash, (Hash, Hash, usize)> = HashMap::new();
    let mut leaves: HashMap<Hash, (Vec<u8>, usize, usize, usize)> = HashMap::new();
    for (ri, r) in records.iter().enumerate() {
        if let Event::Many {
            prefix_blocks,
            len,
            n,
            data,
            out,
        } = &r.event
        {
            for i in 0..*n {
                let d: Hash = out[32 * i..32 * i + 32].try_into().unwrap();
                let input = &data[i * len..(i + 1) * len];
                if is_node(*prefix_blocks, *len) {
                    nodes.insert(
                        d,
                        (input[..32].try_into().unwrap(), input[32..].try_into().unwrap(), ri),
                    );
                } else {
                    let mut image = vec![0u8; prefix_blocks * RATE];
                    image.extend_from_slice(input);
                    leaves.insert(d, (image, ri, *len, *prefix_blocks));
                }
            }
        }
    }
    let children: HashSet<Hash> = nodes.values().flat_map(|(l, r, _)| [*l, *r]).collect();
    let mut trees = vec![];
    for (&root, _) in nodes.iter().filter(|(d, _)| !children.contains(*d)) {
        let mut levels = vec![vec![root]];
        let mut last = 0;
        loop {
            let top = levels.last().unwrap();
            if !top.iter().all(|d| nodes.contains_key(d)) {
                assert!(top.iter().all(|d| !nodes.contains_key(d)), "a tree of uneven depth");
                break;
            }
            let next: Vec<Hash> = top
                .iter()
                .flat_map(|d| {
                    let (l, r, ri) = nodes[d];
                    last = last.max(ri);
                    [l, r]
                })
                .collect();
            levels.push(next);
        }
        levels.reverse();
        let leaf_digests = levels[0].clone();
        let images: Vec<Vec<u8>> = leaf_digests
            .iter()
            .map(|d| {
                let (image, ri, _, _) = &leaves[d];
                last = last.max(*ri);
                image.clone()
            })
            .collect();
        let (_, _, leaf_len, prefix_blocks) = leaves[&leaf_digests[0]];
        trees.push(Tree {
            root,
            n_leaves: leaf_digests.len(),
            leaves: leaf_digests,
            images,
            last,
            leaf_len,
            prefix_blocks,
        });
    }
    trees.sort_by_key(|t| t.last);
    trees
}

/// The trees of a light record: each run of batched hashes between two other records, its root the last digest
/// of a batch of one.
fn trees_light(records: &[Record]) -> Vec<Tree> {
    let mut trees: Vec<Tree> = vec![];
    let mut open = false;
    for (ri, r) in records.iter().enumerate() {
        match &r.event {
            Event::Many {
                prefix_blocks,
                len,
                n,
                out,
                ..
            } => {
                if !open {
                    trees.push(Tree {
                        root: [0; 32],
                        n_leaves: 0,
                        leaves: vec![],
                        images: vec![],
                        last: ri,
                        leaf_len: 0,
                        prefix_blocks: 0,
                    });
                    open = true;
                }
                let t = trees.last_mut().unwrap();
                t.last = ri;
                if is_node(*prefix_blocks, *len) {
                    if *n == 1 {
                        t.root = out[..32].try_into().unwrap();
                    }
                } else {
                    t.n_leaves += n;
                    t.leaf_len = *len;
                    t.prefix_blocks = *prefix_blocks;
                }
            }
            _ => open = false,
        }
    }
    trees
}

// ---------------------------------------------------------------------------------------------------------------
// Tokens

#[derive(Clone, Debug)]
struct Tok {
    key: String,
    class: &'static str,
    info: String,
}

fn rate_scalars(x: &[u64; 25]) -> Vec<(F192, u64)> {
    (0..4)
        .map_while(|s| (x[4 * s + 3] != 0).then(|| (F192::new(x[4 * s], x[4 * s + 1], x[4 * s + 2]), x[4 * s + 3])))
        .collect()
}

fn is_grind_input(x: &[u64; 25]) -> bool {
    rate_scalars(x)
        .last()
        .is_some_and(|(s, tag)| *tag == 4 && s.c1 == 0 && s.c2 == 0)
}

const KC_TAG: &[u8] = b"pcs-quotient-kc1";
const OPENING_LABEL: &[u8] = b"pcs-quotient-opening";

/// The prover's record as the skeleton's operations: every Keccak-256 (classified), each tree once it is done,
/// each permutation (a draw when `sample` asked for it), each grind with the permutation that closes it.
fn rust_tokens(records: &[Record], trees: &[Tree]) -> Vec<Tok> {
    let tree_at: HashMap<usize, usize> = trees.iter().enumerate().map(|(i, t)| (t.last, i)).collect();
    // The IVs' layout ids: bytes 28..60 of an IV input.
    let ids: HashSet<Vec<u8>> = records
        .iter()
        .filter_map(|r| match &r.event {
            Event::Hash { input, .. } if input.starts_with(OPENING_LABEL) && input.len() >= PREFIX_LEN => {
                Some(input[28..60].to_vec())
            }
            _ => None,
        })
        .collect();
    // The cells' runs are hashed before their digest (the one streaming hash); a lane's key is the hash of its
    // table's padding seed and the lane.
    let cells_end = records
        .iter()
        .position(|r| matches!(r.event, Event::Stream { .. }))
        .unwrap_or(0);
    let mut pad_seeds: HashSet<Hash> = HashSet::new();
    let mut toks = vec![];
    let mut chain: Option<Hash> = None;
    let mut sample = false;
    let mut grind: Option<(u32, u64)> = None;
    for (ri, r) in records.iter().enumerate() {
        match &r.event {
            Event::Hash { len, input, out } => {
                let key = format!("H {len} {}", hex(out));
                let (class, key) = if input.starts_with(KC_TAG) {
                    chain = Some(*out);
                    ("label", key)
                } else if chain.is_some_and(|c| input.len() >= 32 && input[..32] == c) {
                    chain = Some(*out);
                    ("chain", format!("C {len} {} {}", hex(input), hex(out)))
                } else if input.starts_with(OPENING_LABEL) {
                    ("iv", key)
                } else if input.starts_with(b"pcs-quotient-kdf-v1-") {
                    ("kdf", key)
                } else if input.starts_with(b"pcs-quotient-pad-") {
                    pad_seeds.insert(*out);
                    ("pad-seed", key)
                } else if ids.contains(out.as_slice()) {
                    ("layout-id", key)
                } else if *len == 40 && pad_seeds.contains(&input[..32]) {
                    ("lane-key", key)
                } else if ri < cells_end {
                    ("cells-run", key)
                } else {
                    ("other", key)
                };
                toks.push(Tok {
                    key,
                    class,
                    info: if input.len() <= 2048 {
                        hex(input)
                    } else {
                        format!("{len} bytes")
                    },
                });
            }
            Event::Stream { out } => toks.push(Tok {
                key: format!("S {}", hex(out)),
                class: "cells-digest",
                info: String::new(),
            }),
            Event::Many { .. } => {
                if let Some(&t) = tree_at.get(&ri) {
                    let t = &trees[t];
                    toks.push(Tok {
                        key: format!("T {} {}", t.n_leaves, hex(&t.root)),
                        class: "tree",
                        info: format!("leaves of {} bytes after {} zero blocks", t.leaf_len, t.prefix_blocks),
                    });
                }
            }
            Event::Sample => sample = true,
            Event::Grind { bits, nonce } => grind = Some((*bits, *nonce)),
            Event::Perm { input, output } => {
                let (class, key) = if sample && is_grind_input(input) && grind.is_some() {
                    let (_, nonce) = grind.take().unwrap();
                    ("grind", format!("G {nonce} {} {}", hex_state(input), hex_state(output)))
                } else if sample {
                    ("draw", format!("X {} {}", hex_state(input), hex_state(output)))
                } else if input[4..].iter().all(|&w| w == 0) {
                    ("seed", format!("F {} {}", hex_state(input), hex_state(output)))
                } else {
                    ("overflow", format!("F {} {}", hex_state(input), hex_state(output)))
                };
                sample = false;
                toks.push(Tok {
                    key,
                    class,
                    info: String::new(),
                });
            }
        }
    }
    toks
}

/// The Lean driver's trace as tokens: a tree is its leaves (`L` lines for a secret table, else equal-length
/// `H` lines) followed by its nodes (`H 64`), its root the last node.
fn lean_tokens(text: &str) -> (Vec<Tok>, Vec<String>) {
    let lines: Vec<Vec<&str>> = text.lines().map(|l| l.split(' ').collect()).collect();
    let mut toks = vec![];
    let mut notes = vec![];
    let is_h = |i: usize, len: &str| lines.get(i).is_some_and(|l| l[0] == "H" && l[1] == len);
    let nodes_from = |i: usize, n: usize| (0..n).all(|k| is_h(i + k, "64"));
    let mut i = 0;
    while i < lines.len() {
        let l = &lines[i];
        match l[0] {
            "L" => {
                let (k, from, to): (usize, usize, usize) =
                    (l[1].parse().unwrap(), l[2].parse().unwrap(), l[3].parse().unwrap());
                let n = to - from + 1;
                if n >= 2 && nodes_from(i + 1, n - 1) {
                    let root = lines[i + n - 1][2];
                    toks.push(Tok {
                        key: format!("T {n} {root}"),
                        class: "tree",
                        info: format!("secret table {k}, leaves {from}..={to}"),
                    });
                    i += n;
                } else {
                    notes.push(format!("leaves {k} {from}..={to} with no tree after them"));
                    i += 1;
                }
            }
            "H" if l[1] != "64" => {
                let mut c = 0;
                while is_h(i + c, l[1]) {
                    c += 1;
                }
                if c >= 2 && nodes_from(i + c, c - 1) {
                    let root = lines[i + 2 * c - 2][2];
                    toks.push(Tok {
                        key: format!("T {c} {root}"),
                        class: "tree",
                        info: format!("public leaves of {} bytes", l[1]),
                    });
                    i += 2 * c - 1;
                } else {
                    for k in 0..c {
                        let m = &lines[i + k];
                        toks.push(Tok {
                            key: format!("H {} {}", m[1], m[2]),
                            class: "lean",
                            info: m.get(3).unwrap_or(&"").to_string(),
                        });
                    }
                    i += c;
                }
            }
            "H" => {
                toks.push(Tok {
                    key: format!("H {} {}", l[1], l[2]),
                    class: "lean",
                    info: String::new(),
                });
                i += 1;
            }
            "C" => {
                toks.push(Tok {
                    key: format!("C {} {} {}", l[1], l[2], l[3]),
                    class: "lean",
                    info: String::new(),
                });
                i += 1;
            }
            "F" | "X" => {
                toks.push(Tok {
                    key: format!("{} {} {}", l[0], l[1], l[2]),
                    class: "lean",
                    info: String::new(),
                });
                i += 1;
            }
            "G" => {
                let (first, last, count): (u64, u64, u64) =
                    (l[1].parse().unwrap(), l[2].parse().unwrap(), l[3].parse().unwrap());
                if first != 0 || count != last + 1 {
                    notes.push(format!(
                        "grinding tries {first}..={last} ({count}): not every nonce from 0"
                    ));
                }
                toks.push(Tok {
                    key: format!("G {last} {} {}", l[4], l[5]),
                    class: "lean",
                    info: format!("{count} tries"),
                });
                i += 1;
            }
            _ => i += 1,
        }
    }
    (toks, notes)
}

/// The longest common subsequence of two key lists: the matched index pairs.
fn lcs(a: &[Tok], b: &[Tok]) -> Vec<(usize, usize)> {
    let (n, m) = (a.len(), b.len());
    let mut t = vec![0u32; (n + 1) * (m + 1)];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            t[i * (m + 1) + j] = if a[i].key == b[j].key {
                t[(i + 1) * (m + 1) + j + 1] + 1
            } else {
                t[(i + 1) * (m + 1) + j].max(t[i * (m + 1) + j + 1])
            };
        }
    }
    let (mut i, mut j, mut out) = (0, 0, vec![]);
    while i < n && j < m {
        if a[i].key == b[j].key {
            out.push((i, j));
            i += 1;
            j += 1;
        } else if t[(i + 1) * (m + 1) + j] >= t[i * (m + 1) + j + 1] {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

// ---------------------------------------------------------------------------------------------------------------
// The openings: the prover's scalars between its draws, against the grammar; the messages

#[derive(Clone, Debug, PartialEq, Eq)]
enum Absorbed {
    Scalar(F192),
    Root(Hash),
    Nonce(u64),
}

#[derive(Clone, Debug)]
enum Item {
    Scalars(Vec<F192>),
    Rows(Vec<Vec<u8>>),
    Opened(Vec<Vec<u64>>),
    Bytes(Vec<u8>),
}

type Msg = Vec<Item>;

/// One opening's record: its IV input, and what each permutation after its seed absorbed, cut at the draws
/// (`intervals[0]` before the first, `intervals[i]` between draws `i - 1` and `i`, the last after the last draw).
struct OpeningRecord {
    iv_input: Vec<u8>,
    intervals: Vec<Vec<Absorbed>>,
    /// The trees made during the opening, in order.
    trees: Vec<usize>,
    draws: usize,
}

fn opening_records(records: &[Record], trees: &[Tree]) -> Vec<OpeningRecord> {
    let roots: HashMap<[F192; 2], Hash> = trees.iter().map(|t| (hash_to_scalars(&t.root), t.root)).collect();
    let starts: Vec<usize> = records
        .iter()
        .enumerate()
        .filter(|(_, r)| matches!(&r.event, Event::Hash { input, .. } if input.starts_with(OPENING_LABEL)))
        .map(|(i, _)| i)
        .collect();
    let mut out = vec![];
    for (k, &s) in starts.iter().enumerate() {
        let e = starts.get(k + 1).copied().unwrap_or(records.len());
        let Event::Hash { input, .. } = &records[s].event else {
            unreachable!()
        };
        let mut intervals: Vec<Vec<(F192, u64)>> = vec![vec![]];
        let (mut sample, mut seeded, mut draws) = (false, false, 0);
        for r in &records[s..e] {
            match &r.event {
                Event::Sample => sample = true,
                Event::Perm { input, .. } => {
                    if !seeded {
                        assert!(!sample && input[4..].iter().all(|&w| w == 0), "the opening's seed");
                        seeded = true;
                        continue;
                    }
                    intervals.last_mut().unwrap().extend(rate_scalars(input));
                    if sample && !is_grind_input(input) {
                        intervals.push(vec![]);
                        draws += 1;
                    }
                    sample = false;
                }
                _ => {}
            }
        }
        let intervals = intervals
            .into_iter()
            .map(|v| {
                let mut a = vec![];
                let mut i = 0;
                while i < v.len() {
                    let (x, tag) = v[i];
                    if tag == 4 {
                        a.push(Absorbed::Nonce(x.c0));
                        i += 1;
                    } else if let Some(&root) = (i + 1 < v.len() && v[i + 1].1 == 1)
                        .then(|| roots.get(&[x, v[i + 1].0]))
                        .flatten()
                    {
                        a.push(Absorbed::Root(root));
                        i += 2;
                    } else {
                        a.push(Absorbed::Scalar(x));
                        i += 1;
                    }
                }
                a
            })
            .collect();
        let made: Vec<usize> = (0..trees.len()).filter(|&t| (s..e).contains(&trees[t].last)).collect();
        out.push(OpeningRecord {
            iv_input: input.clone(),
            intervals,
            trees: made,
            draws,
        });
    }
    out
}

fn kinds(a: &[Absorbed]) -> Vec<char> {
    a.iter()
        .map(|x| match x {
            Absorbed::Scalar(_) => 'S',
            Absorbed::Root(_) => 'R',
            Absorbed::Nonce(_) => 'G',
        })
        .collect()
}

fn slot_kinds(slots: &[Slot]) -> Vec<char> {
    slots
        .iter()
        .flat_map(|s| match s {
            Slot::S(k) => vec!['S'; *k],
            Slot::R => vec!['R'],
            Slot::G => vec!['G'],
            Slot::O => vec![],
        })
        .collect()
}

/// Check an opening's record against the grammar of `sh`, and cut its messages (with `rows` of each tree by root
/// and the multiproofs' rows): the mismatches, and the messages (one after each draw, the claims' first).
fn opening_messages(
    rec: &OpeningRecord,
    sh: &Shape,
    proof: &WhirProof,
    rows_of: &dyn Fn(&Hash) -> Vec<Vec<u8>>,
    name: &str,
) -> (Vec<String>, Vec<Msg>) {
    let g = Grammar::of(sh);
    let mut problems = vec![];
    if kinds(&rec.intervals[0]) != slot_kinds(&g.pre) {
        problems.push(format!(
            "{name}: before the first draw the prover absorbs {:?}",
            rec.intervals[0]
        ));
    }
    if g.msgs.len() != rec.draws {
        problems.push(format!(
            "{name}: the prover draws {} times, the skeleton {}",
            rec.draws,
            g.msgs.len()
        ));
    }
    // The stream is what the permutations absorbed (roots and nonces included).
    let absorbed: Vec<F192> = rec
        .intervals
        .iter()
        .flatten()
        .flat_map(|a| match a {
            Absorbed::Scalar(x) => vec![*x],
            Absorbed::Root(r) => hash_to_scalars(r).to_vec(),
            Absorbed::Nonce(n) => vec![F192::new(*n, 0, 0)],
        })
        .collect();
    if absorbed != proof.stream {
        problems.push(format!(
            "{name}: the permutations absorbed {} scalars, the stream has {}",
            absorbed.len(),
            proof.stream.len()
        ));
    }
    let mut msgs = vec![vec![Item::Bytes(rec.iv_input[PREFIX_LEN..].to_vec())]];
    let mut hints = proof.merkle.iter();
    let empty = vec![];
    for (i, slots) in g.msgs.iter().enumerate() {
        let got = rec.intervals.get(i + 1).unwrap_or(&empty);
        if kinds(got) != slot_kinds(slots) {
            problems.push(format!(
                "{name}: after draw {i} the skeleton reads {slots:?}, the prover absorbs {}",
                kinds(got).iter().collect::<String>()
            ));
        }
        let mut scalars = got.iter().filter_map(|a| match a {
            Absorbed::Scalar(x) => Some(*x),
            _ => None,
        });
        let mut roots = got.iter().filter_map(|a| match a {
            Absorbed::Root(r) => Some(*r),
            _ => None,
        });
        let mut msg = vec![];
        for s in slots {
            match s {
                Slot::S(k) => msg.push(Item::Scalars(
                    (0..*k).map(|_| scalars.next().unwrap_or(F192::ZERO)).collect(),
                )),
                Slot::R => msg.push(Item::Rows(roots.next().map(|r| rows_of(&r)).unwrap_or_default())),
                Slot::O => msg.push(Item::Opened(
                    hints
                        .next()
                        .map(|h| {
                            h.leaf_data
                                .iter()
                                .map(|row| row.iter().map(|w| w.0).collect())
                                .collect()
                        })
                        .unwrap_or_default(),
                )),
                Slot::G => {}
            }
        }
        msgs.push(msg);
    }
    if hints.next().is_some() {
        problems.push(format!("{name}: multiproofs the skeleton does not read"));
    }
    (problems, msgs)
}

// ---------------------------------------------------------------------------------------------------------------
// The Lean driver's input

struct W(Vec<u8>);

impl W {
    fn n(&mut self, x: usize) {
        self.0.extend_from_slice(&(x as u64).to_le_bytes());
    }
    fn w(&mut self, x: u64) {
        self.0.extend_from_slice(&x.to_le_bytes());
    }
    fn raw(&mut self, b: &[u8]) {
        self.0.extend_from_slice(b);
    }
    fn lp(&mut self, b: &[u8]) {
        self.n(b.len());
        self.raw(b);
    }
}

fn write_shape(w: &mut W, id: &[u8; 32], sh: &Shape, secret: usize, rows: &[Vec<u8>]) {
    w.raw(id);
    for x in [sh.log_n, secret, sh.depth0, sh.depth1, sh.ood0, sh.levels.len()] {
        w.n(x);
    }
    for &(a, b, c) in &sh.levels {
        [a, b, c].into_iter().for_each(|x| w.n(x));
    }
    w.n(sh.queries.len());
    sh.queries.iter().for_each(|&q| w.n(q));
    for x in [sh.last_folds, sh.residual, rows.len()] {
        w.n(x);
    }
    rows.iter().for_each(|r| w.lp(r));
}

fn write_msg(w: &mut W, m: &Msg) {
    w.n(m.len());
    for item in m {
        match item {
            Item::Scalars(xs) => {
                w.n(0);
                w.n(xs.len());
                xs.iter()
                    .for_each(|x| [x.c0, x.c1, x.c2].into_iter().for_each(|l| w.w(l)));
            }
            Item::Rows(rows) => {
                w.n(1);
                w.n(rows.len());
                rows.iter().for_each(|r| w.lp(r));
            }
            Item::Opened(rows) => {
                w.n(2);
                w.n(rows.len());
                for r in rows {
                    w.n(r.len());
                    r.iter().for_each(|&x| w.w(x));
                }
            }
            Item::Bytes(b) => {
                w.n(3);
                w.lp(b);
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The checks

struct Report {
    lines: Vec<String>,
    failures: Vec<String>,
}

impl Report {
    fn say(&mut self, s: String) {
        println!("{s}");
        self.lines.push(s);
    }
    fn fail(&mut self, s: String) {
        println!("MISMATCH {s}");
        self.failures.push(s);
    }
}

/// The derived shapes at every size, and what the skeleton cannot express of them.
fn shapes_at(log_rows: usize) -> Vec<(Shape, Vec<String>)> {
    layouts(log_rows).iter().map(|l| Shape::derive(l.log_n)).collect()
}

/// The structure of a run (any mode): the trees' sizes and the openings' grammar against the derived shapes.
fn check_structure(run: &Run, trees: &[Tree], rep: &mut Report) -> Vec<OpeningRecord> {
    let shapes = shapes_at(run.log_rows);
    let recs = opening_records(&run.records, trees);
    assert_eq!(recs.len(), 3, "three openings");
    for (j, rec) in recs.iter().enumerate() {
        let (sh, problems) = &shapes[j];
        for p in problems {
            rep.fail(format!("{}: {p}", NAMES[j]));
        }
        // The trees an opening commits: its level 0 (made before) and the deeper ones, of the shape's depths.
        let depths = sh.depths();
        let sizes: Vec<usize> = rec.trees.iter().map(|&t| trees[t].n_leaves).collect();
        let want: Vec<usize> = depths[1..].iter().map(|d| 1 << d).collect();
        if sizes != want {
            rep.fail(format!(
                "{}: deeper commitments of {sizes:?} leaves, the shape {want:?}",
                NAMES[j]
            ));
        }
        let rows_of = |_: &Hash| vec![];
        let (problems, msgs) = opening_messages(rec, sh, &run.openings[j], &rows_of, NAMES[j]);
        for p in problems {
            rep.fail(p);
        }
        rep.say(format!(
            "{} (2^{} rows): {} draws, {} messages, deeper trees {sizes:?}: grammar checked",
            NAMES[j],
            run.log_rows,
            rec.draws,
            msgs.len()
        ));
    }
    // The level-0 trees: the wiring table's, the witness table's, the quotient table's, of the shapes' depths.
    let l0 = |root: &Hash| trees.iter().find(|t| t.root == *root).map(|t| t.n_leaves);
    for (j, root) in [run.roots[0], run.index_root, run.roots[1]].iter().enumerate() {
        let want = 1usize << shapes[j].0.depth0;
        if l0(root) != Some(want) {
            rep.fail(format!(
                "{}: level 0 has {:?} leaves, the shape {want}",
                NAMES[j],
                l0(root)
            ));
        }
    }
    recs
}

fn parse_kv(line: &str) -> HashMap<String, String> {
    line.split(' ')
        .filter_map(|kv| kv.split_once('=').map(|(k, v)| (k.to_string(), v.to_string())))
        .collect()
}

/// `deployedShape` (the Lean driver's `deployed ...` lines) against the shapes derived at `2^22`, and the IV
/// prefixes against `opening::prefix` of the `2^22` layouts.
fn check_deployed(lean_out: &str, rep: &mut Report) {
    let shapes = shapes_at(22);
    let ls = layouts(22);
    for j in 0..3 {
        let Some(line) = lean_out
            .lines()
            .find(|l| l.starts_with(&format!("deployed {} ", NAMES[j])))
        else {
            rep.fail(format!("no `deployed {}` line from the Lean driver", NAMES[j]));
            continue;
        };
        let body = line.split_once(' ').unwrap().1.split_once(' ').unwrap().1;
        let (lean_shape, lean_prefix) = body.rsplit_once(" ivPrefix=").unwrap();
        let ours = shapes[j].0.line(SECRET[j]);
        if lean_shape != ours {
            rep.fail(format!(
                "deployedShape {}: Lean `{lean_shape}`, Rust `{ours}`",
                NAMES[j]
            ));
        } else {
            rep.say(format!(
                "deployedShape {} = the derived shape at 2^22: {ours}",
                NAMES[j]
            ));
        }
        if lean_prefix != hex(&prefix(&ls[j])) {
            rep.fail(format!(
                "deployedShape {}: IV prefix differs from opening::prefix",
                NAMES[j]
            ));
        } else {
            rep.say(format!(
                "deployedShape {}: IV prefix = opening::prefix (2^22 layout)",
                NAMES[j]
            ));
        }
        let kv = parse_kv(body);
        if kv.get("depth0").map(String::as_str) != Some(&shapes[j].0.depth0.to_string()) {
            rep.fail(format!("deployedShape {}: depth0", NAMES[j]));
        }
    }
    // `zk_deployed_bits` takes the wiring codeword's 2^19 rows; positions are `Fin (2^23)`.
    let (w, q) = (&shapes[1].0, &shapes[2].0);
    if w.depth0 != 19 {
        rep.fail(format!(
            "the wiring codeword at 2^22 has 2^{} rows, zk_deployed_bits says 2^19",
            w.depth0
        ));
    }
    if q.depth0 > 23 {
        rep.fail(format!(
            "the quotient codeword at 2^22 has 2^{} rows, positions are Fin (2^23)",
            q.depth0
        ));
    }
}

/// The expected proof file: the Lean driver's `writeProof` format, from the prover's proof; positions from the
/// opened rows' leaves in the trees.
fn expected_proof(run: &Run, recs: &[OpeningRecord], trees: &[Tree]) -> Vec<String> {
    let mut out = vec![
        format!("wRoot {}", hex(&run.roots[0])),
        format!("qRoot {}", hex(&run.roots[1])),
    ];
    for v in &run.stream[4..9] {
        out.push(format!("value {}", hex_limbs(v)));
    }
    let tree_of = |root: &Hash| trees.iter().find(|t| t.root == *root).unwrap();
    let l0_roots = [run.roots[0], run.index_root, run.roots[1]];
    for (i, o) in run.openings.iter().enumerate() {
        out.push(format!("opening {i} stream {}", o.stream.len()));
        out.extend(o.stream.iter().map(|x| format!("s {}", hex_limbs(x))));
        let committed: Vec<&Tree> = std::iter::once(tree_of(&l0_roots[i]))
            .chain(recs[i].trees.iter().map(|&t| &trees[t]))
            .collect();
        for (j, paths) in o.merkle.iter().enumerate() {
            let tree = committed[j];
            let index: HashMap<Hash, Vec<usize>> =
                tree.leaves.iter().enumerate().fold(HashMap::new(), |mut m, (p, d)| {
                    m.entry(*d).or_insert_with(Vec::new).push(p);
                    m
                });
            let mut pos: Vec<usize> = paths
                .leaf_data
                .iter()
                .flat_map(|row| {
                    let words = tree.images[0].len() / 8;
                    let mut image = vec![0u8; 8 * (words - row.len())];
                    image.extend(words_bytes(row));
                    index.get(&keccak256(&image)).cloned().unwrap_or_default()
                })
                .collect();
            pos.sort_unstable();
            pos.dedup();
            let ps: Vec<String> = pos.iter().map(|p| p.to_string()).collect();
            out.push(format!("merkle {i} {j} positions {} {}", pos.len(), ps.join(" ")));
            out.push(format!("merkle {i} {j} opened {}", paths.leaf_data.len()));
            let ss: Vec<String> = paths.sibling_hashes.iter().map(|h| hex(h)).collect();
            out.push(format!("merkle {i} {j} siblings {} {}", ss.len(), ss.join(" ")));
        }
    }
    out
}

/// The tokens the prover makes and the skeleton does not, by class, and why each is harmless.
fn explain(class: &str) -> Option<&'static str> {
    Some(match class {
        "layout-id" => "the layout's id is Keccak-256 of its encoding; the skeleton takes the id as a constant",
        "kdf" => "the randomness's key derivation (secret seed): the skeleton's randomness is uniform",
        "pad-seed" => "a table's padding seed (secret): the skeleton's randomness is uniform",
        "lane-key" => "the ChaCha12 key of a hidden lane (secret seed): the skeleton's randomness is uniform",
        "cells-run" | "cells-digest" => "the cells' digest the key derivation binds (secret): not in the skeleton",
        _ => return None,
    })
}

fn compare(run: &Run, trees: &[Tree], recs: &[OpeningRecord], dir: &std::path::Path, rep: &mut Report) {
    let suffix = run.log_rows;
    let (Ok(trace_text), Ok(proof_text)) = (
        std::fs::read_to_string(dir.join(format!("lean_trace_{suffix}.txt"))),
        std::fs::read_to_string(dir.join(format!("lean_proof_{suffix}.txt"))),
    ) else {
        rep.say(format!(
            "no Lean output in {} yet: run the Lean driver on input_{suffix}.bin (see this file's docs)",
            dir.display()
        ));
        return;
    };
    if let Ok(out) = std::fs::read_to_string(dir.join(format!("lean_out_{suffix}.txt"))) {
        for l in out.lines().filter(|l| l.starts_with("error")) {
            rep.fail(format!("Lean driver: {l}"));
        }
        for l in out
            .lines()
            .filter(|l| l.starts_with("operations") || l.starts_with("messages"))
        {
            rep.say(format!("Lean driver: {l}"));
        }
        check_deployed(&out, rep);
        // The run's shapes: the input's, the IV prefix by the skeleton's `ivPrefix`.
        let shapes = shapes_at(run.log_rows);
        for j in 0..3 {
            let want = format!(
                "run {} {} ivPrefix={}",
                NAMES[j],
                shapes[j].0.line(SECRET[j]),
                hex(&prefix(&run.layouts[j]))
            );
            if !out.lines().any(|l| l == want) {
                rep.fail(format!(
                    "the Lean run's {} shape or IV prefix is not `{want}`",
                    NAMES[j]
                ));
            }
        }
    }
    let all = rust_tokens(&run.records, trees);
    // A query the prover asks again is the same oracle query (its own `verify` replays the reduction's chain; two
    // runs of equal cells hash alike): only first occurrences are aligned.
    let mut seen = HashSet::new();
    let first: Vec<bool> = all.iter().map(|t| seen.insert(t.key.clone())).collect();
    let mut repeats: HashMap<&str, usize> = HashMap::new();
    for (t, _) in all.iter().zip(&first).filter(|(_, f)| !**f) {
        *repeats.entry(t.class).or_default() += 1;
    }
    let mut repeats: Vec<_> = repeats.into_iter().collect();
    repeats.sort();
    for (class, n) in repeats {
        rep.say(format!(
            "prover only, explained: {n} x {class}: a query the prover made before, asked again (the answer is the same)"
        ));
    }
    let ours: Vec<Tok> = all
        .iter()
        .zip(&first)
        .filter(|(_, f)| **f)
        .map(|(t, _)| t.clone())
        .collect();
    let (theirs, notes) = lean_tokens(&trace_text);
    for n in notes {
        rep.fail(format!("Lean trace: {n}"));
    }
    let pairs = lcs(&ours, &theirs);
    let matched_r: HashSet<usize> = pairs.iter().map(|p| p.0).collect();
    let matched_l: HashSet<usize> = pairs.iter().map(|p| p.1).collect();
    let mut by_class: HashMap<&str, usize> = HashMap::new();
    for &(i, _) in &pairs {
        *by_class.entry(ours[i].class).or_default() += 1;
    }
    let mut classes: Vec<_> = by_class.into_iter().collect();
    classes.sort();
    rep.say(format!(
        "aligned: {} of {} prover tokens with {} of {} skeleton tokens; matched by class {classes:?}",
        pairs.len(),
        ours.len(),
        pairs.len(),
        theirs.len()
    ));
    let lean_left: HashMap<&str, usize> = (0..theirs.len())
        .filter(|j| !matched_l.contains(j))
        .map(|j| (theirs[j].key.as_str(), j))
        .collect();
    let mut explained: HashMap<String, usize> = HashMap::new();
    let mut reordered_l = HashSet::new();
    let mut lean_left = lean_left;
    // A token's neighbours on the other side, to say where it moved.
    let matched_at = |i: usize| pairs.iter().position(|p| p.0 > i).map(|k| pairs[k]);
    for (i, t) in ours.iter().enumerate() {
        if matched_r.contains(&i) {
            continue;
        }
        if let Some(j) = lean_left.remove(t.key.as_str()) {
            reordered_l.insert(j);
            let next = matched_at(i).map_or(String::from("the end"), |(r, _)| ours[r].class.to_string());
            let lean_next = pairs
                .iter()
                .find(|p| p.1 > j)
                .map_or(String::from("the end"), |p| ours[p.0].class.to_string());
            rep.say(format!(
                "REORDERED {} {}: the prover's token {i} (before its next aligned `{next}`), the skeleton's token {j} \
                 (before `{lean_next}`)",
                t.class,
                t.key.chars().take(80).collect::<String>()
            ));
        } else if let Some(why) = explain(t.class) {
            *explained.entry(format!("{}: {why}", t.class)).or_default() += 1;
        } else {
            rep.fail(format!(
                "prover only, token {i} ({}): {} [{}]",
                t.class,
                t.key.chars().take(120).collect::<String>(),
                t.info.chars().take(200).collect::<String>()
            ));
        }
    }
    let mut ex: Vec<_> = explained.into_iter().collect();
    ex.sort();
    for (why, n) in ex {
        rep.say(format!("prover only, explained: {n} x {why}"));
    }
    for (j, t) in theirs.iter().enumerate() {
        if !matched_l.contains(&j) && !reordered_l.contains(&j) {
            rep.fail(format!(
                "skeleton only, token {j}: {} [{}]",
                t.key.chars().take(120).collect::<String>(),
                t.info
            ));
        }
    }
    // The proofs.
    let want = expected_proof(run, recs, trees);
    let got: Vec<&str> = proof_text.lines().collect();
    let mut differ = 0;
    for k in 0..want.len().max(got.len()) {
        let (w, g) = (want.get(k).map(String::as_str), got.get(k).copied());
        if w != g {
            differ += 1;
            if differ <= 10 {
                rep.fail(format!(
                    "proof line {k}: prover `{}`, skeleton `{}`",
                    w.unwrap_or("").chars().take(160).collect::<String>(),
                    g.unwrap_or("").chars().take(160).collect::<String>()
                ));
            }
        }
    }
    if differ == 0 {
        rep.say(format!(
            "proof: the skeleton's equals the prover's ({} lines: roots, values, streams, positions, siblings)",
            want.len()
        ));
    }
}

/// The input of the Lean driver for a full run.
fn lean_input(run: &Run, trees: &[Tree], recs: &[OpeningRecord]) -> Vec<u8> {
    let shapes = shapes_at(run.log_rows);
    let tree_of = |root: &Hash| trees.iter().find(|t| t.root == *root).expect("a tree of this root");
    let mut w = W(b"SKELIN01".to_vec());
    w.raw(&run.index_root);
    w.raw(&run.statement.y);
    w.raw(&run.statement.root);
    for l in layouts(22) {
        w.raw(&layout_id(&l));
    }
    let wiring_rows = tree_of(&run.index_root).images.clone();
    for j in 0..3 {
        let secret = [0, 2, 1][j];
        let rows: &[Vec<u8>] = if j == 1 { &wiring_rows } else { &[] };
        write_shape(&mut w, &layout_id(&run.layouts[j]), &shapes[j].0, secret, rows);
    }
    for root in [run.roots[0], run.roots[1]] {
        let t = tree_of(&root);
        w.n(t.leaves.len());
        t.leaves.iter().for_each(|d| w.raw(d));
    }
    let mut msgs: Vec<Msg> = vec![vec![Item::Scalars(run.stream[4..9].to_vec())]];
    let rows_of = |root: &Hash| tree_of(root).images.clone();
    for (j, rec) in recs.iter().enumerate() {
        // The grammar's problems are `check_structure`'s to report.
        let (_, m) = opening_messages(rec, &shapes[j].0, &run.openings[j], &rows_of, NAMES[j]);
        msgs.extend(m);
    }
    w.n(msgs.len());
    msgs.iter().for_each(|m| write_msg(&mut w, m));
    w.0
}

fn finish(rep: Report, name: &str, dir: &std::path::Path) {
    let text = [
        rep.lines.clone(),
        rep.failures.iter().map(|f| format!("MISMATCH {f}")).collect(),
    ]
    .concat();
    std::fs::write(dir.join(format!("report_{name}.txt")), text.join("\n")).unwrap();
    assert!(
        rep.failures.is_empty(),
        "{} mismatches, see report_{name}.txt",
        rep.failures.len()
    );
}

// ---------------------------------------------------------------------------------------------------------------
// The tests

/// The shapes derived at every supported size are ones the skeleton expresses (six lane rounds, one OOD sample a
/// level, 17 grinding bits), and the grammar's draws are the prover's (checked against a run at 2^17 below).
#[test]
fn derived_shapes() {
    for log_rows in 17..=22 {
        for (j, (sh, problems)) in shapes_at(log_rows).into_iter().enumerate() {
            assert!(problems.is_empty(), "2^{log_rows} {}: {problems:?}", NAMES[j]);
            println!("2^{log_rows} {}: log_n {} {}", NAMES[j], sh.log_n, sh.line(SECRET[j]));
        }
    }
}

/// A full proof at 2^17 rows, every Keccak call recorded: the structure against the grammar, the Lean driver's
/// input written, and, once the Lean driver has run on it, its operations and proof compared.
#[test]
fn skel_trace_17() {
    let dir = out_dir();
    let run = run_prover(17, Mode::Full);
    let trees = trees_full(&run.records);
    let mut rep = Report {
        lines: vec![],
        failures: vec![],
    };
    rep.say(format!("2^17: {} records, {} trees", run.records.len(), trees.len()));
    let recs = check_structure(&run, &trees, &mut rep);
    let input = lean_input(&run, &trees, &recs);
    std::fs::write(dir.join("input_17.bin"), &input).unwrap();
    let toks = rust_tokens(&run.records, &trees);
    let text: Vec<String> = toks.iter().map(|t| format!("{} {}", t.class, t.key)).collect();
    std::fs::write(dir.join("rust_tokens_17.txt"), text.join("\n")).unwrap();
    rep.say(format!(
        "input_17.bin: {} bytes; {} prover tokens",
        input.len(),
        toks.len()
    ));
    compare(&run, &trees, &recs, &dir, &mut rep);
    finish(rep, "17", &dir);
}

/// Proofs at 2^18 .. 2^21 rows (the small circuit), recorded light: their trees' sizes and their openings' messages
/// against the grammar of the shapes derived at each size. Heavy-ish (2^21: a few GiB).
#[test]
#[ignore]
fn skel_structure_18_21() {
    let dir = out_dir();
    let mut rep = Report {
        lines: vec![],
        failures: vec![],
    };
    for log_rows in 18..=21 {
        let run = run_prover(log_rows, Mode::Light);
        let trees = trees_light(&run.records);
        rep.say(format!(
            "2^{log_rows}: {} records, {} trees",
            run.records.len(),
            trees.len()
        ));
        check_structure(&run, &trees, &mut rep);
    }
    finish(rep, "18_21", &dir);
}

/// A full proof at 2^22 rows (the deployed size), recorded light: its trees' sizes and its openings' messages
/// against the grammar of the shapes derived at 2^22, which `skel_trace_17` checks equal `deployedShape`. Heavy.
#[test]
#[ignore]
fn skel_trace_22() {
    let dir = out_dir();
    let run = run_prover(22, Mode::Light);
    let trees = trees_light(&run.records);
    let mut rep = Report {
        lines: vec![],
        failures: vec![],
    };
    rep.say(format!("2^22: {} records, {} trees", run.records.len(), trees.len()));
    check_structure(&run, &trees, &mut rep);
    // The reduction's chain at 2^22: the label, then α, β, γ (after the witness root), t (after the quotient
    // root), and ρ (after the five values) in the prover's own verify.
    let toks = rust_tokens(&run.records, &trees);
    let chain: Vec<&Tok> = toks.iter().filter(|t| t.class == "chain").collect();
    rep.say(format!(
        "2^22 chain: {} label hashes, {} chain steps (prover: α β γ t; its verify: α β γ t ρ)",
        toks.iter().filter(|t| t.class == "label").count(),
        chain.len()
    ));
    if chain.len() != 9 {
        rep.fail(format!("2^22: {} chain steps, 9 expected", chain.len()));
    }
    let text: Vec<String> = toks.iter().map(|t| format!("{} {}", t.class, t.key)).collect();
    std::fs::write(dir.join("rust_tokens_22.txt"), text.join("\n")).unwrap();
    finish(rep, "22", &dir);
}
