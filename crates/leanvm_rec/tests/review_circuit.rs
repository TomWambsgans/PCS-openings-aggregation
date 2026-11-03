// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Review of π2's circuit (REVIEW-REC.md): experiments, no fixes.
//!
//! - `review_free_inputs` (E1): the constraint system `w_(σ_i) = P_i` of the real circuit as a dependency graph
//!   (each non-hole cell is defined by the one push sent to it), its strongly connected components classified,
//!   and the backward closure of the ports' limb cells: every free input the ports depend on, by kind. Built from
//!   `spec::Circuit` only (σ, the regions, the blocks, the ports), not from the compiler's bookkeeping.
//! - `review_mutated_streams` (E2): the circuit compiled on mutated, random and re-seeded streams (and public
//!   inputs): its witness satisfies every internal push, and every port's limbs, read from the witness, are what
//!   `eval::evaluate` of π1's graph gives on the same stream (the calls' elements, the zero checks' values, the
//!   roots, the statement). The repository's tests compare digests and limbs only on the honest stream.
//!
//! `cargo test --release -p leanvm_rec --test review_circuit -- --ignored --nocapture --test-threads 1`

#[path = "../../leanvm_univariate/tests/vectors/mod.rs"]
mod vectors;

use leanvm_flock_gas::evm::record::Node;
use leanvm_flock_gas::field::{E, K};
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_flock_gas::transcript::keccak_seed;
use leanvm_rec::circuit::compile::{Compiled, Inputs, Layout, pi2};
use leanvm_rec::circuit::spec::{self, CallWord, Formula, Source, word_limbs};
use leanvm_rec::eval::{call_inputs, checks, evaluate};
use leanvm_univariate::Claims;
use leanvm_univariate::contract::{NAME, Recorded, SetupRoots, contract_iv, record_verifier};

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

fn layout_of_env() -> Layout {
    match std::env::var("REVIEW_LAYOUT").as_deref() {
        Ok("d32v") => Layout::D32v,
        _ => Layout::D16v,
    }
}

fn setup(name: &str) -> (vectors::Vector, Recorded, [u8; 32], Vec<u8>) {
    let v = vector(name);
    let recorded = record_verifier(&v.shape, vectors::blake2s_of(&v.config), Claims::Point);
    let iv = contract_iv(&v.shape, &PROGRAM_IV, &SetupRoots::REFERENCE);
    let stream = v.calldata[STREAM_AT..].to_vec();
    (v, recorded, iv, stream)
}

/// How a cell is defined: by the one push sent to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Def {
    /// A hole (a port's own position): nothing pushes to it.
    Hole,
    Forward,
    /// An expression slot's push: its position (for the formula).
    Expr(u32),
}

struct Deps {
    def: Vec<Def>,
    offsets: Vec<u32>,
    edges: Vec<u32>,
}

/// Each cell's definition and the cells its defining push reads.
fn dependencies(c: &spec::Circuit) -> Deps {
    let n = c.n();
    let w = c.width();
    let row_regions = c.row_regions();
    let mut def = vec![Def::Hole; n];
    let mut reads: Vec<Vec<u32>> = vec![Vec::new(); n];
    for i in 0..n {
        let f = c.formula(&row_regions, i);
        if matches!(f, Formula::Port(_)) {
            continue;
        }
        let j = c.sigma[i] as usize;
        assert!(j < n, "a non-port position pushes inside");
        assert_eq!(def[j], Def::Hole, "cell {j} pushed twice");
        match f {
            Formula::Forward => {
                def[j] = Def::Forward;
                reads[j] = vec![i as u32];
            }
            Formula::Expr(p) => {
                def[j] = Def::Expr(i as u32);
                let row = i & !(w - 1);
                let mut r: Vec<u32> = p.reads().map(|cell| (row + cell as usize) as u32).collect();
                r.sort_unstable();
                r.dedup();
                reads[j] = r;
            }
            Formula::Port(_) => unreachable!(),
        }
    }
    let mut offsets = Vec::with_capacity(n + 1);
    let mut edges = Vec::new();
    offsets.push(0u32);
    for r in &reads {
        edges.extend_from_slice(r);
        offsets.push(edges.len() as u32);
    }
    Deps { def, offsets, edges }
}

/// Tarjan's SCCs, iterative: each cell's component id.
fn sccs(d: &Deps) -> (Vec<u32>, usize) {
    let n = d.def.len();
    const UNSEEN: u32 = u32::MAX;
    let mut index = vec![UNSEEN; n];
    let mut low = vec![0u32; n];
    let mut on_stack = vec![false; n];
    let mut comp = vec![UNSEEN; n];
    let mut stack: Vec<u32> = Vec::new();
    let mut call: Vec<(u32, u32)> = Vec::new();
    let (mut next, mut comps) = (0u32, 0usize);
    for root in 0..n as u32 {
        if index[root as usize] != UNSEEN {
            continue;
        }
        call.push((root, d.offsets[root as usize]));
        index[root as usize] = next;
        low[root as usize] = next;
        next += 1;
        stack.push(root);
        on_stack[root as usize] = true;
        while let Some(&(v, e)) = call.last() {
            let end = d.offsets[v as usize + 1];
            if e < end {
                let u = d.edges[e as usize];
                call.last_mut().expect("a frame").1 = e + 1;
                if index[u as usize] == UNSEEN {
                    index[u as usize] = next;
                    low[u as usize] = next;
                    next += 1;
                    stack.push(u);
                    on_stack[u as usize] = true;
                    call.push((u, d.offsets[u as usize]));
                } else if on_stack[u as usize] {
                    low[v as usize] = low[v as usize].min(index[u as usize]);
                }
            } else {
                call.pop();
                if let Some(&(p, _)) = call.last() {
                    low[p as usize] = low[p as usize].min(low[v as usize]);
                }
                if low[v as usize] == index[v as usize] {
                    loop {
                        let u = stack.pop().expect("on the stack");
                        on_stack[u as usize] = false;
                        comp[u as usize] = comps as u32;
                        if u == v {
                            break;
                        }
                    }
                    comps += 1;
                }
            }
        }
    }
    (comp, comps)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Kind {
    /// No cycle: determined by what it reads.
    Determined,
    /// A hole read by something.
    Hole,
    /// A cycle of forwards (any word).
    FreeValue(usize),
    /// One `b²` slot on a cycle of forwards (a bit).
    Bit,
    /// Anything else: `(region, role)` of its expression slots.
    Other(Vec<(String, usize)>),
}

#[test]
#[ignore]
fn review_free_inputs() {
    deep(|| {
        let layout = layout_of_env();
        let (v, recorded, iv, stream) = setup("main_line_rec");
        let c = pi2(&recorded, layout, &Inputs { iv, public: v.public, stream: &stream });
        let circuit = &c.finished.circuit;
        let (n, w) = (circuit.n(), circuit.width());
        let row_regions = circuit.row_regions();
        let d = dependencies(circuit);
        let (comp, comps) = sccs(&d);
        // Members of each component.
        let mut size = vec![0u32; comps];
        for &k in &comp {
            size[k as usize] += 1;
        }
        let mut members: Vec<Vec<u32>> = vec![Vec::new(); comps];
        for (i, &k) in comp.iter().enumerate() {
            if size[k as usize] > 1 || d.edges[d.offsets[i] as usize..d.offsets[i + 1] as usize].contains(&(i as u32)) {
                members[k as usize].push(i as u32);
            }
        }
        let mut has_kappa = vec![false; n];
        for &(i, _) in &circuit.kappa {
            has_kappa[i as usize] = true;
        }
        let name_of = |p: u32| -> (String, usize) {
            let r = row_regions[p as usize / w];
            let region = if r == u16::MAX { "(none)".to_string() } else { circuit.regions[r as usize].name.clone() };
            (region, p as usize % w)
        };
        let classify = |k: usize| -> Kind {
            let m = &members[k];
            if m.is_empty() {
                return Kind::Determined;
            }
            let exprs: Vec<u32> = m
                .iter()
                .filter_map(|&j| match d.def[j as usize] {
                    Def::Expr(p) => Some(p),
                    _ => None,
                })
                .collect();
            if exprs.is_empty() {
                return Kind::FreeValue(m.len());
            }
            if exprs.len() == 1 {
                let p = exprs[0] as usize;
                if let Formula::Expr(poly) = circuit.formula(&row_regions, p) {
                    let row = p & !(w - 1);
                    if poly.linear.is_empty()
                        && poly.quadratic.len() == 1
                        && poly.quadratic[0].0 == poly.quadratic[0].1
                        && poly.quadratic[0].2 == K(1)
                        && m.contains(&((row + poly.quadratic[0].0 as usize) as u32))
                        && !has_kappa[p]
                    {
                        return Kind::Bit;
                    }
                }
            }
            Kind::Other(exprs.iter().map(|&p| name_of(p)).collect())
        };
        // Every component's kind, overall.
        let mut overall: std::collections::BTreeMap<String, usize> = Default::default();
        let mut kinds: Vec<Option<Kind>> = vec![None; comps];
        for k in 0..comps {
            let kind = classify(k);
            let key = match &kind {
                Kind::Determined => continue,
                Kind::FreeValue(s) => format!("free value (cycle of {s})"),
                Kind::Bit => "bit".into(),
                Kind::Other(e) => format!("other {e:?}"),
                Kind::Hole => unreachable!(),
            };
            *overall.entry(key).or_default() += 1;
            kinds[k] = Some(kind);
        }
        println!("{layout:?}: N = 2^{}, {comps} components; cyclic ones overall:", circuit.log_n);
        let mut sorted: Vec<(&String, &usize)> = overall.iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(a.1));
        let others: usize = sorted.iter().filter(|(k, _)| k.starts_with("other")).map(|(_, c)| **c).sum();
        for (k, count) in sorted.iter().take(25) {
            println!("  {count:>8}  {k}");
        }
        println!("  ({others} 'other' components, in {} kinds)", sorted.iter().filter(|(k, _)| k.starts_with("other")).count());

        // The ports' backward closure.
        let mut relevant = vec![false; n];
        let mut todo: Vec<u32> = Vec::new();
        for p in &circuit.ports {
            let Formula::Port(limbs) = circuit.formula(&row_regions, p.position as usize) else { unreachable!() };
            let row = p.position as usize & !(w - 1);
            for &l in limbs {
                let cell = (row + l as usize) as u32;
                if !relevant[cell as usize] {
                    relevant[cell as usize] = true;
                    todo.push(cell);
                }
            }
        }
        while let Some(j) = todo.pop() {
            for &u in &d.edges[d.offsets[j as usize] as usize..d.offsets[j as usize + 1] as usize] {
                if !relevant[u as usize] {
                    relevant[u as usize] = true;
                    todo.push(u);
                }
            }
        }
        let mut in_closure: std::collections::BTreeMap<String, usize> = Default::default();
        let mut seen = vec![false; comps];
        let mut holes_read = 0usize;
        let mut bad: Vec<String> = Vec::new();
        for j in 0..n {
            if !relevant[j] {
                continue;
            }
            if d.def[j] == Def::Hole {
                holes_read += 1;
                bad.push(format!("hole {j} ({:?}) is read", name_of(j as u32)));
                continue;
            }
            let k = comp[j] as usize;
            if std::mem::replace(&mut seen[k], true) {
                continue;
            }
            let key = match &kinds[k] {
                None => continue,
                Some(Kind::FreeValue(s)) => format!("free value (cycle of {s})"),
                Some(Kind::Bit) => "bit".into(),
                Some(Kind::Other(e)) => {
                    bad.push(format!("component {k}: {e:?}"));
                    format!("other {e:?}")
                }
                Some(Kind::Determined | Kind::Hole) => unreachable!(),
            };
            *in_closure.entry(key).or_default() += 1;
        }
        let closure_cells = relevant.iter().filter(|&&r| r).count();
        println!("the ports' closure: {closure_cells} cells; its free inputs:");
        for (k, count) in &in_closure {
            println!("  {count:>8}  {k}");
        }
        println!("  holes read: {holes_read}");
        println!(
            "compiler's counts: free bits {:?} (alone, with a copy), free values {}, stream {} B",
            c.free_bits, c.finished.stats.free_values, stream.len()
        );
        for b in bad.iter().take(20) {
            println!("  BAD: {b}");
        }
        assert!(bad.is_empty(), "{} unexpected free inputs in the ports' closure", bad.len());
        let bits = in_closure.get("bit").copied().unwrap_or(0);
        assert_eq!(bits, c.free_bits[0] + c.free_bits[1], "every free bit, and only those, reaches a port");
    });
}

/// Every internal push equals its target's pull, and every hole is 0; the ports are not compared.
fn internal_check(c: &spec::Circuit, w: &[K]) -> Result<(), String> {
    let (n, width) = (c.n(), c.width());
    let row_regions = c.row_regions();
    let kappa = c.kappa_column();
    for i in 0..n {
        let f = c.formula(&row_regions, i);
        if matches!(f, Formula::Port(_)) {
            continue;
        }
        let row = i & !(width - 1);
        let push = f.eval(&w[row..row + width], w[i], K(0)) + kappa[i];
        let t = c.sigma[i] as usize;
        if w[t] != push {
            return Err(format!("position {i} pushes {push:?} to {t}, which holds {:?}", w[t]));
        }
    }
    Ok(())
}

/// The ports' limbs as the witness holds them (the port row's cells), in `circuit.ports` order.
fn port_limbs(c: &spec::Circuit, w: &[K]) -> Vec<Vec<u64>> {
    let row_regions = c.row_regions();
    c.ports
        .iter()
        .map(|p| {
            let Formula::Port(limbs) = c.formula(&row_regions, p.position as usize) else { unreachable!() };
            let row = p.position as usize & !(c.width() - 1);
            limbs.iter().map(|&l| w[row + l as usize].0).collect()
        })
        .collect()
}

/// E2 on one stream: the witness satisfies the internal pushes; its ports are the evaluated graph's outputs.
fn differential(recorded: &Recorded, layout: Layout, iv: [u8; 32], public: [u8; 32], stream: &[u8], label: &str) {
    let c: Compiled = pi2(recorded, layout, &Inputs { iv, public, stream });
    let circuit = &c.finished.circuit;
    let w = &c.finished.witness;
    internal_check(circuit, w).unwrap_or_else(|e| panic!("{label}: {e}"));
    // The reference: π1's graph evaluated on this stream.
    let seed = keccak_seed(&NAME, &iv, &public);
    let values = evaluate(&recorded.graph, seed, &public, stream);
    let expected_calls = call_inputs(recorded, &values, stream);
    let (zero_values, _) = checks(&recorded.graph, &values);
    // Elements by index, from the reference's call bytes.
    let mut elements: std::collections::BTreeMap<u32, E> = Default::default();
    for (words, bytes) in circuit.calls.iter().zip(&expected_calls) {
        assert_eq!(bytes.len(), 32 * words.len(), "{label}: call length");
        for (word, chunk) in words.iter().zip(bytes.as_chunks::<32>().0) {
            match *word {
                CallWord::Element(e) => {
                    let l = word_limbs(chunk);
                    assert_eq!(l[3], 0);
                    let x = E::new(l[0], l[1], l[2]);
                    assert_eq!(*elements.entry(e).or_insert(x), x, "{label}: element {e} repeated");
                }
                CallWord::Const(k) => assert_eq!(&k, chunk, "{label}: a constant word"),
                CallWord::Root(_) => {}
            }
        }
    }
    // Zero checks in the ports' order: those on non-constant nodes (the compiler makes no port for a constant).
    let zero_nonconst: Vec<E> = recorded
        .graph
        .zero
        .iter()
        .zip(&zero_values)
        .filter(|((id, _), _)| !matches!(c.expanded.nodes[c.map[*id as usize] as usize], Node::Const(_)))
        .map(|(_, &x)| x)
        .collect();
    let mut zero_at = 0usize;
    let limbs = port_limbs(circuit, w);
    let mut seen = [0usize; 4];
    for (p, l) in circuit.ports.iter().zip(&limbs) {
        let want: Vec<u64> = match p.source {
            Source::Statement => {
                seen[0] += 1;
                (0..4).map(|k| u64::from_be_bytes(public[8 * k..8 * k + 8].try_into().unwrap())).collect()
            }
            Source::Root(i) => {
                seen[1] += 1;
                let at = recorded.roots_at[i as usize];
                word_limbs(&stream[at..at + 32].try_into().unwrap()).to_vec()
            }
            Source::Element(e) => {
                seen[2] += 1;
                let x = elements[&e];
                vec![x.c0, x.c1, x.c2]
            }
            Source::Zero => {
                seen[3] += 1;
                let x = zero_nonconst[zero_at];
                zero_at += 1;
                vec![x.c0, x.c1, x.c2]
            }
        };
        assert_eq!(l, &want, "{label}: port {:?}", p.source);
    }
    assert_eq!(zero_at, zero_nonconst.len(), "{label}: every non-constant zero check has a port");
    assert_eq!(seen[2], elements.len(), "{label}: every element of the calls has a port");
    let nonzero_checks = zero_nonconst.iter().filter(|x| **x != E::default()).count();
    println!(
        "  {label}: internal pushes hold; ports (statement {}, roots {}, elements {}, zero checks {}) = π1's graph on this stream; {} of its zero checks fail",
        seen[0], seen[1], seen[2], seen[3], nonzero_checks
    );
}

fn xorshift(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

#[test]
#[ignore]
fn review_mutated_streams() {
    deep(|| {
        let layout = layout_of_env();
        let (v, recorded, iv, stream) = setup("main_line_rec");
        println!("{layout:?} × main_line_rec, stream {} B", stream.len());
        differential(&recorded, layout, iv, v.public, &stream, "honest");
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        // One flipped bit, at a few places.
        for _ in 0..2 {
            let mut m = stream.clone();
            let at = xorshift(&mut s) as usize % m.len();
            m[at] ^= 1 << (xorshift(&mut s) % 8);
            differential(&recorded, layout, iv, v.public, &m, &format!("bit flipped in byte {at}"));
        }
        // 300 random bytes changed.
        let mut m = stream.clone();
        for _ in 0..300 {
            let at = xorshift(&mut s) as usize % m.len();
            m[at] = xorshift(&mut s) as u8;
        }
        differential(&recorded, layout, iv, v.public, &m, "300 bytes randomised");
        // A whole random stream, and a random public input.
        let m: Vec<u8> = (0..stream.len()).map(|_| xorshift(&mut s) as u8).collect();
        let mut public = [0u8; 32];
        public.iter_mut().for_each(|b| *b = xorshift(&mut s) as u8);
        differential(&recorded, layout, iv, public, &m, "random stream, random public input");
        // The counts at their extremes (the stream's first 24 bytes are the six 4-byte counts).
        let mut m = stream.clone();
        m[..24].fill(0xff);
        differential(&recorded, layout, iv, v.public, &m, "counts all ones");
        let mut m = stream.clone();
        m[..24].fill(0);
        differential(&recorded, layout, iv, v.public, &m, "counts zero");
    });
}
