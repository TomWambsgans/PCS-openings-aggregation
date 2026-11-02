// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The quotients alone on a real trace, timed one by one, at fixed challenges (no proof):
//! `LEANVM_TRACE=<dir> cargo test --release -p leanvm_univariate --test prove_quotients -- --ignored --nocapture`.

use leanvm_univariate::heap::Leaves;
use leanvm_univariate::prover::bus::{Bus, all_leaves, heap};
use leanvm_univariate::prover::columns::{c1_polys, setup_polys};
use leanvm_univariate::prover::poly::novel_limbs;
use leanvm_univariate::prover::prove::{constraint_count, table_leaf_count};
use leanvm_univariate::prover::quotients::{self, Quotient};
use leanvm_univariate::prover::trace::Trace;
use leanvm_univariate::verifier::chunks;
use primitives::field::{F64, F192};

/// leanVM's CLI allocator, as its reference timings are taken with.
#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

fn timed<R>(name: &str, f: impl FnOnce() -> R) -> R {
    let started = std::time::Instant::now();
    let out = f();
    println!("  {:8.3} s  {name}", started.elapsed().as_secs_f64());
    out
}

#[test]
#[ignore]
fn quotients_alone() {
    let Some(dir) = std::env::var("LEANVM_TRACE").ok() else {
        println!("LEANVM_TRACE is not set: nothing to time");
        return;
    };
    parallel::init();
    let mut trace = Trace::load(std::path::Path::new(&dir)).expect("a trace");
    trace.place();
    let shape = trace.shape();
    let (c1, setup) = timed("C1 and setup polynomials", || (c1_polys(&trace), setup_polys(&trace)));
    let alphas = [
        F192::new(3, 1, 4),
        F192::new(1, 5, 9),
        F192::new(2, 6, 5),
        F192::new(3, 5, 8),
    ];
    let bus = Bus::new(&alphas, F192::new(9, 7, 9));
    let layout = shape.heap();
    let (leaves, heap_novel) = timed("heap: leaves, products, inverse NTT", || {
        let leaves = all_leaves(&trace, &bus).expect("leaves");
        let values = heap(&layout, &leaves);
        (leaves, novel_limbs(&values))
    });
    let mut all: Vec<(String, Quotient)> = Vec::new();
    all.push(("tree".into(), timed("quotient: tree", || quotients::tree(&heap_novel))));
    let started = std::time::Instant::now();
    for block in &layout.blocks {
        let n = 1u64 << block.r;
        let values = match block.leaves {
            Leaves::Unused => continue,
            other => &leaves.iter().find(|(l, _)| *l == other).expect("leaves").1,
        };
        let r_novel = novel_limbs(values);
        let (name, q) = match block.leaves {
            Leaves::Memory => (
                "memory".to_string(),
                timed("leaf: memory", || {
                    quotients::memory_leaf(&trace, &c1, &setup, &bus, &r_novel, n - 1)
                }),
            ),
            Leaves::Bytecode => (
                "bytecode".to_string(),
                timed("leaf: bytecode", || {
                    quotients::bytecode_leaf(&trace, &c1, &setup, &bus, &r_novel, n - 1)
                }),
            ),
            Leaves::Table(t) => {
                let name = leanvm_flock_gas::TABLE_NAMES[t];
                let q = timed(&format!("leaf: {name}"), || {
                    quotients::table_leaf(&trace, t, &c1, &bus, &r_novel, table_leaf_count(t, block.r))
                });
                (name.to_string(), q)
            }
            Leaves::Unused => unreachable!(),
        };
        all.push((name, q));
    }
    println!("  {:8.3} s  quotients: leaves", started.elapsed().as_secs_f64());
    let [a, b] = trace.public;
    let lines = [(F64(a[0]), F64(b[0])), (F64(a[1]), F64(b[1])), (F64::ZERO, F64::ZERO)];
    let constraint = timed("quotient: constraints", || {
        quotients::constraints(&trace, &c1, F192::new(2, 7, 1), constraint_count(&trace), lines)
    });
    all.push(("constraints".into(), constraint));
    timed("chunks in basis B", || {
        for (_, q) in &all {
            let sizes = chunks(q.count);
            for chunk in 0..sizes.len() {
                for limb in 0..3 {
                    let mut out = vec![F64::ZERO; 1 << sizes[chunk]];
                    q.chunk_b(&sizes, chunk, limb, &mut out);
                }
            }
        }
    });
    for (name, q) in &all {
        println!("  {name}: degree {}, count {}, fits {}", q.degree, q.count, q.fits());
    }
    println!("  peak RSS {:.2} GB", bench::peak_rss_bytes() as f64 / 1e9);
}
