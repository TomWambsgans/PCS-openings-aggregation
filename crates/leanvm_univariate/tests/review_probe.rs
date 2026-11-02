// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Review M1 (REVIEW-M1.md): the verifier's actual sizes, read from the code rather than from SPEC.md, for the
//! soundness recomputation (`review/review_m1_soundness.py`).
//!
//! `cargo test --release -p leanvm_univariate --test review_probe -- --nocapture`

use leanvm_flock_gas::shapes::{PROGRAM_IV, WORKLOADS};
use leanvm_univariate::contract::{record_verifier, rust_verifier, sample_stream};
use leanvm_univariate::heap::Leaves;
use leanvm_univariate::{Blake2s, Claims, FLOCK_MAIN, Shape};

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// Prints, per shape: the heap's blocks, every stack's variables and words, the relations, and the stream length.
#[test]
fn sizes_from_the_code() {
    deep(|| {
        for workload in &WORKLOADS {
            let shape = Shape::of(&workload.shape);
            let heap = shape.heap();
            let recorded = record_verifier(&shape, Blake2s::Flock(FLOCK_MAIN), Claims::Point);
            let stream = sample_stream(recorded.stream_len, 1);
            let (reduced, zero, nonzero) =
                rust_verifier(&shape, &PROGRAM_IV, &[1; 32], &stream, Blake2s::Flock(FLOCK_MAIN), Claims::Point)
                    .expect("length");
            println!(
                "SHAPE {} lm {} lb {} rows {:?} heights {:?} r_w {} H {} relations {} stream {} zero-checks {} nonzero-checks {}",
                workload.xmss,
                shape.log_memory,
                shape.log_bytecode,
                shape.table_rows,
                shape.heights(),
                shape.constraint_vars(),
                heap.h,
                reduced.relations,
                recorded.stream_len,
                zero.len(),
                nonzero.len()
            );
            for block in &heap.blocks {
                let name = match block.leaves {
                    Leaves::Memory => "memory".to_string(),
                    Leaves::Bytecode => "bytecode".to_string(),
                    Leaves::Table(t) => format!("table{t}"),
                    Leaves::Unused => "unused".to_string(),
                };
                println!("  BLOCK {name} r {} position {}", block.r, block.position);
            }
            for (commitment, vars) in &reduced.stack_vars {
                println!("  STACK {commitment:?} vars {vars}");
            }
        }
    });
}
