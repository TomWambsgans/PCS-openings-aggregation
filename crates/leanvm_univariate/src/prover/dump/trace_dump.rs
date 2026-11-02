// Part of PCS-openings-aggregation (crates/leanvm_univariate/src/prover/dump), not of leanVM, and not a module of
// that crate: `apply.sh` copies it into a leanVM (https://github.com/leanEthereum/leanVM) checkout at commit 42422001
// as crates/leanvm_core/src/cpu/trace_dump.rs. MIT OR Apache-2.0; see NOTICE.md.
//! The execution trace of a proof, written for the univariate prover (`crates/leanvm_univariate/PROVER.md`): when
//! `LEANVM_TRACE_DUMP` names a directory, [`maybe_dump`] writes there, right after leanVM built its witness, every
//! column leanVM 42422001 commits or carries (its global order: the memory's three limbs, its final counts, the
//! bytecode's final counts, `q_flock`, then each table's columns, BLAKE2S's eighteen virtual value limbs included),
//! the stacked bytecode, and the sizes. leanVM's proof then goes on unchanged.
//!
//! - `meta.txt`: `log_mem`, `log_bytecode`, `rows` (six), `taus` (six), `pi` (the two public cells, three limbs
//!   each), `columns n`, then `column i len committed|virtual` per column;
//! - `columns.bin`: the columns in that order, each its `len` words, 8 little-endian bytes a word;
//! - `bytecode.bin`: the stacked bytecode (`layout::bytecode_table`), 8 little-endian bytes a word.

use std::fmt::Write as _;
use std::io::Write as _;

use super::Program;
use super::layout::Witness;

pub(crate) fn maybe_dump(program: &Program, w: &Witness) {
    let Some(dir) = std::env::var_os("LEANVM_TRACE_DUMP") else {
        return;
    };
    let started = std::time::Instant::now();
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).expect("the dump directory");
    let l = &w.layout;
    let columns = w.columns();
    let join = |v: &[usize]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
    let mut meta = String::new();
    writeln!(meta, "log_mem {}", w.log_mem).unwrap();
    writeln!(meta, "log_bytecode {}", program.prog.len().trailing_zeros()).unwrap();
    writeln!(meta, "rows {}", join(&l.rows)).unwrap();
    writeln!(meta, "taus {}", join(&l.taus)).unwrap();
    let [a, b] = l.pi;
    writeln!(meta, "pi {} {} {} {} {} {}", a.c0, a.c1, a.c2, b.c0, b.c1, b.c2).unwrap();
    writeln!(meta, "columns {}", columns.len()).unwrap();
    for (i, column) in columns.iter().enumerate() {
        let kind = if l.placements[i].is_virtual() { "virtual" } else { "committed" };
        writeln!(meta, "column {i} {} {kind}", column.len()).unwrap();
    }
    std::fs::write(dir.join("meta.txt"), meta).expect("meta.txt");
    let mut out = std::io::BufWriter::with_capacity(1 << 24, std::fs::File::create(dir.join("columns.bin")).unwrap());
    for column in &columns {
        for chunk in column.chunks(1 << 16) {
            let bytes: Vec<u8> = chunk.iter().flat_map(|x| x.0.to_le_bytes()).collect();
            out.write_all(&bytes).expect("columns.bin");
        }
    }
    out.flush().expect("columns.bin");
    let table = super::layout::bytecode_table(&program.prog);
    let bytes: Vec<u8> = table.iter().flat_map(|x| x.0.to_le_bytes()).collect();
    std::fs::write(dir.join("bytecode.bin"), bytes).expect("bytecode.bin");
    eprintln!(
        "trace dumped to {} in {:.2} s",
        dir.display(),
        started.elapsed().as_secs_f64()
    );
}
