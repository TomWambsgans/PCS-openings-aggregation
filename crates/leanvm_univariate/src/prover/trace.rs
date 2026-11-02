// Part of this repository. Reads what `dump/trace_dump.rs` writes from a leanVM 42422001 checkout: leanVM's own
// execution and witness generation (crates/leanvm_core/src/cpu/{execute,layout}.rs there), column for column.
// MIT OR Apache-2.0; see NOTICE.md.
//! An execution trace of leanVM 42422001, as its prover laid it out: the tables' columns (in `leanvm_flock_gas`'s
//! `layout::tables` order, BLAKE2S's eighteen value limbs included), the memory image and its final counts, the
//! bytecode's final counts, `q_flock`, and the stacked bytecode.

use std::path::Path;

use leanvm_flock_gas::N_TABLES;
use leanvm_flock_gas::layout::tables;
use primitives::field::F64;

use crate::verifier::Shape;

/// One execution: every column leanVM 42422001 commits or carries, at its padded height.
pub struct Trace {
    pub log_memory: usize,
    pub log_bytecode: usize,
    pub rows: [u64; N_TABLES],
    pub heights: [usize; N_TABLES],
    /// The public input: memory cells 0 and 1, three limbs each.
    pub public: [[u64; 3]; 2],
    /// The memory's three limbs and its final counts `g^(accesses)`, `2^log_memory` each.
    pub memory: [Vec<F64>; 4],
    /// The bytecode's final counts, `2^log_bytecode`.
    pub bytecode_final: Vec<F64>,
    /// Flock's packed witness: word `slot + 256 · instance`.
    pub qflock: Vec<F64>,
    /// `tables[t][c][i]`: table `t`'s column `c` at row `i` (`2^heights[t]` rows, padding rows included).
    pub tables: Vec<Vec<Vec<F64>>>,
    /// leanVM's stacked bytecode: word `instruction + 2^log_bytecode · slot`.
    pub bytecode: Vec<F64>,
}

fn words(bytes: &[u8]) -> Vec<F64> {
    bytes
        .as_chunks::<8>()
        .0
        .iter()
        .map(|w| F64(u64::from_le_bytes(*w)))
        .collect()
}

impl Trace {
    /// The trace `trace_dump.rs` wrote to `dir`.
    pub fn load(dir: &Path) -> std::io::Result<Self> {
        let meta = std::fs::read_to_string(dir.join("meta.txt"))?;
        let field = |name: &str| -> Vec<u64> {
            let line = meta
                .lines()
                .find(|l| l.split_whitespace().next() == Some(name))
                .unwrap_or_else(|| panic!("meta.txt has no {name}"));
            line.split_whitespace().skip(1).map(|x| x.parse().expect("a number")).collect()
        };
        let log_memory = field("log_mem")[0] as usize;
        let log_bytecode = field("log_bytecode")[0] as usize;
        let rows: [u64; N_TABLES] = field("rows").try_into().expect("six tables");
        let heights: [usize; N_TABLES] = field("taus")
            .into_iter()
            .map(|x| x as usize)
            .collect::<Vec<_>>()
            .try_into()
            .expect("six tables");
        let pi = field("pi");
        let lengths: Vec<usize> = meta
            .lines()
            .filter(|l| l.starts_with("column "))
            .map(|l| l.split_whitespace().nth(2).expect("a length").parse().expect("a number"))
            .collect();
        let all = std::fs::read(dir.join("columns.bin"))?;
        let total: usize = lengths.iter().sum();
        assert_eq!(all.len(), 8 * total, "columns.bin holds the columns meta.txt lists");
        let mut columns = Vec::with_capacity(lengths.len());
        let mut at = 0;
        for &len in &lengths {
            columns.push(words(&all[8 * at..8 * (at + len)]));
            at += len;
        }
        drop(all);
        let layout = tables();
        let widths: Vec<usize> = layout.iter().map(|t| t.width()).collect();
        assert_eq!(columns.len(), 6 + widths.iter().sum::<usize>(), "leanVM's columns are the port's");
        let mut rest = columns.split_off(6);
        let qflock = columns.pop().expect("q_flock");
        let bytecode_final = columns.pop().expect("the bytecode's final counts");
        let memory: [Vec<F64>; 4] = columns.try_into().expect("the memory's four columns");
        let mut tables_columns = Vec::with_capacity(N_TABLES);
        for (t, &width) in widths.iter().enumerate() {
            let table: Vec<Vec<F64>> = rest.drain(..width).collect();
            assert!(table.iter().all(|c| c.len() == 1 << heights[t]), "table {t} at its height");
            tables_columns.push(table);
        }
        let bytecode = words(&std::fs::read(dir.join("bytecode.bin"))?);
        assert!(memory.iter().all(|c| c.len() == 1 << log_memory));
        assert_eq!(bytecode_final.len(), 1 << log_bytecode);
        assert_eq!(bytecode.len(), 16 << log_bytecode);
        assert_eq!(qflock.len(), 1 << (heights[5] + 8));
        Ok(Self {
            log_memory,
            log_bytecode,
            rows,
            heights,
            public: [[pi[0], pi[1], pi[2]], [pi[3], pi[4], pi[5]]],
            memory,
            bytecode_final,
            qflock,
            tables: tables_columns,
            bytecode,
        })
    }

    /// The shape the verifier is built for.
    pub fn shape(&self) -> Shape {
        Shape {
            log_memory: self.log_memory,
            log_bytecode: self.log_bytecode,
            table_rows: self.rows,
        }
    }

    /// The public input as the contract's calldata carries it: four 64-bit words, big-endian, cell 0's two low limbs
    /// then cell 1's (the verifier's lines put word `k` and `k + 2` at limb `k` of cells 0 and 1).
    pub fn public_input(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        let words = [self.public[0][0], self.public[0][1], self.public[1][0], self.public[1][1]];
        for (k, w) in words.iter().enumerate() {
            out[8 * k..8 * k + 8].copy_from_slice(&w.to_be_bytes());
        }
        out
    }
}
