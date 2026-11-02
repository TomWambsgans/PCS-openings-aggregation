// Part of this repository. The tiny executions (`Rng`, `row_of`, `execution`) are copied from tests/review_honest.rs
// (review M1's independent honest prover) as iteration 2 has them (the rows placed at the fixed cosets, SPEC.md
// §13), unchanged but for `Witness` keeping only what a trace needs.
// MIT OR Apache-2.0; see NOTICE.md.
//! The prover at tiny and uneven sizes: the review's 15- to 31-cycle executions over all six tables (memory and
//! bytecode of `2^4` and `2^5`, tables of 0 to 6 rows, DEREF's gated store), as a leanVM trace, proven by the prover
//! and accepted by the verifier with its three WHIR openings. Flock is omitted, as in the review's prover.
//!
//! `cargo test --release -p leanvm_univariate --test prove_tiny -- --nocapture`

// The copied execution keeps the review's spelling.
#![allow(clippy::assign_op_pattern)]

use leanvm_flock_gas::field::{E, GEN, ONE, ZERO};
use leanvm_flock_gas::layout::{
    BLAKE2S_SLOTS, N_TABLES, OP_BLAKE2S, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_XOR, SEP_BYTECODE, SEP_MEM, SEP_STATE,
    Table, gpow, tables,
};
use leanvm_univariate::prover::prove::{Config, prove, verify};
use leanvm_univariate::contract::SetupRoots;
use leanvm_univariate::domain::active_positions;
use leanvm_univariate::prover::trace::Trace;
use leanvm_univariate::{Blake2s, Claims, Shape};
use primitives::field::F64;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn k(&mut self) -> E {
        E::new(self.next(), 0, 0)
    }
}

thread_local! { static SIZES: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((4, 4)) }; }
fn lm() -> usize {
    SIZES.get().0
}
fn lb() -> usize {
    SIZES.get().1
}

fn col(table: &Table, name: &str) -> usize {
    table.columns.iter().position(|&c| c == name).unwrap_or_else(|| panic!("column {name}"))
}

/// A row's column values from its instruction: the operands as `g^cell`, the values read from `memory`.
fn row_of(table: &Table, step: u64, cells: &[u64], memory: &[[E; 3]]) -> Vec<E> {
    let mut row = vec![ZERO; table.width()];
    row[col(table, "pc")] = gpow(step);
    row[col(table, "fp")] = ONE;
    let set = |row: &mut Vec<E>, name: &str, v: E| row[col(table, name)] = v;
    match table.opcode {
        OP_SET => {
            set(&mut row, "o", gpow(cells[0]));
            for k in 0..3 {
                set(&mut row, &format!("k_{k}"), memory[cells[0] as usize][k]);
            }
        }
        OP_XOR | OP_MUL => {
            for (name, &c) in ["o_a", "o_b", "o_c"].iter().zip(cells) {
                set(&mut row, name, gpow(c));
            }
            for k in 0..3 {
                set(&mut row, &format!("va_{k}"), memory[cells[0] as usize][k]);
                set(&mut row, &format!("vb_{k}"), memory[cells[1] as usize][k]);
            }
        }
        OP_JUMP => {
            for (name, &c) in ["o_c", "o_d", "o_f"].iter().zip(cells) {
                set(&mut row, name, gpow(c));
            }
            set(&mut row, "v_cond", memory[cells[0] as usize][0]);
            set(&mut row, "v_pc", memory[cells[1] as usize][0]);
            set(&mut row, "v_fp", memory[cells[2] as usize][0]);
        }
        OP_BLAKE2S => {
            let names = ["o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md"];
            for (name, &c) in names.iter().zip(cells) {
                set(&mut row, name, gpow(c));
            }
            let reads = [
                ("m0", cells[0]),
                ("m1", cells[1]),
                ("m2", cells[2]),
                ("m3", cells[3]),
                ("cv0", cells[4]),
                ("cv1", cells[4] + 1),
                ("out0", cells[5]),
                ("out1", cells[5] + 1),
                ("md", cells[6]),
            ];
            for (cell, c) in reads {
                set(&mut row, &format!("{cell}_lo"), memory[c as usize][0]);
                set(&mut row, &format!("{cell}_hi"), memory[c as usize][1]);
            }
        }
        OP_DEREF => {
            set(&mut row, "o1", gpow(cells[0]));
            set(&mut row, "o2", gpow(cells[1]));
            set(&mut row, "o3", gpow(cells[2]));
            set(&mut row, "f_fp", E::new(cells[3], 0, 0));
            set(&mut row, "ptr", memory[cells[0] as usize][0]);
            for k in 0..3 {
                set(&mut row, &format!("v3_{k}"), memory[cells[2] as usize][k]);
            }
        }
        _ => unreachable!(),
    }
    row
}

struct Witness {
    rows: Vec<Vec<Vec<E>>>,
    active: [u64; N_TABLES],
    memory: Vec<[E; 3]>,
    memory_final: Vec<E>,
    bytecode: Vec<[E; 16]>,
    bytecode_final: Vec<E>,
    qflock: Vec<E>,
    public: [u64; 4],
}

fn shape_of(table_rows: [u64; N_TABLES]) -> Shape {
    Shape {
        log_memory: lm(),
        log_bytecode: lb(),
        table_rows,
    }
}

fn execution(rng: &mut Rng) -> Witness {
    let tables = tables();
    let public = [rng.next(), rng.next(), rng.next(), rng.next()];
    let mut memory = vec![[ZERO; 3]; 1 << lm()];
    memory[0] = [E::new(public[0], 0, 0), E::new(public[1], 0, 0), ZERO];
    memory[1] = [E::new(public[2], 0, 0), E::new(public[3], 0, 0), ZERO];
    memory[2] = [rng.k(), rng.k(), rng.k()];
    memory[3] = [rng.k(), rng.k(), rng.k()];
    memory[4] = std::array::from_fn(|k| memory[2][k] + memory[3][k]);
    let lanes: [&[(usize, usize)]; 3] = [
        &[(0, 0), (1, 2), (2, 1)],
        &[(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
        &[(0, 2), (1, 1), (2, 0), (2, 2)],
    ];
    memory[5] = std::array::from_fn(|k| lanes[k].iter().fold(ZERO, |acc, &(j, l)| acc + memory[2][j] * memory[3][l]));
    memory[6] = [ZERO; 3];
    memory[7] = [rng.k(), ZERO, ZERO];
    for cell in memory.iter_mut().skip(8) {
        *cell = [rng.k(), rng.k(), ZERO];
    }
    let blake = [8, 9, 10, 11, 12, 14, 8];
    let deref = lm() >= 5 && lb() >= 5;
    if deref {
        memory[16] = [gpow(17), ZERO, ZERO];
        memory[19] = [rng.k(), rng.k(), rng.k()];
        memory[18] = memory[19];
        memory[20] = [ONE, ZERO, ZERO];
    }
    let round = if deref { 6 } else { 5 };
    let program: Vec<(usize, Vec<u64>)> = (0..(1usize << lb()) - 1)
        .map(|step| match step % round {
            0 => (OP_SET, vec![2 + (step / round % 3) as u64]),
            1 => (OP_XOR, vec![2, 3, 4]),
            2 => (OP_MUL, vec![2, 3, 5]),
            3 => (OP_JUMP, vec![6, 7, 7]),
            4 => (OP_BLAKE2S, blake.to_vec()),
            _ => {
                if step / round % 2 == 0 {
                    (OP_DEREF, vec![16, 1, 19, 0])
                } else {
                    (OP_DEREF, vec![16, 3, 19, 1])
                }
            }
        })
        .collect();
    let cell_of = |address: E| (0..1u64 << lm()).find(|&c| gpow(c) == address).expect("an address of the memory");
    let mut memory_count = vec![ONE; 1 << lm()];
    let mut bytecode_count = vec![ONE; 1 << lb()];
    let mut bytecode = vec![[ZERO; 16]; 1 << lb()];
    let mut active: Vec<Vec<Vec<E>>> = vec![vec![]; N_TABLES];
    for (step, (opcode, cells)) in program.iter().enumerate() {
        let table = &tables[*opcode];
        let mut row = row_of(table, step as u64, cells, &memory);
        for pulled in &table.flushes.pull {
            let separator = pulled[0].evaluate(&row);
            let counter = || -> usize {
                let (monomial, _) = pulled[2].terms().next().expect("a counter");
                monomial[0]
            };
            if separator == SEP_MEM {
                let cell = cell_of(pulled[1].evaluate(&row)) as usize;
                row[counter()] = memory_count[cell];
                memory_count[cell] = memory_count[cell] * GEN;
                for k in 0..3 {
                    assert_eq!(pulled[3 + k].evaluate(&row), memory[cell][k], "the memory holds what step {step} reads");
                }
            } else if separator == SEP_BYTECODE {
                row[counter()] = bytecode_count[step];
                bytecode_count[step] = bytecode_count[step] * GEN;
                let mut slots = [ZERO; 16];
                for (s, form) in pulled.iter().enumerate().skip(3) {
                    slots[s] = form.evaluate(&row);
                }
                bytecode[step] = slots;
            } else {
                assert_eq!(separator, SEP_STATE);
            }
        }
        active[*opcode].push(row);
    }
    bytecode[(1 << lb()) - 1] = std::array::from_fn(|s| if s >= 3 { rng.k() } else { ZERO });
    for (i, slots) in bytecode.iter_mut().enumerate() {
        slots[0] = SEP_BYTECODE;
        slots[1] = gpow(i as u64);
        slots[2] = ZERO;
    }
    let counts: [u64; N_TABLES] = std::array::from_fn(|t| active[t].len() as u64);
    let shape = shape_of(counts);
    let heights = shape.heights();
    let mut rows = Vec::new();
    for table in &tables {
        let r = heights[table.opcode];
        let n = 1usize << r;
        // Padding rows are free, but the counters' constraint holds on every row (SPEC.md §13): nonzero counters,
        // here 1.
        let mut padding = table.padding.clone();
        for c in table.count_columns() {
            padding[c] = ONE;
        }
        // The active rows sit at the fixed cosets of their count's set bits (SPEC.md §13), in order.
        let mut all = vec![padding; n];
        let count = active[table.opcode].len() as u64;
        for (row, at) in active[table.opcode].iter().zip(active_positions(count, r)) {
            all[at as usize] = row.clone();
        }
        rows.push(all);
    }
    // q_flock: instance i's slots are BLAKE2S row i's limbs (padding rows included); the other words random.
    let h_b = heights[OP_BLAKE2S];
    let mut qflock: Vec<E> = (0..1usize << (h_b + 8)).map(|_| rng.k()).collect();
    let blake = &tables[OP_BLAKE2S];
    for (i, row) in rows[OP_BLAKE2S].iter().enumerate() {
        for (slot, name) in BLAKE2S_SLOTS.iter().enumerate() {
            if let Some(name) = name {
                qflock[slot + 256 * i] = row[col(blake, name)];
            }
        }
    }
    Witness {
        rows,
        active: counts,
        memory,
        memory_final: memory_count,
        bytecode,
        bytecode_final: bytecode_count,
        qflock,
        public,
    }
}

/// The witness as the trace leanVM would dump: columns of K-words, leanVM's stacked bytecode (slots 0..2 zero).
fn trace_of(w: &Witness) -> Trace {
    let k = |x: E| {
        assert!(x.c1 == 0 && x.c2 == 0, "K-valued");
        F64(x.c0)
    };
    let heights = shape_of(w.active).heights();
    let tables = tables();
    let n_b = 1usize << lb();
    let mut bytecode = vec![F64::ZERO; 16 * n_b];
    for (i, slots) in w.bytecode.iter().enumerate() {
        for s in 3..16 {
            bytecode[s * n_b + i] = k(slots[s]);
        }
    }
    Trace {
        log_memory: lm(),
        log_bytecode: lb(),
        rows: w.active,
        heights,
        public: [[w.public[0], w.public[1], 0], [w.public[2], w.public[3], 0]],
        memory: [
            w.memory.iter().map(|c| k(c[0])).collect(),
            w.memory.iter().map(|c| k(c[1])).collect(),
            w.memory.iter().map(|c| k(c[2])).collect(),
            w.memory_final.iter().map(|&c| k(c)).collect(),
        ],
        bytecode_final: w.bytecode_final.iter().map(|&c| k(c)).collect(),
        qflock: w.qflock.iter().map(|&c| k(c)).collect(),
        tables: tables
            .iter()
            .map(|t| (0..t.width()).map(|c| w.rows[t.opcode].iter().map(|row| k(row[c])).collect()).collect())
            .collect(),
        bytecode,
        // The review's execution places its rows as the verifier wants them (SPEC.md §13, F1b).
        placed: true,
    }
}

#[test]
fn tiny_executions_are_proven_and_verified() {
    parallel::init();
    for (memory, bytecode) in [(4, 4), (5, 4), (4, 5), (5, 5)] {
        SIZES.set((memory, bytecode));
        let mut rng = Rng(0x5EED ^ (memory << 8 | bytecode) as u64);
        let trace = trace_of(&execution(&mut rng));
        let config = Config {
            blake2s: Blake2s::Omitted,
            claims: Claims::Point,
            check: true,
            garbage: false,
            stand_in_roots: None,
            roots: SetupRoots::REFERENCE,
        };
        let (proof, report) = prove(&trace, None, &[0x77; 32], config).expect("a proof");
        assert!(report.checks.iter().all(|(_, ok)| *ok), "{:?}", report.checks);
        for (name, degree, count, _) in &report.quotients {
            assert!(*degree < *count as i64, "{name}");
        }
        verify(&trace.shape(), &[0x77; 32], &trace.public_input(), &proof, Blake2s::Omitted, false).expect("accepted");
        // The review's honest prover sends these stand-in roots (it commits nothing): with them, the stream is the
        // one it writes for the same execution, byte for byte, if the two provers agree on every value.
        let stand_in = Config {
            stand_in_roots: Some([
                [E::new(0x1111, 0x2222, 0), E::new(0x3333, 0x4444, 0)],
                [E::new(0x5555, 0x6666, 0), E::new(0x7777, 0x8888, 0)],
            ]),
            ..config
        };
        let (cross, _) = prove(&trace, None, &[0x77; 32], stand_in).expect("a proof");
        // The review's prover's streams for these executions (`honest_proofs_at_other_sizes`, point claims, at
        // leanvm-univariate b948bfc), their Keccak-256's first bytes: the same, byte for byte. A protocol change
        // re-records them.
        let review: Option<[u8; 8]> = match (memory, bytecode) {
            (5, 4) => Some([0x46, 0xf7, 0x32, 0xab, 0xb5, 0x70, 0x15, 0x64]),
            (4, 5) => Some([0x64, 0xe3, 0x78, 0x10, 0xcc, 0xf4, 0x3b, 0xf0]),
            (5, 5) => Some([0xfe, 0x6d, 0xc4, 0x8f, 0xc5, 0xe4, 0x5b, 0xb0]),
            _ => None,
        };
        if let Some(review) = review {
            assert_eq!(&leanvm_flock_gas::transcript::keccak256(&cross.stream)[..8], &review, "the review's stream");
        }
        println!(
            "lm {memory} lb {bytecode}: rows {:?}, heights {:?}, stream {} bytes, accepted; with the review's stand-in \
             roots, stream keccak {:02x?}",
            trace.rows,
            trace.heights,
            proof.stream.len(),
            &leanvm_flock_gas::transcript::keccak256(&cross.stream)[..8]
        );
    }
}
