// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Review M1 (REVIEW-M1.md): a tiny honest prover for the univariate PIOP, written from SPEC.md and leanVM's tables
//! independently of the verifier's own evaluation code, and the experiments run on it.
//!
//! The prover works on polynomials in the monomial basis: every identity of SPEC.md §5–§6 is built as a polynomial,
//! divided exactly by its vanishing polynomial (a nonzero remainder fails the test), its quotient cut into the
//! verifier's chunks, and every committed column put in basis `B` by interpolation on `V_r`. The values at `t` are
//! monomial evaluations; the verifier's are multilinear claims at the digits, so the two paths are independent.
//! Flock is omitted (`Blake2s::Omitted`): BLAKE2S's rows are then only bus rows.
//!
//! `cargo test --release -p leanvm_univariate --test review_honest -- --nocapture`

use leanvm_flock_gas::evm::machine::{PcsOpen, call};
use leanvm_flock_gas::field::{E, GEN, ONE, ZERO};
use leanvm_flock_gas::layout::{
    BLAKE2S_SLOTS, Form, N_TABLES, OP_BLAKE2S, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_XOR, SEP_BYTECODE, SEP_MEM,
    SEP_STATE, Table, gpow, tables,
};
use leanvm_flock_gas::multilinear::{eq_kernel, multilinear_eval};
use leanvm_flock_gas::transcript::{Checks, KeccakChannel, KeccakWriter, keccak_seed};
use leanvm_univariate::claims::{Column, Combined, Commitment};
use leanvm_univariate::contract::{NAME, SetupRoots, calldata, compile_verifier, contract_iv, record_verifier};
use leanvm_univariate::domain::{coordinate_functionals, point_e};
use leanvm_univariate::heap::Leaves;
use leanvm_univariate::stacks::{StackLayout, limb_basis};
use leanvm_univariate::verifier::{chunks, degree, sent_columns};
use leanvm_univariate::{Blake2s, Claims, Opening, Shape, reduce};

// ---------------------------------------------------------------------------------------------------------------
// Polynomials over E, monomial basis, low first.

#[derive(Clone, Debug, PartialEq)]
struct Poly(Vec<E>);

impl Poly {
    fn zero() -> Self {
        Poly(vec![])
    }
    fn constant(c: E) -> Self {
        Poly(vec![c]).trim()
    }
    fn x() -> Self {
        Poly(vec![ZERO, ONE])
    }
    fn trim(mut self) -> Self {
        while self.0.last() == Some(&ZERO) {
            self.0.pop();
        }
        self
    }
    fn degree(&self) -> Option<usize> {
        let p = self.clone().trim();
        if p.0.is_empty() { None } else { Some(p.0.len() - 1) }
    }
    fn add(&self, o: &Poly) -> Poly {
        let n = self.0.len().max(o.0.len());
        Poly((0..n)
            .map(|i| self.0.get(i).copied().unwrap_or(ZERO) + o.0.get(i).copied().unwrap_or(ZERO))
            .collect())
        .trim()
    }
    fn mul(&self, o: &Poly) -> Poly {
        if self.0.is_empty() || o.0.is_empty() {
            return Poly::zero();
        }
        let mut out = vec![ZERO; self.0.len() + o.0.len() - 1];
        for (i, &a) in self.0.iter().enumerate() {
            if a == ZERO {
                continue;
            }
            for (j, &b) in o.0.iter().enumerate() {
                out[i + j] += a * b;
            }
        }
        Poly(out).trim()
    }
    fn scale(&self, c: E) -> Poly {
        Poly(self.0.iter().map(|&a| a * c).collect()).trim()
    }
    fn eval(&self, x: E) -> E {
        self.0.iter().rev().fold(ZERO, |acc, &c| acc * x + c)
    }
    fn compose(&self, inner: &Poly) -> Poly {
        self.0
            .iter()
            .rev()
            .fold(Poly::zero(), |acc, &c| acc.mul(inner).add(&Poly::constant(c)))
    }
    /// Division by a monic polynomial.
    fn divmod(&self, m: &Poly) -> (Poly, Poly) {
        let m = m.clone().trim();
        let dm = m.0.len() - 1;
        assert_eq!(m.0[dm], ONE, "monic divisor");
        let mut r = self.clone().trim().0;
        if r.len() <= dm {
            return (Poly::zero(), Poly(r).trim());
        }
        let mut q = vec![ZERO; r.len() - dm];
        for i in (dm..r.len()).rev() {
            let c = r[i];
            if c == ZERO {
                continue;
            }
            q[i - dm] = c;
            for j in 0..=dm {
                r[i - dm + j] += c * m.0[j];
            }
        }
        (Poly(q).trim(), Poly(r).trim())
    }
}

/// `w_0 = x`, `w_(l+1) = w_l^2 + w_l`.
fn w_polys(count: usize) -> Vec<Poly> {
    let mut w = vec![Poly::x()];
    for l in 1..count {
        let p = &w[l - 1];
        w.push(p.mul(p).add(p));
    }
    w
}

/// Basis `B` on `V_r`: `B_k = Π_l (w_l if k_l else 1 + w_l)` as monomial polynomials, and the inverse of
/// `M[i][k] = B_k(ω_i)`.
struct BasisB {
    r: usize,
    mono: Vec<Poly>,
    inverse: Vec<Vec<E>>,
}

impl BasisB {
    fn new(r: usize, w: &[Poly]) -> Self {
        let n = 1usize << r;
        let mono: Vec<Poly> = (0..n)
            .map(|k| {
                (0..r).fold(Poly::constant(ONE), |acc, l| {
                    let f = if k >> l & 1 == 1 { w[l].clone() } else { w[l].add(&Poly::constant(ONE)) };
                    acc.mul(&f)
                })
            })
            .collect();
        // M[i][k] = B_k(ω_i) = Π_l (ω_(i>>l) if k_l else 1 + ω_(i>>l)).
        let mut m: Vec<Vec<E>> = (0..n)
            .map(|i| {
                (0..n)
                    .map(|k| {
                        (0..r).fold(ONE, |acc, l| {
                            let d = point_e((i >> l) as u64);
                            acc * if k >> l & 1 == 1 { d } else { ONE + d }
                        })
                    })
                    .collect()
            })
            .collect();
        let mut inv: Vec<Vec<E>> = (0..n).map(|i| (0..n).map(|j| if i == j { ONE } else { ZERO }).collect()).collect();
        for col in 0..n {
            let pivot = (col..n).find(|&i| m[i][col] != ZERO).expect("invertible");
            m.swap(col, pivot);
            inv.swap(col, pivot);
            let p = m[col][col].inv();
            for j in 0..n {
                m[col][j] = m[col][j] * p;
                inv[col][j] = inv[col][j] * p;
            }
            for i in 0..n {
                let f = m[i][col];
                if i != col && f != ZERO {
                    for j in 0..n {
                        let (a, b) = (m[col][j], inv[col][j]);
                        m[i][j] += f * a;
                        inv[i][j] += f * b;
                    }
                }
            }
        }
        Self { r, mono, inverse: inv }
    }

    /// Values on `V_r` (row `i` at `ω_i`) to basis-`B` coefficients and the monomial polynomial.
    fn from_values(&self, values: &[E]) -> (Vec<E>, Poly) {
        let n = 1usize << self.r;
        assert_eq!(values.len(), n);
        let coefficients: Vec<E> =
            (0..n).map(|k| (0..n).fold(ZERO, |acc, i| acc + self.inverse[k][i] * values[i])).collect();
        let mono = coefficients
            .iter()
            .zip(&self.mono)
            .fold(Poly::zero(), |acc, (&c, b)| acc.add(&b.scale(c)));
        (coefficients, mono)
    }

    /// A polynomial of degree `< 2^r` to its basis-`B` coefficients.
    fn coefficients(&self, p: &Poly) -> Vec<E> {
        if let Some(d) = p.degree() {
            assert!(d < 1 << self.r, "degree {d} >= 2^{}", self.r);
        }
        let values: Vec<E> = (0..1u64 << self.r).map(|i| p.eval(point_e(i))).collect();
        self.from_values(&values).0
    }
}

struct Bases {
    w: Vec<Poly>,
    b: Vec<BasisB>,
}

impl Bases {
    fn new(max_r: usize) -> Self {
        let w = w_polys(max_r + 1);
        let b = (0..=max_r).map(|r| BasisB::new(r, &w)).collect();
        Self { w, b }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// A deterministic source of K elements.

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
    fn e(&mut self) -> E {
        E::new(self.next(), self.next(), self.next())
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The execution: a tiny program run from (pc 1, fp 1) to (g^15, 1).

thread_local! { static SIZES: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((4, 4)) }; }
fn lm() -> usize { SIZES.get().0 }
fn lb() -> usize { SIZES.get().1 }

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
            // No jump: v_cond = 0, b = 0, w = 0.
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
            // cells: the pointer's cell, o2's exponent, v3's cell, f_fp. The store goes to ptr · o2.
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

/// What the prover holds: every table's rows (padding included), the memory image and its final counts, the
/// bytecode and its final counts, and `q_flock` (the counter inverses are computed from the rows when proving).
#[derive(Clone)]
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

fn execution(rng: &mut Rng) -> Witness {
    let tables = tables();
    let public = [rng.next(), rng.next(), rng.next(), rng.next()];
    let mut memory = vec![[ZERO; 3]; 1 << lm()];
    memory[0] = [E::new(public[0], 0, 0), E::new(public[1], 0, 0), ZERO];
    memory[1] = [E::new(public[2], 0, 0), E::new(public[3], 0, 0), ZERO];
    memory[2] = [rng.k(), rng.k(), rng.k()];
    memory[3] = [rng.k(), rng.k(), rng.k()];
    // XOR's result: limb-wise sum; MUL's: the tower product (layout.rs's TOWER_LANES).
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
    // With 32 cells, DEREF too: cell 16 holds the pointer g^17; with f_fp = 0 the store at g^17 · g = cell 18 is
    // v3 = cell 19's value, with f_fp = 1 the store at g^17 · g^3 = cell 20 is (fp, 0, 0).
    let deref = lm() >= 5 && lb() >= 5;
    if deref {
        memory[16] = [gpow(17), ZERO, ZERO];
        memory[19] = [rng.k(), rng.k(), rng.k()];
        memory[18] = memory[19];
        memory[20] = [ONE, ZERO, ZERO];
    }
    let round = if deref { 6 } else { 5 };
    // A round of instructions, the SET's cell cycling 2, 3, 4; as many as the bytecode's 2^lb - 1 steps.
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
    assert!(lm() >= 4, "the program reads cells up to 15");
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
    // The last instruction is never run: any content.
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
        let n = 1usize << heights[table.opcode];
        let mut all = active[table.opcode].clone();
        while all.len() < n {
            // Padding rows are free, but the counters' constraint holds on every row (SPEC.md §13): nonzero
            // counters, here 1.
            let mut row = table.padding.clone();
            for c in table.count_columns() {
                row[c] = ONE;
            }
            all.push(row);
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

fn shape_of(table_rows: [u64; N_TABLES]) -> Shape {
    Shape {
        log_memory: lm(),
        log_bytecode: lb(),
        table_rows,
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The prover.

/// A form of a table's columns, on the columns' polynomials.
fn form_poly(form: &Form, columns: &[Poly]) -> Poly {
    form.terms().fold(Poly::zero(), |acc, (monomial, &c)| {
        let term = monomial.iter().fold(Poly::constant(c), |p, &i| p.mul(&columns[i]));
        acc.add(&term)
    })
}

fn fingerprint_poly(tuple: &[Form], weights: &[E], beta: E, columns: &[Poly]) -> Poly {
    tuple
        .iter()
        .zip(weights)
        .fold(Poly::constant(beta), |acc, (form, &w)| acc.add(&form_poly(form, columns).scale(w)))
}

fn fingerprint(tuple: &[Form], weights: &[E], beta: E, row: &[E]) -> E {
    tuple.iter().zip(weights).fold(beta, |acc, (form, &w)| acc + w * form.evaluate(row))
}

fn tuple_degree(tuple: &[Form]) -> usize {
    tuple
        .iter()
        .flat_map(|f| f.terms().filter(|(_, c)| **c != ZERO).map(|(m, _)| m.len()))
        .max()
        .unwrap_or(0)
        .max(1)
}

fn has_unsent(tuple: &[Form], sent: &[bool]) -> bool {
    tuple
        .iter()
        .any(|f| f.terms().any(|(m, c)| *c != ZERO && m.iter().any(|&i| !sent[i])))
}

/// The vanishing polynomial of the aligned cosets of `[0, rows)` (`prefix`) or of `[rows, 2^r)`.
fn vanishing(w: &[Poly], rows: u64, r: usize, prefix: bool) -> Poly {
    let mut out = Poly::constant(ONE);
    let factor = |b: usize, start: u64| w[b].add(&Poly::constant(point_e(start >> b)));
    if prefix {
        let mut start = 0u64;
        for b in (0..64).rev() {
            if rows >> b & 1 == 1 {
                out = out.mul(&factor(b, start));
                start += 1 << b;
            }
        }
    } else {
        let mut start = rows;
        while start < 1 << r {
            let mut b = (start.trailing_zeros() as usize).min(r);
            while start + (1 << b) > 1 << r {
                b -= 1;
            }
            out = out.mul(&factor(b, start));
            start += 1 << b;
        }
    }
    out
}

fn lift(w: &[Poly], r: usize, m: usize) -> Poly {
    (r..m).fold(Poly::constant(ONE), |acc, j| acc.mul(&w[j].add(&Poly::constant(ONE))))
}

/// A quotient cut into chunks `Q = Q_0 + w_(e_0) (Q_1 + w_(e_1) Q_2)`, each in basis `B`.
fn cut(q: &Poly, sizes: &[usize], bases: &Bases) -> Vec<Vec<E>> {
    let mut rest = q.clone();
    let mut out = Vec::new();
    for (c, &e) in sizes.iter().enumerate() {
        if c + 1 < sizes.len() {
            let (quotient, remainder) = rest.divmod(&bases.w[e]);
            out.push(bases.b[e].coefficients(&remainder));
            rest = quotient;
        } else {
            out.push(bases.b[e].coefficients(&rest));
        }
    }
    out
}

/// What is committed, column by column: coefficients (basis `B`, or values for `q_flock`) and variables.
#[derive(Clone, Default)]
struct Committed {
    columns: Vec<(Column, usize, Vec<E>)>,
}

impl Committed {
    fn push(&mut self, column: Column, vars: usize, data: Vec<E>) {
        assert_eq!(data.len(), 1 << vars, "{column:?}");
        self.columns.push((column, vars, data));
    }
    fn get(&self, column: Column) -> (usize, &[E]) {
        let (_, vars, data) = self.columns.iter().find(|(c, ..)| *c == column).unwrap_or_else(|| panic!("{column:?}"));
        (*vars, data)
    }
    /// A term's column at its point: the multilinear extension of the column's words at the point's first coordinates.
    fn at(&self, column: Column, point: &[E]) -> E {
        match column {
            Column::QflockSlot(j) => {
                let (vars, data) = self.get(Column::Qflock);
                let row: Vec<E> = (0..8).map(|b| E::new((j >> b & 1) as u64, 0, 0)).chain(point.iter().copied()).collect();
                assert_eq!(row.len(), vars);
                multilinear_eval(data, &row).unwrap()
            }
            _ => {
                let (vars, data) = self.get(column);
                multilinear_eval(data, &point[..vars]).unwrap()
            }
        }
    }
    fn claim_holds(&self, claim: &Combined<E>) -> bool {
        let total = claim.terms.iter().fold(ZERO, |acc, &(column, p, twist, coefficient)| {
            assert_eq!(twist, 0, "no Frobenius twist without Flock");
            acc + coefficient * self.at(column, &claim.points[p])
        });
        total == claim.value
    }
}

/// The stack of a commitment's columns (`stacks.rs`'s layout), as K-words.
fn stack(layout: &StackLayout, committed: &Committed) -> Vec<E> {
    let mut words = vec![ZERO; 1 << layout.vars];
    for &(column, limb, vars, offset) in &layout.blocks {
        let (v, data) = committed.get(column);
        assert_eq!(v, vars);
        for (i, x) in data.iter().enumerate() {
            if column.commitment() != Commitment::C2 {
                assert!(x.c1 == 0 && x.c2 == 0, "{column:?} is K-valued");
            }
            words[offset as usize + i] = E::new([x.c0, x.c1, x.c2][limb], 0, 0);
        }
    }
    words
}

/// The verifier's layouts (verifier.rs `layouts`), rebuilt from the same column lists.
fn c1_columns(shape: &Shape) -> Vec<(Column, usize, bool)> {
    let heights = shape.heights();
    let mut c1 = vec![(Column::Qflock, heights[OP_BLAKE2S] + 8, false)];
    for table in tables() {
        let h = heights[table.opcode];
        c1.extend((0..table.width()).map(|column| (Column::Table { table: table.opcode, column }, h, false)));
        c1.push((Column::Inverse(table.opcode), h, false));
    }
    c1.extend((0..4).map(|k| (Column::Memory(k), shape.log_memory, false)));
    c1.push((Column::BytecodeFinal, shape.log_bytecode, false));
    c1
}

/// The proof's knobs for the experiments.
#[derive(Clone, Copy, Default)]
struct Tamper {
    /// Heap position 0's value (unconstrained by the tree identity).
    node_zero: Option<E>,
}

struct Proof {
    stream: Vec<u8>,
    public: [u8; 32],
    c1: Committed,
    c2: Committed,
    setup: Committed,
    layouts: Vec<(Commitment, StackLayout)>,
    /// Every polynomial identity divided exactly.
    exact: bool,
}

const IV: [u8; 32] = [0x77; 32];

fn prove(witness: &Witness, mode: Claims, tamper: Tamper, bases: &Bases) -> Proof {
    let tables = tables();
    let shape = shape_of(witness.active);
    let heights = shape.heights();
    let heap = shape.heap();
    let h = heap.h;
    let r_w = shape.constraint_vars();
    let w = &bases.w;
    let mut exact = true;
    let public: [u8; 32] = {
        let mut b = [0u8; 32];
        for k in 0..4 {
            b[8 * k..8 * k + 8].copy_from_slice(&witness.public[k].to_be_bytes());
        }
        b
    };
    let seed = keccak_seed(&NAME, &contract_iv(&shape, &IV, &SetupRoots::REFERENCE), &public);
    let mut writer = KeccakWriter::new(seed);

    // C1 and the setup.
    let mut c1 = Committed::default();
    let mut setup = Committed::default();
    let mut columns: Vec<Vec<Poly>> = Vec::new();
    let mut inverse: Vec<Poly> = Vec::new();
    for table in &tables {
        let r = heights[table.opcode];
        let mut polys = Vec::new();
        for c in 0..table.width() {
            let values: Vec<E> = witness.rows[table.opcode].iter().map(|row| row[c]).collect();
            let (coefficients, mono) = bases.b[r].from_values(&values);
            c1.push(Column::Table { table: table.opcode, column: c }, r, coefficients);
            polys.push(mono);
        }
        let z: Vec<E> = witness.rows[table.opcode]
            .iter()
            .map(|row| table.count_columns().fold(ONE, |acc, c| acc * row[c]).inv())
            .collect();
        let (coefficients, mono) = bases.b[r].from_values(&z);
        c1.push(Column::Inverse(table.opcode), r, coefficients);
        inverse.push(mono);
        columns.push(polys);
    }
    let mut memory = Vec::new();
    for k in 0..3 {
        let values: Vec<E> = witness.memory.iter().map(|cell| cell[k]).collect();
        let (coefficients, mono) = bases.b[lm()].from_values(&values);
        c1.push(Column::Memory(k), lm(), coefficients);
        memory.push(mono);
    }
    let (coefficients, memory_final) = bases.b[lm()].from_values(&witness.memory_final);
    c1.push(Column::Memory(3), lm(), coefficients);
    let (coefficients, bytecode_final) = bases.b[lb()].from_values(&witness.bytecode_final);
    c1.push(Column::BytecodeFinal, lb(), coefficients);
    let h_b = heights[OP_BLAKE2S];
    c1.push(Column::Qflock, h_b + 8, witness.qflock.clone());
    let addresses: Vec<E> = (0..1u64 << lm()).map(gpow).collect();
    let (coefficients, address) = bases.b[lm()].from_values(&addresses);
    setup.push(Column::Address, lm(), coefficients);
    let mut slots = Vec::new();
    let mut tuple_words = vec![ZERO; 1 << (lb() + 4)];
    for s in 0..16 {
        let values: Vec<E> = witness.bytecode.iter().map(|slots| slots[s]).collect();
        let (coefficients, mono) = bases.b[lb()].from_values(&values);
        for (k, &c) in coefficients.iter().enumerate() {
            tuple_words[s + 16 * k] = c;
        }
        slots.push(mono);
    }
    setup.push(Column::BytecodeTuple, lb() + 4, tuple_words);

    // The tables' row counts (iteration 2, review M1's F1): six 32-bit integers before C1's root.
    for &rows in &witness.active {
        writer.send_integer(rows, 4);
    }
    writer.send_root([E::new(0x1111, 0x2222, 0), E::new(0x3333, 0x4444, 0)]);
    let alphas: Vec<E> = (0..4).map(|_| writer.sample()).collect();
    let beta = writer.sample();
    let gamma = writer.sample();
    let weights = eq_kernel(&alphas);

    // The heap's leaves.
    let mut leaves = vec![ZERO; 1 << h];
    let mut table_products: Vec<(Poly, Poly)> = Vec::new();
    for table in &tables {
        let r = heights[table.opcode];
        let mut p = Poly::constant(ONE);
        let mut q = Poly::constant(ONE);
        for (pulled, pushed) in table.flushes.pull.iter().zip(&table.flushes.push) {
            p = p.mul(&fingerprint_poly(pulled, &weights, beta, &columns[table.opcode]));
            q = q.mul(&fingerprint_poly(pushed, &weights, beta, &columns[table.opcode]));
        }
        table_products.push((p, q));
        let _ = r;
    }
    let memory_pull_poly = memory
        .iter()
        .enumerate()
        .fold(
            Poly::constant(beta + weights[0] * SEP_MEM)
                .add(&address.scale(weights[1]))
                .add(&memory_final.scale(weights[2])),
            |acc, (k, m)| acc.add(&m.scale(weights[3 + k])),
        );
    let memory_push_poly = memory_pull_poly.add(&memory_final.add(&Poly::constant(ONE)).scale(weights[2]));
    let bytecode_pull_poly = slots
        .iter()
        .enumerate()
        .fold(Poly::constant(beta).add(&bytecode_final.scale(weights[2])), |acc, (s, p)| acc.add(&p.scale(weights[s])));
    let bytecode_push_poly = bytecode_pull_poly.add(&bytecode_final.add(&Poly::constant(ONE)).scale(weights[2]));
    for block in &heap.blocks {
        let n = 1usize << block.r;
        for i in 0..n {
            let leaf = match block.leaves {
                Leaves::Unused => ONE,
                Leaves::Memory => {
                    let x = point_e(i as u64);
                    memory_push_poly.eval(x) * memory_pull_poly.eval(x).inv()
                }
                Leaves::Bytecode => {
                    let x = point_e(i as u64);
                    bytecode_push_poly.eval(x) * bytecode_pull_poly.eval(x).inv()
                }
                Leaves::Table(t) => {
                    if (i as u64) < witness.active[t] {
                        let row = &witness.rows[t][i];
                        let table = &tables[t];
                        let (mut p, mut q) = (ONE, ONE);
                        for (pulled, pushed) in table.flushes.pull.iter().zip(&table.flushes.push) {
                            p = p * fingerprint(pulled, &weights, beta, row);
                            q = q * fingerprint(pushed, &weights, beta, row);
                        }
                        q * p.inv()
                    } else {
                        ONE
                    }
                }
            };
            leaves[block.position as usize + i] = leaf;
        }
    }
    let mut heap_values = leaves;
    for j in (1..1usize << (h - 1)).rev() {
        heap_values[j] = heap_values[2 * j] * heap_values[2 * j + 1];
    }
    heap_values[0] = tamper.node_zero.unwrap_or(ZERO);
    let init = beta + weights[0] * SEP_STATE + weights[1] + weights[2];
    let fin = beta + weights[0] * SEP_STATE + weights[1] * gpow((1 << lb()) - 1) + weights[2];
    let balanced = heap_values[1] * init == fin;

    // C2: the heap, its tree quotient, the leaf quotients and the constraint quotient.
    let mut c2 = Committed::default();
    let mut c2_list: Vec<(Column, usize, bool)> = vec![
        (Column::Heap, h, true),
        (Column::TreeQuotient(0), h, true),
        (Column::TreeQuotient(1), 0, true),
    ];
    let (heap_coefficients, heap_poly) = bases.b[h].from_values(&heap_values);
    c2.push(Column::Heap, h, heap_coefficients);
    {
        let s = w[1].clone();
        let shifted = heap_poly.compose(&Poly::x().add(&Poly::constant(ONE)));
        let lhs = w[1].mul(&heap_poly.compose(&s).add(&heap_poly.mul(&shifted)));
        let (q, rem) = lhs.divmod(&w[h]);
        exact &= rem == Poly::zero();
        let (q1, q0) = q.divmod(&w[h]);
        assert!(q1.degree().unwrap_or(0) == 0, "Q_tree = Q_0 + w_H q_1");
        c2.push(Column::TreeQuotient(0), h, bases.b[h].coefficients(&q0));
        c2.push(Column::TreeQuotient(1), 0, vec![q1.0.first().copied().unwrap_or(ZERO)]);
    }

    // Q_W, in the verifier's order of γ's powers.
    let mut constraint = Poly::zero();
    let mut power = ONE;
    let mut quotient_degree: u64 = 0;
    let mut add_constraint = |c: Poly, l: &Poly, power: &mut E| {
        constraint = constraint.add(&c.mul(l).scale(*power));
        *power = *power * gamma;
    };
    for table in &tables {
        let t = table.opcode;
        let r = heights[t];
        let n = 1u64 << r;
        let l = lift(w, r, r_w);
        let cols = &columns[t];
        if t == OP_JUMP {
            let [cond, inverse_column, flag] = ["v_cond", "w", "b"].map(|name| col(table, name));
            add_constraint(cols[flag].add(&cols[cond].mul(&cols[inverse_column])), &l, &mut power);
            add_constraint(cols[cond].mul(&cols[flag].add(&Poly::constant(ONE))), &l, &mut power);
            quotient_degree = quotient_degree.max(degree(n, 2));
        }
        let counters = table.count_columns().fold(inverse[t].clone(), |acc, c| acc.mul(&cols[c]));
        add_constraint(counters.add(&Poly::constant(ONE)), &l, &mut power);
        let counts = table.count_columns().count() as u64;
        quotient_degree = quotient_degree.max(degree((n - 1) * (1 + counts), n));
        if t == OP_BLAKE2S {
            let functionals = coordinate_functionals(r);
            let y: Vec<Poly> = functionals
                .iter()
                .map(|row| {
                    row.iter().enumerate().fold(Poly::zero(), |acc, (m, &a)| {
                        let mut monomial = vec![ZERO; (1 << m) + 1];
                        monomial[1 << m] = E::from(a);
                        acc.add(&Poly(monomial))
                    })
                })
                .collect();
            for (c, &name) in table.columns.iter().enumerate() {
                if let Some(slot) = BLAKE2S_SLOTS.iter().position(|&s| s == Some(name)) {
                    let composed = (0..1usize << r).fold(Poly::zero(), |acc, i| {
                        let basis = (0..r).fold(Poly::constant(ONE), |p, b| {
                            p.mul(&if i >> b & 1 == 1 { y[b].clone() } else { y[b].add(&Poly::constant(ONE)) })
                        });
                        acc.add(&basis.scale(witness.qflock[slot + 256 * i]))
                    });
                    add_constraint(cols[c].add(&composed), &l, &mut power);
                }
            }
            quotient_degree = quotient_degree.max(degree((r as u64) * (n / 2), n));
        }
    }
    let [w0, w1, w2, w3] = witness.public.map(|v| E::new(v, 0, 0));
    let lines = [(w0, w2), (w1, w3), (ZERO, ZERO)];
    let l = lift(w, 1, r_w);
    for (k, (low, high)) in lines.into_iter().enumerate() {
        let line = Poly::constant(low).add(&Poly::x().scale(low + high));
        add_constraint(memory[k].add(&line), &l, &mut power);
    }
    quotient_degree = quotient_degree.max(degree(1 << lm(), 3));
    let (constraint_quotient, rem) = constraint.divmod(&w[r_w]);
    exact &= rem == Poly::zero();
    let constraint_chunks = chunks(quotient_degree + 1);
    for (c, coefficients) in cut(&constraint_quotient, &constraint_chunks, bases).into_iter().enumerate() {
        c2.push(Column::ConstraintQuotient(c), constraint_chunks[c], coefficients);
        c2_list.push((Column::ConstraintQuotient(c), constraint_chunks[c], true));
    }

    // The leaf quotients, block by block.
    for (index, block) in heap.blocks.iter().enumerate() {
        let n = 1u64 << block.r;
        let values: Vec<E> = (0..n as usize).map(|i| heap_values[block.position as usize + i]).collect();
        let (_, restriction) = bases.b[block.r].from_values(&values);
        let (a, b, degree) = match block.leaves {
            Leaves::Unused => continue,
            Leaves::Memory => (memory_pull_poly.clone(), memory_push_poly.clone(), degree(2 * (n - 1), n)),
            Leaves::Bytecode => (bytecode_pull_poly.clone(), bytecode_push_poly.clone(), degree(2 * (n - 1), n)),
            Leaves::Table(t) => {
                let table = &tables[t];
                let rows = witness.active[t];
                let active = vanishing(w, rows, block.r, true);
                let padding = vanishing(w, rows, block.r, false);
                let (p, q) = &table_products[t];
                let pull_degree = 1 + table.flushes.pull.iter().map(|f| tuple_degree(f)).sum::<usize>();
                let push_degree = table.flushes.push.iter().map(|f| tuple_degree(f)).sum::<usize>();
                // The capacity is the height's fewest rows', 2^(r-1) + 1 (iteration 2).
                let d = degree((pull_degree.max(push_degree) as u64) * (n - 1) + (n - Shape::least_rows(block.r)), n);
                (p.mul(&padding).add(&active), q.mul(&padding).add(&active), d)
            }
        };
        let lhs = restriction.mul(&a).add(&b);
        let (q, rem) = lhs.divmod(&w[block.r]);
        exact &= rem == Poly::zero();
        let sizes = chunks(degree + 1);
        for (chunk, coefficients) in cut(&q, &sizes, bases).into_iter().enumerate() {
            c2.push(Column::LeafQuotient { block: index, chunk }, sizes[chunk], coefficients);
            c2_list.push((Column::LeafQuotient { block: index, chunk }, sizes[chunk], true));
        }
    }

    writer.send_root([E::new(0x5555, 0x6666, 0), E::new(0x7777, 0x8888, 0)]);
    let t = writer.sample();

    // The values at t, in the verifier's order (SPEC.md §8).
    for table in &tables {
        let cols = &columns[table.opcode];
        let mut sent = vec![false; table.width()];
        for c in sent_columns(table) {
            writer.send(cols[c].eval(t));
            sent[c] = true;
        }
        for (pulled, pushed) in table.flushes.pull.iter().zip(&table.flushes.push) {
            if has_unsent(pulled, &sent) {
                writer.send(fingerprint_poly(pulled, &weights, beta, cols).eval(t));
            }
            let difference: Vec<Form> = pushed
                .iter()
                .zip(pulled)
                .map(|(a, b)| {
                    let mut d = a.clone();
                    d.add_scaled(b, ONE);
                    d
                })
                .collect();
            if has_unsent(&difference, &sent) {
                writer.send(fingerprint_poly(pushed, &weights, beta, cols).eval(t));
            }
        }
    }
    writer.send(memory_final.eval(t));
    writer.send(address.eval(t));
    writer.send(memory_pull_poly.eval(t));
    writer.send(bytecode_final.eval(t));
    writer.send(bytecode_pull_poly.eval(t));
    writer.send(heap_poly.eval(t));
    writer.send(constraint_quotient.eval(t));

    let layouts = vec![
        (Commitment::C1, StackLayout::new(&c1_columns(&shape))),
        (Commitment::C2, StackLayout::new(&c2_list)),
        (
            Commitment::Setup,
            StackLayout::new(&[(Column::BytecodeTuple, lb() + 4, false), (Column::Address, lm(), false)]),
        ),
    ];

    if mode == Claims::Point {
        // ρ, then the batching sumcheck: the verifier's combined claims are what it computes from the stream so far.
        let mut channel = KeccakChannel::new(seed, &writer.stream, Checks::Enforce);
        let words = witness.public.map(|v| E::new(v, 0, 0));
        let reduced = reduce(&shape, words, &mut channel, Blake2s::Omitted, Claims::Weighted).expect("the prefix");
        let _rho = writer.sample();
        let lambda = writer.sample();
        let committed = [&c1, &c2, &setup];
        let vars = layouts.iter().map(|(_, l)| l.vars).max().unwrap();
        let basis = limb_basis::<E>();
        let mut tables_w: Vec<Vec<E>> = Vec::new();
        let mut tables_c: Vec<Vec<E>> = Vec::new();
        let mut scale = ONE;
        for ((commitment, opening), (_, layout)) in reduced.openings.iter().zip(&layouts) {
            let Opening::Weighted(claim) = opening else { unreachable!() };
            let k = [Commitment::C1, Commitment::C2, Commitment::Setup].iter().position(|c| c == commitment).unwrap();
            let mut weight = vec![ZERO; 1 << vars];
            for &(column, p, _, coefficient) in &claim.terms {
                let point = &claim.points[p];
                let (stacked, row): (Column, Vec<E>) = match column {
                    Column::QflockSlot(j) => (
                        Column::Qflock,
                        (0..8).map(|b| E::new((j >> b & 1) as u64, 0, 0)).chain(point.iter().copied()).collect(),
                    ),
                    _ => (column, point.clone()),
                };
                for (limb, v, offset) in layout.limbs(stacked) {
                    let eq = eq_kernel(&row[..v]);
                    for (i, e) in eq.iter().enumerate() {
                        weight[offset as usize + i] += coefficient * basis[limb] * *e;
                    }
                }
            }
            let mut words = stack(layout, committed[k]);
            words.resize(1 << vars, ZERO);
            tables_w.push(weight.into_iter().map(|x| x * scale).collect());
            tables_c.push(words);
            scale = scale * lambda;
        }
        let mut challenges = Vec::new();
        for _ in 0..vars {
            let half = tables_w[0].len() / 2;
            let (mut c0, mut c2) = (ZERO, ZERO);
            for (wt, ct) in tables_w.iter().zip(&tables_c) {
                for i in 0..half {
                    c0 += wt[2 * i] * ct[2 * i];
                    c2 += (wt[2 * i + 1] + wt[2 * i]) * (ct[2 * i + 1] + ct[2 * i]);
                }
            }
            writer.send(c0);
            writer.send(c2);
            let r = writer.sample();
            challenges.push(r);
            for table in tables_w.iter_mut().chain(tables_c.iter_mut()) {
                for i in 0..half {
                    table[i] = table[2 * i] + r * (table[2 * i + 1] + table[2 * i]);
                }
                table.truncate(half);
            }
        }
        for (k, (_, layout)) in layouts.iter().enumerate() {
            let words = stack(layout, committed[k]);
            writer.send(multilinear_eval(&words, &challenges[..layout.vars]).unwrap());
        }
    }
    let _ = balanced;
    Proof {
        stream: writer.stream,
        public,
        c1,
        c2,
        setup,
        layouts,
        exact,
    }
}

/// The verifier on a proof, and what `PCS_OPEN` would answer: every claim checked against what was committed.
fn verify(witness: &Witness, proof: &Proof, mode: Claims) -> Result<bool, leanvm_flock_gas::VerifierError> {
    let shape = shape_of(witness.active);
    let seed = keccak_seed(&NAME, &contract_iv(&shape, &IV, &SetupRoots::REFERENCE), &proof.public);
    let mut channel = KeccakChannel::new(seed, &proof.stream, Checks::Enforce);
    let words = witness.public.map(|v| E::new(v, 0, 0));
    let reduced = reduce(&shape, words, &mut channel, Blake2s::Omitted, mode)?;
    channel.finish()?;
    let committed = |c: Commitment| match c {
        Commitment::C1 => &proof.c1,
        Commitment::C2 => &proof.c2,
        Commitment::Setup => &proof.setup,
    };
    let mut all = true;
    for (commitment, opening) in &reduced.openings {
        let holds = match opening {
            Opening::Weighted(claim) => committed(*commitment).claim_holds(claim),
            Opening::Point { point, value, .. } => {
                let layout = &proof.layouts.iter().find(|(c, _)| c == commitment).unwrap().1;
                let words = stack(layout, committed(*commitment));
                multilinear_eval(&words, point).unwrap() == *value
            }
        };
        if !holds {
            println!("  the claim on {commitment:?} is false");
        }
        all &= holds;
    }
    Ok(all)
}

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// Completeness: the honest proof of the tiny execution divides every identity exactly, and the verifier accepts it,
/// with weighted claims (each commitment's combined relations true of what was committed) and with `PCS_OPEN`'s
/// point claims (the batching sumcheck closes, its point claims true).
#[test]
fn honest_proof_is_accepted() {
    deep(|| {
        let bases = Bases::new(7);
        let mut rng = Rng(0x5EED);
        let witness = execution(&mut rng);
        println!("rows {:?}, heap {:?}", witness.active, shape_of(witness.active).heap().blocks.len());
        for mode in [Claims::Weighted, Claims::Point] {
            let proof = prove(&witness, mode, Tamper::default(), &bases);
            assert!(proof.exact, "every identity divides exactly");
            assert_eq!(verify(&witness, &proof, mode), Ok(true), "{mode:?}");
        }
    });
}

/// Completeness at other sizes: the memory larger than the bytecode and smaller (the bytecode's block first in the
/// heap, as at 128 signatures), tables of 8 rows, every unused-block arrangement these give.
#[test]
fn honest_proofs_at_other_sizes() {
    for (memory, bytecode) in [(5, 4), (4, 5), (5, 5)] {
        deep(move || {
            SIZES.set((memory, bytecode));
            let bases = Bases::new(8);
            let mut rng = Rng(0x5EED ^ (memory << 8 | bytecode) as u64);
            let witness = execution(&mut rng);
            let shape = shape_of(witness.active);
            let blocks: Vec<_> = shape.heap().blocks.iter().map(|b| (b.leaves, b.r)).collect();
            println!("lm {memory} lb {bytecode}: rows {:?}, H {}, blocks {blocks:?}", witness.active, shape.heap().h);
            for mode in [Claims::Weighted, Claims::Point] {
                let proof = prove(&witness, mode, Tamper::default(), &bases);
                assert!(proof.exact, "every identity divides exactly");
                assert_eq!(verify(&witness, &proof, mode), Ok(true), "lm {memory} lb {bytecode} {mode:?}");
            }
        });
    }
}

/// Finding (shape validation), fixed in iteration 2: the quotients' degrees no longer wrap at small heights
/// (`verifier::degree`), so the shapes that made `reduce` panic (BLAKE2S at 2 rows, JUMP at 1) are recorded.
#[test]
fn small_heights_are_recorded() {
    for rows in [[3u64, 3, 3, 0, 3, 2], [3, 3, 3, 0, 1, 3]] {
        let outcome = std::panic::catch_unwind(|| {
            let shape = shape_of(rows);
            leanvm_univariate::contract::record_verifier(&shape, Blake2s::Omitted, Claims::Point).stream_len
        });
        println!("rows {rows:?}: {}", if outcome.is_err() { "reduce panics" } else { "recorded" });
        assert!(outcome.is_ok(), "rows {rows:?}");
    }
}

/// Negative control: the same execution, but the proof claims a public input the memory does not hold. The constraint
/// quotient does not divide, and the claim on `C1` is false.
#[test]
fn wrong_public_input_is_rejected() {
    deep(|| {
        let bases = Bases::new(7);
        let mut rng = Rng(0x5EED);
        let mut witness = execution(&mut rng);
        witness.public[2] ^= 1;
        for mode in [Claims::Weighted, Claims::Point] {
            let proof = prove(&witness, mode, Tamper::default(), &bases);
            assert!(!proof.exact, "Q_W does not divide");
            // Weighted: a false claim; point claims: the batching sumcheck's terminal fails first.
            let verdict = verify(&witness, &proof, mode);
            println!("  wrong public input, {mode:?}: {verdict:?}");
            assert!(verdict != Ok(true), "{mode:?}");
        }
    });
}

/// Negative control: one row reads a value the memory image does not hold (its instruction says so too, so only the
/// bus can catch it). Built honestly from that witness, the heap's root misses the boundary, and a claim is false.
#[test]
fn inconsistent_read_is_rejected() {
    deep(|| {
        let bases = Bases::new(7);
        let mut rng = Rng(0x5EED);
        let mut witness = execution(&mut rng);
        let set = &tables()[OP_SET];
        witness.rows[OP_SET][0][col(set, "k_0")] += ONE;
        witness.bytecode[0][5] += ONE; // SET's tuple: SEP, pc, count, tag, o, k_0, k_1, k_2
        for mode in [Claims::Weighted, Claims::Point] {
            let proof = prove(&witness, mode, Tamper::default(), &bases);
            let verdict = verify(&witness, &proof, mode);
            println!("  inconsistent read, {mode:?}: {verdict:?}");
            assert!(verdict != Ok(true), "{mode:?}");
        }
    });
}

/// Experiment (attack area 1, padding rows): rows past the fixed active count hold anything, here rows whose flushes
/// would write a fake public input (SET and XOR rows "storing" into cell 0) and a BLAKE2S row of another instance. The
/// proof is accepted, and nothing of those rows reaches the bus: their leaves are 1. The prover cannot move the
/// boundary between active and padding rows: `rows` is the contract's constant.
#[test]
fn padding_rows_are_inert() {
    deep(|| {
        let bases = Bases::new(7);
        let mut rng = Rng(0x5EED);
        let mut witness = execution(&mut rng);
        for t in [OP_SET, OP_XOR, OP_BLAKE2S] {
            let table = &tables()[t];
            let last = witness.rows[t].len() - 1;
            assert!(last as u64 >= witness.active[t], "a padding row");
            let row = &mut witness.rows[t][last];
            for v in row.iter_mut() {
                *v = rng.k();
            }
            // A "write" of cell 0 (fp · o = g^0) with fake values, from pc 1.
            for name in ["pc", "fp"] {
                row[col(table, name)] = ONE;
            }
            if t == OP_SET {
                row[col(table, "o")] = ONE;
            }
            if t == OP_XOR {
                row[col(table, "o_c")] = ONE;
            }
        }
        // q_flock follows the BLAKE2S row (the limb copies are constrained on every row).
        let blake = &tables()[OP_BLAKE2S];
        let last = witness.rows[OP_BLAKE2S].len() - 1;
        for (slot, name) in BLAKE2S_SLOTS.iter().enumerate() {
            if let Some(name) = name {
                witness.qflock[slot + 256 * last] = witness.rows[OP_BLAKE2S][last][col(blake, name)];
            }
        }
        for mode in [Claims::Weighted, Claims::Point] {
            let proof = prove(&witness, mode, Tamper::default(), &bases);
            assert!(proof.exact);
            assert_eq!(verify(&witness, &proof, mode), Ok(true), "{mode:?}");
        }
    });
}

/// Experiment (attack area 1, nodes 0 and 1): heap position 0 is outside the tree identity (`w_1` vanishes on
/// `V_1 = {ω_0, ω_1}`). Any value there is accepted; nothing reads it. Position 1 is the root: its value is the
/// product of its children (the identity at `ω_2`, `ω_3`).
#[test]
fn heap_node_zero_is_free_and_unused() {
    deep(|| {
        let bases = Bases::new(7);
        let mut rng = Rng(0x5EED);
        let witness = execution(&mut rng);
        let tamper = Tamper {
            node_zero: Some(E::new(0xDEAD, 0xBEEF, 7)),
        };
        let proof = prove(&witness, Claims::Point, tamper, &bases);
        assert!(proof.exact);
        assert_eq!(verify(&witness, &proof, Claims::Point), Ok(true));
    });
}

fn element_of(word: &[u8]) -> E {
    let limb = |i: usize| u64::from_be_bytes(word[24 - 8 * i..32 - 8 * i].try_into().unwrap());
    assert!(word[..8].iter().all(|&b| b == 0), "a field element is 192-bit");
    E::new(limb(0), limb(1), limb(2))
}

/// Attack area 6: the verifying contract (not the measuring build the parity tests use), on the honest proof. It
/// returns 1 with exactly its `PCS_OPEN` calls attested, and those calls are true claims of what was committed. It
/// reverts when any scalar of the stream is changed, when one claim is not attested, on a wrong selector and on a
/// stream one byte short or long. The measuring build agrees with the Rust verifier word for word on this proof.
#[test]
fn verifying_contract_accepts_the_honest_proof_and_rejects_mutations() {
    deep(|| {
        let bases = Bases::new(7);
        let mut rng = Rng(0x5EED);
        let witness = execution(&mut rng);
        let shape = shape_of(witness.active);
        let proof = prove(&witness, Claims::Point, Tamper::default(), &bases);
        assert_eq!(verify(&witness, &proof, Claims::Point), Ok(true));
        let recorded = record_verifier(&shape, Blake2s::Omitted, Claims::Point);
        assert_eq!(recorded.stream_len, proof.stream.len());
        leanvm_univariate::contract::parity(&shape, &IV, &proof.public, &proof.stream, Blake2s::Omitted, Claims::Point);
        let contract = compile_verifier(&recorded, &IV, false);
        let data = calldata(&proof.public, &proof.stream);
        let one = {
            let mut w = [0u8; 32];
            w[31] = 1;
            w
        };
        let accepted =
            |data: &[u8], block: &PcsOpen| call(&contract.code, &[], data, block).output.as_deref() == Some(&one[..]);
        let outcome = call(&contract.code, &[], &data, &PcsOpen::attesting_all(0));
        assert_eq!(outcome.output.as_deref(), Some(&one[..]), "the honest proof, every call attested");
        assert_eq!(outcome.pcs_calls.len(), 3);
        // The calls are true point claims on C1, C2 and the setup.
        for input in &outcome.pcs_calls {
            let words: Vec<&[u8]> = input.chunks(32).collect();
            // The layout word: the shape's bytes, the opening's code (bytes 22..24), its variables and placed words.
            let layout_id = u16::from_be_bytes(words[1][22..24].try_into().unwrap());
            let (commitment, committed) = match layout_id {
                0x5501 => (Commitment::C1, &proof.c1),
                0x5502 => (Commitment::C2, &proof.c2),
                0x5503 => (Commitment::Setup, &proof.setup),
                other => panic!("layout {other:#x}"),
            };
            let layout = &proof.layouts.iter().find(|(c, _)| *c == commitment).unwrap().1;
            assert_eq!(words.len(), 3 + layout.vars + 1, "{commitment:?}");
            assert_eq!(element_of(words[2]), ONE, "one claim");
            let point: Vec<E> = words[3..3 + layout.vars].iter().map(|w| element_of(w)).collect();
            let value = element_of(words[3 + layout.vars]);
            assert_eq!(multilinear_eval(&stack(layout, committed), &point).unwrap(), value, "{commitment:?}");
        }
        assert_eq!(&outcome.pcs_calls[0][..32], &proof.stream[24..56], "C1's root word is the stream's");
        let mut block = PcsOpen::default();
        for input in &outcome.pcs_calls {
            block.register(input.clone());
        }
        assert!(accepted(&data, &block), "exactly its calls attested");
        for skip in 0..3 {
            let mut partial = PcsOpen::default();
            for (k, input) in outcome.pcs_calls.iter().enumerate() {
                if k != skip {
                    partial.register(input.clone());
                }
            }
            assert!(!accepted(&data, &partial), "call {skip} not attested");
        }
        // Each scalar (and each root half) of the stream changed in turn: rejected, even with every call attested.
        let header = 4 + 32;
        // The six row counts (4 bytes each), C1's root halves, then the scalars.
        let mut offsets: Vec<usize> = (0..6).map(|k| 4 * k + 3).collect();
        offsets.extend([24 + 15, 24 + 31, 24 + 32 + 15, 24 + 32 + 31]);
        offsets.extend((24 + 64..proof.stream.len()).step_by(24).map(|at| at + 23));
        let mut rejected = 0;
        for &at in &offsets {
            let mut mutated = data.clone();
            mutated[header + at] ^= 1;
            assert!(!accepted(&mutated, &PcsOpen::attesting_all(0)), "byte {at} of the stream changed");
            assert!(!accepted(&mutated, &block), "byte {at}, the honest calls attested");
            rejected += 1;
        }
        println!("{rejected} mutations of {} stream bytes rejected", proof.stream.len());
        let mut selector = data.clone();
        selector[0] ^= 1;
        assert!(!accepted(&selector, &PcsOpen::attesting_all(0)), "wrong selector");
        assert!(!accepted(&data[..data.len() - 1], &PcsOpen::attesting_all(0)), "one byte short");
        let mut long = data.clone();
        long.push(0);
        assert!(!accepted(&long, &PcsOpen::attesting_all(0)), "one byte long");

        // The deployable verifying build (crates/evm_link), cut into contracts of at most 4 KB, likewise.
        use leanvm_flock_gas::evm::codegen::{Ending, Entry, compile_deployable};
        let call_words = leanvm_univariate::contract::calls(&recorded);
        let ending = Ending::PcsOpen(call_words.iter().map(Vec::len).collect());
        let entry = Entry {
            name: NAME,
            iv: contract_iv(&shape, &IV, &recorded.roots),
            stream_len: recorded.stream_len,
            measure: false,
        };
        let real = compile_deployable(&recorded.graph, &call_words.concat(), &ending, &entry, 4096);
        let deployed = leanvm_flock_gas::evm::contract::deploy(&real, &[]);
        println!("deployable verifying build: {} contracts", deployed.contracts.len());
        assert!(deployed.contracts.len() > 1, "cut into parts");
        let linked_accepts =
            |data: &[u8], block: &PcsOpen| deployed.chain.call(deployed.address, data, block).output.as_deref() == Some(&one[..]);
        assert!(linked_accepts(&data, &block), "the linked build accepts the honest proof");
        for &at in offsets.iter().step_by(7) {
            let mut mutated = data.clone();
            mutated[header + at] ^= 1;
            assert!(!linked_accepts(&mutated, &PcsOpen::attesting_all(0)), "linked, byte {at} changed");
        }
        for skip in 0..3 {
            let mut partial = PcsOpen::default();
            for (k, input) in outcome.pcs_calls.iter().enumerate() {
                if k != skip {
                    partial.register(input.clone());
                }
            }
            assert!(!linked_accepts(&data, &partial), "linked, call {skip} not attested");
        }
    });
}
