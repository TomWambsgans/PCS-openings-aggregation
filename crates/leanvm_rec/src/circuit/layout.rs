// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The layout framework (SPEC-REC.md §2.3, §7 R2 step 2): rows of a region type, values placed in their cells, the
//! wiring `σ` derived from where each value is placed, the region blocks, `κ`, and the witness.
//!
//! **Values.** A value is one `K` word of the computation. It is produced by an **expression slot** (a role whose
//! formula is `Expr`: its push), or it is **free** (no producer: it lives on a cycle of forwards, any word). The
//! compiler **places** a value at the cells that read it ([`Builder::place`]).
//!
//! **Chains.** A value produced at slot `p` and placed at forwards `f_1..f_k` and at most one slot `e` travels
//! `p → f_1 → … → f_k → e`: `e` is its **end**. A value with no slot placement ends at a **free end**: a slot whose
//! pull nothing places (so no formula of its row may read it). A free value's forwards form a cycle.
//!
//! **The balancing rule is automatic.** Every non-port slot produces exactly one value (a slot whose push the
//! compiler does not ask for, but whose pull it placed, produces **junk**), and every placed slot ends exactly one
//! value. So the values without a slot placement are exactly as many as the slots without a placed pull, and any
//! matching of the two closes every chain. A slot with neither is **dead**: a self-loop of the word 0, and its formula
//! must vanish there.
//!
//! **The invariant** ([`Builder::finish`] checks it):
//! - a value is placed at one slot at most, and a free value at none;
//! - every cell a live formula reads (a slot that is not dead, a port) is placed: an end is read by its row, nothing
//!   live reads a free end or an unplaced forward;
//! - every placed cell is read by some formula of its row (nothing is placed in vain).
//!
//! **Placement.** Rows of one region go to aligned blocks of `2^s` rows, the binary digits of their count, the largest
//! first (so each is aligned). Unused rows are in no block (forwards, self-loops of 0).

use std::collections::BTreeMap;

use leanvm_flock_gas::field::K;

use super::spec::{Block, CallWord, Circuit, Formula, Poly, Port, Region, Source, Witness};

pub type Value = u32;

const NONE: u32 = u32::MAX;
/// A value's producer when it is free.
const FREE: u32 = u32::MAX;

/// `Σ coefficient · cell` and `Σ coefficient · cell_a · cell_b`, built term by term; equal terms cancel (char 2).
#[derive(Clone, Debug, Default)]
pub struct PolyBuilder {
    terms: BTreeMap<(u8, u8), u64>,
}

/// The marker of a linear term in [`PolyBuilder`]'s keys.
const LINEAR: u8 = u8::MAX;

impl PolyBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn linear(mut self, cell: usize, k: u64) -> Self {
        self.add_linear(cell, k);
        self
    }

    pub fn add_linear(&mut self, cell: usize, k: u64) {
        let e = self.terms.entry((cell as u8, LINEAR)).or_insert(0);
        *e ^= k;
    }

    pub fn add_quadratic(&mut self, a: usize, b: usize, k: u64) {
        let (a, b) = (a.min(b) as u8, a.max(b) as u8);
        // Over GF(2)-coefficients a square of a bit is the bit, but cells are K words: keep the square.
        let e = self.terms.entry((a, b)).or_insert(0);
        *e ^= k;
    }

    pub fn quadratic(mut self, a: usize, b: usize, k: u64) -> Self {
        self.add_quadratic(a, b, k);
        self
    }

    /// Add another polynomial times the constant `k ∈ {0, 1}` (sums of polynomials with coefficient 1).
    pub fn add(&mut self, other: &PolyBuilder) {
        for (&key, &v) in &other.terms {
            let e = self.terms.entry(key).or_insert(0);
            *e ^= v;
        }
    }

    pub fn build(self) -> Poly {
        let mut p = Poly::default();
        for ((a, b), k) in self.terms {
            if k == 0 {
                continue;
            }
            if b == LINEAR {
                p.linear.push((a, K(k)));
            } else {
                p.quadratic.push((a, b, K(k)));
            }
        }
        p
    }
}

/// Counts of the finished layout.
#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub log_n: u8,
    pub log_width: u8,
    /// Rows used, by region name.
    pub rows: BTreeMap<String, usize>,
    pub rows_used: usize,
    pub positions_used: usize,
    pub blocks: usize,
    /// (block, role) selector pairs.
    pub pairs: usize,
    pub values: usize,
    pub free_values: usize,
    pub junk: usize,
    pub free_ends: usize,
    pub dead_slots: usize,
    pub kappa: usize,
    pub ports: usize,
    /// Positions by kind: forwards placed, slots (ends), free-end slots, dead or unplaced, ports.
    pub forwards_placed: usize,
    pub forwards_unplaced: usize,
}

impl Stats {
    pub fn fill(&self) -> f64 {
        self.positions_used as f64 / (1u64 << self.log_n) as f64
    }
}

/// The layout under construction.
pub struct Builder {
    pub log_width: u8,
    regions: Vec<Region>,
    region_index: BTreeMap<String, u16>,
    /// Per region: for each role, the cells some role of the region reads (a row's read set), and per role whether
    /// it is a slot (`Expr`).
    read_by_row: Vec<Vec<bool>>,
    /// Each row's region, in creation order.
    row_region: Vec<u16>,
    /// Per position (creation row · W + role): the value placed there.
    cell: Vec<Value>,
    /// Per position: the value its slot produces.
    produced: Vec<Value>,
    /// Per position: κ.
    kappa: BTreeMap<u32, K>,
    /// Per position: a port's source.
    ports: BTreeMap<u32, Source>,
    /// Per value: its producing position, or `FREE`.
    producer: Vec<u32>,
    /// Words given for free values and self-referential slots.
    given: BTreeMap<Value, K>,
    pub calls: Vec<Vec<CallWord>>,
}

/// The finished layout: the circuit, its honest witness, and its counts.
pub struct Finished {
    pub circuit: Circuit,
    pub witness: Witness,
    pub stats: Stats,
    /// Each value's word.
    pub words: Vec<K>,
    /// Each creation row's final row.
    pub row_map: Vec<u32>,
}

impl Builder {
    pub fn new(log_width: u8) -> Self {
        Self {
            log_width,
            regions: Vec::new(),
            region_index: BTreeMap::new(),
            read_by_row: Vec::new(),
            row_region: Vec::new(),
            cell: Vec::new(),
            produced: Vec::new(),
            kappa: BTreeMap::new(),
            ports: BTreeMap::new(),
            producer: Vec::new(),
            given: BTreeMap::new(),
            calls: Vec::new(),
        }
    }

    pub fn width(&self) -> usize {
        1 << self.log_width
    }

    /// Register a region type (once per name; later calls return the first's index, and must agree).
    pub fn region(&mut self, name: &str, roles: Vec<Formula>) -> u16 {
        assert_eq!(roles.len(), self.width(), "region {name}: one formula a role");
        if let Some(&r) = self.region_index.get(name) {
            debug_assert_eq!(self.regions[r as usize].roles, roles, "region {name} redefined");
            return r;
        }
        let mut read = vec![false; self.width()];
        for f in &roles {
            for c in f.reads() {
                read[c as usize] = true;
            }
        }
        let r = self.regions.len() as u16;
        self.regions.push(Region {
            name: name.to_string(),
            roles,
        });
        self.read_by_row.push(read);
        self.region_index.insert(name.to_string(), r);
        r
    }

    pub fn region_roles(&self, region: u16) -> &[Formula] {
        &self.regions[region as usize].roles
    }

    pub fn rows(&self) -> usize {
        self.row_region.len()
    }

    /// A new row of `region`.
    pub fn row(&mut self, region: u16) -> u32 {
        let r = self.row_region.len() as u32;
        self.row_region.push(region);
        self.cell.extend(std::iter::repeat_n(NONE, self.width()));
        self.produced.extend(std::iter::repeat_n(NONE, self.width()));
        r
    }

    fn pos(&self, row: u32, role: usize) -> usize {
        assert!(role < self.width());
        row as usize * self.width() + role
    }

    fn formula(&self, row: u32, role: usize) -> &Formula {
        &self.regions[self.row_region[row as usize] as usize].roles[role]
    }

    /// Place `value` at `(row, role)`: that cell reads it.
    pub fn place(&mut self, row: u32, role: usize, value: Value) {
        let p = self.pos(row, role);
        assert_eq!(self.cell[p], NONE, "cell ({row}, {role}) placed twice");
        assert!((value as usize) < self.producer.len(), "an unknown value");
        self.cell[p] = value;
    }

    fn new_value(&mut self, producer: u32) -> Value {
        let v = self.producer.len() as Value;
        self.producer.push(producer);
        v
    }

    /// The value the slot at `(row, role)` pushes.
    pub fn produce(&mut self, row: u32, role: usize) -> Value {
        let p = self.pos(row, role);
        assert!(
            matches!(self.formula(row, role), Formula::Expr(_)),
            "({row}, {role}) is not an expression slot"
        );
        assert_eq!(self.produced[p], NONE, "slot ({row}, {role}) produced twice");
        let v = self.new_value(p as u32);
        self.produced[p] = v;
        v
    }

    /// The value of a self-referential slot (one whose formula reads its own value, placed at itself, such as a
    /// bit's `b = b²`): its word is given.
    pub fn produce_given(&mut self, row: u32, role: usize, word: K) -> Value {
        let v = self.produce(row, role);
        self.given.insert(v, word);
        v
    }

    /// A free value: any word, on a cycle of the forwards it is placed at.
    pub fn free(&mut self, word: K) -> Value {
        let v = self.new_value(FREE);
        self.given.insert(v, word);
        v
    }

    pub fn set_kappa(&mut self, row: u32, role: usize, k: K) {
        let p = self.pos(row, role);
        assert!(
            matches!(self.formula(row, role), Formula::Expr(_)),
            "κ off an expression slot"
        );
        if k != K(0) {
            self.kappa.insert(p as u32, k);
        }
    }

    /// The port at `(row, role)` binds the public `source`.
    pub fn port(&mut self, row: u32, role: usize, source: Source) {
        let p = self.pos(row, role);
        assert!(matches!(self.formula(row, role), Formula::Port(_)), "not a port role");
        assert!(self.ports.insert(p as u32, source).is_none(), "port set twice");
    }

    /// The value placed at a cell, if any.
    pub fn placed(&self, row: u32, role: usize) -> Option<Value> {
        let v = self.cell[self.pos(row, role)];
        (v != NONE).then_some(v)
    }

    pub fn values(&self) -> usize {
        self.producer.len()
    }

    /// Lay the rows out, derive `σ`, check the invariant and compute the witness.
    pub fn finish(mut self) -> Finished {
        let w = self.width();
        let rows = self.row_region.len();

        // Every port row's port must be set: a port role with no source is an error.
        for row in 0..rows as u32 {
            for role in 0..w {
                if matches!(self.formula(row, role), Formula::Port(_)) {
                    assert!(
                        self.ports.contains_key(&(self.pos(row, role) as u32)),
                        "port ({row}, {role}) has no source"
                    );
                }
            }
        }

        // Junk: a placed slot whose push nobody asked for still pushes.
        let mut junk = 0usize;
        for row in 0..rows as u32 {
            for role in 0..w {
                let p = self.pos(row, role);
                if matches!(self.formula(row, role), Formula::Expr(_))
                    && self.produced[p] == NONE
                    && self.cell[p] != NONE
                {
                    let v = self.new_value(p as u32);
                    self.produced[p] = v;
                    junk += 1;
                }
            }
        }
        let values = self.producer.len();

        // The invariant: slot placements, live reads, placed cells read.
        let mut slot_end: Vec<u32> = vec![NONE; values];
        let mut forwards: Vec<Vec<u32>> = vec![Vec::new(); values];
        for p in 0..rows * w {
            let v = self.cell[p];
            if v == NONE {
                continue;
            }
            let (row, role) = ((p / w) as u32, p % w);
            match self.formula(row, role) {
                Formula::Forward => forwards[v as usize].push(p as u32),
                Formula::Expr(_) => {
                    assert_ne!(self.producer[v as usize], FREE, "free value {v} placed at slot ({row}, {role})");
                    assert_eq!(
                        slot_end[v as usize], NONE,
                        "value {v} placed at two slots (the second at ({row}, {role}))"
                    );
                    slot_end[v as usize] = p as u32;
                }
                Formula::Port(_) => panic!("a value placed at port ({row}, {role})"),
            }
            assert!(
                self.read_by_row[self.row_region[row as usize] as usize][role],
                "value {v} placed at ({row}, {role}) of {}, which no formula of the row reads",
                self.regions[self.row_region[row as usize] as usize].name
            );
        }
        let mut dead = 0usize;
        for row in 0..rows as u32 {
            for role in 0..w {
                let p = self.pos(row, role);
                let live = match self.formula(row, role) {
                    Formula::Forward => false,
                    Formula::Expr(_) => self.produced[p] != NONE,
                    Formula::Port(_) => true,
                };
                if !live {
                    if matches!(self.formula(row, role), Formula::Expr(_)) {
                        dead += 1;
                    }
                    continue;
                }
                for c in self.formula(row, role).reads() {
                    assert_ne!(
                        self.cell[self.pos(row, c as usize)],
                        NONE,
                        "({row}, {role}) of {} reads cell {c}, which holds nothing",
                        self.regions[self.row_region[row as usize] as usize].name
                    );
                }
            }
        }

        // The words, in value order.
        let mut words: Vec<K> = vec![K(0); values];
        let mut known = vec![false; values];
        let mut cells = vec![K(0); w];
        for v in 0..values {
            if let Some(&g) = self.given.get(&(v as Value)) {
                words[v] = g;
                known[v] = true;
                continue;
            }
            let p = self.producer[v] as usize;
            let (row, role) = ((p / w) as u32, p % w);
            let f = self.formula(row, role).clone();
            for c in f.reads() {
                let u = self.cell[self.pos(row, c as usize)];
                assert!(
                    known[u as usize],
                    "value {v} at ({row}, {role}) reads value {u}, not computed before it"
                );
                cells[c as usize] = words[u as usize];
            }
            let k = self.kappa.get(&(p as u32)).copied().unwrap_or(K(0));
            words[v] = f.eval(&cells, K(0), K(0)) + k;
            known[v] = true;
        }

        // Dead slots: self-loops of 0, so their formula must vanish on their row.
        for row in 0..rows as u32 {
            for role in 0..w {
                let p = self.pos(row, role);
                if let Formula::Expr(poly) = self.formula(row, role)
                    && self.produced[p] == NONE
                {
                    let cells: Vec<K> = (0..w)
                        .map(|c| match self.cell[self.pos(row, c)] {
                            NONE => K(0),
                            u => words[u as usize],
                        })
                        .collect();
                    let k = self.kappa.get(&(p as u32)).copied().unwrap_or(K(0));
                    assert_eq!(
                        poly.eval(&cells) + k,
                        K(0),
                        "dead slot ({row}, {role}) of {} does not push 0",
                        self.regions[self.row_region[row as usize] as usize].name
                    );
                }
            }
        }

        // Placement: blocks by region, largest first.
        let mut count: Vec<usize> = vec![0; self.regions.len()];
        for &r in &self.row_region {
            count[r as usize] += 1;
        }
        let mut wanted: Vec<(u8, u16)> = Vec::new();
        for (r, &c) in count.iter().enumerate() {
            for bit in 0..usize::BITS as u8 {
                if c >> bit & 1 == 1 {
                    wanted.push((bit, r as u16));
                }
            }
        }
        wanted.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
        let mut blocks = Vec::new();
        let mut next_row = 0u32;
        // Rows of each region, handed out in creation order across its blocks.
        let mut region_starts: Vec<Vec<(u32, u32)>> = vec![Vec::new(); self.regions.len()];
        for &(bit, r) in &wanted {
            blocks.push(Block {
                row: next_row,
                log_rows: bit,
                region: r,
            });
            region_starts[r as usize].push((next_row, 1 << bit));
            next_row += 1 << bit;
        }
        let total_rows = next_row as usize;
        let log_rows = (total_rows.max(1)).next_power_of_two().trailing_zeros() as u8;
        let log_n = log_rows + self.log_width;
        let n = 1usize << log_n;
        let mut row_map = vec![0u32; rows];
        {
            let mut cursor: Vec<(usize, u32)> = vec![(0, 0); self.regions.len()];
            for (row, &r) in self.row_region.iter().enumerate() {
                let (b, off) = &mut cursor[r as usize];
                let (start, len) = region_starts[r as usize][*b];
                row_map[row] = start + *off;
                *off += 1;
                if *off == len {
                    *b += 1;
                    *off = 0;
                }
            }
        }
        let fpos = |p: usize| -> u32 { row_map[p / w] * w as u32 + (p % w) as u32 };

        // Ports, in final position order.
        let mut ports: Vec<Port> = self
            .ports
            .iter()
            .map(|(&p, &source)| Port {
                position: fpos(p as usize),
                source,
            })
            .collect();
        ports.sort_by_key(|p| p.position);

        // σ: self-loops by default, then the chains.
        let mut sigma: Vec<u32> = (0..n as u32).collect();
        for (j, port) in ports.iter().enumerate() {
            sigma[port.position as usize] = (n + j) as u32;
        }
        let mut free_ends: Vec<u32> = Vec::new();
        for p in 0..rows * w {
            let (row, role) = ((p / w) as u32, p % w);
            if matches!(self.formula(row, role), Formula::Expr(_)) && self.cell[p] == NONE && self.produced[p] != NONE
            {
                free_ends.push(p as u32);
            }
        }
        let mut end_of = slot_end.clone();
        let mut pool = free_ends.iter().copied();
        for v in 0..values {
            if self.producer[v] != FREE && end_of[v] == NONE {
                end_of[v] = pool.next().expect("as many free ends as values without an end");
            }
        }
        assert!(pool.next().is_none(), "as many free ends as values without an end");
        // A free end's pull is the value that ends there.
        let mut pulled_at_free_end: BTreeMap<u32, Value> = BTreeMap::new();
        for v in 0..values {
            let e = end_of[v];
            if e != NONE && slot_end[v] == NONE {
                pulled_at_free_end.insert(e, v as Value);
            }
        }
        for v in 0..values {
            let chain = &forwards[v];
            if self.producer[v] == FREE {
                for (k, &f) in chain.iter().enumerate() {
                    sigma[fpos(f as usize) as usize] = fpos(chain[(k + 1) % chain.len()] as usize);
                }
                continue;
            }
            let mut at = self.producer[v] as usize;
            for &f in chain {
                sigma[fpos(at) as usize] = fpos(f as usize);
                at = f as usize;
            }
            sigma[fpos(at) as usize] = fpos(end_of[v] as usize);
        }

        // The witness.
        let mut witness = vec![K(0); n];
        for p in 0..rows * w {
            let v = match self.cell[p] {
                NONE => pulled_at_free_end.get(&(p as u32)).copied(),
                v => Some(v),
            };
            if let Some(v) = v {
                witness[fpos(p) as usize] = words[v as usize];
            }
        }

        let kappa: Vec<(u32, K)> = {
            let mut k: Vec<(u32, K)> = self.kappa.iter().map(|(&p, &k)| (fpos(p as usize), k)).collect();
            k.sort_by_key(|x| x.0);
            k
        };

        let mut stats = Stats {
            log_n,
            log_width: self.log_width,
            rows_used: rows,
            positions_used: rows * w,
            blocks: blocks.len(),
            values,
            free_values: self.producer.iter().filter(|&&p| p == FREE).count(),
            junk,
            free_ends: free_ends.len(),
            dead_slots: dead,
            kappa: kappa.len(),
            ports: ports.len(),
            ..Stats::default()
        };
        for (r, &c) in count.iter().enumerate() {
            if c > 0 {
                stats.rows.insert(self.regions[r].name.clone(), c);
            }
        }
        for p in 0..rows * w {
            if matches!(self.formula((p / w) as u32, p % w), Formula::Forward) {
                if self.cell[p] == NONE {
                    stats.forwards_unplaced += 1;
                } else {
                    stats.forwards_placed += 1;
                }
            }
        }
        let circuit = Circuit {
            log_n,
            log_width: self.log_width,
            regions: self.regions,
            blocks,
            sigma,
            kappa,
            ports,
            calls: std::mem::take(&mut self.calls),
        };
        stats.pairs = circuit.pairs().len();
        Finished {
            circuit,
            witness,
            stats,
            words,
            row_map,
        }
    }
}

/// Units of `size` consecutive roles, packed `per_row` to a row of one region: the next free unit.
pub struct Units {
    pub region: u16,
    pub size: usize,
    pub per_row: usize,
    row: u32,
    used: usize,
}

impl Units {
    pub fn new(region: u16, size: usize, per_row: usize) -> Self {
        Self {
            region,
            size,
            per_row,
            row: 0,
            used: per_row,
        }
    }

    /// The next unit: its row and its first role.
    pub fn next(&mut self, b: &mut Builder) -> (u32, usize) {
        if self.used == self.per_row {
            self.row = b.row(self.region);
            self.used = 0;
        }
        let base = self.used * self.size;
        self.used += 1;
        (self.row, base)
    }
}

/// `W` forwards.
pub fn forwards(w: usize) -> Vec<Formula> {
    (0..w).map(|_| Formula::Forward).collect()
}
