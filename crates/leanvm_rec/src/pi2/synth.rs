// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Synthetic circuits built with the interface ([`Circuit`]), and their witnesses: the PIOP's tests before the real
//! circuit exists, and the target shapes the verifier's gas is measured at (SPEC-REC.md §2.4.5–§2.4.6, §2.6).
//!
//! A [`Design`] lists row types (a role kind for each of a row's `2^r` positions) and regions (a row type on aligned
//! blocks of rows). [`build`] places the blocks (largest first, so each is aligned), makes the pairs, and wires the
//! rows in their regions' order: every pulling position takes the oldest pending push (a FIFO), and every push joins
//! the queue once its row is evaluated. Positions that find the queue empty (only spare slots, read by no formula)
//! are fed by the pushes left at the end. So every pull is the push sent to it, by construction.

use std::collections::{HashMap, VecDeque};

use primitives::field::{F64, F192};

use super::circuit::{Circuit, Coeff, Formula, Lin, Pair, PublicTerm, Read};
use super::prover::PublicValue;

/// What a role does.
#[derive(Clone, Debug)]
pub enum Role {
    /// Its push is this formula of its row (in `K`).
    Expr(Formula),
    /// Its push is its pull.
    Forward,
    /// Its push is this constant (`κ`), in a pair of the zero formula.
    Const(u64),
    /// A free bit: pushes `v_k^2` to itself.
    SelfBit,
    /// A spare slot: pushes its own value to itself (no pair).
    SelfFree(Free),
    /// Pull-less: pushes this public element's fingerprint, read from these cells, outside.
    Sink(Sink, Vec<usize>),
}

/// A spare slot's value.
#[derive(Clone, Copy, Debug)]
pub enum Free {
    Zero,
    Word,
    U32,
}

/// The public elements a sink binds (SPEC-REC.md §2.4.6), each one public term.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sink {
    /// An element of `E` from three `K` limbs (a claim's coordinate or value): `v_a + Y v_b + Y² v_c`.
    Element,
    /// A root's two halves: `(v_a + Y v_b) + γ (v_c + Y v_d)`.
    Root,
    /// Three 4-byte row counts: `v_a + Y v_b + Y² v_c`.
    Counts,
    /// The public input's four words: `v_a + Y v_b + Y² v_c + γ v_d`.
    Statement,
    /// A zero check: `v_a + Y v_b + Y² v_c = 0`.
    Zero,
}

#[derive(Clone, Debug)]
pub struct RowType {
    pub name: String,
    pub roles: Vec<Role>,
}

/// A row type on aligned blocks of `2^s` rows.
#[derive(Clone, Debug)]
pub struct Region {
    pub row_type: usize,
    pub blocks: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct Design {
    pub log_n: usize,
    pub log_row: usize,
    pub types: Vec<RowType>,
    /// In the order the rows are wired.
    pub regions: Vec<Region>,
}

/// A circuit, a witness satisfying it, and the public data.
pub struct Built {
    pub circuit: Circuit,
    pub witness: Vec<F64>,
    pub public_input: [u8; 32],
    pub values: Vec<PublicValue>,
    /// Rows used.
    pub used_rows: usize,
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn y() -> F192 {
    F192::Y
}

fn y2() -> F192 {
    F192::Y * F192::Y
}

/// The fingerprint formula of a sink on its cells: the adapter's port fingerprint (`pi2::adapt`).
fn sink_formula(kind: Sink, cells: &[usize]) -> Formula {
    let limbs = match kind {
        Sink::Root | Sink::Statement => 4,
        _ => 3,
    };
    assert_eq!(cells.len(), limbs);
    super::adapt::port_formula(&cells.iter().map(|&c| c as u8).collect::<Vec<_>>())
}

/// Build the circuit of `design` and a witness of it.
pub fn build(design: &Design, seed: u64) -> Built {
    let (m, r) = (design.log_n, design.log_row);
    let (n, width) = (1usize << m, 1usize << r);
    let rows = n >> r;
    let mut rng = Rng(seed | 1);
    for t in &design.types {
        assert_eq!(t.roles.len(), width, "row type {}", t.name);
    }

    // Placement: every block, largest first.
    let mut blocks: Vec<(usize, usize, usize)> = vec![]; // (log size, region, index in region)
    for (g, region) in design.regions.iter().enumerate() {
        for (j, &s) in region.blocks.iter().enumerate() {
            blocks.push((s, g, j));
        }
    }
    blocks.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)).then(a.2.cmp(&b.2)));
    let mut start: HashMap<(usize, usize), usize> = HashMap::new();
    let mut next_row = 0;
    for &(s, g, j) in &blocks {
        assert!(next_row % (1 << s) == 0);
        start.insert((g, j), next_row);
        next_row += 1 << s;
    }
    assert!(next_row <= rows, "{next_row} rows of {rows}");
    let used_rows = next_row;

    // Pairs and formulas.
    let mut formulas: Vec<Formula> = vec![];
    let mut formula_ids: HashMap<Formula, usize> = HashMap::new();
    let mut formula_id = |f: Formula, formulas: &mut Vec<Formula>| {
        *formula_ids.entry(f.clone()).or_insert_with(|| {
            formulas.push(f);
            formulas.len() - 1
        })
    };
    let mut pairs = vec![];
    for (g, region) in design.regions.iter().enumerate() {
        let t = &design.types[region.row_type];
        for (j, &s) in region.blocks.iter().enumerate() {
            let first_row = start[&(g, j)];
            for (role, kind) in t.roles.iter().enumerate() {
                let (formula, pulls) = match kind {
                    Role::Expr(f) => (f.clone(), true),
                    Role::Const(_) => (Formula::zero(), true),
                    Role::SelfBit => (
                        Formula::zero().plus_product(Coeff::ONE, Lin::cell(role), Lin::cell(role)),
                        true,
                    ),
                    Role::Sink(kind, cells) => (sink_formula(*kind, cells), false),
                    Role::Forward | Role::SelfFree(_) => continue,
                };
                pairs.push(Pair {
                    first_row,
                    log_rows: s,
                    role,
                    formula: formula_id(formula, &mut formulas),
                    pulls,
                });
            }
        }
    }

    // Wiring and the witness, rows in their regions' order.
    let mut w = vec![F64::ZERO; n];
    let mut sigma: Vec<u32> = (0..n as u32).collect();
    let mut kappa = vec![F64::ZERO; n];
    let mut queue: VecDeque<(usize, F64)> = VecDeque::new();
    let mut deferred: Vec<usize> = vec![];
    let mut reads = vec![];
    let mut values = vec![];
    let mut public = vec![];
    let mut public_input = [0u8; 32];
    let mut scalars = 4usize;
    let mut next_tag = n as u32;
    for (g, region) in design.regions.iter().enumerate() {
        let t = &design.types[region.row_type];
        // Which cells the row's formulas read.
        let mut read = vec![false; width];
        for kind in &t.roles {
            match kind {
                Role::Expr(f) => f.cells().into_iter().for_each(|c| read[c] = true),
                Role::Sink(_, cells) => cells.iter().for_each(|&c| read[c] = true),
                _ => {}
            }
        }
        for (k, kind) in t.roles.iter().enumerate() {
            if matches!(kind, Role::SelfBit) {
                read[k] = true;
            }
            if matches!(kind, Role::Sink(..)) {
                assert!(!read[k], "{}: a sink's cell is read", t.name);
            }
        }
        for (j, &s) in region.blocks.iter().enumerate() {
            for row_index in start[&(g, j)]..start[&(g, j)] + (1 << s) {
                let row = row_index << r;
                for (k, kind) in t.roles.iter().enumerate() {
                    let x = row + k;
                    match kind {
                        Role::SelfBit => w[x] = F64(rng.next() & 1),
                        Role::SelfFree(free) => {
                            w[x] = match free {
                                Free::Zero => F64::ZERO,
                                Free::Word => F64(rng.next()),
                                Free::U32 => F64(rng.next() & 0xffff_ffff),
                            }
                        }
                        Role::Sink(..) => {}
                        // A spare slot (an expression or constant slot no formula reads) takes a push left at the
                        // end: the queue grows by one.
                        _ if !read[k] && !matches!(kind, Role::Forward) => deferred.push(x),
                        _ => match queue.pop_front() {
                            Some((src, value)) => {
                                sigma[src] = x as u32;
                                w[x] = value;
                            }
                            None => panic!("{}: role {k} finds no push to pull", t.name),
                        },
                    }
                }
                let cell = |c: usize| w[row + c];
                for (k, kind) in t.roles.iter().enumerate() {
                    let x = row + k;
                    match kind {
                        Role::Expr(f) => queue.push_back((x, f.eval_k(&cell))),
                        Role::Forward => queue.push_back((x, w[x])),
                        Role::Const(c) => {
                            kappa[x] = F64(*c);
                            queue.push_back((x, F64(*c)));
                        }
                        Role::SelfBit | Role::SelfFree(_) => {}
                        Role::Sink(sink, cells) => {
                            let v: Vec<u64> = cells.iter().map(|&c| cell(c).0).collect();
                            sigma[x] = next_tag;
                            let mut lin = Lin::default();
                            match sink {
                                Sink::Element => {
                                    reads.push(Read::Scalar);
                                    values.push(PublicValue::Scalar(F192::new(v[0], v[1], v[2])));
                                    lin.terms.push((Coeff::ONE, scalars as u16));
                                    scalars += 1;
                                }
                                Sink::Root => {
                                    // Limb `l` is bytes `24 - 8l .. 32 - 8l`, big-endian; the halves are bytes 0..16
                                    // and 16..32, and the fingerprint half 1 + γ half 0.
                                    reads.push(Read::Root);
                                    let mut root = [0u8; 32];
                                    for (l, &limb) in v.iter().enumerate() {
                                        root[24 - 8 * l..32 - 8 * l].copy_from_slice(&limb.to_be_bytes());
                                    }
                                    values.push(PublicValue::Root(root));
                                    lin.terms.push((Coeff::ONE, scalars as u16 + 1));
                                    lin.terms.push((Coeff::gamma(1), scalars as u16));
                                    scalars += 2;
                                }
                                Sink::Counts => {
                                    for (q, coeff) in [Coeff::ONE, Coeff::e(y()), Coeff::e(y2())].into_iter().enumerate() {
                                        assert!(v[q] >> 32 == 0, "a count is 4 bytes");
                                        reads.push(Read::Integer(4));
                                        values.push(PublicValue::Integer(v[q]));
                                        lin.terms.push((coeff, scalars as u16));
                                        scalars += 1;
                                    }
                                }
                                Sink::Statement => {
                                    for (q, &limb) in v.iter().enumerate() {
                                        public_input[8 * q..8 * q + 8].copy_from_slice(&limb.to_be_bytes());
                                    }
                                    let coeffs = [Coeff::ONE, Coeff::e(y()), Coeff::gamma(1), Coeff { gamma: 1, ..Coeff::e(y()) }];
                                    lin.terms = coeffs.into_iter().zip(0..4u16).collect();
                                }
                                Sink::Zero => {
                                    assert!(v.iter().all(|&x| x == 0), "a zero check of zeros");
                                }
                            }
                            public.push(PublicTerm {
                                tag: next_tag,
                                value: lin,
                            });
                            next_tag += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(queue.len(), deferred.len(), "pushes left and spare slots");
    for ((src, value), x) in queue.into_iter().zip(deferred) {
        sigma[src] = x as u32;
        w[x] = value;
    }
    let circuit = Circuit {
        log_n: m,
        log_row: r,
        formulas,
        pairs,
        sigma,
        kappa,
        reads,
        public,
    };
    Built {
        circuit,
        witness: w,
        public_input,
        values,
        used_rows,
    }
}

fn lin_sum(cells: &[usize]) -> Lin {
    Lin::sum(cells.iter().copied())
}

/// Keccak's χ on the row's `b_i = v_{a_i} + v_{d_i}` (`a`, `d` the `A_{j-1}` and `D_j` cells of the five lanes):
/// lane `x`: `b_x + b_{x+2} + b_{x+1} b_{x+2}`, plus `rc`.
fn chi(a: [usize; 5], d: [usize; 5], x: usize, rc: bool) -> Formula {
    let b = |i: usize| lin_sum(&[a[i % 5], d[i % 5]]);
    let lin = b(x).plus(&b(x + 2));
    let lin = if rc { lin.with_constant(Coeff::ONE) } else { lin };
    Formula::linear(lin).plus_product(Coeff::ONE, b(x + 1), b(x + 2))
}

/// The row types of D16v (SPEC-REC.md §2.4.1, §2.4.3, §2.4.4) and the sinks of §2.4.6, 16 cells a row.
pub fn d16v_types() -> Vec<RowType> {
    let a = [0, 1, 2, 3, 4];
    let d = [5, 6, 7, 8, 9];
    let mut types = vec![];
    // K1: A_j[x', y'] (0–4), D's forwards (5–9), P_{y'} = P_{y'-1} + A_j (10–14), a free bit (15).
    let mut k1: Vec<Role> = (0..5).map(|x| Role::Expr(chi(a, d, x, false))).collect();
    k1.extend((5..10).map(|_| Role::Forward));
    k1.extend((0..5).map(|x| {
        let mut f = chi(a, d, x, false);
        f.lin = f.lin.plus(&Lin::cell(10 + x));
        Role::Expr(f)
    }));
    k1.push(Role::SelfBit);
    types.push(RowType { name: "K1".into(), roles: k1 });
    // K0a, K0b: A_j[x', 0] (0–4) and P_0 (5–9), the round constant on lane 0 for K0b; three D units (10–15).
    for rc in [false, true] {
        let mut roles: Vec<Role> = (0..5).map(|x| Role::Expr(chi(a, d, x, rc && x == 0))).collect();
        roles.extend((0..5).map(|x| Role::Expr(chi(a, d, x, rc && x == 0))));
        for u in 0..3 {
            roles.push(Role::Expr(Formula::linear(lin_sum(&[10 + 2 * u, 11 + 2 * u]))));
            roles.push(Role::Forward);
        }
        types.push(RowType {
            name: if rc { "K0b" } else { "K0a" }.into(),
            roles,
        });
    }
    // KD and the later blocks' XORs: eight units, an end and a forward.
    for name in ["KD", "XOR"] {
        let mut roles = vec![];
        for u in 0..8 {
            roles.push(Role::Expr(Formula::linear(lin_sum(&[2 * u, 2 * u + 1]))));
            roles.push(Role::Forward);
        }
        types.push(RowType { name: name.into(), roles });
    }
    // Kprep: three units of five bits, their sum; a free bit.
    let mut prep = vec![];
    for u in 0..3 {
        prep.extend((0..4).map(|_| Role::Forward));
        prep.push(Role::Expr(Formula::linear(lin_sum(&(5 * u..5 * u + 5).collect::<Vec<_>>()))));
    }
    prep.push(Role::SelfBit);
    types.push(RowType { name: "Kprep".into(), roles: prep });
    // Packing: fifteen bits and an accumulator, five offsets of the exponents.
    for offset in [0usize, 15, 30, 45, 60] {
        let mut roles: Vec<Role> = (0..15).map(|_| Role::Forward).collect();
        let mut lin = Lin::cell(15);
        lin.terms
            .extend((0..15).map(|e| (Coeff::k(1u64 << ((offset + e) % 64)), e as u16)));
        roles.push(Role::Expr(Formula::linear(lin)));
        types.push(RowType {
            name: format!("Pack{offset}"),
            roles,
        });
    }
    // Free bits: eight self-loops and the slots producing them.
    let mut free: Vec<Role> = (0..8).map(|_| Role::SelfBit).collect();
    free.extend((0..8).map(|k| Role::Expr(Formula::cell(k))));
    types.push(RowType { name: "Free".into(), roles: free });
    types.extend(e_units(16));
    // Constants.
    types.push(RowType {
        name: "Const".into(),
        roles: (0..16).map(|k| Role::Const(0x1000_0000_0000_0001 * (k as u64 + 1))).collect(),
    });
    types.extend(sinks(16));
    types
}

/// `E` products and sums on limbs: units of six pulls, three pushes and three forwards (SPEC-REC.md §2.4.4).
fn e_units(width: usize) -> Vec<RowType> {
    let units = width / 6;
    let mut mul = vec![];
    let mut add = vec![];
    let p = |i: usize, j: usize| (Coeff::ONE, Lin::cell(i), Lin::cell(j));
    for u in 0..units {
        let (a, b) = (6 * u, 6 * u + 3);
        let c0 = vec![p(a, b), p(a + 1, b + 2), p(a + 2, b + 1)];
        let c1 = vec![p(a, b + 1), p(a + 1, b), p(a + 1, b + 2), p(a + 2, b + 1), p(a + 2, b + 2)];
        let c2 = vec![p(a, b + 2), p(a + 1, b + 1), p(a + 2, b), p(a + 2, b + 2)];
        for products in [c0, c1, c2] {
            mul.push(Role::Expr(Formula {
                lin: Lin::default(),
                products,
            }));
        }
        mul.extend((0..3).map(|_| Role::Forward));
        add.extend((0..3).map(|i| Role::Expr(Formula::linear(lin_sum(&[a + i, b + i])))));
        add.extend((0..3).map(|_| Role::Forward));
    }
    for roles in [&mut mul, &mut add] {
        while roles.len() < width {
            roles.push(Role::SelfFree(Free::Word));
        }
    }
    vec![
        RowType { name: "Emul".into(), roles: mul },
        RowType { name: "Eadd".into(), roles: add },
    ]
}

/// The sinks' row types: role 0 pull-less, its cells after it, the rest spare.
fn sinks(width: usize) -> Vec<RowType> {
    [
        (Sink::Element, "SinkElement", 3, false),
        (Sink::Zero, "SinkZero", 3, true),
        (Sink::Root, "SinkRoot", 4, false),
        (Sink::Counts, "SinkCounts", 3, true),
        (Sink::Statement, "SinkStatement", 4, false),
    ]
    .into_iter()
    .map(|(kind, name, cells, spare)| {
        let mut roles = vec![Role::Sink(kind, (1..=cells).collect())];
        for _ in 0..cells {
            roles.push(if spare {
                Role::SelfFree(if kind == Sink::Zero { Free::Zero } else { Free::U32 })
            } else {
                Role::Forward
            });
        }
        while roles.len() < width {
            roles.push(Role::SelfFree(Free::Zero));
        }
        RowType { name: name.into(), roles }
    })
    .collect()
}

/// The row types of D32v (SPEC-REC.md §2.6): slice rows of 32 cells, the round constant split, θ's preparation, and
/// the other row types widened to 32 cells.
pub fn d32v_types() -> Vec<RowType> {
    let mut types = vec![];
    // A slice row: b (0–24, lane x + 5y), C_prev (25–29). A_j = χ(b) (+ RC on lane 0), C = Σ_y A_j,
    // a'_{j+1}[x, y] = A_j[x, y] + C[x - 1] + C_prev[x + 1]; pushes the 25 a' and the 5 C.
    for rc in [false, true] {
        let chi = |x: usize, yy: usize| -> Formula {
            let b = |i: usize| Lin::cell(i % 5 + 5 * yy);
            let lin = b(x).plus(&b(x + 2));
            let lin = if rc && x == 0 && yy == 0 {
                lin.with_constant(Coeff::ONE)
            } else {
                lin
            };
            Formula::linear(lin).plus_product(Coeff::ONE, b(x + 1), b(x + 2))
        };
        let column = |x: usize| -> Formula {
            let mut f = Formula::zero();
            for yy in 0..5 {
                let c = chi(x, yy);
                f.lin = f.lin.plus(&c.lin);
                f.products.extend(c.products);
            }
            f
        };
        let mut roles = vec![];
        for yy in 0..5 {
            for x in 0..5 {
                let mut f = chi(x, yy);
                let c = column((x + 4) % 5);
                f.lin = f.lin.plus(&c.lin).plus(&Lin::cell(25 + (x + 1) % 5));
                f.products.extend(c.products);
                roles.push(Role::Expr(f));
            }
        }
        roles.extend((0..5).map(|x| Role::Expr(column(x))));
        roles.extend([Role::SelfFree(Free::Word), Role::SelfFree(Free::Word)]);
        types.push(RowType {
            name: if rc { "KS1" } else { "KS0" }.into(),
            roles,
        });
    }
    // θ's preparation: the 25 input bits forwarded, the five columns' sums.
    let mut prep: Vec<Role> = (0..25).map(|_| Role::Forward).collect();
    prep.extend((0..5).map(|x| Role::Expr(Formula::linear(lin_sum(&[x, x + 5, x + 10, x + 15, x + 20])))));
    prep.extend([Role::SelfBit, Role::SelfBit]);
    types.push(RowType { name: "KSprep".into(), roles: prep });
    let mut xor = vec![];
    for u in 0..16 {
        xor.push(Role::Expr(Formula::linear(lin_sum(&[2 * u, 2 * u + 1]))));
        xor.push(Role::Forward);
    }
    types.push(RowType { name: "XOR".into(), roles: xor });
    for offset in [0usize, 31] {
        let mut roles: Vec<Role> = (0..31).map(|_| Role::Forward).collect();
        let mut lin = Lin::cell(31);
        lin.terms
            .extend((0..31).map(|e| (Coeff::k(1u64 << ((offset + e) % 64)), e as u16)));
        roles.push(Role::Expr(Formula::linear(lin)));
        types.push(RowType {
            name: format!("Pack{offset}"),
            roles,
        });
    }
    let mut free: Vec<Role> = (0..16).map(|_| Role::SelfBit).collect();
    free.extend((0..16).map(|k| Role::Expr(Formula::cell(k))));
    types.push(RowType { name: "Free".into(), roles: free });
    types.extend(e_units(32));
    types.push(RowType {
        name: "Const".into(),
        roles: (0..32).map(|k| Role::Const(0x1000_0000_0000_0001 * (k as u64 + 1))).collect(),
    });
    types.extend(sinks(32));
    types
}

fn index(types: &[RowType], name: &str) -> usize {
    types.iter().position(|t| t.name == name).unwrap_or_else(|| panic!("row type {name}"))
}

/// The sinks of π1's public data, the ports of the circuit compiler (`circuit::spec::Source`): the public input,
/// π1's two roots, its claims' 51 distinct elements (46 coordinates, 5 values), its 13 zero checks: 67 public
/// terms (SPEC-REC.md §2.4.6 counted the six row counts too; they are π1's proof, not public). Its regions, in order.
fn pi1_sinks(types: &[RowType]) -> Vec<Region> {
    let region = |name: &str, blocks: Vec<usize>| Region {
        row_type: index(types, name),
        blocks,
    };
    vec![
        region("SinkStatement", vec![0]),
        region("SinkRoot", vec![1]),
        // 51 = 32 + 16 + 2 + 1, and 13 = 8 + 4 + 1.
        region("SinkElement", vec![5, 4, 1, 0]),
        region("SinkZero", vec![3, 2, 0]),
    ]
}

/// Fewer elements and zero checks than π1's, and three 4-byte integers (the stream's other read).
fn small_sinks(types: &[RowType]) -> Vec<Region> {
    let mut sinks = pi1_sinks(types);
    sinks[2].blocks = vec![1, 0];
    sinks[3].blocks = vec![0];
    sinks.push(Region {
        row_type: index(types, "SinkCounts"),
        blocks: vec![0],
    });
    sinks
}

/// A small D16v circuit with every row type, for tests: `2^log_n` positions (at least `2^11`).
pub fn small_d16v(log_n: usize) -> Design {
    let types = d16v_types();
    let mut regions = vec![Region {
        row_type: index(&types, "Free"),
        blocks: vec![2],
    }];
    for name in ["K1", "K0a", "K0b", "KD", "XOR", "Kprep", "Pack0", "Pack15", "Pack30", "Pack45", "Pack60", "Emul", "Eadd", "Const"] {
        regions.push(Region {
            row_type: index(&types, name),
            blocks: vec![if name == "K1" { 1 } else { 0 }],
        });
    }
    regions.push(Region {
        row_type: index(&types, "Free"),
        blocks: vec![0],
    });
    regions.extend(small_sinks(&types));
    Design {
        log_n,
        log_row: 4,
        types,
        regions,
    }
}

/// A small D32v circuit with every row type, for tests.
pub fn small_d32v(log_n: usize) -> Design {
    let types = d32v_types();
    let mut regions = vec![Region {
        row_type: index(&types, "Free"),
        blocks: vec![1],
    }];
    for name in ["KSprep", "KS0", "KS1", "XOR", "Pack0", "Pack31", "Emul", "Eadd", "Const"] {
        regions.push(Region {
            row_type: index(&types, name),
            blocks: vec![if name == "KS0" { 1 } else { 0 }],
        });
    }
    regions.push(Region {
        row_type: index(&types, "Free"),
        blocks: vec![0],
    });
    regions.extend(small_sinks(&types));
    Design {
        log_n,
        log_row: 5,
        types,
        regions,
    }
}

/// D16v at its target shape (SPEC-REC.md §2.4.5, π1-rec): `N = 2^24` positions, 86% of them used; about 200
/// (block, role) pairs and π1's 69 public terms. The rows by type follow §2.4.5's totals (Keccak-f's 107
/// permutations: K1 657,408 rows, K0 164,352, KD 41,088, Kprep 11,449; the later blocks' XORs, the packings and
/// free bits, the `E` units, the constants), each region on two or three aligned blocks.
pub fn target_d16v() -> Design {
    let types = d16v_types();
    let region = |name: &str, blocks: Vec<usize>| Region {
        row_type: index(&types, name),
        blocks,
    };
    let mut regions = vec![
        region("Free", vec![13]),
        region("K1", vec![19, 17, 11]),
        region("K0a", vec![17, 14]),
        region("K0b", vec![13, 12]),
        region("KD", vec![15, 13]),
        region("Kprep", vec![13, 12]),
        region("XOR", vec![12]),
        region("Pack0", vec![10, 7]),
        region("Pack15", vec![10, 7]),
        region("Pack30", vec![10, 7]),
        region("Pack45", vec![10, 7]),
        region("Pack60", vec![10, 7]),
        region("Emul", vec![11, 10]),
        region("Eadd", vec![11, 9]),
        region("Const", vec![5]),
    ];
    regions.extend(pi1_sinks(&types));
    Design {
        log_n: 24,
        log_row: 4,
        types,
        regions,
    }
}

/// A target design on `2^log_n` positions: every region's blocks `delta` times smaller (at least one row), the sinks
/// as they are. The same pairs, formulas and public side: for timings below the target size.
pub fn scaled(design: &Design, log_n: usize) -> Design {
    let delta = design.log_n - log_n;
    let mut out = design.clone();
    out.log_n = log_n;
    for region in &mut out.regions {
        if !design.types[region.row_type].name.starts_with("Sink") {
            region.blocks.iter_mut().for_each(|s| *s = s.saturating_sub(delta));
        }
    }
    out
}

/// D32v at its target shape (SPEC-REC.md §2.6, π1's main line): `N = 2^23` positions, 32-cell slice rows (131
/// permutations of 1,600 slice rows), π1's 69 public terms.
pub fn target_d32v() -> Design {
    let types = d32v_types();
    let region = |name: &str, blocks: Vec<usize>| Region {
        row_type: index(&types, name),
        blocks,
    };
    let mut regions = vec![
        region("Free", vec![12]),
        region("KSprep", vec![13]),
        region("KS0", vec![17, 16]),
        region("KS1", vec![13, 12]),
        region("XOR", vec![11]),
        region("Pack0", vec![10, 8]),
        region("Pack31", vec![10, 8]),
        region("Emul", vec![10, 9]),
        region("Eadd", vec![10, 8]),
        region("Const", vec![4]),
    ];
    regions.extend(pi1_sinks(&types));
    Design {
        log_n: 23,
        log_row: 5,
        types,
        regions,
    }
}
