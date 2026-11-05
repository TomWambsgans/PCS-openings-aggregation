// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Linear relations on committed polynomials, and their combination into one weighted claim per commitment
//! (SPEC.md §8).
//!
//! A *term* is `coefficient · col(point)` for a column of a commitment's layout, read at a point (the column's own
//! coordinates, low first), optionally Frobenius-twisted (`eq(φ^k(point), ·)`, for the ring switch). A *relation* is
//! `Σ terms = value`. All relations on one commitment are combined with the powers of one late challenge into one
//! claim, whose terms with the same column, point and twist are merged.

use leanvm_flock_gas::scalar::Scalar;

/// The commitments a proof's claims are on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Commitment {
    /// The witness: the tables' columns, and Flock's `q_flock`.
    C1,
    /// After the bus challenges: the product heap and the quotients.
    C2,
    /// Setup: the bytecode's tuples and the memory's addresses.
    Setup,
}

pub const COMMITMENTS: [Commitment; 3] = [Commitment::C1, Commitment::C2, Commitment::Setup];

/// A column of a commitment's layout (SPEC.md §3).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Column {
    /// `C1`: a table's column, by leanVM's opcode and local index (BLAKE2S's limbs are the univariate copies).
    Table { table: usize, column: usize },
    /// `C1`: a table's counter-inverse column `z_T`.
    Inverse(usize),
    /// `C1`: the memory's limbs 0, 1, 2 and its final counts (3).
    Memory(usize),
    /// `C1`: the bytecode's final counts.
    BytecodeFinal,
    /// `C1`: `q_flock` (values), its slot `j` as a table of the BLAKE2S rows.
    QflockSlot(usize),
    /// `C1`: `q_flock` (values), whole.
    Qflock,
    /// `C1`: `q_flock`'s bit-slice `i` (the term's twist field), an `E`-valued multilinear of its word coordinates:
    /// a term of the bit-slice claim type (SPEC-FLOCK.md, lever (a)), which `PCS_OPEN` ring-switches.
    QflockBits,
    /// `C2`: the product heap.
    Heap,
    /// `C2`: the tree quotient's chunk.
    TreeQuotient(usize),
    /// `C2`: a heap block's leaf quotient, its chunk.
    LeafQuotient { block: usize, chunk: usize },
    /// `C2`: the constraint quotient's chunk.
    ConstraintQuotient(usize),
    /// Setup: the bytecode's 16 tuple slots (slot 1 the pc `g^i`, slot 2 zero).
    BytecodeTuple,
    /// Setup: the memory's addresses `g^i`.
    Address,
    /// A column of another protocol's layout on the same stacks (`crates/slh_fast`, SLH-DSA's π1): its commitment
    /// and its number there.
    Extra { commitment: Commitment, id: u16 },
}

impl Column {
    pub fn commitment(self) -> Commitment {
        match self {
            Column::Table { .. }
            | Column::Inverse(_)
            | Column::Memory(_)
            | Column::BytecodeFinal
            | Column::QflockSlot(_)
            | Column::Qflock
            | Column::QflockBits => Commitment::C1,
            Column::Heap | Column::TreeQuotient(_) | Column::LeafQuotient { .. } | Column::ConstraintQuotient(_) => {
                Commitment::C2
            }
            Column::BytecodeTuple | Column::Address => Commitment::Setup,
            Column::Extra { commitment, .. } => commitment,
        }
    }

    /// The column's id in its layout, as a term's word carries it.
    pub fn id(self) -> u64 {
        match self {
            Column::Table { table, column } => (table as u64) << 8 | column as u64,
            Column::Inverse(t) => 0x1000 | t as u64,
            Column::Memory(k) => 0x1100 | k as u64,
            Column::BytecodeFinal => 0x1200,
            Column::QflockSlot(j) => 0x1300 | j as u64,
            Column::Qflock => 0x1400,
            Column::QflockBits => 0x1500,
            Column::Heap => 0x2000,
            Column::TreeQuotient(c) => 0x2100 | c as u64,
            Column::LeafQuotient { block, chunk } => 0x2200 | (block as u64) << 4 | chunk as u64,
            Column::ConstraintQuotient(c) => 0x2300 | c as u64,
            Column::BytecodeTuple => 0x3000,
            Column::Address => 0x3100,
            Column::Extra { commitment, id } => {
                let c = match commitment {
                    Commitment::C1 => 1,
                    Commitment::C2 => 2,
                    Commitment::Setup => 3,
                };
                0x0080_0000 | c << 16 | id as u64
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Term<S> {
    pub column: Column,
    pub point: Vec<S>,
    pub twist: u8,
    pub coefficient: S,
}

/// `Σ terms = value`.
#[derive(Clone, Debug)]
pub struct Relation<S> {
    pub terms: Vec<Term<S>>,
    pub value: S,
}

/// One weighted claim: its points (each a column's low coordinates), its terms (column, point index, twist,
/// coefficient) and its value.
#[derive(Clone, Debug)]
pub struct Combined<S> {
    pub points: Vec<Vec<S>>,
    pub terms: Vec<(Column, usize, u8, S)>,
    pub value: S,
    /// How many relations it combines.
    pub relations: usize,
}

/// The relations a verifier states, by commitment.
pub struct Relations<S> {
    pub list: Vec<Relation<S>>,
}

impl<S: Scalar + PartialEq> Default for Relations<S> {
    fn default() -> Self {
        Self { list: Vec::new() }
    }
}

impl<S: Scalar + PartialEq> Relations<S> {
    pub fn push(&mut self, terms: Vec<Term<S>>, value: S) {
        let commitment = terms[0].column.commitment();
        assert!(
            terms.iter().all(|term| term.column.commitment() == commitment),
            "a relation is on one commitment"
        );
        self.list.push(Relation { terms, value });
    }

    /// One term at `point`, coefficient 1, equal to `value`.
    pub fn equal(&mut self, column: Column, point: &[S], value: S) {
        self.push(vec![term(column, point, S::one())], value);
    }

    /// The relations on `commitment`, combined with the powers of `rho`.
    pub fn combine(&self, commitment: Commitment, rho: S) -> Option<Combined<S>> {
        let mine: Vec<&Relation<S>> = self
            .list
            .iter()
            .filter(|relation| relation.terms[0].column.commitment() == commitment)
            .collect();
        if mine.is_empty() {
            return None;
        }
        let mut points: Vec<Vec<S>> = Vec::new();
        let mut terms: Vec<(Column, usize, u8, S)> = Vec::new();
        let mut value = S::zero();
        let mut scale = S::one();
        for relation in &mine {
            value += scale * relation.value;
            for term in &relation.terms {
                let p = match points.iter().position(|p| *p == term.point) {
                    Some(p) => p,
                    None => {
                        points.push(term.point.clone());
                        points.len() - 1
                    }
                };
                let coefficient = scale * term.coefficient;
                match terms
                    .iter_mut()
                    .find(|(c, q, k, _)| *c == term.column && *q == p && *k == term.twist)
                {
                    Some((_, _, _, existing)) => *existing += coefficient,
                    None => terms.push((term.column, p, term.twist, coefficient)),
                }
            }
            scale *= rho;
        }
        // A point that is a prefix of a longer one is that one: a column reads as many of a point's coordinates as
        // it has variables, which its layout says. The empty point (`TreeQuotient(1)`, a column of 0 variables) is a
        // prefix of every point, so it merges into the first longest one; harmless, since that column reads none of
        // its coordinates (found by the Lean transcription, UniStatement).
        let longest: Vec<usize> = (0..points.len())
            .map(|p| {
                (0..points.len())
                    .filter(|&q| points[q].len() >= points[p].len() && points[q][..points[p].len()] == points[p][..])
                    .max_by_key(|&q| (points[q].len(), std::cmp::Reverse(q)))
                    .expect("a point is its own prefix")
            })
            .collect();
        let kept: Vec<usize> = (0..points.len()).filter(|&p| longest[p] == p).collect();
        let renumber = |p: usize| kept.iter().position(|&q| q == longest[p]).expect("kept");
        let mut merged: Vec<(Column, usize, u8, S)> = Vec::new();
        for (column, p, twist, coefficient) in terms {
            let p = renumber(p);
            match merged.iter_mut().find(|(c, q, k, _)| *c == column && *q == p && *k == twist) {
                Some((_, _, _, existing)) => *existing += coefficient,
                None => merged.push((column, p, twist, coefficient)),
            }
        }
        Some(Combined {
            points: kept.iter().map(|&p| points[p].clone()).collect(),
            terms: merged,
            value,
            relations: mine.len(),
        })
    }
}

pub fn term<S: Scalar>(column: Column, point: &[S], coefficient: S) -> Term<S> {
    Term {
        column,
        point: point.to_vec(),
        twist: 0,
        coefficient,
    }
}
