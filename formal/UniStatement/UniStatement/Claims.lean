-- Part of this repository. Transcribed from `crates/leanvm_univariate/src/claims.rs`. MIT OR Apache-2.0; see
-- NOTICE.md.
module

public import UniStatement.Basic

/-!
# Relations and their combination (`claims.rs`, SPEC.md §8)

A **term** is `coefficient · col(point)` for a column of a commitment's layout, read at a point (the
column's own coordinates, low first), optionally Frobenius-twisted (`eq(φ^k(point), ·)`, the ring switch's).
A **relation** is `Σ terms = value`, all its terms on one commitment. All the relations on one commitment
are **combined** with the powers of one late challenge `ρ` into one claim (`combine`): its points (each
point once, in order of first use), its terms (the same column, point and twist merged), its value; then a
point that is a prefix of a longer one is that one (a column reads as many of a point's coordinates as it
has variables).
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters

/-- **The commitments** a proof's claims are on (`Commitment`). -/
inductive Commitment where
  /-- The witness: the tables' columns, and Flock's `q_flock`. -/
  | c1
  /-- After the bus challenges: the product heap and the quotients. -/
  | c2
  /-- Setup: the bytecode's tuples and the memory's addresses. -/
  | setup
  deriving DecidableEq, Repr, Inhabited

/-- `COMMITMENTS`. -/
def commitments : List Commitment := [.c1, .c2, .setup]

/-- The Rust's name (`Debug`). -/
def Commitment.name : Commitment → String
  | .c1 => "C1"
  | .c2 => "C2"
  | .setup => "Setup"

/-- **A column of a commitment's layout** (`Column`, SPEC.md §3). -/
inductive Column where
  /-- `C1`: a table's column, by opcode and local index (BLAKE2S's limbs are the univariate copies). -/
  | table (table column : ℕ)
  /-- `C1`: a table's counter-inverse column `z_T`. -/
  | inverse (table : ℕ)
  /-- `C1`: the memory's limbs `0, 1, 2` and its final counts (`3`). -/
  | memory (k : ℕ)
  /-- `C1`: the bytecode's final counts. -/
  | bytecodeFinal
  /-- `C1`: `q_flock` (values), its slot `j` as a table of the BLAKE2S rows. -/
  | qflockSlot (j : ℕ)
  /-- `C1`: `q_flock` (values), whole. -/
  | qflock
  /-- `C1`: `q_flock`'s bit-slice `i` (the term's twist), the bit-slice claim type (extension B). -/
  | qflockBits
  /-- `C2`: the product heap. -/
  | heap
  /-- `C2`: the tree quotient's chunk. -/
  | treeQuotient (c : ℕ)
  /-- `C2`: a heap block's leaf quotient, its chunk. -/
  | leafQuotient (block chunk : ℕ)
  /-- `C2`: the constraint quotient's chunk. -/
  | constraintQuotient (c : ℕ)
  /-- Setup: the bytecode's 16 tuple slots. -/
  | bytecodeTuple
  /-- Setup: the memory's addresses `g^i`. -/
  | address
  deriving DecidableEq, Repr, Inhabited

/-- `Column::commitment`. -/
def Column.commitment : Column → Commitment
  | .table .. | .inverse _ | .memory _ | .bytecodeFinal | .qflockSlot _ | .qflock | .qflockBits => .c1
  | .heap | .treeQuotient _ | .leafQuotient .. | .constraintQuotient _ => .c2
  | .bytecodeTuple | .address => .setup

/-- `Column::id`: the column's id in its layout, as a term's word carries it. -/
def Column.id : Column → ℕ
  | .table t c => t <<< 8 ||| c
  | .inverse t => 0x1000 ||| t
  | .memory k => 0x1100 ||| k
  | .bytecodeFinal => 0x1200
  | .qflockSlot j => 0x1300 ||| j
  | .qflock => 0x1400
  | .qflockBits => 0x1500
  | .heap => 0x2000
  | .treeQuotient c => 0x2100 ||| c
  | .leafQuotient b c => 0x2200 ||| b <<< 4 ||| c
  | .constraintQuotient c => 0x2300 ||| c
  | .bytecodeTuple => 0x3000
  | .address => 0x3100

/-- **A term** (`Term`). -/
structure Term where
  column : Column
  point : List E
  twist : ℕ
  coefficient : E

/-- `term(column, point, coefficient)`: untwisted. -/
def term (column : Column) (point : List E) (coefficient : E) : Term := ⟨column, point, 0, coefficient⟩

/-- **A relation** `Σ terms = value` (`Relation`). -/
structure Relation where
  terms : List Term
  value : E

/-- A relation's commitment: its first term's (`Relations::push` asserts they all agree). -/
def Relation.commitment (r : Relation) : Commitment :=
  match r.terms with
  | t :: _ => t.column.commitment
  | [] => .c1

/-- `Relations::equal(column, point, value)`: one term at `point`, coefficient `1`. -/
def Relation.equal (column : Column) (point : List E) (value : E) : Relation := ⟨[term column point 1], value⟩

/-- **One weighted claim** (`Combined`): its points, its terms (column, point index, twist, coefficient),
its value, and how many relations it combines. -/
structure Combined where
  points : List (List E)
  terms : List (Column × ℕ × ℕ × E)
  value : E
  relations : ℕ
  deriving Inhabited

/-- Add `coefficient` to the term `(column, p, twist)`, or append it. -/
def mergeTerm (terms : Array (Column × ℕ × ℕ × E)) (column : Column) (p twist : ℕ) (coefficient : E) :
    Array (Column × ℕ × ℕ × E) :=
  match terms.findIdx? (fun (c, q, k, _) ↦ c == column && q == p && k == twist) with
  | some i => terms.modify i fun (c, q, k, v) ↦ (c, q, k, v + coefficient)
  | none => terms.push (column, p, twist, coefficient)

/-- `longest[p]`: of the points having point `p` as a prefix (itself included), the longest, the first
among equals (`max_by_key((len, Reverse(q)))`). -/
def longestOf (points : Array (List E)) (p : ℕ) : ℕ :=
  let pp := points.getD p []
  (List.range points.size).foldl (fun best q ↦
    let pq := points.getD q []
    if pq.length ≥ pp.length ∧ pq.take pp.length == pp ∧ pq.length > (points.getD best []).length then q
    else best) p

/-- **`Relations::combine(commitment, ρ)`**: the relations on `commitment`, combined with the powers of
`ρ`; `none` if there are none. -/
def combine (relations : List Relation) (commitment : Commitment) (rho : E) : Option Combined :=
  let mine := relations.filter (·.commitment == commitment)
  if mine.isEmpty then none else
  let (points, terms, value, _) := mine.foldl
    (fun (acc : Array (List E) × Array (Column × ℕ × ℕ × E) × E × E) relation ↦
      let (points, terms, value, scale) := acc
      let value := value + scale * relation.value
      let (points, terms) := relation.terms.foldl
        (fun (acc : Array (List E) × Array (Column × ℕ × ℕ × E)) t ↦
          let (points, terms) := acc
          let (points, p) := match points.findIdx? (· == t.point) with
            | some p => (points, p)
            | none => (points.push t.point, points.size)
          (points, mergeTerm terms t.column p t.twist (scale * t.coefficient)))
        (points, terms)
      (points, terms, value, scale * rho))
    (#[], #[], 0, 1)
  let longest := (List.range points.size).map (longestOf points)
  let kept := (List.range points.size).filter fun p ↦ longest.getD p p == p
  let renumber (p : ℕ) : ℕ := kept.idxOf (longest.getD p p)
  let merged := terms.foldl (fun acc (column, p, twist, coefficient) ↦
    mergeTerm acc column (renumber p) twist coefficient) #[]
  some ⟨kept.map (points.getD · []), merged.toList, value, mine.length⟩

end UniStatement

end
