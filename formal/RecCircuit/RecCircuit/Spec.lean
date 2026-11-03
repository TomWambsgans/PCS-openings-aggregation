-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/circuit/spec.rs`.
import Field.F192

/-!
# π2's circuit as its PIOP sees it (`spec.rs`)

`N = 2^logN` positions `i = W·y + k`, rows of `W = 2^logWidth`. Every position has a pull `w i` and a push
`P i = F i + κ i` to the position `σ i`; `F i` is the formula of `i`'s role in the region of the block holding `i`'s
row (`formulaAt`; a row in no block is all forwards). A `port` role's push leaves the domain (its position is a
*hole*). `Satisfied C w`: every push to a position equals that position's pull, holes excluded — the relation π2's
PIOP proves (`PI2.md` §1, the pull-less form of `spec.rs`'s (1), (2)). The witness is a function, not an array: the
theorems never evaluate a circuit.

The semantic lookups follow the Rust's dense columns: `regionOf` is `row_regions` (each block in order fills its
rows, the last one wins), `kappaAt` is `kappa_column` (the last entry at a position wins).
-/

namespace RecCircuit

open Primitives

/-- `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, the witness's words (`leanvm_flock_gas::field::K`). -/
abbrev K := F64

/-- A polynomial of degree ≤ 2 in a row's cells, coefficients in `K`, no constant term (`Poly`). -/
structure Poly where
  /-- `(cell, coefficient)`. -/
  linear : List (ℕ × K)
  /-- `(cell a, cell b, coefficient)`, `a ≤ b`. -/
  quadratic : List (ℕ × ℕ × K)
  deriving DecidableEq, Inhabited

/-- `Poly::eval`: the linear terms, then the quadratic ones, in order. -/
def Poly.eval (p : Poly) (cells : ℕ → K) : K :=
  p.quadratic.foldl (fun acc t => acc + t.2.2 * cells t.1 * cells t.2.1)
    (p.linear.foldl (fun acc t => acc + t.2 * cells t.1) 0)

/-- The cells a polynomial reads. -/
def Poly.reads (p : Poly) : List ℕ :=
  p.linear.map (·.1) ++ p.quadratic.flatMap fun t => [t.1, t.2.1]

/-- What a role pushes (`Formula`). -/
inductive Formula where
  /-- Its own pull. -/
  | forward
  /-- A polynomial of degree ≤ 2 in the row's cells (an expression slot). -/
  | expr (p : Poly)
  /-- `Σ_l γ^l · cells[limbs[l]]`, to its port's outside tag; the position is a hole. -/
  | port (limbs : List ℕ)
  deriving DecidableEq, Inhabited

/-- `Formula::eval` (`γ` is the PIOP's; the pushes to positions never read it). -/
def Formula.eval (f : Formula) (cells : ℕ → K) (own gamma : K) : K :=
  match f with
  | .forward => own
  | .expr p => p.eval cells
  | .port limbs => (limbs.foldl (fun (acc : K × K) c => (acc.1 + acc.2 * cells c, acc.2 * gamma)) (0, 1)).1

def Formula.reads : Formula → List ℕ
  | .forward => []
  | .expr p => p.reads
  | .port limbs => limbs

def Formula.isPort : Formula → Bool
  | .port _ => true
  | _ => false

/-- A row type: the formula of each of its `W` roles. -/
structure Region where
  name : String
  roles : Array Formula
  deriving DecidableEq, Inhabited

/-- `2^logRows` rows of one region from row `row`, a multiple of `2^logRows`. -/
structure Block where
  row : ℕ
  logRows : ℕ
  region : ℕ
  deriving DecidableEq, Inhabited, Repr

/-- Where a port's limbs come from in the public inputs (`Source`). -/
inductive Source where
  /-- The statement's four 64-bit words, big-endian, word `l` limb `l`. -/
  | statement
  /-- Root `i`'s 32-byte `PCS_OPEN` word as four big-endian words, bytes `24 − 8l .. 32 − 8l` limb `l`. -/
  | root (i : ℕ)
  /-- Element `i`: its limbs `c0, c1, c2`. -/
  | element (i : ℕ)
  /-- A check of π1's verifier: three zero limbs. -/
  | zero
  /-- Padding of the zero checks to a power of two: three zero limbs of constants. -/
  | pad
  deriving DecidableEq, Inhabited, Repr

def Source.limbs : Source → ℕ
  | .statement | .root _ => 4
  | .element _ | .zero | .pad => 3

/-- A port: a hole whose push leaves the domain, to the outside tag `N + J`. -/
structure Port where
  position : ℕ
  source : Source
  deriving DecidableEq, Inhabited, Repr

/-- A 32-byte word of one of π1's `PCS_OPEN` inputs (`CallWord`); a constant word is its big-endian number. -/
inductive CallWord where
  | const (w : ℕ)
  | root (i : ℕ)
  | element (i : ℕ)
  /-- Coordinate `coordinate` of `pair_point` of element `element`. -/
  | pair (element coordinate : ℕ)
  deriving DecidableEq, Inhabited, Repr

/-- π2's circuit (`Circuit`). -/
structure Circuit where
  logN : ℕ
  logWidth : ℕ
  regions : Array Region
  /-- Aligned, disjoint; rows in none are all forwards. -/
  blocks : Array Block
  /-- The push's tag index, a position `< N` or `N + J`. -/
  sigma : Array ℕ
  /-- `κ ≠ 0` at these positions (increasing), all of them expression slots. -/
  kappa : Array (ℕ × K)
  /-- Port `J`'s outside tag is `N + J`, in block order. -/
  ports : Array Port
  /-- π1's `PCS_OPEN` inputs, in call order. -/
  calls : List (List CallWord)
  deriving Inhabited

namespace Circuit

variable (C : Circuit)

def n : ℕ := 2 ^ C.logN

def width : ℕ := 2 ^ C.logWidth

/-- Row `y`'s region (`row_regions`: the blocks in order, each filling its rows). -/
def regionOf (y : ℕ) : Option ℕ :=
  C.blocks.foldl (fun acc b => if b.row ≤ y ∧ y < b.row + 2 ^ b.logRows then some b.region else acc) none

/-- The formula of position `i`'s role (`Circuit::formula`). -/
def formulaAt (i : ℕ) : Formula :=
  match C.regionOf (i / C.width) with
  | none => .forward
  | some r => (C.regions.getD r default).roles.getD (i % C.width) .forward

/-- `κ` at position `i` (`kappa_column`). -/
def kappaAt (i : ℕ) : K := C.kappa.foldl (fun acc e => if e.1 = i then e.2 else acc) 0

/-- The cells of position `i`'s row: `cells c = w (W·y + c)`. -/
def cells (w : ℕ → K) (i : ℕ) : ℕ → K := fun c => w (C.width * (i / C.width) + c)

/-- Position `i`'s push, `F_i + κ_i` (`Circuit::check`'s `push`). -/
def push (w : ℕ → K) (i : ℕ) : K := (C.formulaAt i).eval (C.cells w i) (w i) 0 + C.kappaAt i

/-- `σ i`. -/
def sigmaAt (i : ℕ) : ℕ := C.sigma.getD i 0

/-- **The circuit is satisfied by `w`**: every push to a position equals that position's pull, holes (port
positions) excluded. -/
def Satisfied (w : ℕ → K) : Prop :=
  ∀ i < C.n, (C.formulaAt i).isPort = false → C.sigmaAt i < C.n → w (C.sigmaAt i) = C.push w i

/-- Port `J`'s limbs as the witness carries them: its formula's cells, read on its row. -/
def portLimbs (w : ℕ → K) (J : ℕ) : List K :=
  let p := C.ports.getD J default
  match C.formulaAt p.position with
  | .port limbs => limbs.map fun c => C.cells w p.position c
  | _ => []

end Circuit

end RecCircuit
