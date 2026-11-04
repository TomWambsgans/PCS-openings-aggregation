-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `viewOf` is transcribed from
-- `crates/leanvm_rec/src/pi2/adapt.rs` (`adapt`, `expr`, `port_formula`, `public_counts`) and
-- `crates/leanvm_rec/src/pi2/circuit.rs` (`Coeff::ONE`, `Coeff::k`, `Coeff::e`, `Coeff::gamma`, `Lin::cell`), branch
-- `leanvm-rec` @ 2b22581; the validity check is `pi2::circuit::Circuit::validate` with `spec::Circuit::check_shape`, as
-- `RecPiop.Circuit.Valid` states them.
import RecCircuit.Check
import RecStatement.Data

/-!
# The compiled circuit's view, and the checks run on it

π2's verifier is built from `RecStatement.Circuit` (`Data.circuit`, the Rust's `adapt` of the Rust compiler's circuit);
the theorems are about the Lean compiler's circuit (`RecCircuit.compile`). This file computes, in compiled code, what
links them:

* **`viewOf`**: the Lean compiler's circuit as π2's verifier reads it, `adapt` transcribed: every non-forward role of
  every block a pair (in block order, roles in order), its formula deduplicated by first appearance (`formulasOf`, the
  Rust's `id`), an expression's coefficients in `K`, a port's fingerprint `1, Y, Y²` or `1, Y, γ, γY`; the reads, the
  roots then the elements (`publicCounts`: one past the largest index the ports and calls name); one public term per
  port, tag `N + j`.
* **`callOf`**: a call word in the verifier's terms (a constant word its 32 bytes).
* **`validB`**: `RecPiop.Circuit.Valid` of `toPiop`, decided by loops over the positions, the blocks and the ports
  (`RecCompose.Valid`: `validB_sound`).
* **`viewCheck`**: the three, against `Data.circuit` and `Data.pi1Calls`; `Pi2ViewChecked` (`Facts.lean`) is it at
  every 32-byte π1 IV, **checked by evaluation at three IVs** (`RecComposeTest/ViewCheck.lean`, `RealCheck.lean`) and
  assumed at the others.
-/

namespace RecCompose

open LeanVM.Parameters

/-! ## `adapt` -/

/-- `Coeff::k(x)`: an element of `K`. -/
def kCoeff (k : RecCircuit.K) : RecStatement.Coeff := ⟨K.lane k, 0, 0, 0⟩

/-- `Coeff::ONE`, `Coeff::e(Y)`, `Coeff::e(Y²)`, `Coeff::gamma(1)`, `γ Y`. -/
def oneC : RecStatement.Coeff := ⟨1, 0, 0, 0⟩
def yC : RecStatement.Coeff := ⟨0, 1, 0, 0⟩
def y2C : RecStatement.Coeff := ⟨0, 0, 1, 0⟩
def gC : RecStatement.Coeff := ⟨1, 0, 0, 1⟩
def gyC : RecStatement.Coeff := ⟨0, 1, 0, 1⟩

/-- `Lin::cell(c)`. -/
def cellLin (c : ℕ) : RecStatement.Lin := ⟨[(oneC, c)], none⟩

/-- **`expr(poly)`**: the linear terms `(k, cell)`, the products `k · cell_a · cell_b`. -/
def exprFormula (p : RecCircuit.Poly) : RecStatement.Formula :=
  ⟨⟨p.linear.map fun t ↦ (kCoeff t.2, t.1), none⟩,
    p.quadratic.map fun t ↦ (kCoeff t.2.2, cellLin t.1, cellLin t.2.1)⟩

/-- **`port_formula(limbs)`**: `1, Y, Y²` on three limbs, `1, Y, γ, γY` on four (other lengths, which the Rust
refuses, as `RecCircuit.portWeights` takes them: each limb once). -/
def portFormula : List ℕ → RecStatement.Formula
  | [a, b, d] => ⟨⟨[(oneC, a), (yC, b), (y2C, d)], none⟩, []⟩
  | [a, b, d, e] => ⟨⟨[(oneC, a), (yC, b), (gC, d), (gyC, e)], none⟩, []⟩
  | ls => ⟨⟨ls.map fun c ↦ (oneC, c), none⟩, []⟩

/-- A role's pair: its formula and whether it pulls (a port does not); none for a forward. -/
def roleFormula : RecCircuit.Formula → Option (RecStatement.Formula × Bool)
  | .forward => none
  | .expr p => some (exprFormula p, true)
  | .port ls => some (portFormula ls, false)

/-- A block's region's roles. -/
def blockRoles (c : RecCircuit.Circuit) (b : RecCircuit.Block) : List RecCircuit.Formula :=
  (c.regions.getD b.region default).roles.toList

/-- **The slots**: every non-forward role of every block, in block order, roles in order, with its pair's formula and
pull flag. -/
def slots (c : RecCircuit.Circuit) : List (RecCircuit.Block × ℕ × RecStatement.Formula × Bool) :=
  c.blocks.toList.flatMap fun b ↦
    (List.range (blockRoles c b).length).filterMap fun k ↦
      (roleFormula ((blockRoles c b).getD k .forward)).map fun fp ↦ (b, k, fp)

/-- A formula added unless already there (the Rust's `id`). -/
def addFormula (fs : List RecStatement.Formula) (f : RecStatement.Formula) : List RecStatement.Formula :=
  if f ∈ fs then fs else fs ++ [f]

/-- **The formulas**, deduplicated in first appearance. -/
def formulasOf (c : RecCircuit.Circuit) : List RecStatement.Formula :=
  (slots c).foldl (fun fs s ↦ addFormula fs s.2.2.1) []

/-- **The pairs**: one per slot, its formula's index the first appearance's. -/
def pairsOf (c : RecCircuit.Circuit) : List RecStatement.Pair :=
  (slots c).map fun s ↦ ⟨s.1.row, s.1.logRows, s.2.1, (formulasOf c).idxOf s.2.2.1, s.2.2.2⟩

/-- `public_counts`' step on a port's source. -/
def sourceCounts (acc : ℕ × ℕ) : RecCircuit.Source → ℕ × ℕ
  | .root i => (max acc.1 (i + 1), acc.2)
  | .element i => (acc.1, max acc.2 (i + 1))
  | _ => acc

/-- `public_counts`' step on a call word. -/
def wordCounts (acc : ℕ × ℕ) : RecCircuit.CallWord → ℕ × ℕ
  | .root i => (max acc.1 (i + 1), acc.2)
  | .element i => (acc.1, max acc.2 (i + 1))
  | .pair i _ => (acc.1, max acc.2 (i + 1))
  | .const _ => acc

/-- **`public_counts`**: one past the largest root and element the ports and the calls name. -/
def publicCounts (c : RecCircuit.Circuit) : ℕ × ℕ :=
  c.calls.flatten.foldl wordCounts (c.ports.toList.foldl (fun a p ↦ sourceCounts a p.source) (0, 0))

/-- A port's public term's linear form: the statement `(S_0 + Y S_1) + γ (S_2 + Y S_3)`, a root `half 1 + γ half 0`,
an element itself, a zero check or a padding port nothing. -/
def termOf (roots : ℕ) : RecCircuit.Source → List (RecStatement.Coeff × ℕ)
  | .statement => [(oneC, 0), (yC, 1), (gC, 2), (gyC, 3)]
  | .root i => [(oneC, 4 + 2 * i + 1), (gC, 4 + 2 * i)]
  | .element i => [(oneC, 4 + 2 * roots + i)]
  | .zero | .pad => []

/-- The public terms: port `j`'s at tag `N + j`. -/
def publicTermsOf (c : RecCircuit.Circuit) : List RecStatement.PublicTerm :=
  (List.range c.ports.size).map fun j ↦
    ⟨2 ^ c.logN + j, ⟨termOf (publicCounts c).1 (c.ports.getD j default).source, none⟩⟩

/-- **`adapt`**: the Lean compiler's circuit as π2's verifier reads it. -/
def viewOf (c : RecCircuit.Circuit) : RecStatement.Circuit :=
  ⟨c.logN, c.logWidth, formulasOf c, pairsOf c,
    List.replicate (publicCounts c).1 .root ++ List.replicate (publicCounts c).2 .scalar, publicTermsOf c⟩

/-- A call word in the verifier's terms: a constant word its 32 bytes. -/
def callOf : RecCircuit.CallWord → RecStatement.CallWord
  | .const w => .const (RecCircuit.wordBytes32 w)
  | .root i => .root i
  | .element i => .element i
  | .pair e co => .pair e co

/-- The circuit's calls in the verifier's terms. -/
def callsOf (c : RecCircuit.Circuit) : List (List RecStatement.CallWord) := c.calls.map (·.map callOf)

/-! ## Validity, by loops -/

/-- The holes, as a bitmap of the positions: the ports' positions. -/
def holeMap (c : RecCircuit.Circuit) : Array Bool :=
  c.ports.foldl (fun a p ↦ a.set! p.position true) (Array.replicate c.n false)

/-- `σ` marked on `[0, n)`: `none` if two positions push to one tag or a tag is out of `[0, n + ports)`. -/
def sigmaMarks (c : RecCircuit.Circuit) : Option (Array Bool) :=
  Nat.fold c.n (fun i _ acc ↦ acc.bind fun a ↦
    if c.sigmaAt i < c.n + c.ports.size ∧ a.getD (c.sigmaAt i) true = false then some (a.set! (c.sigmaAt i) true)
    else none) (some (Array.replicate (c.n + c.ports.size) false))

/-- Every role of every region reads its row. -/
def readsB (c : RecCircuit.Circuit) : Bool :=
  c.regions.all fun r ↦ r.roles.all fun f ↦ f.reads.all (· < c.width)

/-- The blocks: aligned, in range, their regions existing, pairwise disjoint. -/
def blocksB (c : RecCircuit.Circuit) : Bool :=
  c.blocks.all (fun b ↦ b.row % 2 ^ b.logRows == 0 && decide (b.row + 2 ^ b.logRows ≤ 2 ^ (c.logN - c.logWidth)) &&
    decide (b.region < c.regions.size)) &&
  RecCircuit.allBelow c.blocks.size fun a ↦ RecCircuit.allBelow c.blocks.size fun b ↦
    !(a < b) || (c.blocks.getD a default).row + 2 ^ (c.blocks.getD a default).logRows ≤ (c.blocks.getD b default).row ||
      (c.blocks.getD b default).row + 2 ^ (c.blocks.getD b default).logRows ≤ (c.blocks.getD a default).row

/-- The ports: distinct positions, each a hole of the domain pushing to its outside tag; every hole of every block a
port's. -/
def portsB (c : RecCircuit.Circuit) : Bool :=
  (RecCircuit.allBelow c.ports.size fun a ↦ RecCircuit.allBelow c.ports.size fun b ↦
    a == b || (c.ports.getD a default).position != (c.ports.getD b default).position) &&
  (RecCircuit.allBelow c.ports.size fun j ↦ (c.ports.getD j default).position < c.n &&
    (c.formulaAt (c.ports.getD j default).position).isPort && c.sigmaAt (c.ports.getD j default).position == c.n + j) &&
  c.blocks.all fun b ↦ RecCircuit.allBelow (blockRoles c b).length fun k ↦
    !((blockRoles c b).getD k .forward).isPort ||
      RecCircuit.allBelow (2 ^ b.logRows) fun y ↦ c.ports.any fun p ↦ p.position == c.width * (b.row + y) + k

/-- No formula reads a hole: no role of a hole's row reads the hole's cell. -/
def noHoleReadB (c : RecCircuit.Circuit) : Bool :=
  c.ports.all fun p ↦ RecCircuit.allBelow c.width fun k ↦
    !(c.formulaAt (c.width * (p.position / c.width) + k)).reads.contains (p.position % c.width)

/-- `κ` only at expression slots. -/
def kappaExprB (c : RecCircuit.Circuit) : Bool :=
  c.kappa.all fun e ↦ e.2 == 0 || !decide (e.1 < c.n) || match c.formulaAt e.1 with
    | .expr _ => true
    | _ => false

/-- `σ` on the non-holes: inside, onto the non-holes, injective with the ports' tags. -/
def sigmaOkB (c : RecCircuit.Circuit) : Bool :=
  let holes := holeMap c
  match sigmaMarks c with
  | none => false
  | some marks =>
    RecCircuit.allBelow c.n fun i ↦ holes.getD i false ||
      (decide (c.sigmaAt i < c.n) && !holes.getD (c.sigmaAt i) false && marks.getD i false)

/-- **`RecPiop.Circuit.Valid` of `toPiop`, decided by loops** (`validB_sound`). -/
def validB (c : RecCircuit.Circuit) : Bool :=
  decide (c.logWidth < c.logN) && (c.regions.all fun r ↦ r.roles.size == c.width) && readsB c && blocksB c &&
    portsB c && noHoleReadB c && kappaExprB c && sigmaOkB c

/-! ## The check -/

deriving instance DecidableEq for RecStatement.Circuit

/-- **The compiled circuit's check against the deployment's data**: its view is `Data.circuit`, its calls
`Data.pi1Calls`, and it is valid. -/
def viewCheck (c : RecCircuit.Compiled) : Bool :=
  decide (viewOf c.circuit = RecStatement.Data.circuit) && decide (callsOf c.circuit = RecStatement.Data.pi1Calls) &&
    validB c.circuit

end RecCompose
