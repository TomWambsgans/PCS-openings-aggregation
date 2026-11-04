-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.ComposeBase
import RecGraph.Hazard

/-!
# The composition's interface: what each part of π1-rec3's verifier is to satisfy

`Pi1Sim` is composed (`Sim/Compose.lean`) from the parts below, each stated here as a `Prop` the parts' files prove:

* `FlockSpec`: Flock (`Pi1.verifyWalked` against `Flock.verifyWalkedFs`): its point, its ring map and target, and the
  hazard's coordinate (its challenge 39 is the point's first coordinate);
* `TableSpec PR TS nT`, `ConstraintSpec PR CS`, `DegreeSpec`, `HeapSpec PR HS`: the tables' parts, the constraint and
  heap relations (`PR` the parts' representation, `TS`, `CS`, `HS` shapes of `UniStatement`'s values, as the tail
  needs them);
* `TailSpec OK nB chB`: the tail after `ρ` (`tailP`: one claim per commitment, then the batch) against `batchFs`, for
  relations satisfying `OK`;
* `ShapeSpec TS CS HS OK`: reduce's relations (`relsUni`, `c2Uni`) satisfy `OK` off the hazard.

Every part is stated for every permutation, IV, public input and stream.
-/

-- The judgment is `RecGraph.Sim.Sim`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-- The digits' count at π1-rec3's shape (`max h (r_W + 4) + 2`). -/
abbrev wLen : Nat := max reference.heap.h (reference.constraintVars + 4) + 2

/-- A table part's representation. -/
abbrev PartRep : Type :=
  (KeccakState → KeccakState) → List UInt8 → List UInt8 → Array UInt8 → RecState → TablePartS → TablePart → Prop

/-- The representation grows with the state. -/
def PartRepGrows (PR : PartRep) : Prop :=
  ∀ π iv publicInput stream (st st' : RecState) p u, KInv st → Grows st st' →
    PR π iv publicInput stream st p u → PR π iv publicInput stream st' p u

/-- **Flock** (helper b's `verifyWalked_sim`): `3552` bytes, `46` challenges; the point (of `26` coordinates), the
ring end's map and target; the challenge `39` after the start, the point's first coordinate. -/
def FlockSpec : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState),
    Sim π iv publicInput stream st (Pi1.verifyWalked 32 flockMain .rec3)
      (UniStatement.Flock.verifyWalkedFs (Fp π) 32 flockMain .rec3) 3552 46
      (fun st' a b ↦ RpL π iv publicInput stream st' a.1 b.1 ∧ b.1.length = 26 ∧
        (∃ mapE tgtE, b.2 = .ring mapE tgtE ∧ RpL π iv publicInput stream st' a.2.1 mapE ∧
          Rp π iv publicInput stream st' a.2.2 tgtE) ∧
        val π iv publicInput stream st' ((chIds st').getD ((chIds st).length + 39) 0) = b.1.headD 0)

/-- **A table's part** (`table_part`): `nT t` bytes, no challenge. -/
def TableSpec (PR : PartRep) (TS : Table → List E → TablePart × List Relation → Prop) (nT : Table → Nat) :
    Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (t : Table), t ∈ tables →
    ∀ (weights : Array Nat) (weightsE : Array E) (beta : Nat) (betaE : E) (w : List Nat) (wE : List E),
    st.nodes[0]? = some Node.seed → RpL π iv publicInput stream st weights.toList weightsE.toList → weightsE.size = 16 →
    Rp π iv publicInput stream st beta betaE → RpL π iv publicInput stream st w wE → wE.length = wLen →
    Sim π iv publicInput stream st (Pi1.tablePart t (reference.heights.getD t.opcode 0) weights beta w)
      (UniStatement.tablePart (m := Id) t (reference.heights.getD t.opcode 0) weightsE betaE wE) (nT t) 0
      (fun st' a b ↦ PR π iv publicInput stream st' a.1 b.1 ∧ RpRels π iv publicInput stream st' a.2 b.2 ∧
        TS t wE b)

/-- **The constraint quotient's relation** (`constraintRelation`, pure). -/
def ConstraintSpec (PR : PartRep) (CS : List E → E → Relation → Prop) : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (parts : List TablePartS) (partsE : List TablePart) (pw : List Nat) (pwE : List E) (gamma t cv : Nat)
    (gammaE tE cvE : E) (w : List Nat) (wE : List E),
    Good st → st.nodes[0]? = some Node.seed → List.Forall₂ (PR π iv publicInput stream st) parts partsE → RpL π iv publicInput stream st pw pwE →
    pwE.length = 4 → Rp π iv publicInput stream st gamma gammaE → Rp π iv publicInput stream st t tE →
    Rp π iv publicInput stream st cv cvE → RpL π iv publicInput stream st w wE → wE = digits tE wLen →
    PSim st (Pi1.constraintRelation reference parts pw gamma t cv w)
      (UniStatement.constraintRelation reference partsE pwE gammaE tE cvE wE).1
      (fun st' a b ↦ RpRel π iv publicInput stream st' a b ∧ CS wE tE b)

/-- **The constraint quotient's degree** is the shape's (`Shape.constraintDegree`). -/
def DegreeSpec : Prop :=
  ∀ (partsE : List TablePart) (pwE : List E) (gammaE tE cvE : E) (wE : List E), partsE.length = 6 →
    (UniStatement.constraintRelation reference partsE pwE gammaE tE cvE wE).2 = reference.constraintDegree

/-- **The heap's relations** (`heapRelations`, pure), and the leaf quotients' columns. -/
def HeapSpec (PR : PartRep) (HS : List E → List Relation × List (Column × Nat × Bool) → Prop) : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (active : List Nat) (activeE : List E) (parts : List TablePartS) (partsE : List TablePart)
    (weights : Array Nat) (weightsE : Array E) (beta hv cv mpl mps bpl bps : Nat)
    (betaE hvE cvE mplE mpsE bplE bpsE : E) (w : List Nat) (wE : List E),
    Good st → st.nodes[0]? = some Node.seed → RpL π iv publicInput stream st active activeE → activeE.length = 6 →
    List.Forall₂ (PR π iv publicInput stream st) parts partsE → partsE.length = 6 →
    RpL π iv publicInput stream st weights.toList weightsE.toList → weightsE.size = 16 →
    Rp π iv publicInput stream st beta betaE → Rp π iv publicInput stream st hv hvE →
    Rp π iv publicInput stream st cv cvE → Rp π iv publicInput stream st mpl mplE →
    Rp π iv publicInput stream st mps mpsE → Rp π iv publicInput stream st bpl bplE →
    Rp π iv publicInput stream st bps bpsE → RpL π iv publicInput stream st w wE → wE.length = wLen →
    PSim st
      (Pi1.heapRelations reference active parts weights beta hv cv mpl mps bpl bps w
        (chunks (reference.constraintDegree + 1)))
      (UniStatement.heapRelations reference activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE
        (chunks (reference.constraintDegree + 1)))
      (fun st' a b ↦ RpRels π iv publicInput stream st' a.1 b.1 ∧ a.2 = b.2 ∧ HS wE b)

/-- **π1-rec3's verifier after `ρ`** (`reduce`'s tail, literally): one claim per commitment, then the batch. -/
def tailP (relations : List RelationS) (rho : Sym) (c2Columns : List (Column × Nat × Bool)) (map : List Sym) :
    Prog (List (Commitment × List Sym × Sym)) := do
  let mut combined : Array (Commitment × CombinedS) := #[]
  for c in commitments do
    if let some claim ← Pi1.combine relations c rho then
      combined := combined.push (c, claim)
  let _ ← one
  let stackLayouts := layouts reference c2Columns
  Pi1.batch combined.toList stackLayouts (some map)

/-- `UniStatement`'s tail after `ρ`, as `reduceWithFs` has it at π1-rec3. -/
def tailU (π : KeccakState → KeccakState) (relations : List Relation) (rho : E)
    (c2Columns : List (Column × Nat × Bool)) (map : List E) :
    ChanM Id (List (Commitment × Opening) × Option Flock.MatrixClaim) :=
  batchFs (Fp π) .rec3
    (List.filterMap (fun x ↦ Option.map (fun y ↦ (x, y)) (UniStatement.combine relations x rho)) commitments)
    (layouts reference c2Columns) (UniStatement.combine [] .c1 1) (some map) none

/-- **The openings, represented**: one point claim per commitment, its point and value represented. -/
def OpeningsR (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)
    (st : RecState) (a : List (Commitment × List Nat × Nat)) (b : List (Commitment × Opening)) : Prop :=
  List.Forall₂ (fun x y ↦ ∃ ptE vE, y = (x.1, .point ptE vE none) ∧ RpL π iv publicInput stream st x.2.1 ptE ∧
    Rp π iv publicInput stream st x.2.2 vE) a b

/-- **The tail**: for relations satisfying `OK`, `nB` bytes and `chB` challenges, the openings represented, no
pending matrices. -/
def TailSpec (OK : List Relation → List (Column × Nat × Bool) → Prop)
    (nB chB : List Relation → List (Column × Nat × Bool) → Nat) : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (relsS : List RelationS) (rels : List Relation) (rhoS : Nat) (ρ : E) (c2 : List (Column × Nat × Bool))
    (mapS : List Nat) (mapE : List E),
    Good st → 0 < st.nodes.size → RpRels π iv publicInput stream st relsS rels →
    Rp π iv publicInput stream st rhoS ρ → RpL π iv publicInput stream st mapS mapE → OK rels c2 →
    Sim π iv publicInput stream st (tailP relsS rhoS c2 mapS) (tailU π rels ρ c2 mapE) (nB rels c2) (chB rels c2)
      (fun st' a b ↦ OpeningsR π iv publicInput stream st' a b.1 ∧ b.2 = none)

/-- The tables' relations, as `reduceWithFs` concatenates them. -/
def tabRels (outs : List (TablePart × List Relation)) : Array Relation :=
  outs.foldl (fun acc o ↦ acc ++ o.2.toArray) #[]

/-- **The relations `reduceWithFs` states at π1-rec3**, from its intermediate values (step 4 to 7). -/
def relsUni (outs : List (TablePart × List Relation)) (wE alphasE : List E) (betaE mfc addr mpl bfc bpl : E)
    (constraint : Relation) (heapRels : List Relation) (flockPt : List E) (target : E) : List Relation :=
  ((((((((tabRels outs).push (Relation.equal (.memory 3) (wE.take reference.logMemory) mfc)).push
    (Relation.equal .address (wE.take reference.logMemory) addr)).push
    { terms := (List.range 3).map fun k ↦
        term (.memory k) (wE.take reference.logMemory) ((UniStatement.eqKernel alphasE).getD (3 + k) 0),
      value := mpl + betaE + (UniStatement.eqKernel alphasE).getD 0 0 * sepMem +
        (UniStatement.eqKernel alphasE).getD 1 0 * addr + (UniStatement.eqKernel alphasE).getD 2 0 * mfc }).push
    (Relation.equal .bytecodeFinal (wE.take reference.logBytecode) bfc)).push
    (Relation.equal .bytecodeTuple (alphasE ++ wE.take reference.logBytecode)
      (bpl + betaE + (UniStatement.eqKernel alphasE).getD 2 0 * bfc))).push constraint ++ heapRels.toArray).push
    { terms := [{ column := .qflock, point := flockPt, twist := ringTwist, coefficient := 1 }],
      value := target }).toList

/-- **`C2`'s columns at π1-rec3**: the heap, the tree quotient, the constraint quotient's chunks, the leaves'. -/
def c2Uni (leaf : List (Column × Nat × Bool)) : List (Column × Nat × Bool) :=
  [(.heap, reference.heap.h, true), (.treeQuotient 0, reference.heap.h, true), (.treeQuotient 1, 0, true)] ++
    List.map (fun x ↦ (Column.constraintQuotient x.2, x.1, true))
      ((chunks (reference.constraintDegree + 1)).zip (List.range (chunks (reference.constraintDegree + 1)).length)) ++
    leaf

/-- **Off the hazard, reduce's relations satisfy `OK`**, from the parts' shapes. -/
def ShapeSpec (TS : Table → List E → TablePart × List Relation → Prop) (CS : List E → E → Relation → Prop)
    (HS : List E → List Relation × List (Column × Nat × Bool) → Prop)
    (OK : List Relation → List (Column × Nat × Bool) → Prop) : Prop :=
  ∀ (tE : E) (alphasE : List E) (betaE : E) (flockPt : List E) (target : E) (outs : List (TablePart × List Relation))
    (mfc addr mpl bfc bpl : E) (constraint : Relation) (heapOut : List Relation × List (Column × Nat × Bool)),
    alphasE.length = 4 → flockPt.length = 26 → List.Forall₂ (fun t o ↦ TS t (digits tE wLen) o) tables outs →
    CS (digits tE wLen) tE constraint → HS (digits tE wLen) heapOut → ¬ Hazard (flockPt.headD 0) tE →
    OK (relsUni outs (digits tE wLen) alphasE betaE mfc addr mpl bfc bpl constraint heapOut.1 flockPt target)
      (c2Uni heapOut.2)

/-- No hazard at a channel's challenges `42` (`p_0`) and `49` (`t`), `t` drawn: `MergeHazard`'s condition. -/
def NoHazardAt (c : Chan) : Prop :=
  ¬ (50 ≤ c.challenges.size ∧ Hazard (c.challenges.getD 42 0) (c.challenges.getD 49 0))

/-- A root's halves, represented, at their stream offsets. -/
def RootR (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (a : Sym × Sym) (x : E × E) (off : Nat) : Prop :=
  Rp π iv publicInput stream st a.1 x.1 ∧ Rp π iv publicInput stream st a.2 x.2 ∧
    st.nodes[a.1]? = some (.input off 16) ∧ st.nodes[a.2]? = some (.input (off + 16) 16)

/-- **What reduce leaves, represented**: the roots (at `24` and `3608`), the openings, no pending matrices. -/
def RedR (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (red : ReducedS) (r : Reduced) : Prop :=
  RootR π iv publicInput stream st red.root1 r.roots.1 24 ∧ RootR π iv publicInput stream st red.root2 r.roots.2 3608 ∧
    OpeningsR π iv publicInput stream st red.openings r.openings ∧ r.matrices = none

end RecGraph.Sim
