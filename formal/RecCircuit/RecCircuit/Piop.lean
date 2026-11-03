-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Ports
import RecPiop.Dataflow

/-!
# π2's PIOP's relation gives the circuit satisfied

`RecPiop` (branch `lean-rec-piop`) states π2's PIOP's relation for any circuit (`RecPiop.Circuit.Satisfies`, over `E`)
and its dataflow lemma (`RecPiop.Circuit.copy_iff_flow`: the copy constraints are the witness being a fixed point of
the circuit's dataflow). `Circuit.toPiop`: this compiler's circuit as `RecPiop`'s (the same positions, roles, blocks,
`σ`, `κ` and ports; a port's limbs weighted as `PI2.md` §4.2: a three-limb port's fingerprint is the element
`L₀ + Y L₁ + Y² L₂`, a four-limb port's `(L₀ + Y L₁) + γ (L₂ + Y L₃)`), a witness of `K` words in `E` (`emb`).
`satisfied_of_piop`, `satisfied_of_flow`: a witness the PIOP's relation holds of, or a fixed point of its dataflow,
satisfies this circuit (`Circuit.Satisfied`), the hypothesis the end theorem consumes.
-/

namespace RecCircuit

open Primitives

/-- A witness of `K` words, in `E`. -/
def emb (w : ℕ → K) : ℕ → F192 := fun i => F192.ofF64 (w i)

def toPoly2 (p : Poly) : RecPiop.Poly2 F192 :=
  ⟨p.linear.map fun t => (t.1, F192.ofF64 t.2), p.quadratic.map fun t => (t.1, t.2.1, F192.ofF64 t.2.2)⟩

/-- A port's limbs with `PI2.md` §4.2's weights (polynomials in `γ`, the constant first). -/
def portWeights (limbs : List ℕ) : List (RecPiop.Limb F192) :=
  match limbs with
  | [a, b, d] => [⟨a, [1]⟩, ⟨b, [F192.Y]⟩, ⟨d, [F192.Y ^ 2]⟩]
  | [a, b, d, e] => [⟨a, [1]⟩, ⟨b, [F192.Y]⟩, ⟨d, [0, 1]⟩, ⟨e, [0, F192.Y]⟩]
  | _ => limbs.map fun c => ⟨c, [1]⟩

def toRole : Formula → RecPiop.Role F192
  | .forward => .forward
  | .expr p => .expr (toPoly2 p)
  | .port ls => .port (portWeights ls)

def toBlock (b : Block) : RecPiop.Block := ⟨b.row, b.logRows, b.region⟩

/-- **This compiler's circuit as `RecPiop`'s.** -/
def Circuit.toPiop (C : Circuit) : RecPiop.Circuit F192 where
  logN := C.logN
  logW := C.logWidth
  regions := C.regions.toList.map fun r => r.roles.toList.map toRole
  blocks := C.blocks.toList.map toBlock
  sigma := C.sigmaAt
  kappa := fun i => F192.ofF64 (C.kappaAt i)
  ports := C.ports.toList.map (·.position)

theorem list_getD_map {α β : Type} (f : α → β) (l : List α) (n : ℕ) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

theorem arr_toList_getD {α : Type} (a : Array α) (n : ℕ) (d : α) : a.toList.getD n d = a.getD n d := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem toPiop_role (C : Circuit) (i : ℕ) : C.toPiop.role i = toRole (C.formulaAt i) := by
  unfold RecPiop.Circuit.role Circuit.formulaAt Circuit.regionOf RecPiop.Circuit.blockAt
  have hW : C.toPiop.W = C.width := rfl
  rw [hW]
  simp only [Circuit.toPiop, List.find?_map]
  have hp : ((fun b => decide (RecPiop.Circuit.Covers b (i / C.width))) ∘ toBlock) =
      fun b => decide (b.row ≤ i / C.width ∧ i / C.width < b.row + 2 ^ b.logRows) := by
    funext b
    simp only [Function.comp, RecPiop.Circuit.Covers, toBlock]
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact decide_eq_true_iff
  rw [hp, ← Array.find?_toList]
  cases C.blocks.toList.find? (fun b => decide (b.row ≤ i / C.width ∧ i / C.width < b.row + 2 ^ b.logRows)) with
  | none => rfl
  | some b =>
    simp only [Option.map_some, RecPiop.Circuit.regionRole, toBlock]
    have h1 : (C.regions.toList.map fun r => r.roles.toList.map toRole).getD b.region [] =
        ((C.regions.getD b.region default).roles.toList.map toRole) := by
      rw [show ([] : List (RecPiop.Role F192)) = (fun r : Region => r.roles.toList.map toRole) default from rfl,
        list_getD_map, arr_toList_getD]
    rw [h1, show (RecPiop.Role.forward : RecPiop.Role F192) = toRole .forward from rfl, list_getD_map,
      arr_toList_getD]

theorem toRole_isPort (f : Formula) : (toRole f).isPort = f.isPort := by cases f <;> rfl

theorem toPiop_push (C : Circuit) (w : ℕ → K) (i : ℕ) (h : (C.formulaAt i).isPort = false) :
    C.toPiop.push (emb w) 0 i = F192.ofF64 (C.push w i) := by
  unfold RecPiop.Circuit.push Circuit.push
  rw [toPiop_role]
  have hb : C.toPiop.base i = C.width * (i / C.width) := by
    show i / C.width * C.width = _; ring
  cases hf : C.formulaAt i with
  | forward =>
    simp only [toRole, RecPiop.Role.value, Formula.eval, emb, Circuit.toPiop, F192.ofF64_add]
  | expr p =>
    simp only [toRole, RecPiop.Role.value, Formula.eval]
    rw [hb, show C.toPiop.kappa i = F192.ofF64 (C.kappaAt i) from rfl, F192.ofF64_add]
    congr 1
    rw [RecPiop.Poly2.eval, Poly.eval_eq]
    simp only [F192.ofF64_eq_algebraMap, map_add, map_list_sum, List.map_map, toPoly2, Algebra.algebraMap_self,
      RingHom.id_apply, Function.comp_def, map_mul, emb, Circuit.cells, mul_assoc]
  | port ls => rw [hf] at h; cases h

/-- **The PIOP's copy constraints give the circuit satisfied.** -/
theorem satisfied_of_copy (C : Circuit) (w : ℕ → K)
    (h : ∀ i < C.toPiop.N, ¬ C.toPiop.IsHole i → emb w (C.toPiop.sigma i) = C.toPiop.push (emb w) 0 i) :
    C.Satisfied w := by
  intro i hi hp _
  have hh : ¬ C.toPiop.IsHole i := by
    unfold RecPiop.Circuit.IsHole; rw [toPiop_role, toRole_isPort, hp]; exact Bool.false_ne_true
  have := h i hi hh
  rw [toPiop_push C w i hp] at this
  exact F192.ofF64_injective this

/-- **A witness π2's PIOP's relation holds of satisfies the circuit.** -/
theorem satisfied_of_piop (C : Circuit) {pub : ℕ → List F192} {w : ℕ → K} (h : C.toPiop.Satisfies pub (emb w)) :
    C.Satisfied w := satisfied_of_copy C w h.copy

/-- **A fixed point of the circuit's dataflow** (`RecPiop.Circuit.copy_iff_flow`) satisfies the circuit. -/
theorem satisfied_of_flow (C : Circuit) (hV : C.toPiop.Valid) {w : ℕ → K} (h : C.toPiop.flow (emb w) = emb w) :
    C.Satisfied w := satisfied_of_copy C w ((RecPiop.Circuit.copy_iff_flow hV (emb w)).mpr h)

end RecCircuit
