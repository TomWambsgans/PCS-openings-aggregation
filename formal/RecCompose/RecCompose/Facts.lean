-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.FactsSpecOf
import RecCompose.Valid

/-!
# `Pi2Facts`, from the compiled circuit and one evaluated check

**`pi2Facts hD C hchk : Pi2Facts D C`** at the real deployment, for the compiled circuits `C` (the run-checked
`Pi2Circuits`) and **`Pi2ViewChecked C`**: at every π1 IV the compiled circuit passes `viewCheck` (its view `viewOf`, the
Rust's `adapt` transcribed, is `Data.circuit`; its calls are `Data.pi1Calls`; `validB` accepts it). That check is a
`Bool` of the compiled circuit, **checked by evaluation** (`rec-view-check`, `RecComposeTest/ViewCheck.lean`, at π1's
reference IV and at the zero IV), as `Pi2Circuits` itself is; no kernel evaluation of the circuit.

From it: `SpecOf` (`specOf_data`), validity (`validB_sound`), `2^24` positions and rows of `16` (the view's), three
four-limb ports (`Data`'s terms), the public limbs `pubOfC` (their lengths, `pub_canon`). `pi2Facts_pubOf` states the
public limbs.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Primitives Finset

/-- **The compiled circuits pass the view check** at every π1 IV (`viewCheck`: the view is `Data.circuit`, the calls
`Data.pi1Calls`, the circuit valid). A `Bool` of the compiled circuit: **checked by evaluation** (`rec-view-check`). -/
def Pi2ViewChecked {D : RecDeployment} (C : Pi2Circuits D) : Prop := ∀ iv, viewCheck (C.compiled iv) = true

theorem viewCheck_parts {c : RecCircuit.Compiled} (h : viewCheck c = true) :
    viewOf c.circuit = Data.circuit ∧ callsOf c.circuit = Data.pi1Calls ∧ validB c.circuit = true := by
  unfold viewCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## The public limbs are determined by their fingerprint -/

theorem mem_subK {x : E} (h : x ∈ subK) : ∃ a : K, F192.ofF64 a = x := by
  obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.mp h
  exact ⟨a, rfl⟩

theorem portWeights_length {L : ℕ} (hL : L = 3 ∨ L = 4) : (RecCircuit.portWeights (List.range L)).length = L := by
  rcases hL with rfl | rfl <;> rfl

theorem canon2_append_fp (X Z γ : E) : RecPiop.fpList (RecPiop.rootLimbs 0 1 2 3 F192.Y) γ (canon2 X ++ canon2 Z) =
    X + γ * Z := by
  have hX := canon2_fp X
  have hZ := canon2_fp Z
  simp only [canon2, List.getD_cons_zero, List.getD_cons_succ] at hX hZ
  simp only [canon2, List.cons_append, List.nil_append]
  rw [RecPiop.fpList_root, hX, hZ]

/-- **The public limbs are what the fingerprint determines among limbs in `K`.** -/
theorem pubOfC_canon {r : RecCircuit.Recorded} {c : RecCircuit.Compiled} (hc : RecCircuit.compile r = .ok c)
    {j : ℕ} (hj : j < c.circuit.toPiop.nP) (pubs : List E) (u : List E)
    (hul : u.length = (c.circuit.toPiop.limbs j).length) (huK : ∀ x ∈ u, x ∈ subK)
    (hfp : ∀ γ, RecPiop.fpList (c.circuit.toPiop.limbs j) γ u = c.circuit.toPiop.pubFp γ (pubOfC c.circuit pubs) j) :
    u = pubOfC c.circuit pubs j := by
  unfold RecPiop.Circuit.pubFp pubOfC at hfp
  unfold pubOfC
  rw [limbs_toPiop hc hj] at hfp hul
  cases hs : (c.circuit.ports.getD j default).source with
  | statement =>
    rw [hs] at hfp hul
    obtain ⟨u0, u1, u2, u3, rfl⟩ := RecPiop.list_four (hul.trans rfl)
    obtain ⟨a0, rfl⟩ := mem_subK (huK u0 (by simp))
    obtain ⟨a1, rfl⟩ := mem_subK (huK u1 (by simp))
    obtain ⟨a2, rfl⟩ := mem_subK (huK u2 (by simp))
    obtain ⟨a3, rfl⟩ := mem_subK (huK u3 (by simp))
    have h := fun γ ↦ hfp γ
    simp only [RecCircuit.Source.limbs, pubOfSource] at h
    have e : ∀ γ, RecPiop.fpList (RecCircuit.portWeights (List.range 4)) γ =
        RecPiop.fpList (RecPiop.rootLimbs 0 1 2 3 F192.Y) γ := fun γ ↦ rfl
    simp only [e, RecPiop.fpList_root, canon2_append_fp] at h
    have h0 := h 0
    have h1 := h 1
    simp only [zero_mul, add_zero, one_mul] at h0 h1
    simp only [pubOfSource]
    rw [← h0, show pubs.getD 2 0 + F192.Y * pubs.getD 3 0 = F192.ofF64 a2 + F192.Y * F192.ofF64 a3 by
      linear_combination h0 - h1, canon2_ofF64, canon2_ofF64]
    rfl
  | root i =>
    rw [hs] at hfp hul
    obtain ⟨u0, u1, u2, u3, rfl⟩ := RecPiop.list_four (hul.trans rfl)
    obtain ⟨a0, rfl⟩ := mem_subK (huK u0 (by simp))
    obtain ⟨a1, rfl⟩ := mem_subK (huK u1 (by simp))
    obtain ⟨a2, rfl⟩ := mem_subK (huK u2 (by simp))
    obtain ⟨a3, rfl⟩ := mem_subK (huK u3 (by simp))
    have h := fun γ ↦ hfp γ
    simp only [RecCircuit.Source.limbs, pubOfSource] at h
    have e : ∀ γ, RecPiop.fpList (RecCircuit.portWeights (List.range 4)) γ =
        RecPiop.fpList (RecPiop.rootLimbs 0 1 2 3 F192.Y) γ := fun γ ↦ rfl
    simp only [e, RecPiop.fpList_root, canon2_append_fp] at h
    have h0 := h 0
    have h1 := h 1
    simp only [zero_mul, add_zero, one_mul] at h0 h1
    simp only [pubOfSource]
    rw [← h0, show pubs.getD (4 + 2 * i) 0 = F192.ofF64 a2 + F192.Y * F192.ofF64 a3 by
      linear_combination h0 - h1, canon2_ofF64, canon2_ofF64]
    rfl
  | element i =>
    rw [hs] at hfp hul
    obtain ⟨u0, u1, u2, rfl⟩ := RecPiop.list_three (hul.trans rfl)
    obtain ⟨a0, rfl⟩ := mem_subK (huK u0 (by simp))
    obtain ⟨a1, rfl⟩ := mem_subK (huK u1 (by simp))
    obtain ⟨a2, rfl⟩ := mem_subK (huK u2 (by simp))
    have h := hfp 0
    simp only [RecCircuit.Source.limbs, pubOfSource] at h
    have e : RecPiop.fpList (RecCircuit.portWeights (List.range 3)) 0 =
        RecPiop.fpList (RecPiop.elemLimbs 0 1 2 F192.Y) 0 := rfl
    have hx := limbs3_fp (pubs.getD (4 + 2 * (publicCounts c.circuit).1 + i) 0)
    simp only [limbs3, List.getD_cons_zero, List.getD_cons_succ] at hx
    rw [e, RecPiop.fpList_elem, limbs3, RecPiop.fpList_elem, hx] at h
    have hl : F192.ofLimbs a0 a1 a2 = pubs.getD (4 + 2 * (publicCounts c.circuit).1 + i) 0 := by
      rw [F192.ofLimbs_eq, ← h]
      ring
    simp only [pubOfSource, limbs3, ← hl, F192.limb_ofLimbs_zero, F192.limb_ofLimbs_one, F192.limb_ofLimbs_two]
  | zero =>
    rw [hs] at hfp hul
    obtain ⟨u0, u1, u2, rfl⟩ := RecPiop.list_three (hul.trans rfl)
    obtain ⟨a0, rfl⟩ := mem_subK (huK u0 (by simp))
    obtain ⟨a1, rfl⟩ := mem_subK (huK u1 (by simp))
    obtain ⟨a2, rfl⟩ := mem_subK (huK u2 (by simp))
    have h := hfp 0
    simp only [RecCircuit.Source.limbs, pubOfSource] at h
    have e : RecPiop.fpList (RecCircuit.portWeights (List.range 3)) 0 =
        RecPiop.fpList (RecPiop.elemLimbs 0 1 2 F192.Y) 0 := rfl
    rw [e, RecPiop.fpList_elem, RecPiop.fpList_elem] at h
    have hl : F192.ofLimbs a0 a1 a2 = F192.ofLimbs 0 0 0 := by
      rw [F192.ofLimbs_eq, F192.ofLimbs_eq]
      simp only [F192.ofF64_zero, zero_mul, add_zero]
      linear_combination h
    obtain ⟨rfl, rfl, rfl⟩ := F192.ofLimbs_injective hl
    simp [pubOfSource]
  | pad =>
    rw [hs] at hfp hul
    obtain ⟨u0, u1, u2, rfl⟩ := RecPiop.list_three (hul.trans rfl)
    obtain ⟨a0, rfl⟩ := mem_subK (huK u0 (by simp))
    obtain ⟨a1, rfl⟩ := mem_subK (huK u1 (by simp))
    obtain ⟨a2, rfl⟩ := mem_subK (huK u2 (by simp))
    have h := hfp 0
    simp only [RecCircuit.Source.limbs, pubOfSource] at h
    have e : RecPiop.fpList (RecCircuit.portWeights (List.range 3)) 0 =
        RecPiop.fpList (RecPiop.elemLimbs 0 1 2 F192.Y) 0 := rfl
    rw [e, RecPiop.fpList_elem, RecPiop.fpList_elem] at h
    have hl : F192.ofLimbs a0 a1 a2 = F192.ofLimbs 0 0 0 := by
      rw [F192.ofLimbs_eq, F192.ofLimbs_eq]
      simp only [F192.ofF64_zero, zero_mul, add_zero]
      linear_combination h
    obtain ⟨rfl, rfl, rfl⟩ := F192.ofLimbs_injective hl
    simp [pubOfSource]

/-! ## The facts -/

theorem list_range_sum_nat (f : ℕ → ℕ) : ∀ N, ((List.range N).map f).sum = ∑ i ∈ range N, f i
  | 0 => rfl
  | N + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_range_sum_nat f N, Finset.sum_range_succ]
    simp

section Facts

variable {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)

include hchk in
/-- The view check at a setup. -/
theorem viewChecked_at (roots : RecSetupRoots) :
    viewOf (C.compiled (D.pi1IvAt roots.pi1)).circuit = Data.circuit ∧
      callsOf (C.compiled (D.pi1IvAt roots.pi1)).circuit = Data.pi1Calls ∧
      validB (C.compiled (D.pi1IvAt roots.pi1)).circuit = true :=
  viewCheck_parts (hchk _)

include hchk in
/-- Four limbs at port `j` exactly when `Data`'s term `j` has two or four terms. -/
theorem four_sum (roots : RecSetupRoots) : ∑ j ∈ range (C.G roots).nP, C.d roots j = 3 := by
  obtain ⟨hview, -, -⟩ := viewChecked_at C hchk roots
  have hports := viewOf_ports hview
  have hroots := viewOf_roots hview
  have hterms := viewOf_terms hview
  have hnP : (C.G roots).nP = 36 := by
    show ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.toList.map (·.position)).length = 36
    rw [List.length_map, Array.length_toList, hports]
  rw [hnP, ← data_four, list_range_sum_nat]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j < 36 := Finset.mem_range.mp hj
  rw [← hterms, publicTermsOf_getD _ (by rw [hports]; exact hj'), hroots]
  unfold Pi2Circuits.d
  have key := termOf_length_four 2 ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.getD j default).source
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.mp h1) h2
  · exact absurd (key.mpr h2) h1
  · rfl

include hD hchk in
/-- **`Pi2Facts` at the real deployment**, from the compiled circuits and the view check. -/
def pi2Facts : Pi2Facts D C where
  pairOf roots := pairOfC (C.compiled (D.pi1IvAt roots.pi1)).circuit
  portOf _ J := 16 + J
  nz _ := 16
  pubOf roots := pubOfC (C.compiled (D.pi1IvAt roots.pi1)).circuit
  spec roots := by
    obtain ⟨hview, -, hval⟩ := viewChecked_at C hchk roots
    rw [show (D.circuitAt roots.pi1).circuit = Data.circuit from hD.1 _]
    exact specOf_data (C.compile_ok _) hview (validB_sound hval)
  valid roots := validB_sound (viewChecked_at C hchk roots).2.2
  logN roots := viewOf_logN (viewChecked_at C hchk roots).1
  logW roots := viewOf_logW (viewChecked_at C hchk roots).1
  four roots := four_sum C hchk roots
  pub_len roots scalars j hj := by
    unfold pubOfC
    rw [limbs_toPiop (C.compile_ok _) hj, pubOfSource_length, portWeights_length (source_limbs _)]
  pub_canon roots scalars j hj u hul huK hfp := pubOfC_canon (C.compile_ok _) hj scalars u hul huK hfp

/-- **`pi2Facts`' public limbs**: `pubOfC` of the compiled circuit (by port source: the statement's words and a root's
halves as `canon2` pairs, an element's three limbs, zeros). -/
theorem pi2Facts_pubOf (roots : RecSetupRoots) :
    (pi2Facts hD C hchk).pubOf roots = pubOfC (C.compiled (D.pi1IvAt roots.pi1)).circuit := rfl

end Facts

end RecCompose

/-- info: 'RecCompose.specOf_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.specOf_data

/-- info: 'RecCompose.validB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.validB_sound

/-- info: 'RecCompose.pi2Facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Facts
