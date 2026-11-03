-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.FactsSpec

/-!
# `SpecOf (Spec.of Data.circuit).core` of a compiled circuit whose view is `Data.circuit`

**`specOf_data`**: the compiler accepted (`compile r = .ok c`), the view is `Data.circuit`, the circuit valid; then the
verifier's constants are the compiled circuit's, its pairs `pairOfC` (the slots), its ports after the zero coset's `16`
in order (`16 + J`), its public limbs `pubOfC`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Primitives Finset

/-! ## `Spec.of Data.circuit`'s fields -/

theorem spec_publicTerms : (Spec.of Data.circuit).publicTerms = Data.publicTerms.drop 16 := by
  unfold Spec.of
  rw [show Data.circuit.publicTerms = Data.publicTerms from rfl, data_zeroCoset]

theorem spec_zeroCoset : (Spec.of Data.circuit).zeroCoset = some (16777216, 4, subspaceCoefficients 4) := by
  unfold Spec.of
  rw [show Data.circuit.publicTerms = Data.publicTerms from rfl, data_zeroCoset]

theorem spec_maxGamma : (Spec.of Data.circuit).maxGamma = 1 := by
  unfold Spec.of
  rw [show Data.circuit.publicTerms = Data.publicTerms from rfl, data_zeroCoset]
  exact data_maxGamma

theorem spec_pairs : (Spec.of Data.circuit).pairs = Data.pairs.map fun p ↦
    (⟨p.logRows, (pairConstants p 4 (cosetConstants 4 20)).1 * ((pairConstants p 4 (cosetConstants 4 20)).2)⁻¹⟩ :
      SpecPair) := by
  unfold Spec.of
  rw [show Data.circuit.publicTerms = Data.publicTerms from rfl, data_zeroCoset]
  dsimp only
  exact List.map_congr_left fun p _ ↦ rfl

theorem spec_groups : (Spec.of Data.circuit).groups = groupsOf Data.circuit := by
  unfold Spec.of
  rw [show Data.circuit.publicTerms = Data.publicTerms from rfl, data_zeroCoset]

theorem spec_c : (Spec.of Data.circuit).c = normalisedConstants (cosetConstants 4 20) := by
  unfold Spec.of
  rw [show Data.circuit.publicTerms = Data.publicTerms from rfl, data_zeroCoset]
  dsimp only
  rw [show Data.circuit.logRow = 4 from rfl, show Data.circuit.logN = 24 from rfl]

theorem core_groups : (Spec.of Data.circuit).core.groups =
    (groupsOf Data.circuit).map fun g ↦ (⟨g.role, g.formula.toF, g.pulls, g.pairs⟩ : GroupF E) := by
  simp only [Spec.core, spec_groups]

theorem core_maxGamma : (Spec.of Data.circuit).core.maxGamma = 1 := by
  simp only [Spec.core, spec_maxGamma]

theorem core_c_data : (Spec.of Data.circuit).core.c =
    normalisedConstantsF (cosetConstantsF (blockBasis (Heap.omega UniComplete.Domain.basisE) 4) 20) := by
  simp only [Spec.core, spec_c]
  exact core_c 4 20

theorem core_zeroCoset : (Spec.of Data.circuit).core.zeroCoset =
    some (16777216, 4, (subspaceCoefficients 4).map kE) := by
  simp only [Spec.core, spec_zeroCoset, Option.map_some]

theorem core_walk : (Spec.of Data.circuit).core.walk = tagWalk ((Data.publicTerms.drop 16).map (·.tag)) := by
  simp only [Spec.core, spec_publicTerms]

theorem core_pairs : (Spec.of Data.circuit).core.pairs = Data.pairs.map fun p ↦
    (p.logRows, kE ((pairConstants p 4 (cosetConstants 4 20)).1 * ((pairConstants p 4 (cosetConstants 4 20)).2)⁻¹)) := by
  simp only [Spec.core, spec_pairs, List.map_map]
  rfl

theorem core_publicTerms : (Spec.of Data.circuit).core.publicTerms =
    (Data.publicTerms.drop 16).map fun t ↦ (t.tag, t.value.toF) := by
  simp only [Spec.core, spec_publicTerms]

theorem core_terms_getD {J : ℕ} (hJ : J < 20) : (Spec.of Data.circuit).core.publicTerms.getD J noTerm =
    ((Data.publicTerms.getD (16 + J) default).tag, (Data.publicTerms.getD (16 + J) default).value.toF) := by
  have hl : (Data.publicTerms.drop 16).length = 20 := by rw [List.length_drop, data_terms_length]
  rw [core_publicTerms, List.getD_eq_getElem _ _ (by rw [List.length_map, hl]; exact hJ), List.getElem_map,
    List.getElem_drop, List.getD_eq_getElem _ _ (by rw [data_terms_length]; omega)]

/-! ## The assembly -/

/-- **The verifier's constants are the compiled circuit's.** -/
theorem specOf_data {r : RecCircuit.Recorded} {c : RecCircuit.Compiled} (hc : RecCircuit.compile r = .ok c)
    (hview : viewOf c.circuit = Data.circuit) (hV : c.circuit.toPiop.Valid) :
    SpecOf (Spec.of Data.circuit).core c.circuit.toPiop UniComplete.Domain.basisE (pairOfC c.circuit) (fun J ↦ 16 + J)
      16 (pubOfC c.circuit) := by
  have hlogN := viewOf_logN hview
  have hlogW := viewOf_logW hview
  have hports := viewOf_ports hview
  have hroots := viewOf_roots hview
  have hpairs := viewOf_pairs hview
  have hformulas := viewOf_formulas hview
  have hterms := viewOf_terms hview
  have hslen : (Spec.of Data.circuit).core.pairs.length = (slots c.circuit).length := by
    rw [core_pairs, List.length_map, ← hpairs, pairsOf_length]
  have htl : (Spec.of Data.circuit).core.publicTerms.length = 20 := by
    rw [core_publicTerms, List.length_map, List.length_drop, data_terms_length]
  have hnP : c.circuit.toPiop.nP = 36 := by
    show (c.circuit.ports.toList.map (·.position)).length = 36
    rw [List.length_map, Array.length_toList, hports]
  have hN : c.circuit.toPiop.N = 2 ^ 24 := by
    show 2 ^ c.circuit.logN = _
    rw [hlogN]
  have hW : c.circuit.toPiop.W = 16 := by
    show 2 ^ c.circuit.logWidth = _
    rw [hlogW]
    rfl
  have hpd : ∀ i < (slots c.circuit).length, Data.pairs.getD i default = (pairsOf c.circuit).getD i default :=
    fun i _ ↦ by rw [hpairs]
  -- the source of a port, from `Data`'s public terms
  have hsrc : ∀ j < 36, Data.publicTerms.getD j default =
      ⟨2 ^ 24 + j, ⟨termOf 2 (c.circuit.ports.getD j default).source, none⟩⟩ := by
    intro j hj
    rw [← hterms, publicTermsOf_getD _ (by rw [hports]; exact hj), hlogN, hroots]
  have hgam := powersList_two
  exact {
    logN := hlogN.symm
    logRow := hlogW.symm
    hn := by show c.circuit.logN ≤ 32; rw [hlogN]; norm_num
    omega := funext fun i ↦ (UniComplete.Domain.omega_basisE i).symm
    c := by
      rw [core_c_data, show c.circuit.toPiop.logW = c.circuit.logWidth from rfl,
        show c.circuit.toPiop.logN = c.circuit.logN from rfl, hlogN, hlogW]
      exact normConsts_of_spec _ 20
    pair_mem := fun i hi ↦ pairOfC_mem hV (hslen ▸ hi)
    pair_inj := fun i hi j hj h ↦ pairOfC_inj hV (hslen ▸ hi) (hslen ▸ hj) h
    pair_surj := fun p hp ↦ by
      obtain ⟨i, hi, he⟩ := pairOfC_surj hV hp
      exact ⟨i, hslen ▸ hi, he⟩
    pair_s := fun i hi ↦ by
      have hi' := hslen ▸ hi
      rw [core_pairs, List.getD_eq_getElem _ _ (by rw [List.length_map]; rw [← hpairs, pairsOf_length]; exact hi'),
        List.getElem_map, ← List.getD_eq_getElem _ default, hpd i hi', pairsOf_getD _ hi']
      rfl
    pair_z := fun i hi ↦ by
      have hi' := hslen ▸ hi
      rw [core_pairs, List.getD_eq_getElem _ _ (by rw [List.length_map]; rw [← hpairs, pairsOf_length]; exact hi'),
        List.getElem_map, ← List.getD_eq_getElem _ default, hpd i hi']
      rw [core_c_data, pair_z_eq _ (by
        rw [pairsOf_getD _ hi']
        have := pairOfC_logRows_le hV hi'
        rw [hlogN, hlogW] at this
        exact this)]
      rw [pairsOf_getD _ hi']
      show zHat _ _ (Heap.omega _ (_ * 2 ^ 4 + _)) = zHat _ _ (Heap.omega _ (_ * c.circuit.toPiop.W + _))
      rw [hW]
      rfl
    groups_perm := by
      rw [core_groups, List.flatMap_map, core_pairs, List.length_map]
      exact groupsOf_perm Data.circuit
    group_role := fun g hg i hi ↦ by
      rw [core_groups] at hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hil, hrole, -, -⟩ := groupsOf_mem Data.circuit hg0 hi
      have hi' : i < (slots c.circuit).length := by rw [← pairsOf_length, hpairs]; exact hil
      show (pairOfC c.circuit i).2 = g0.role
      rw [hrole, show Data.circuit.pairs = Data.pairs from rfl, hpd i hi', pairsOf_getD _ hi']
      rfl
    group_pulls := fun g hg i hi ↦ by
      rw [core_groups] at hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hil, -, hpulls, -⟩ := groupsOf_mem Data.circuit hg0 hi
      have hi' : i < (slots c.circuit).length := by rw [← pairsOf_length, hpairs]; exact hil
      show g0.pulls = _
      rw [hpulls, show Data.circuit.pairs = Data.pairs from rfl, hpd i hi', pairsOf_getD _ hi']
      obtain ⟨-, -, hf⟩ := mem_slots.mp (slot_mem hV hi')
      show _ = !(c.circuit.toPiop.regionRole (RecCircuit.toBlock ((slots c.circuit).getD i default).1)
        ((slots c.circuit).getD i default).2.1).isPort
      rw [toPiop_regionRole]
      exact roleFormula_pulls hf
    group_formula := fun g hg i hi γ v ↦ by
      rw [core_groups] at hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hil, hrole, -, hform⟩ := groupsOf_mem Data.circuit hg0 hi
      have hi' : i < (slots c.circuit).length := by rw [← pairsOf_length, hpairs]; exact hil
      show g0.formula.toF.eval (powersList γ ((Spec.of Data.circuit).core.maxGamma + 1)) (fun c ↦ v (c ^^^ g0.role)) = _
      rw [core_maxGamma, hform, show Data.circuit.formulas = Data.formulas from rfl,
        show Data.circuit.pairs = Data.pairs from rfl, hpd i hi', ← hformulas, formulasOf_getD_pair _ hi', hrole,
        show Data.circuit.pairs = Data.pairs from rfl, hpd i hi', pairsOf_getD _ hi']
      obtain ⟨-, -, hf⟩ := mem_slots.mp (slot_mem hV hi')
      show _ = (c.circuit.toPiop.regionRole (RecCircuit.toBlock ((slots c.circuit).getD i default).1)
        ((slots c.circuit).getD i default).2.1).value γ (v 0) fun x ↦ v (((slots c.circuit).getD i default).2.1 ^^^ x)
      rw [toPiop_regionRole, roleFormula_eval hf _ γ (hgam γ).1 (hgam γ).2 (v 0)]
      congr 1
      funext x
      rw [Nat.xor_comm]
    walk_perm := by
      rw [htl, core_walk]
      exact data_walk
    coset := by
      refine Or.inr ⟨4, ?_, rfl, by rw [show c.circuit.toPiop.logN = c.circuit.logN from rfl, hlogN]; norm_num⟩
      have hm : (subspaceCoefficients 4).map kE = (subspaceCoeffsF 4 : List E) :=
        map_subspaceCoeffsF (algebraMap K E) 4
      rw [core_zeroCoset, hN, hm, show (2 : ℕ) ^ 24 = 16777216 from rfl]
    nz_le := by rw [hnP]; norm_num
    zero_ports := fun j hj pubs γ ↦ by
      have h := hsrc j (by omega)
      have ht := data_zero_terms j hj
      rw [h] at ht
      unfold RecPiop.Circuit.pubFp pubOfC
      rw [hroots]
      rcases termOf_eq_nil ht with hz | hz <;> rw [hz] <;> exact fpList_zero _ γ
    port_mem := fun J hJ ↦ by rw [htl] at hJ; rw [hnP]; omega
    port_inj := fun J _ J' _ h ↦ by omega
    port_surj := fun j hj hj' ↦ ⟨j - 16, by rw [htl]; rw [hnP] at hj'; omega, by omega⟩
    term_tag := fun J hJ ↦ by
      rw [htl] at hJ
      rw [core_terms_getD hJ, hsrc _ (by omega), hN]
    tags_lt := by rw [hN, hnP]; norm_num
    term_value := fun J hJ pubs γ ↦ by
      rw [htl] at hJ
      rw [core_terms_getD hJ, hsrc _ (by omega), core_maxGamma]
      have hJ' : 16 + J < c.circuit.toPiop.nP := by rw [hnP]; omega
      unfold RecPiop.Circuit.pubFp pubOfC
      rw [limbs_toPiop hc hJ', hroots]
      exact term_value_source 2 _ pubs γ }

end RecCompose
