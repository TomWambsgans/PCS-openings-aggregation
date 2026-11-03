-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.FactsAlg
import RecStatement.Lemmas.SpecLink

/-!
# `SpecOf`: the verifier's constants are the compiled circuit's

For a compiled circuit whose view (`viewOf`, `adapt` transcribed) is `Data.circuit` and which is valid,
**`specOf_data`**: `SpecOf (Spec.of Data.circuit).core c.circuit.toPiop basisE (pairOfC …) (16 + ·) 16 (pubOfC …)`.

* `Data`'s own facts, by kernel decision on its small terms (`data_*`): `maxGamma = 1`, its `36` public terms the
  zero coset's `16` (tags `N .. N + 15`, `w_4`) then `20` others, the walk a permutation of them, three four-limb ports
  (`List.mergeSort` taken off first, the lists being sorted: `List.mergeSort_of_pairwise`);
* the recursion's constants (`core_c`: `Spec.of`'s in `K`, embedded, are `normalisedConstantsF` of the blocks' basis,
  `RecStatement.normConsts_of_spec`), the pairs' `Ẑ_s(c_p)` (`pairZ_eq_zHat`; the coset constants nonzero by the
  Cantor basis's independence, `zConst_ne_zero`);
* the pairs are the slots (`pairOfC`), the groups `Spec.of`'s (`View.lean`), their formulas the roles' values
  (`FactsAlg.lean`), the public terms the ports' fingerprints of `pubOfC`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Primitives Finset

/-! ## `Data`'s facts -/

theorem data_maxGamma : Data.circuit.maxGamma = 1 := by decide +kernel

theorem data_terms_length : Data.publicTerms.length = 36 := by decide +kernel

theorem data_zero_terms : ∀ j < 16, (Data.publicTerms.getD j default).value.terms = [] := by decide +kernel

theorem data_four : ((List.range 36).map fun j ↦ if (Data.publicTerms.getD j default).value.terms.length = 2 ∨
    (Data.publicTerms.getD j default).value.terms.length = 4 then 1 else 0).sum = 3 := by decide +kernel

theorem data_reads_roots : Data.reads.count .root = 2 := by decide +kernel

theorem data_walk : (tagWalk ((Data.publicTerms.drop 16).map (·.tag))).Perm (List.range 20) := by
  unfold tagWalk
  rw [List.mergeSort_of_pairwise (by decide +kernel)]
  decide +kernel

theorem data_zeroCoset : zeroCosetOf Data.publicTerms =
    (some (16777216, 4, subspaceCoefficients 4), Data.publicTerms.drop 16) := by
  unfold zeroCosetOf
  dsimp only
  rw [List.mergeSort_of_pairwise (by decide +kernel)]
  split_ifs with h
  · congr 1
  · exact absurd (by decide +kernel) h

/-! ## The view's shape from `Data` -/

section View

variable {C : RecCircuit.Circuit} (hview : viewOf C = Data.circuit)
include hview

theorem viewOf_logN : C.logN = 24 := congrArg Circuit.logN hview

theorem viewOf_logW : C.logWidth = 4 := congrArg Circuit.logRow hview

theorem viewOf_terms : publicTermsOf C = Data.publicTerms := congrArg Circuit.publicTerms hview

theorem viewOf_pairs : pairsOf C = Data.pairs := congrArg Circuit.pairs hview

theorem viewOf_formulas : formulasOf C = Data.formulas := congrArg Circuit.formulas hview

theorem viewOf_reads : List.replicate (publicCounts C).1 Read.root ++ List.replicate (publicCounts C).2 Read.scalar =
    Data.reads := congrArg Circuit.reads hview

theorem viewOf_roots : (publicCounts C).1 = 2 := by
  have h := congrArg (List.count Read.root) (viewOf_reads hview)
  rw [data_reads_roots, List.count_append, List.count_replicate_self, List.count_replicate] at h
  simpa using h

theorem viewOf_ports : C.ports.size = 36 := by
  have h := congrArg List.length (viewOf_terms hview)
  rw [data_terms_length] at h
  simpa [publicTermsOf] using h

end View

theorem publicTermsOf_getD (C : RecCircuit.Circuit) {j : ℕ} (hj : j < C.ports.size) :
    (publicTermsOf C).getD j default =
      ⟨2 ^ C.logN + j, ⟨termOf (publicCounts C).1 (C.ports.getD j default).source, none⟩⟩ := by
  simp [publicTermsOf, List.getD_eq_getElem?_getD, hj]

theorem termOf_eq_nil {roots : ℕ} {s : RecCircuit.Source} (h : termOf roots s = []) : s = .zero ∨ s = .pad := by
  cases s <;> simp_all [termOf]

theorem termOf_length_four (roots : ℕ) (s : RecCircuit.Source) :
    s.limbs = 4 ↔ (termOf roots s).length = 2 ∨ (termOf roots s).length = 4 := by
  cases s <;> simp [termOf, RecCircuit.Source.limbs]

/-! ## The recursion's constants -/

theorem beta_getD_ge {k : ℕ} (hk : 32 ≤ k) : UniStatement.beta.getD k 0 = 0 := by
  rw [UniComplete.Domain.beta_getD, List.getD_eq_default _ _ (by
    have : UniComplete.Domain.betaWords.length = 32 := by decide +kernel
    omega)]
  rfl

/-- `Spec.of`'s basis `β_{r+s}`, embedded, is the blocks' basis on the Cantor points. -/
theorem blockBasis_eq (r : ℕ) :
    (fun s ↦ ofK (UniStatement.beta.getD (r + s) 0)) = blockBasis (Heap.omega UniComplete.Domain.basisE) r := by
  funext s
  unfold blockBasis
  rw [omega_two_pow]
  split_ifs with h
  · rfl
  · rw [beta_getD_ge (by omega)]
    exact map_zero (algebraMap K E)

theorem map_cosetConstants (r count : ℕ) :
    (cosetConstants r count).map kE = cosetConstantsF (blockBasis (Heap.omega UniComplete.Domain.basisE) r) count := by
  rw [← blockBasis_eq]
  exact map_cosetConstantsF (algebraMap K E) _ count

/-- **The recursion's constants over `E`**: `normalisedConstantsF` of the blocks' basis. -/
theorem core_c (r count : ℕ) :
    (normalisedConstants (cosetConstants r count)).map kE =
      normalisedConstantsF (cosetConstantsF (blockBasis (Heap.omega UniComplete.Domain.basisE) r) count) := by
  rw [← map_cosetConstants]
  exact map_normalisedConstantsF (algebraMap K E) _

/-- **The coset constants are nonzero**: `Z_{U_j}(β_{r+j}) = Π_u (ω(2^(r+j)) + ω(u 2^r))`, the points distinct. -/
theorem zConst_ne_zero {r j : ℕ} (hrj : r + j < 32) :
    zConst (blockBasis (Heap.omega UniComplete.Domain.basisE) r) j ≠ 0 := by
  have hP := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  unfold zConst
  rw [← zrec_eval, zrec_eq_prod hP.xor, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun u hu ↦ ?_
  rw [Finset.mem_range] at hu
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, blockBasis]
  have h1 : u * 2 ^ r < 2 ^ (r + j) := by
    rw [pow_add, mul_comm (2 ^ r)]
    exact Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos r)
  have h32 : 2 ^ (r + j) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) hrj
  exact hP.add_ne_zero h32 (h1.trans h32) (by omega)

/-! ## The pairs -/

/-- **Pair `i` of the compiled circuit**: slot `i`'s block and role. -/
def pairOfC (C : RecCircuit.Circuit) (i : ℕ) : RecPiop.Block × ℕ :=
  (RecCircuit.toBlock ((slots C).getD i default).1, ((slots C).getD i default).2.1)

theorem toPiop_regionRole (C : RecCircuit.Circuit) (b : RecCircuit.Block) (k : ℕ) :
    C.toPiop.regionRole (RecCircuit.toBlock b) k = RecCircuit.toRole ((blockRoles C b).getD k .forward) := by
  unfold RecPiop.Circuit.regionRole blockRoles
  simp only [RecCircuit.Circuit.toPiop, RecCircuit.toBlock]
  have h1 : (C.regions.toList.map fun r => r.roles.toList.map RecCircuit.toRole).getD b.region [] =
      ((C.regions.getD b.region default).roles.toList.map RecCircuit.toRole) := by
    rw [show ([] : List (RecPiop.Role F192)) = (fun r : RecCircuit.Region => r.roles.toList.map RecCircuit.toRole)
      default from rfl, RecCircuit.list_getD_map, RecCircuit.arr_toList_getD]
  rw [h1, show (RecPiop.Role.forward : RecPiop.Role F192) = RecCircuit.toRole .forward from rfl,
    RecCircuit.list_getD_map]

theorem roleFormula_isForward {f : RecCircuit.Formula} {fp : Formula × Bool} (h : roleFormula f = some fp) :
    (RecCircuit.toRole f).isForward = false := by
  cases f <;> simp_all [roleFormula, RecCircuit.toRole, RecPiop.Role.isForward]

theorem roleFormula_of_isForward {f : RecCircuit.Formula} (h : (RecCircuit.toRole f).isForward = false) :
    ∃ fp, roleFormula f = some fp := by
  cases f <;> simp_all [roleFormula, RecCircuit.toRole, RecPiop.Role.isForward]

theorem toBlock_injective : Function.Injective RecCircuit.toBlock := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [RecCircuit.toBlock, RecPiop.Block.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

section Valid

variable {C : RecCircuit.Circuit} (hV : C.toPiop.Valid)
include hV

theorem blocks_nodup : C.blocks.toList.Nodup := by
  have h : (C.blocks.toList.map RecCircuit.toBlock).Nodup := hV.disjoint.imp fun {b b'} hd heq ↦ by
    subst heq
    have := Nat.two_pow_pos b.logRows
    omega
  exact h.of_map _

theorem blockRoles_length {b : RecCircuit.Block} (hb : b ∈ C.blocks.toList) :
    (blockRoles C b).length = C.toPiop.W := by
  have hr := hV.region_lt _ (List.mem_map_of_mem (f := RecCircuit.toBlock) hb)
  simp only [RecCircuit.Circuit.toPiop, RecCircuit.toBlock, List.length_map, Array.length_toList] at hr
  have hw := hV.width _ (List.getElem_mem (l := C.toPiop.regions) (n := b.region) (by
    simp only [RecCircuit.Circuit.toPiop, List.length_map, Array.length_toList]; exact hr))
  simp only [RecCircuit.Circuit.toPiop, List.getElem_map, Array.getElem_toList, List.length_map,
    Array.length_toList] at hw
  unfold blockRoles
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hr, Option.getD_some, Array.length_toList]
  exact hw

theorem slot_mem {i : ℕ} (hi : i < (slots C).length) : ((slots C).getD i default) ∈ slots C :=
  getD_mem_of_lt default hi

theorem pairOfC_mem {i : ℕ} (hi : i < (slots C).length) : pairOfC C i ∈ C.toPiop.pairs := by
  obtain ⟨hb, hk, hf⟩ := mem_slots.mp (slot_mem hV hi)
  refine RecPiop.Circuit.mem_pairs.mpr ⟨?_, ?_, ?_⟩
  · exact List.mem_map_of_mem hb
  · rw [← blockRoles_length hV hb]; exact hk
  · show (C.toPiop.regionRole (RecCircuit.toBlock ((slots C).getD i default).1)
      ((slots C).getD i default).2.1).isForward = false
    rw [toPiop_regionRole]
    exact roleFormula_isForward hf

theorem pairOfC_inj {i j : ℕ} (hi : i < (slots C).length) (hj : j < (slots C).length)
    (h : pairOfC C i = pairOfC C j) : i = j := by
  have hn := slotKeys_nodup (blocks_nodup hV)
  have hi' : i < (slotKeys C).length := by rw [slotKeys_length]; exact hi
  have hj' : j < (slotKeys C).length := by rw [slotKeys_length]; exact hj
  refine (hn.getElem_inj_iff (hi := hi') (hj := hj')).mp ?_
  simp only [pairOfC, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, Prod.mk.injEq] at h
  simp only [slotKeys, List.getElem_map, Prod.mk.injEq]
  exact ⟨toBlock_injective h.1, h.2⟩

theorem pairOfC_surj {p : RecPiop.Block × ℕ} (hp : p ∈ C.toPiop.pairs) :
    ∃ i < (slots C).length, pairOfC C i = p := by
  obtain ⟨hb, hk, hf⟩ := RecPiop.Circuit.mem_pairs.mp hp
  obtain ⟨b, hb', hbe⟩ := List.mem_map.mp (show p.1 ∈ C.blocks.toList.map RecCircuit.toBlock from hb)
  rw [← hbe, toPiop_regionRole] at hf
  obtain ⟨fp, hfp⟩ := roleFormula_of_isForward hf
  have hmem : (b, p.2, fp) ∈ slots C :=
    mem_slots.mpr ⟨hb', by rw [blockRoles_length hV hb']; exact hk, hfp⟩
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨i, hi, ?_⟩
  rw [pairOfC, List.getD_eq_getElem _ _ hi, hie, hbe]

theorem pairOfC_logRows_le {i : ℕ} (hi : i < (slots C).length) :
    (pairOfC C i).1.logRows ≤ C.logN - C.logWidth := by
  obtain ⟨hb, -, -⟩ := mem_slots.mp (slot_mem hV hi)
  have h := hV.in_range _ (List.mem_map_of_mem (f := RecCircuit.toBlock) hb)
  have h2 : 2 ^ (pairOfC C i).1.logRows ≤ 2 ^ (C.logN - C.logWidth) := by
    have : C.toPiop.rows = 2 ^ (C.logN - C.logWidth) := rfl
    simp only [pairOfC]
    simp only [RecCircuit.toBlock] at h ⊢
    omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

end Valid

/-! ## The pairs' constants -/

theorem map_foldl_mul_take {F F' : Type} [Field F] [Field F'] (φ : F →+* F') (e : List F) {s : ℕ}
    (hs : s ≤ e.length) : φ ((e.take s).foldl (· * ·) 1) = ((e.map φ).take s).foldl (· * ·) 1 := by
  rw [foldl_mul_take e s hs, foldl_mul_take (e.map φ) s (by rw [List.length_map]; exact hs), map_prod]
  exact Finset.prod_congr rfl fun j _ ↦ (map_getD φ e j).symm

/-- **A pair's `Ẑ_s(c_p)`**, `Spec.of`'s in `K` embedded, is the normalised recursion's at the pair's point. -/
theorem pair_z_eq (p : Pair) (hs : p.logRows ≤ 20) :
    kE ((pairConstants p 4 (cosetConstants 4 20)).1 * ((pairConstants p 4 (cosetConstants 4 20)).2)⁻¹) =
      zHat (normalisedConstantsF (cosetConstantsF (blockBasis (Heap.omega UniComplete.Domain.basisE) 4) 20))
        p.logRows (Heap.omega UniComplete.Domain.basisE (p.firstRow * 2 ^ 4 + p.role)) := by
  have hlen : (cosetConstants 4 20).length = 20 := cosetConstantsF_length _ 20
  show algebraMap K E (vanishingF (UniStatement.point (p.firstRow * 2 ^ 4 + p.role)) (cosetConstants 4 20)
      p.logRows * (((cosetConstants 4 20).take p.logRows).foldl (· * ·) 1)⁻¹) = _
  rw [map_mul, map_inv₀, map_vanishingF, map_foldl_mul_take _ _ (by rw [hlen]; exact hs)]
  have hm : (cosetConstants 4 20).map (algebraMap K E) =
      cosetConstantsF (blockBasis (Heap.omega UniComplete.Domain.basisE) 4) 20 := map_cosetConstants 4 20
  rw [hm, pairZ_eq_zHat _ hs (fun j hj ↦ zConst_ne_zero (by omega)), UniComplete.Domain.omega_basisE]
  rfl

theorem map_subspaceStep {F F' : Type} [Field F] [Field F'] (φ : F →+* F') (a : List F) :
    (subspaceStep a).map φ = subspaceStep (a.map φ) := by
  unfold subspaceStep
  rw [List.map_map, List.length_map]
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp, map_add, map_getD]
  split_ifs <;> simp

theorem map_subspaceCoeffsF {F F' : Type} [Field F] [Field F'] (φ : F →+* F') (k : ℕ) :
    (subspaceCoeffsF k : List F).map φ = subspaceCoeffsF k := by
  unfold subspaceCoeffsF
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [map_subspaceStep, ih]

/-! ## The formulas as the roles' values -/

theorem roleFormula_pulls {f : RecCircuit.Formula} {fm : Formula} {pl : Bool} (h : roleFormula f = some (fm, pl)) :
    pl = !(RecCircuit.toRole f).isPort := by
  cases f with
  | forward => simp [roleFormula] at h
  | expr p =>
    simp only [roleFormula, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl
  | port ls =>
    simp only [roleFormula, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl

/-- **A slot's formula is its role's value**, at the powers `1, γ`. -/
theorem roleFormula_eval {f : RecCircuit.Formula} {fm : Formula} {pl : Bool} (h : roleFormula f = some (fm, pl))
    (gs : List E) (γ : E) (hg0 : gs.getD 0 0 = 1) (hg1 : gs.getD 1 0 = γ) (own : E) (cell : ℕ → E) :
    fm.toF.eval gs cell = (RecCircuit.toRole f).value γ own cell := by
  cases f with
  | forward => simp [roleFormula] at h
  | expr p =>
    simp only [roleFormula, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, exprFormula_eval p gs hg0]
    rfl
  | port ls =>
    simp only [roleFormula, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, portFormula_eval ls gs γ hg0 hg1]
    rfl

theorem powersList_two (γ : E) : (powersList γ 2).getD 0 0 = 1 ∧ (powersList γ 2).getD 1 0 = γ := by
  simp [powersList, List.range_succ]

/-! ## The public side -/

/-- A linear form's value over `E`: its terms'. -/
theorem linF_eval (ts : List (Coeff × ℕ)) (gs : List E) (cell : ℕ → E) :
    (⟨ts, none⟩ : Lin).toF.eval gs cell = (ts.map fun t ↦ t.1.toF.eval gs * cell t.2).sum := by
  show (ts.map fun t ↦ (t.1.toF, t.2)).foldl (fun acc t ↦ acc + t.1.eval gs * cell t.2) 0 = _
  rw [foldl_add_sum, zero_add, List.map_map]
  rfl

theorem fpList_zero (ls : List (RecPiop.Limb E)) (γ : E) : RecPiop.fpList ls γ [0, 0, 0] = 0 := by
  unfold RecPiop.fpList
  refine List.sum_eq_zero fun x hx ↦ ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have := (List.of_mem_zip hp).2
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at this
  rw [this, mul_zero]

/-- **A port's public term is its fingerprint of `pubOfSource`**, at every scalar list. -/
theorem term_value_source (roots : ℕ) (src : RecCircuit.Source) (pubs : List E) (γ : E) :
    (⟨termOf roots src, none⟩ : Lin).toF.eval (powersList γ 2) (fun c ↦ pubs.getD c 0) =
      RecPiop.fpList (RecCircuit.portWeights (List.range src.limbs)) γ (pubOfSource roots pubs src) := by
  obtain ⟨hg0, hg1⟩ := powersList_two γ
  rw [linF_eval]
  cases src with
  | statement =>
    have e : List.range 4 = [0, 1, 2, 3] := rfl
    simp only [RecCircuit.Source.limbs, e, termOf, pubOfSource, canon2, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.cons_append, List.nil_append]
    rw [oneC_eval _ hg0, yC_eval _ hg0, gC_eval _ γ hg1, gyC_eval _ γ hg1]
    show _ = RecPiop.fpList (RecPiop.rootLimbs 0 1 2 3 F192.Y) γ _
    rw [RecPiop.fpList_root]
    linear_combination (-1 : E) * (F192.Y * F192.ofF64 (F192.limb (pubs.getD 0 0 + F192.Y * pubs.getD 1 0) 1) +
      γ * (F192.Y * F192.ofF64 (F192.limb (pubs.getD 2 0 + F192.Y * pubs.getD 3 0) 1))) *
        CharTwo.two_eq_zero (R := E)
  | root i =>
    have e : List.range 4 = [0, 1, 2, 3] := rfl
    simp only [RecCircuit.Source.limbs, e, termOf, pubOfSource, canon2, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.cons_append, List.nil_append]
    rw [oneC_eval _ hg0, gC_eval _ γ hg1]
    show _ = RecPiop.fpList (RecPiop.rootLimbs 0 1 2 3 F192.Y) γ _
    rw [RecPiop.fpList_root]
    linear_combination (-1 : E) * (F192.Y * F192.ofF64 (F192.limb (pubs.getD (4 + 2 * i + 1) 0) 1) +
      γ * (F192.Y * F192.ofF64 (F192.limb (pubs.getD (4 + 2 * i) 0) 1))) * CharTwo.two_eq_zero (R := E)
  | element i =>
    have e : List.range 3 = [0, 1, 2] := rfl
    simp only [RecCircuit.Source.limbs, e, termOf, pubOfSource, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [oneC_eval _ hg0]
    show _ = RecPiop.fpList (RecPiop.elemLimbs 0 1 2 F192.Y) γ _
    have h := limbs3_fp (pubs.getD (4 + 2 * roots + i) 0)
    simp only [limbs3, List.getD_cons_zero, List.getD_cons_succ] at h
    rw [limbs3, RecPiop.fpList_elem, h]
    ring
  | zero =>
    simp only [termOf, pubOfSource, List.map_nil, List.sum_nil]
    exact (fpList_zero _ γ).symm
  | pad =>
    simp only [termOf, pubOfSource, List.map_nil, List.sum_nil]
    exact (fpList_zero _ γ).symm

end RecCompose
