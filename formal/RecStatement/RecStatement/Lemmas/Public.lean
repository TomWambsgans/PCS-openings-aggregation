-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecStatement.Lemmas.SpecOf

/-!
# The public side is the copy argument's target

`PI2.md` §2 step 4 and §9 lever 3c: the verifier sums the public terms along the walk as one fraction
(`walkDens`, `fraction`) and the zero coset in closed form (`cosetSum`), and combines the two (`publicSide`). Under
`SpecOf`, the walked terms are the ports `nz … nP − 1` (`portOf`), each term's denominator that port's
`d_pub(j) = α + F_j + β ω_{N+j}` (`RecPiop.Circuit.dPub`), and the zero coset the ports `0 … nz − 1`, whose public
fingerprints vanish. So (**`publicSide_eq`**) the public side's denominator is `Π_{j<nP} d_pub(j)`, and where none
vanishes its numerator is that product times `T = Σ_j 1/d_pub(j)` (`RecPiop.Circuit.target`).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset RecPiop

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

theorem public_list_range_prod (f : ℕ → F) : ∀ N, ((List.range N).map f).prod = ∏ i ∈ range N, f i
  | 0 => rfl
  | N + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, public_list_range_prod f N, Finset.prod_range_succ]
    simp

/-- `publicSide`'s combination of the walked fraction and the zero coset's. -/
def publicCombine : Option (F × F) → Option (F × F) → Option (F × F)
  | some (n, d), some (nz, dz) => some (n * dz + d * nz, d * dz)
  | side, none => side
  | none, coset => coset

theorem publicSide_eq_combine (S : CoreSpec F) (gs pubs : List F) (α β : F) :
    publicSide S gs pubs α β =
      publicCombine (if S.publicTerms.isEmpty then none else some (fraction (walkDens S gs pubs α β)))
        (S.zeroCoset.map fun (tag, k, a) ↦ cosetSum S.ω α β tag k a) := by
  unfold publicSide publicCombine
  rfl

/-- The combination's denominator is the product, its numerator the cross sum. -/
theorem publicCombine_getD (side coset : Option (F × F)) :
    ((publicCombine side coset).map (·.2)).getD 1 = (side.map (·.2)).getD 1 * (coset.map (·.2)).getD 1 ∧
      ((publicCombine side coset).map (·.1)).getD 0 =
        (side.map (·.1)).getD 0 * (coset.map (·.2)).getD 1 + (side.map (·.2)).getD 1 * (coset.map (·.1)).getD 0 := by
  rcases side with _ | ⟨n, d⟩ <;> rcases coset with _ | ⟨nz, dz⟩ <;> simp [publicCombine]

/-- **The public side** (PI2.md §2 step 4, §9 lever 3c): its denominator is the product of the ports' public
denominators, and where none vanishes its fraction is the target `T = Σ_j 1/d_pub(j)`. -/
theorem publicSide_eq {n : ℕ} {S : CoreSpec F} {G : RecPiop.Circuit F} {B : QuotientSecurity.CantorBasis F n}
    {pairOf : ℕ → Block × ℕ} {portOf : ℕ → ℕ} {nz : ℕ} {pubOf : List F → ℕ → List F}
    (hS : SpecOf S G B pairOf portOf nz pubOf) (pubs : List F) (α β γ : F) :
    ((publicSide S (powersList γ (S.maxGamma + 1)) pubs α β).map (·.2)).getD 1 =
        ∏ j ∈ range G.nP, G.dPub (Heap.omega B) (pubOf pubs) α β γ j ∧
      ((∀ j < G.nP, G.dPub (Heap.omega B) (pubOf pubs) α β γ j ≠ 0) →
        ((publicSide S (powersList γ (S.maxGamma + 1)) pubs α β).map (·.1)).getD 0 =
          ((publicSide S (powersList γ (S.maxGamma + 1)) pubs α β).map (·.2)).getD 1 *
            G.target (Heap.omega B) (pubOf pubs) α β γ) := by
  set gs := powersList γ (S.maxGamma + 1) with hgs
  set d : ℕ → F := fun j ↦ G.dPub (Heap.omega B) (pubOf pubs) α β γ j with hd
  have hNP := hS.nz_le
  -- Each walked term is its port's public denominator.
  have hterm : ∀ J < S.publicTerms.length, termDen S gs pubs α β J = d (portOf J) := by
    intro J hJ
    have hv := hS.term_value J hJ pubs γ
    have ht := hS.term_tag J hJ
    show α + (S.publicTerms.getD J noTerm).2.eval gs (fun c ↦ pubs.getD c 0) +
        β * S.ω (S.publicTerms.getD J noTerm).1 =
      den α β (G.pubFp γ (pubOf pubs) (portOf J), Heap.omega B (G.N + portOf J))
    rw [hv, ht, hS.omega]
    rfl
  -- The walk's denominators.
  have hwalk : walkDens S gs pubs α β = S.walk.map (termDen S gs pubs α β) := by
    refine walkDens_eq S gs pubs α β (by rw [hS.omega]; exact Heap.omega_xor B)
      (by rw [hS.omega]; exact fun x hx ↦ omega_bits B hx) ?_
    intro j hj
    have hjL : j < S.publicTerms.length := List.mem_range.mp (hS.walk_perm.subset hj)
    have ht := hS.term_tag j hjL
    have hp := (hS.port_mem j hjL).2
    have h28 := hS.tags_lt
    show (S.publicTerms.getD j noTerm).1 < 2 ^ 28
    rw [ht]
    omega
  -- `portOf` maps the terms onto the ports `nz … nP − 1`.
  have hinj : Set.InjOn portOf ↑(range S.publicTerms.length) := fun J hJ J' hJ' h ↦
    hS.port_inj J (mem_range.mp (mem_coe.mp hJ)) J' (mem_range.mp (mem_coe.mp hJ')) h
  have hsurj : Set.SurjOn portOf ↑(range S.publicTerms.length) ↑(Ico nz G.nP) := by
    intro j hj
    obtain ⟨h1, h2⟩ := mem_Ico.mp (mem_coe.mp hj)
    obtain ⟨J, hJ, e⟩ := hS.port_surj j h1 h2
    exact ⟨J, mem_coe.mpr (mem_range.mpr hJ), e⟩
  have hmaps : ∀ J ∈ range S.publicTerms.length, portOf J ∈ Ico nz G.nP := fun J hJ ↦
    mem_Ico.mpr (hS.port_mem J (mem_range.mp hJ))
  have hprodW : (S.walk.map (termDen S gs pubs α β)).prod = ∏ j ∈ Ico nz G.nP, d j := by
    rw [(hS.walk_perm.map _).prod_eq, public_list_range_prod,
      Finset.prod_congr rfl fun J hJ ↦ hterm J (mem_range.mp hJ)]
    exact Finset.prod_nbij portOf hmaps hinj hsurj fun _ _ ↦ rfl
  have hsumW : ((S.walk.map (termDen S gs pubs α β)).map (·⁻¹)).sum = ∑ j ∈ Ico nz G.nP, (d j)⁻¹ := by
    rw [List.map_map, (hS.walk_perm.map _).sum_eq, list_range_sum,
      Finset.sum_congr rfl fun J hJ ↦ by rw [Function.comp_apply, hterm J (mem_range.mp hJ)]]
    exact Finset.sum_nbij portOf hmaps hinj hsurj fun _ _ ↦ rfl
  -- The walked fraction.
  set side : Option (F × F) :=
    if S.publicTerms.isEmpty then none else some (fraction (walkDens S gs pubs α β)) with hside
  have hsideD : (side.map (·.2)).getD 1 = ∏ j ∈ Ico nz G.nP, d j ∧
      ((∀ j < G.nP, d j ≠ 0) → (side.map (·.1)).getD 0 = (side.map (·.2)).getD 1 * ∑ j ∈ Ico nz G.nP, (d j)⁻¹) := by
    cases hE : S.publicTerms.isEmpty with
    | true =>
      have hnil : S.publicTerms = [] := List.isEmpty_iff.mp hE
      have hIco : Ico nz G.nP = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun j hj ↦ ?_
        obtain ⟨h1, h2⟩ := mem_Ico.mp hj
        obtain ⟨J, hJ, -⟩ := hS.port_surj j h1 h2
        rw [hnil] at hJ
        exact Nat.not_lt_zero _ hJ
      simp [hside, hE, hIco]
    | false =>
      have hne : S.publicTerms ≠ [] := fun h ↦ by rw [h] at hE; simp at hE
      have hwne : S.walk.map (termDen S gs pubs α β) ≠ [] := by
        intro h
        have hw : S.walk = [] := List.map_eq_nil_iff.mp h
        have hl := hS.walk_perm.length_eq
        rw [hw, List.length_nil, List.length_range] at hl
        exact hne (List.length_eq_zero_iff.mp hl.symm)
      have hs : side = some (fraction (S.walk.map (termDen S gs pubs α β))) := by
        simp only [hside, hE, hwalk, Bool.false_eq_true, ite_false]
      rw [hs]
      refine ⟨by simp [fraction_snd _ hwne, hprodW], fun hnz ↦ ?_⟩
      have hx : ∀ x ∈ S.walk.map (termDen S gs pubs α β), x ≠ 0 := by
        intro x hx
        obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hx
        have hJL : J < S.publicTerms.length := List.mem_range.mp (hS.walk_perm.subset hJ)
        rw [hterm J hJL]
        exact hnz _ (hS.port_mem J hJL).2
      simp only [Option.map_some, Option.getD_some]
      rw [fraction_fst _ hwne hx, fraction_snd _ hwne, hprodW, hsumW]
  -- The zero coset.
  set coset : Option (F × F) := S.zeroCoset.map fun (tag, k, a) ↦ cosetSum S.ω α β tag k a with hcoset
  have hcosetD : (coset.map (·.2)).getD 1 = ∏ j ∈ range nz, d j ∧
      ((∀ j < G.nP, d j ≠ 0) → (coset.map (·.1)).getD 0 = (coset.map (·.2)).getD 1 * ∑ j ∈ range nz, (d j)⁻¹) := by
    rcases hS.coset with ⟨hc, hnz⟩ | ⟨k, hc, hnz, hk⟩
    · simp [hcoset, hc, hnz]
    · have hcs : coset = some (cosetSum (Heap.omega B) α β G.N k (subspaceCoeffsF k)) := by
        simp only [hcoset, hc, Option.map_some, hS.omega]
      have hdvd : 2 ^ k ∣ G.N := pow_dvd_pow 2 hk
      obtain ⟨hprod, hsum⟩ := coset_closed B (hk.trans hS.hn) α β hdvd
      have hdz : ∀ j < nz, d j = α + β * Heap.omega B (G.N + j) := by
        intro j hj
        show den α β (G.pubFp γ (pubOf pubs) j, Heap.omega B (G.N + j)) = _
        rw [hS.zero_ports j hj pubs γ]
        simp [den]
      have hP : ∏ u ∈ range (2 ^ k), (α + β * Heap.omega B (G.N + u)) = ∏ j ∈ range nz, d j := by
        rw [hnz]
        exact Finset.prod_congr rfl fun j hj ↦ (hdz j (by rw [hnz]; exact mem_range.mp hj)).symm
      have hT : ∑ u ∈ range (2 ^ k), (α + β * Heap.omega B (G.N + u))⁻¹ = ∑ j ∈ range nz, (d j)⁻¹ := by
        rw [hnz]
        exact Finset.sum_congr rfl fun j hj ↦ by rw [hdz j (by rw [hnz]; exact mem_range.mp hj)]
      rw [hcs]
      simp only [Option.map_some, Option.getD_some]
      refine ⟨by rw [hprod, hP], fun hnz' ↦ ?_⟩
      have hne : (cosetSum (Heap.omega B) α β G.N k (subspaceCoeffsF k)).2 ≠ 0 := by
        rw [hprod, hP]
        exact Finset.prod_ne_zero_iff.mpr fun j hj ↦ hnz' j (by have := mem_range.mp hj; omega)
      have := hsum hne
      rw [← hT, ← this, mul_div_cancel₀ _ hne]
  -- Combine.
  rw [publicSide_eq_combine]
  obtain ⟨h2, h1⟩ := publicCombine_getD side coset
  have hprodAll : ∏ j ∈ range G.nP, d j = (∏ j ∈ range nz, d j) * ∏ j ∈ Ico nz G.nP, d j :=
    (prod_range_mul_prod_Ico d hNP).symm
  have hsumAll : G.target (Heap.omega B) (pubOf pubs) α β γ =
      ∑ j ∈ range nz, (d j)⁻¹ + ∑ j ∈ Ico nz G.nP, (d j)⁻¹ :=
    (sum_range_add_sum_Ico (fun j ↦ (d j)⁻¹) hNP).symm
  refine ⟨?_, fun hnz ↦ ?_⟩
  · rw [h2, hsideD.1, hcosetD.1, hprodAll, mul_comm]
  · rw [h1, h2, hsideD.2 hnz, hcosetD.2 hnz, hsideD.1, hcosetD.1, hsumAll]
    ring

end RecStatement
