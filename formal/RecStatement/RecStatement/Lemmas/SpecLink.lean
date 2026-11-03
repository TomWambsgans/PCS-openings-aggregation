-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecStatement.Lemmas.Subspace

/-!
# `Spec::of`'s constants are the blocks' normalised ones

What `Spec.of` computes (`cosetConstants`, `normalisedConstants`, `pairConstants`: the Rust's `coset_constants`,
`normalised_constants`, `pair_constants` in `K`, here generic over a field) is what `SpecOf` asks for:

* `cosetConstantsF b count` is `e_s = Z_{U_s}(b_s)` (`cosetConstantsF_getD`), `vanishingF x e s` is `Z_{U_s}(x)`
  (`vanishingF_eq_zEval`);
* `normalisedConstantsF e` is `c_s = Π_{j<s} e_j / e_s` (`normalisedConstantsF_getD`), so the two together are
  `NormConsts` (`normConsts_of_spec`);
* a pair's `Z_{U_s}(c_p) / Π_{j<s} e_j` is `Ẑ_s(c_p)` by the normalised recursion (`pairZ_eq_zHat`);
* every one of them commutes with a field homomorphism (`K → E`: `map_vanishingF`, `map_cosetConstantsF`,
  `map_normalisedConstantsF`, `map_zHat`), so `Spec.core`'s constants, `Spec.of`'s in `K` embedded in `E`, are the
  same computed in `E`.
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset

variable {F : Type} [Field F]

theorem vanishingF_succ (x : F) (e : List F) (s : ℕ) :
    vanishingF x e (s + 1) = vanishingF x e s * vanishingF x e s + e.getD s 0 * vanishingF x e s := by
  unfold vanishingF
  rw [List.range_succ, List.foldl_append]
  rfl

theorem vanishingF_eq_zEval [CharP F 2] (b : ℕ → F) (e : List F) :
    ∀ s, (∀ j < s, e.getD j 0 = zConst b j) → ∀ x, vanishingF x e s = zEval b s x
  | 0, _, _ => rfl
  | s + 1, h, x => by
    rw [vanishingF_succ, vanishingF_eq_zEval b e s (fun j hj ↦ h j (by omega)) x, h s (by omega)]
    rfl

theorem cosetConstantsF_succ (b : ℕ → F) (count : ℕ) :
    cosetConstantsF b (count + 1) = cosetConstantsF b count ++ [vanishingF (b count) (cosetConstantsF b count) count] := by
  unfold cosetConstantsF
  rw [List.range_succ, List.foldl_append]
  rfl

theorem cosetConstantsF_length (b : ℕ → F) : ∀ count, (cosetConstantsF b count).length = count
  | 0 => rfl
  | count + 1 => by rw [cosetConstantsF_succ, List.length_append, cosetConstantsF_length b count]; rfl

/-- **`coset_constants` is `e_s = Z_{U_s}(b_s)`.** -/
theorem cosetConstantsF_getD [CharP F 2] (b : ℕ → F) :
    ∀ count, ∀ j < count, (cosetConstantsF b count).getD j 0 = zConst b j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | count + 1, j, hj => by
    have hl := cosetConstantsF_length b count
    rw [cosetConstantsF_succ]
    rcases Nat.lt_or_ge j count with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact cosetConstantsF_getD b count j h
    · have : j = count := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero,
        vanishingF_eq_zEval b _ j (cosetConstantsF_getD b j) (b j)]
      rfl

theorem foldl_normalised (e : List F) : ∀ acc : List F × F,
    e.foldl (fun (acc : List F × F) x ↦ (acc.1 ++ [acc.2 * x⁻¹], acc.2 * x)) acc =
      (acc.1 ++ (List.range e.length).map (fun s ↦ acc.2 * (∏ j ∈ range s, e.getD j 0) * (e.getD s 0)⁻¹),
        acc.2 * e.prod) := by
  induction e with
  | nil => intro acc; simp
  | cons x e ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.append_assoc,
      List.singleton_append, List.prod_cons]
    refine Prod.ext ?_ (by simp only; ring)
    simp only [Finset.range_zero, Finset.prod_empty, List.getD_cons_zero, mul_one]
    congr 2
    refine List.map_congr_left fun s _ ↦ ?_
    simp only [Function.comp, Finset.prod_range_succ', List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- **`normalised_constants` is `c_s = Π_{j<s} e_j / e_s`.** -/
theorem normalisedConstantsF_getD (e : List F) {s : ℕ} (hs : s < e.length) :
    (normalisedConstantsF e).getD s 0 = (∏ j ∈ range s, e.getD j 0) / e.getD s 0 := by
  unfold normalisedConstantsF
  rw [foldl_normalised]
  simp [List.getD_eq_getElem?_getD, hs, div_eq_mul_inv]

/-- **`Spec::of`'s recursion constants are `NormConsts`.** -/
theorem normConsts_of_spec [CharP F 2] (b : ℕ → F) (count : ℕ) :
    NormConsts b (normalisedConstantsF (cosetConstantsF b count)) count := by
  intro s hs
  rw [normalisedConstantsF_getD _ (by rw [cosetConstantsF_length]; exact hs), cosetConstantsF_getD b count s hs]
  congr 1
  exact Finset.prod_congr rfl fun j hj ↦ cosetConstantsF_getD b count j (by have := Finset.mem_range.mp hj; omega)

theorem foldl_mul_take (e : List F) : ∀ s ≤ e.length, (e.take s).foldl (· * ·) 1 = ∏ j ∈ range s, e.getD j 0
  | 0, _ => rfl
  | s + 1, hs => by
    rw [List.take_add_one, List.foldl_append, foldl_mul_take e s (by omega), Finset.prod_range_succ,
      List.getElem?_eq_getElem (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s < e.length by omega)]

/-- **A pair's `Z_{U_s}(c_p) / Π_{j<s} e_j` is `Ẑ_s(c_p)`** (`pair_constants`, then `Spec.of`'s division). -/
theorem pairZ_eq_zHat [CharP F 2] (b : ℕ → F) {count s : ℕ} (hs : s ≤ count) (he : ∀ j < count, zConst b j ≠ 0) (x : F) :
    vanishingF x (cosetConstantsF b count) s * (((cosetConstantsF b count).take s).foldl (· * ·) 1)⁻¹ =
      zHat (normalisedConstantsF (cosetConstantsF b count)) s x := by
  rw [vanishingF_eq_zEval b _ s (fun j hj ↦ cosetConstantsF_getD b count j (by omega)) x,
    foldl_mul_take _ s (by rw [cosetConstantsF_length]; exact hs),
    zHat_eq_zEval b _ (fun s' hs' ↦ normConsts_of_spec b count s' (by omega)) (fun j hj ↦ he j (by omega)) x,
    div_eq_mul_inv]
  congr 2
  exact Finset.prod_congr rfl fun j hj ↦ cosetConstantsF_getD b count j (by have := Finset.mem_range.mp hj; omega)

/-! ## Field homomorphisms -/

section Map

variable {F' : Type} [Field F'] (φ : F →+* F')

theorem map_getD (e : List F) (j : ℕ) : (e.map φ).getD j 0 = φ (e.getD j 0) := by
  rw [← map_zero φ, List.getD_map]

theorem map_vanishingF (x : F) (e : List F) (s : ℕ) : φ (vanishingF x e s) = vanishingF (φ x) (e.map φ) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [vanishingF_succ, vanishingF_succ, ← ih, map_getD]
    simp

theorem map_cosetConstantsF (b : ℕ → F) : ∀ count, (cosetConstantsF b count).map φ = cosetConstantsF (φ ∘ b) count
  | 0 => rfl
  | count + 1 => by
    rw [cosetConstantsF_succ, cosetConstantsF_succ, List.map_append, map_cosetConstantsF b count, List.map_singleton,
      map_vanishingF, map_cosetConstantsF b count]
    rfl

theorem map_normalisedConstantsF (e : List F) : (normalisedConstantsF e).map φ = normalisedConstantsF (e.map φ) := by
  unfold normalisedConstantsF
  rw [foldl_normalised, foldl_normalised]
  simp only [List.nil_append, List.map_map, List.length_map, one_mul]
  refine List.map_congr_left fun s _ ↦ ?_
  simp only [Function.comp, map_mul, map_inv₀, map_prod, map_getD]

theorem map_zHat (c : List F) : ∀ (s : ℕ) (x : F), φ (zHat c s x) = zHat (c.map φ) s (φ x)
  | 0, _ => rfl
  | s + 1, x => by
    simp only [zHat, map_add, map_mul, map_zHat c s x, map_getD]

end Map

end RecStatement
