-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Heap.Leaf
import LeanVM.Protocol.Fingerprint

/-!
# The bus fingerprint and its soundness

SPEC §1, §5: a bus tuple `τ` (sixteen coordinates of `K`) has the fingerprint
`β + Σ_s eq(α, s)·τ_s`, `α ∈ E⁴`, `β ∈ E` (`fp`). It is leanerVM `6175f1a0`'s
`LeanVM.Protocol.fingerprint` shifted by `β`, and in characteristic two `β + π_α(τ) = β − π_α(τ)`,
so a product of fingerprints is leanerVM's `sideProduct` (`fpProd_fp_eq_sideProduct`), and
**Theorem 5.1** there (`card_sideProduct_collision_le`, `sideProduct_collision`) applies as it is:

* **`card_fpProd_eq_le`, `prob_fpProd_eq_le`**: two lists of at most `N` tuples that are not
  permutations of each other have equal fingerprint products at no more than `4·N·|E|⁴` of the
  `|E|⁵` challenges `(α, β)`: probability at most `busError N = 4·N / |E| = 4·N / 2^192`. The `4`
  is the total degree of a factor in `(α, β)` (the weights `eq(α, s)` are multilinear in the four
  coordinates of `α`); one Schwartz–Zippel bound over `E⁵` covers both the compression of a tuple
  by `eq(α, ·)` and the product in `β`. The lists are fixed before the challenge.
* **`card_heapSat_le`, `prob_heapSat_le`**: hence a heap whose push and pull tuples are not
  permutations of each other can be made to hold (some `T` meeting the tree, leaf and root
  identities) at the same few challenges: `heap_prod_eq` turns any such `T` into equal products.
  Zero fingerprints need no exclusion: the chain multiplies only, and the bound counts every
  challenge, those at which a fingerprint vanishes included.
-/

namespace Heap

open LeanVM.Parameters LeanVM.Protocol Finset OracleComp
open scoped ENNReal

/-- **The bus fingerprint** (SPEC §1): `β + Σ_s eq(α, s)·τ_s`. -/
def fp (α : Fin 4 → E) (β : E) (t : Vector K 16) : E := β + fingerprint α t

/-- In characteristic two the fingerprint is leanerVM's factor `β − π_α(τ)`. -/
theorem fp_eq_sub (α : Fin 4 → E) (β : E) (t : Vector K 16) : fp α β t = β - fingerprint α t :=
  (CharTwo.sub_eq_add β _).symm

/-- A product of fingerprints is leanerVM's `sideProduct` of the multiset of the tuples. -/
theorem fpProd_fp_eq_sideProduct (α : Fin 4 → E) (β : E) (l : List (Vector K 16)) :
    fpProd (fp α β) l = sideProduct α β (l : Multiset (Vector K 16)) := by
  rw [sideProduct, Multiset.map_coe, Multiset.prod_coe, fpProd]
  exact congrArg List.prod (List.map_congr_left fun t _ ↦ fp_eq_sub α β t)

/-- **The bus error**: `4·N / |E|`, `N` bounding both sides' tuple counts. -/
noncomputable def busError (N : ℕ) : ℝ≥0∞ := ((4 * N : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

/-- `busError N = 4·N / 2^192`. -/
theorem busError_eq (N : ℕ) : busError N = ((4 * N : ℕ) : ℝ≥0∞) / 2 ^ 192 := by
  simp only [busError, card_E, Nat.cast_pow, Nat.cast_ofNat]

/-- A count of challenges `(α, β)` of at most `4·N·|E|⁴` is a probability of at most
`busError N`. -/
theorem prob_le_busError_of_card_le (p : (Fin 4 → E) × E → Prop) [DecidablePred p] {N : ℕ}
    (h : (univ.filter p).card ≤ 4 * N * Fintype.card E ^ 4) :
    Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[p ab] ≤ busError N := by
  have hcard : Fintype.card ((Fin 4 → E) × E) = Fintype.card E * Fintype.card E ^ 4 := by
    simp [mul_comm]
  have hdiv : busError N =
      ((4 * N * Fintype.card E ^ 4 : ℕ) : ℝ≥0∞) / (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞) := by
    rw [busError, hcard, Nat.cast_mul (4 * N), Nat.cast_mul (Fintype.card E),
      ENNReal.mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ Fintype.card_ne_zero))
        (ENNReal.natCast_ne_top _)]
  rw [hdiv, SampleableType.prEvent_uniformSample_le_div_iff]
  exact h

open Classical in
/-- **Fingerprint soundness, counting form.** Two lists of at most `N` tuples that are not
permutations of each other have equal fingerprint products at no more than `4·N·|E|⁴`
challenges `(α, β)`. -/
theorem card_fpProd_eq_le {l₁ l₂ : List (Vector K 16)} (h : ¬ l₁.Perm l₂) {N : ℕ}
    (h₁ : l₁.length ≤ N) (h₂ : l₂.length ≤ N) :
    (univ.filter fun ab : (Fin 4 → E) × E ↦
        fpProd (fp ab.1 ab.2) l₁ = fpProd (fp ab.1 ab.2) l₂).card ≤
      4 * N * Fintype.card E ^ 4 := by
  have hne : (l₁ : Multiset (Vector K 16)) ≠ l₂ := fun he ↦ h (Multiset.coe_eq_coe.mp he)
  have hc := card_sideProduct_collision_le hne (N := N) (by simpa using h₁) (by simpa using h₂)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card] at hc
  refine le_of_eq_of_le (congrArg Finset.card (Finset.filter_congr fun ab _ ↦ ?_)) hc
  rw [fpProd_fp_eq_sideProduct, fpProd_fp_eq_sideProduct]

/-- **Fingerprint soundness.** Two lists of at most `N` tuples that are not permutations of each
other have equal fingerprint products at a uniform challenge `(α, β)` with probability at most
`busError N = 4·N / |E|`. -/
theorem prob_fpProd_eq_le {l₁ l₂ : List (Vector K 16)} (h : ¬ l₁.Perm l₂) {N : ℕ}
    (h₁ : l₁.length ≤ N) (h₂ : l₂.length ≤ N) :
    Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[fpProd (fp ab.1 ab.2) l₁ = fpProd (fp ab.1 ab.2) l₂] ≤
      busError N := by
  classical
  exact prob_le_busError_of_card_le _ (card_fpProd_eq_le h h₁ h₂)

/-! ## The heap at the challenges -/

/-- **A heap layout**: its depth `n` (`2^n` positions, `2^(n-1)` leaves), its blocks of leaves
laid end to end from the first leaf, and the state boundary's push `init` and pull `fin`. -/
structure HeapData where
  /-- The depth: `2^n` positions, the leaves at `[2^(n-1), 2^n)`. -/
  n : ℕ
  /-- The blocks of leaves, in heap order. -/
  blocks : List (LeafBlock (Vector K 16))
  /-- The state boundary's push, at the root. -/
  init : Vector K 16
  /-- The state boundary's pull, at the root. -/
  fin : Vector K 16

namespace HeapData

variable (D : HeapData)

/-- The layout is a heap: at least one level, and the blocks fill the leaves exactly. -/
structure WellFormed : Prop where
  depth : 1 ≤ D.n
  fills : total D.blocks = 2 ^ (D.n - 1)

/-- The heap's push tuples: the blocks', then `init`. -/
abbrev pushes : List (Vector K 16) := heapPush D.blocks D.init

/-- The heap's pull tuples: the blocks', then `fin`. -/
abbrev pulls : List (Vector K 16) := heapPull D.blocks D.fin

/-- **The heap holds at `(α, β)`**: some heap values `T` meet the tree identity, every block's
leaf identity and the root identity, with the fingerprints at `(α, β)`. The verifier's identities
at the committed heap, read on the domain points (`Heap.Cantor`), give it. -/
def Sat (α : Fin 4 → E) (β : E) : Prop :=
  ∃ T : ℕ → E, HeapHolds D.n D.blocks D.init D.fin (fp α β) T

/-- **Where the heap holds, the products are equal.** -/
theorem fpProd_eq_of_sat (hD : D.WellFormed) {α : Fin 4 → E} {β : E} (h : D.Sat α β) :
    fpProd (fp α β) D.pushes = fpProd (fp α β) D.pulls := by
  obtain ⟨T, hT⟩ := h
  exact heap_prod_eq hD.depth hD.fills hT

open Classical in
/-- **The heap's soundness, counting form.** If the heap's push and pull tuples are not
permutations of each other, and each side has at most `N`, the heap holds at no more than
`4·N·|E|⁴` challenges `(α, β)`. -/
theorem card_sat_le (hD : D.WellFormed) (hne : ¬ D.pushes.Perm D.pulls) {N : ℕ}
    (h₁ : D.pushes.length ≤ N) (h₂ : D.pulls.length ≤ N) :
    (univ.filter fun ab : (Fin 4 → E) × E ↦ D.Sat ab.1 ab.2).card ≤ 4 * N * Fintype.card E ^ 4 :=
  (card_le_card fun ab hab ↦ by
      rw [mem_filter] at hab ⊢
      exact ⟨hab.1, D.fpProd_eq_of_sat hD hab.2⟩).trans
    (card_fpProd_eq_le hne h₁ h₂)

/-- **The heap's soundness.** If the heap's push and pull tuples are not permutations of each
other, and each side has at most `N`, the heap holds at a uniform `(α, β)` with probability at
most `busError N`. -/
theorem prob_sat_le (hD : D.WellFormed) (hne : ¬ D.pushes.Perm D.pulls) {N : ℕ}
    (h₁ : D.pushes.length ≤ N) (h₂ : D.pulls.length ≤ N) :
    Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[D.Sat ab.1 ab.2] ≤ busError N := by
  classical
  exact prob_le_busError_of_card_le _ (D.card_sat_le hD hne h₁ h₂)

end HeapData

end Heap
