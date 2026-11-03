-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- `frobPair`, `frobPair_stage` and `card_frob_root_le_one` are leanerVM's
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit f0393df4,
-- `lean_vm/LeanVM/Protocol/ToArkLib/Flock/FrobeniusMap.lean`, MIT OR Apache-2.0), as they are; the
-- staged map with any order of the shifts (`stagedMap`, `rel`, `ring_escape`) is new here.
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin

/-!
# The staged Frobenius map of the ring switch, its stages in any order

The ring switch's map `Φ` applies stages `a ↦ a + f · a^(2^s)` (`stagedMap`), a shift `s` and a
challenge `f` each, in the order of the list of shifts: leanVM's `32, 16, 8, 4, 2, 1`
(`flock_min`'s `ring_map` at milestone 1) or the tower order `1, 2, 4, 8, 16, 32` (iteration 2's
lever 1a). For weights `w` and a family `b`, `π_k(b) = Σ_i w_i b_i^(2^k)` (`frobPair`); one stage
of shift `s` sends `π_k` to `π_k + f^(2^k) π_(k + s)`. The final value `Σ_i w_i Φ(b_i)` is `π_0`
after every stage.

**The relevant twists** (`rel`): after the last stage only `π_0` matters; before a stage of shift
`s`, the twists `k` and `k + s` for every `k` relevant after it. If some relevant `π_k` is nonzero
before a stage, some relevant `π_k` is nonzero after it for every challenge but one at most
(`card_ringStage_le`): so each stage's challenge has one bad value (`ringBad`, a function of the
challenges before it), and `π_0 ≠ 0` at the end unless one is hit (**`ring_escape`**). For both
orders the relevant twists before the first stage are all of `0, …, 63` (`range_subset_rel_leanvm`,
`range_subset_rel_tower`), so ring switching's injectivity (no nonzero family has all its 64
`π_k` zero) makes the map's error `6/|E|` in either order.

Characteristic two throughout.
-/

namespace FlockSound

open Finset

variable {R : Type*} [CommRing R]

/-- `π_k(b) = Σ_i w_i · b_i ^ 2 ^ k` (leanerVM's). -/
def frobPair {ι : Type*} (s : Finset ι) (w b : ι → R) (k : ℕ) : R :=
  ∑ i ∈ s, w i * b i ^ 2 ^ k

variable [CharP R 2]

/-- One stage with shift `M` and coefficient `f` sends `π_k` to `π_k + f ^ 2 ^ k · π_{M + k}`
(leanerVM's). -/
theorem frobPair_stage {ι : Type*} (s : Finset ι) (w b : ι → R) (M : ℕ) (f : R) (k : ℕ) :
    frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k =
      frobPair s w b k + f ^ 2 ^ k * frobPair s w b (M + k) := by
  simp only [frobPair, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [add_pow_char_pow, mul_pow, ← pow_mul, ← pow_add]
  ring

/-- `a + f ^ 2 ^ k · b = 0` with `(a, b) ≠ (0, 0)` has one root `f` at most (leanerVM's). -/
theorem card_frob_root_le_one {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    (k : ℕ) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    (Finset.univ.filter fun f : F ↦ a + f ^ 2 ^ k * b = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun f₁ h₁ f₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [mul_zero, add_zero] at h₁
    exact hab.elim (· h₁.2) (· rfl)
  have heq : f₁ ^ 2 ^ k = f₂ ^ 2 ^ k :=
    mul_right_cancel₀ hb (add_left_cancel (h₁.2.trans h₂.2.symm))
  exact iterateFrobenius_inj F 2 k heq

/-! ## The staged map -/

/-- **The staged map**: stage `j` sends `a` to `a + f_j · a ^ 2 ^ s_j`, in the order of `sh`. -/
def stagedMap : (sh : List ℕ) → (Fin sh.length → R) → R → R
  | [], _, a => a
  | s :: sh, f, a => stagedMap sh (Fin.tail f) (a + f 0 * a ^ 2 ^ s)

theorem stagedMap_add : ∀ (sh : List ℕ) (f : Fin sh.length → R) (a b : R),
    stagedMap sh f (a + b) = stagedMap sh f a + stagedMap sh f b
  | [], _, _, _ => rfl
  | s :: sh, f, a, b => by
    simp only [stagedMap]
    rw [← stagedMap_add sh, add_pow_char_pow]
    congr 1
    ring

theorem stagedMap_zero : ∀ (sh : List ℕ) (f : Fin sh.length → R), stagedMap sh f 0 = 0
  | [], _ => rfl
  | s :: sh, f => by
    simp only [stagedMap]
    rw [zero_pow (pow_ne_zero _ two_ne_zero), mul_zero, add_zero, stagedMap_zero sh]

theorem stagedMap_neg (sh : List ℕ) (f : Fin sh.length → R) (a : R) :
    stagedMap sh f (-a) = -stagedMap sh f a := by
  rw [eq_neg_iff_add_eq_zero, ← stagedMap_add, neg_add_cancel, stagedMap_zero]

theorem stagedMap_sub (sh : List ℕ) (f : Fin sh.length → R) (a b : R) :
    stagedMap sh f (a - b) = stagedMap sh f a - stagedMap sh f b := by
  rw [sub_eq_add_neg, stagedMap_add, stagedMap_neg, ← sub_eq_add_neg]

/-- The map of a sum is the sum of the maps. -/
theorem stagedMap_sum {ι : Type*} (sh : List ℕ) (f : Fin sh.length → R) (s : Finset ι)
    (a : ι → R) : stagedMap sh f (∑ i ∈ s, a i) = ∑ i ∈ s, stagedMap sh f (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [stagedMap_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, stagedMap_add, ih]

/-- A bit commutes with the map: `Φ(b a) = b Φ(a)` for `b ∈ {0, 1}`. -/
theorem stagedMap_bit_mul (sh : List ℕ) (f : Fin sh.length → R) {b : R} (hb : b = 0 ∨ b = 1)
    (a : R) : stagedMap sh f (b * a) = b * stagedMap sh f a := by
  rcases hb with rfl | rfl
  · simp [stagedMap_zero]
  · simp

/-! ## The relevant twists and the bad challenges -/

/-- **The relevant twists** before the stages `sh`: `{0}` after the last; before a stage of shift
`s`, `k` and `k + s` for each `k` relevant after it. -/
def rel : List ℕ → Finset ℕ
  | [] => {0}
  | s :: sh => rel sh ∪ (rel sh).image (· + s)

/-- leanVM's order: every twist below `64` is relevant before the first stage. -/
theorem range_subset_rel_leanvm : Finset.range 64 ⊆ rel [32, 16, 8, 4, 2, 1] := by decide +kernel

/-- The tower order (iteration 2, lever 1a): every twist below `64` is relevant too. -/
theorem range_subset_rel_tower : Finset.range 64 ⊆ rel [1, 2, 4, 8, 16, 32] := by decide +kernel

/-- **One stage, one bad challenge**: a family with a nonzero relevant `π_k` before a stage keeps
one after it but for one challenge at most. -/
theorem card_ringStage_le {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    {ι : Type*} (s : Finset ι) (w b : ι → F) (M : ℕ) (sh : List ℕ)
    (h : ∃ k ∈ rel (M :: sh), frobPair s w b k ≠ 0) :
    (Finset.univ.filter fun f : F ↦
      ∀ k ∈ rel sh, frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k = 0).card ≤ 1 := by
  obtain ⟨k₀, hk₀, hne⟩ := h
  obtain ⟨k, hk, hab⟩ : ∃ k ∈ rel sh, frobPair s w b k ≠ 0 ∨ frobPair s w b (M + k) ≠ 0 := by
    simp only [rel, Finset.mem_union, Finset.mem_image] at hk₀
    rcases hk₀ with h | ⟨k, hk, rfl⟩
    · exact ⟨k₀, h, Or.inl hne⟩
    · exact ⟨k, hk, Or.inr (by rwa [add_comm])⟩
  refine (Finset.card_le_card fun f hf ↦ ?_).trans (card_frob_root_le_one k hab)
  rw [Finset.mem_filter] at hf ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← frobPair_stage]
  exact hf.2 k hk

section Bad

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F] {ι : Type*}

/-- One stage's bad challenges: where every relevant `π_k` after it vanishes though one before
did not. -/
noncomputable def stageBad (s : Finset ι) (w : ι → F) (M : ℕ) (sh : List ℕ) (b : ι → F) :
    Finset F := by
  classical
  exact if ∃ k ∈ rel (M :: sh), frobPair s w b k ≠ 0 then
    univ.filter (fun x ↦ ∀ k ∈ rel sh, frobPair s w (fun i ↦ b i + x * b i ^ 2 ^ M) k = 0)
  else ∅

/-- **The ring map's bad challenges**: stage `0`'s (`stageBad`); stage `j + 1`'s, those of the
family after stage `0`. -/
noncomputable def ringBad (s : Finset ι) (w : ι → F) :
    (sh : List ℕ) → (ι → F) → (Fin sh.length → F) → Fin sh.length → Finset F
  | [], _, _, j => j.elim0
  | M :: sh, b, f, j => Fin.cases (stageBad s w M sh b)
      (fun j ↦ ringBad s w sh (fun i ↦ b i + f 0 * b i ^ 2 ^ M) (Fin.tail f) j) j

theorem card_ringBad_le (s : Finset ι) (w : ι → F) : ∀ (sh : List ℕ) (b : ι → F)
    (f : Fin sh.length → F) (j : Fin sh.length), (ringBad s w sh b f j).card ≤ 1
  | [], _, _, j => j.elim0
  | M :: sh, b, f, j => by
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · show (stageBad s w M sh b).card ≤ 1
      classical
      unfold stageBad
      split_ifs with h
      · exact card_ringStage_le s w b M sh h
      · simp
    · exact card_ringBad_le s w sh _ _ j

/-- Stage `j`'s bad challenges depend on the challenges before it only. -/
theorem ringBad_congr (s : Finset ι) (w : ι → F) : ∀ (sh : List ℕ) (b : ι → F)
    (f f' : Fin sh.length → F) (j : Fin sh.length), (∀ i : Fin sh.length, i.val < j.val → f i = f' i) →
    ringBad s w sh b f j = ringBad s w sh b f' j
  | [], _, _, _, j, _ => j.elim0
  | M :: sh, b, f, f', j, h => by
    refine Fin.cases (fun _ ↦ rfl) (fun j h ↦ ?_) j h
    show ringBad s w sh _ (Fin.tail f) j = ringBad s w sh _ (Fin.tail f') j
    rw [h 0 (Nat.succ_pos _)]
    exact ringBad_congr s w sh _ _ _ j fun i hi ↦ h i.succ (by simpa using hi)

/-- **The ring map's soundness**: a family with a nonzero relevant `π_k` has
`Σ_i w_i Φ(b_i) ≠ 0` unless a stage's challenge is bad. -/
theorem ring_escape (s : Finset ι) (w : ι → F) : ∀ (sh : List ℕ) (b : ι → F)
    (f : Fin sh.length → F), (∃ k ∈ rel sh, frobPair s w b k ≠ 0) →
    (∀ j, f j ∉ ringBad s w sh b f j) → ∑ i ∈ s, w i * stagedMap sh f (b i) ≠ 0
  | [], b, f, h, _ => by
    obtain ⟨k, hk, hne⟩ := h
    simp only [rel, Finset.mem_singleton] at hk
    subst hk
    simpa [frobPair, stagedMap] using hne
  | M :: sh, b, f, h, hgood => by
    classical
    have h0 : f 0 ∉ stageBad s w M sh b := hgood 0
    unfold stageBad at h0
    rw [if_pos h] at h0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h0
    push Not at h0
    have := ring_escape s w sh (fun i ↦ b i + f 0 * b i ^ 2 ^ M) (Fin.tail f) h0 fun j ↦ hgood j.succ
    simpa [stagedMap] using this

end Bad

end FlockSound
