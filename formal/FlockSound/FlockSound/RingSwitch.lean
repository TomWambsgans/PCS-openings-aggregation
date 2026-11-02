-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Matrices
import FlockSound.Frobenius

/-!
# The ring switch: the slices sent, checked on the packed column

The lincheck ends on the slices `ŝ(cy)` of the bits at the point `p = (χ', χ_rest)` of the words
(`strue`, `strue_eq`). The prover sends values `s(cy)`; the verifier draws the staged map `Φ`
(`stagedMap`, any order of the shifts) and states, on the committed column `Q` of packed words
(`Q(u) = Σ_cy w(cy) z(cy, u)`, `w(cy) = x^cy`), the claim `Σ_u Φ(eq(p, u)) Q(u) = T` with
`T = Σ_cy w(cy) Φ(s(cy))` (milestone 1: its 64 Frobenius-twisted terms `Σ_k c_k Q̂(p^(2^k))`;
iteration 2: one ring-twist term, the same weight).

* `ringClaim_eq`: for a Boolean witness, `Σ_u Φ(eq(p, u)) Q(u) = Σ_cy w(cy) Φ(ŝ(cy))`;
* **`ring_sound`**: if the claim holds of the column and the target is the sent slices', the
  sent slices are the true ones, unless a stage's challenge is bad (one value each), given
  ring-switching injectivity on the relevant twists.

Characteristic two. Nothing here transcribes a source.
-/

namespace FlockSound

open Finset

variable {F : Type*} [Field F] {k l m κ : ℕ}

/-- The bits of packing index `cy` as a table of the words `u = (slot bits, block)`. -/
def wordBits (Z : Cube (k + l) → Cube m → Cube κ → F) (cy : Cube (k + l)) (u : Cube (m + κ)) : F :=
  Z cy (lowPart u) (highPart u)

/-- The true slices are the bits' extensions at the point of the words. -/
theorem strue_eq (Z : Cube (k + l) → Cube m → Cube κ → F) (rt : Fin κ → F) (χ' : Fin m → F)
    (cy : Cube (k + l)) : strue Z rt χ' cy = mle (wordBits Z cy) (Fin.append χ' rt) := by
  rw [mle_append]
  simp only [strue, zhat, wordBits, lowPart_append, highPart_append, mle, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ch _ ↦ Finset.sum_congr rfl fun t _ ↦ by ring

variable [CharP F 2]

/-- **The ring claim's true value**: the packed column against `Φ(eq(p, ·))` is the weights
against `Φ` of the true slices. -/
theorem ringClaim_eq (sh : List ℕ) (f : Fin sh.length → F) (w : Cube (k + l) → F)
    (Z : Cube (k + l) → Cube m → Cube κ → F) (hZ : ∀ y c t, Z y c t = 0 ∨ Z y c t = 1)
    (Q : Cube (m + κ) → F) (hpack : ∀ u, Q u = ∑ cy, w cy * wordBits Z cy u) (p : Fin (m + κ) → F) :
    ∑ u, stagedMap sh f (eqP p u) * Q u =
      ∑ cy, w cy * stagedMap sh f (mle (wordBits Z cy) p) := by
  simp only [hpack, Finset.mul_sum, mle, stagedMap_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun cy _ ↦ Finset.sum_congr rfl fun u _ ↦ ?_
  have hb : wordBits Z cy u = 0 ∨ wordBits Z cy u = 1 := hZ cy (lowPart u) (highPart u)
  rw [stagedMap_bit_mul sh f hb]
  ring

variable [Fintype F] [DecidableEq F]

/-- **The ring switch's soundness**: the target the sent slices give equals the true slices'
(the claim on the column holds), so the sent slices are the true ones unless a stage's challenge
is bad. -/
theorem ring_sound (sh : List ℕ) (f : Fin sh.length → F) (w : Cube (k + l) → F) (S : Finset ℕ)
    (hinj : ∀ δ : Cube (k + l) → F, (∀ j ∈ S, frobPair univ w δ j = 0) → δ = 0)
    (hcov : S ⊆ rel sh) (s st : Cube (k + l) → F)
    (hT : ∑ cy, w cy * stagedMap sh f (s cy) = ∑ cy, w cy * stagedMap sh f (st cy))
    (hgood : ∀ j, f j ∉ ringBad univ w sh (fun cy ↦ s cy - st cy) f j) : s = st := by
  by_contra hne
  have hδ : (fun cy ↦ s cy - st cy) ≠ 0 := by
    intro h0
    exact hne (funext fun cy ↦ sub_eq_zero.mp (congrFun h0 cy))
  obtain ⟨j, hj, hπ⟩ : ∃ j ∈ S, frobPair univ w (fun cy ↦ s cy - st cy) j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hδ (hinj _ hall)
  apply ring_escape univ w sh _ f ⟨j, hcov hj, hπ⟩ hgood
  simp only [stagedMap_sub, mul_sub, Finset.sum_sub_distrib, hT, sub_self]

end FlockSound
