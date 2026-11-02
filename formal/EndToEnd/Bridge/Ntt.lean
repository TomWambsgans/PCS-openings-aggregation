-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient.Domain
import Completeness.Read

/-!
# The statement's additive transform is the novel-basis evaluation

`PcsQuotient.Domain.values m offset c` (`domain.rs:257-260`) takes the `2^m` novel-basis
coefficients `c` of a polynomial to its values at the points `offset + B(i)` of a coset of the span of
the Cantor basis `β₀ … β_{m−1}` (`betaAt`), one butterfly stage per basis vector, and
`Domain.coefficients` undoes it. Here, for every `m` (no evaluation at any size):

* `values_coefficients_K`, `coefficients_values_K` (and `_E`): on arrays of `2^m` entries the two
  transforms are inverse, at any offset, with no hypothesis on the basis (each stage is undone by its
  inverse stage, in characteristic two);
* `values_getD_K`: entry `p < 2^m` of `values m offset c` is `Σ_j c_j X_j(offset + B(p))`, the
  novel-basis polynomial of `c` (`X_j = ∏_{bit t of j} w_t`, `w_t = S^t`), given that `betaAt` is a
  Cantor basis (`IsCantorBasis`, the statement's own decidable property) and `m ≤ 28`; and that is
  F1's `tablePoly` of the table `b ↦ c[idx b]` at the point (`values_getD_tablePoly`), the point
  being F1's `CantorBasis.point` of the bits of `p` for the basis `cantorOf hB` (`point_eq_cantor`);
* `tablePoly_coefficients`: so the table `coefficients m offset v` holds the polynomial taking the
  value `v[p]` at `offset + B(p)`, for every `p < 2^m`.

The proof runs on sequences (`stageF`, `valuesF`, `coefficientsF`): after the stages `m − 1, …, k`,
each block of `2^k` entries holds the novel-basis coefficients (in `w_0 … w_{k−1}`) of a polynomial
that agrees with the whole one on that block's points (`inv_step`), since on the block's coset
`w_k = λ + s`, `λ` the stage's twiddle (`iterate_point`: `S^k(B(n)) = B(n / 2^k)`).
-/

set_option linter.unusedSectionVars false

open LeanVM.Parameters PcsQuotient.Domain QuotientSecurity Finset

namespace Bridge

/-- `K` has characteristic two (a subfield of `E`). -/
instance instCharPK : CharP K 2 := RingHom.charP (algebraMap K E) (algebraMap K E).injective 2

namespace Ntt

/-! ## One stage, on sequences -/

section Core

variable {M : Type} [CommRing M] [Algebra K M] [CharP M 2]

/-- **Stage `k` of the transform on a sequence**, as `Domain.stage` computes each entry: in the
block of `2^(k+1)` entries holding `p`, the pair at `base` and `base + 2^k`, the twiddle `lam` of the
block. -/
def stageF (fwd : Bool) (lam : ℕ → K) (k : ℕ) (a : ℕ → M) (p : ℕ) : M :=
  let half := 2 ^ k
  let r := p % (2 * half)
  let base := p - r + r % half
  let lo := a base
  let hi := a (base + half)
  let l := algebraMap K M (lam (p / (2 * half)))
  if fwd then (if r < half then lo + l * hi else lo + l * hi + hi)
  else (if r < half then lo + l * (lo + hi) else lo + hi)

theorem two_pow_pos' (k : ℕ) : 0 < 2 * 2 ^ k := by positivity

/-- A stage at the position `r` of block `Q`. -/
theorem stageF_at (fwd : Bool) (lam : ℕ → K) (k : ℕ) (a : ℕ → M) (Q r : ℕ)
    (hr : r < 2 * 2 ^ k) :
    stageF fwd lam k a (2 * 2 ^ k * Q + r) =
      if fwd then
        (if r < 2 ^ k then a (2 * 2 ^ k * Q + r % 2 ^ k) +
            algebraMap K M (lam Q) * a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k)
          else a (2 * 2 ^ k * Q + r % 2 ^ k) +
            algebraMap K M (lam Q) * a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k) +
            a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k))
      else
        (if r < 2 ^ k then a (2 * 2 ^ k * Q + r % 2 ^ k) +
            algebraMap K M (lam Q) *
              (a (2 * 2 ^ k * Q + r % 2 ^ k) + a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k))
          else a (2 * 2 ^ k * Q + r % 2 ^ k) + a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k)) := by
  have hm : (2 * 2 ^ k * Q + r) % (2 * 2 ^ k) = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hd : (2 * 2 ^ k * Q + r) / (2 * 2 ^ k) = Q := by
    rw [Nat.mul_add_div (two_pow_pos' k), Nat.div_eq_of_lt hr, add_zero]
  have hb : 2 * 2 ^ k * Q + r - r = 2 * 2 ^ k * Q := Nat.add_sub_cancel _ _
  simp only [stageF, hm, hd, hb]

/-- Every position is a position in its block. -/
theorem pos_decomp (k p : ℕ) : 2 * 2 ^ k * (p / (2 * 2 ^ k)) + p % (2 * 2 ^ k) = p :=
  Nat.div_add_mod p _

theorem two_eq_zero_M : (2 : M) = 0 := CharTwo.two_eq_zero

/-- **The inverse stage undoes the stage.** -/
theorem stageF_true_false (lam : ℕ → K) (k : ℕ) (a : ℕ → M) :
    stageF true lam k (stageF false lam k a) = a := by
  funext p
  rw [← pos_decomp k p]
  generalize p / (2 * 2 ^ k) = Q
  have hr : p % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (two_pow_pos' k)
  generalize p % (2 * 2 ^ k) = r at hr ⊢
  have hh : 0 < 2 ^ k := by positivity
  have h1 : r % 2 ^ k < 2 * 2 ^ k := by have := Nat.mod_lt r hh; omega
  have h2 : r % 2 ^ k + 2 ^ k < 2 * 2 ^ k := by have := Nat.mod_lt r hh; omega
  have e1 := stageF_at false lam k a Q (r % 2 ^ k) h1
  have e2 := stageF_at false lam k a Q (r % 2 ^ k + 2 ^ k) h2
  rw [stageF_at true lam k _ Q r hr]
  simp only [Nat.mod_mod, Nat.mod_lt r hh, Nat.add_mod_right, Bool.false_eq_true,
    ↓reduceIte] at e1 e2 ⊢
  rw [← add_assoc] at e2
  have hn : ¬ (r % 2 ^ k + 2 ^ k < 2 ^ k) := by omega
  rw [if_neg hn] at e2
  rw [e1, e2]
  have h2' := two_eq_zero_M (M := M)
  by_cases hrh : r < 2 ^ k
  · rw [if_pos hrh, Nat.mod_eq_of_lt hrh]
    linear_combination (algebraMap K M (lam Q) *
      (a (2 * 2 ^ k * Q + r) + a (2 * 2 ^ k * Q + r + 2 ^ k))) * h2'
  · rw [if_neg hrh]
    have hrm : r % 2 ^ k = r - 2 ^ k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have he : 2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k = 2 * 2 ^ k * Q + r := by rw [hrm]; omega
    rw [he]
    linear_combination (a (2 * 2 ^ k * Q + r % 2 ^ k) + algebraMap K M (lam Q) *
      (a (2 * 2 ^ k * Q + r % 2 ^ k) + a (2 * 2 ^ k * Q + r))) * h2'

/-- **The stage undoes the inverse stage.** -/
theorem stageF_false_true (lam : ℕ → K) (k : ℕ) (a : ℕ → M) :
    stageF false lam k (stageF true lam k a) = a := by
  funext p
  rw [← pos_decomp k p]
  generalize p / (2 * 2 ^ k) = Q
  have hr : p % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (two_pow_pos' k)
  generalize p % (2 * 2 ^ k) = r at hr ⊢
  have hh : 0 < 2 ^ k := by positivity
  have h1 : r % 2 ^ k < 2 * 2 ^ k := by have := Nat.mod_lt r hh; omega
  have h2 : r % 2 ^ k + 2 ^ k < 2 * 2 ^ k := by have := Nat.mod_lt r hh; omega
  have e1 := stageF_at true lam k a Q (r % 2 ^ k) h1
  have e2 := stageF_at true lam k a Q (r % 2 ^ k + 2 ^ k) h2
  rw [stageF_at false lam k _ Q r hr]
  simp only [Nat.mod_mod, Nat.mod_lt r hh, Nat.add_mod_right, Bool.false_eq_true,
    ↓reduceIte] at e1 e2 ⊢
  rw [← add_assoc] at e2
  have hn : ¬ (r % 2 ^ k + 2 ^ k < 2 ^ k) := by omega
  rw [if_neg hn] at e2
  rw [e1, e2]
  have h2' := two_eq_zero_M (M := M)
  by_cases hrh : r < 2 ^ k
  · rw [if_pos hrh, Nat.mod_eq_of_lt hrh]
    linear_combination (algebraMap K M (lam Q) *
      (a (2 * 2 ^ k * Q + r) + a (2 * 2 ^ k * Q + r + 2 ^ k) +
        algebraMap K M (lam Q) * a (2 * 2 ^ k * Q + r + 2 ^ k))) * h2'
  · rw [if_neg hrh]
    have hrm : r % 2 ^ k = r - 2 ^ k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have he : 2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k = 2 * 2 ^ k * Q + r := by rw [hrm]; omega
    rw [he]
    linear_combination (a (2 * 2 ^ k * Q + r % 2 ^ k) + algebraMap K M (lam Q) *
      a (2 * 2 ^ k * Q + r)) * h2'

/-! ## The transforms, on sequences -/

/-- `values` on sequences: the stages `m − 1, …, 0`, stage `k` with the twiddles `lamOf k`. -/
def valuesF (lamOf : ℕ → ℕ → K) (m : ℕ) (c : ℕ → M) : ℕ → M :=
  (List.range m).foldr (fun k a ↦ stageF true (lamOf k) k a) c

/-- `coefficients` on sequences: the inverse stages `0, …, m − 1`. -/
def coefficientsF (lamOf : ℕ → ℕ → K) (m : ℕ) (v : ℕ → M) : ℕ → M :=
  (List.range m).foldl (fun a k ↦ stageF false (lamOf k) k a) v

theorem valuesF_succ (lamOf : ℕ → ℕ → K) (m : ℕ) (c : ℕ → M) :
    valuesF lamOf (m + 1) c = valuesF lamOf m (stageF true (lamOf m) m c) := by
  simp [valuesF, List.range_succ, List.foldr_append]

theorem coefficientsF_succ (lamOf : ℕ → ℕ → K) (m : ℕ) (v : ℕ → M) :
    coefficientsF lamOf (m + 1) v = stageF false (lamOf m) m (coefficientsF lamOf m v) := by
  simp [coefficientsF, List.range_succ, List.foldl_append]

theorem valuesF_coefficientsF (lamOf : ℕ → ℕ → K) :
    ∀ (m : ℕ) (v : ℕ → M), valuesF lamOf m (coefficientsF lamOf m v) = v
  | 0, _ => rfl
  | m + 1, v => by
    rw [valuesF_succ, coefficientsF_succ, stageF_true_false, valuesF_coefficientsF lamOf m v]

theorem coefficientsF_valuesF (lamOf : ℕ → ℕ → K) :
    ∀ (m : ℕ) (c : ℕ → M), coefficientsF lamOf m (valuesF lamOf m c) = c
  | 0, _ => rfl
  | m + 1, c => by
    rw [valuesF_succ, coefficientsF_succ, coefficientsF_valuesF lamOf m, stageF_false_true]

end Core

end Ntt

end Bridge
