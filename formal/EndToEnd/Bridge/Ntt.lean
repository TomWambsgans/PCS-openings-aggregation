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

/-! ## Only the entries below `2^m` matter -/

section Congr

variable {M : Type} [CommRing M] [Algebra K M] [CharP M 2]

/-- A stage `k < m` reads, at a position below `2^m`, only entries below `2^m`. -/
theorem stageF_congr {m k : ℕ} (hk : k < m) (fwd : Bool) (lam : ℕ → K) {a b : ℕ → M}
    (h : ∀ i < 2 ^ m, a i = b i) {p : ℕ} (hp : p < 2 ^ m) :
    stageF fwd lam k a p = stageF fwd lam k b p := by
  have hsplit : 2 ^ m = 2 * 2 ^ k * 2 ^ (m - (k + 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [← pos_decomp k p] at hp ⊢
  generalize p / (2 * 2 ^ k) = Q at hp ⊢
  have hr : p % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (two_pow_pos' k)
  generalize p % (2 * 2 ^ k) = r at hr hp ⊢
  have hQ' : Q < 2 ^ (m - (k + 1)) := by
    have : 2 * 2 ^ k * Q < 2 * 2 ^ k * 2 ^ (m - (k + 1)) := by
      rw [← hsplit]; exact lt_of_le_of_lt (Nat.le_add_right _ _) hp
    exact Nat.lt_of_mul_lt_mul_left this
  have hQ : 2 * 2 ^ k * Q + 2 * 2 ^ k ≤ 2 ^ m := by
    rw [hsplit, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hQ'
  have hrm : r % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  rw [stageF_at fwd lam k a Q r hr, stageF_at fwd lam k b Q r hr]
  generalize 2 * 2 ^ k * Q = X at hQ ⊢
  generalize r % 2 ^ k = y at hrm ⊢
  have hb1 : X + y < 2 ^ m := by omega
  have hb2 : X + y + 2 ^ k < 2 ^ m := by omega
  rw [h _ hb1, h _ hb2]

theorem foldr_congr {m : ℕ} (fwd : Bool) (lamOf : ℕ → ℕ → K) :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ {a b : ℕ → M}, (∀ i < 2 ^ m, a i = b i) →
      ∀ i < 2 ^ m, l.foldr (fun k a ↦ stageF fwd (lamOf k) k a) a i =
        l.foldr (fun k a ↦ stageF fwd (lamOf k) k a) b i
  | [], _, _, _, h => h
  | k :: l, hl, a, b, h => fun i hi ↦ by
    simp only [List.foldr_cons]
    exact stageF_congr (hl k List.mem_cons_self) _ _
      (foldr_congr fwd lamOf l (fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)) h) hi

theorem foldl_congr {m : ℕ} (fwd : Bool) (lamOf : ℕ → ℕ → K) :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ {a b : ℕ → M}, (∀ i < 2 ^ m, a i = b i) →
      ∀ i < 2 ^ m, l.foldl (fun a k ↦ stageF fwd (lamOf k) k a) a i =
        l.foldl (fun a k ↦ stageF fwd (lamOf k) k a) b i
  | [], _, _, _, h => h
  | k :: l, hl, a, b, h => fun i hi ↦ by
    simp only [List.foldl_cons]
    exact foldl_congr fwd lamOf l (fun k hk ↦ hl k (List.mem_cons_of_mem _ hk))
      (fun j hj ↦ stageF_congr (hl k List.mem_cons_self) _ _ h hj) i hi

end Congr

/-! ## The arrays: `Domain.stage`, `values`, `coefficients` -/

/-- The twiddles of stage `k` (`Domain.stage`'s `lams`): `w_k(offset) + B(2j)` for block `j`. -/
def lamAt (od : List K) (k j : ℕ) : K := od.getD k 0 + point (2 * j)

theorem stage_size {M : Type} [Scalable M] (fwd : Bool) (od : List K) (k : ℕ) (a : Array M) :
    (stage fwd od k a).size = a.size := by
  simp [stage]

theorem foldr_stage_size {M : Type} [Scalable M] (fwd : Bool) (od : List K) :
    ∀ (l : List ℕ) (a : Array M), (l.foldr (fun k a ↦ stage fwd od k a) a).size = a.size
  | [], _ => rfl
  | k :: l, a => by rw [List.foldr_cons, stage_size, foldr_stage_size fwd od l a]

theorem foldl_stage_size {M : Type} [Scalable M] (fwd : Bool) (od : List K) :
    ∀ (l : List ℕ) (a : Array M), (l.foldl (fun a k ↦ stage fwd od k a) a).size = a.size
  | [], _ => rfl
  | k :: l, a => by rw [List.foldl_cons, foldl_stage_size fwd od l, stage_size]

/-- `values` keeps the size. -/
theorem values_size {M : Type} [Scalable M] (m : ℕ) (offset : K) (a : Array M) :
    (values m offset a).size = a.size :=
  foldr_stage_size true _ _ a

/-- `coefficients` keeps the size. -/
theorem coefficients_size {M : Type} [Scalable M] (m : ℕ) (offset : K) (a : Array M) :
    (coefficients m offset a).size = a.size :=
  foldl_stage_size false _ _ a

theorem lams_lt (p n k : ℕ) (hp : p < n) : p / (2 * 2 ^ k) < n / (2 * 2 ^ k) + 1 :=
  Nat.lt_succ_of_le (Nat.div_le_div_right hp.le)

/-- **A stage of `K` entries is `stageF`**, below the array's size. -/
theorem stage_getD_K (fwd : Bool) (od : List K) (k : ℕ) (a : Array K) (p : ℕ) (hp : p < a.size) :
    (stage fwd od k a).getD p 0 = stageF fwd (lamAt od k) k (fun i ↦ a.getD i 0) p := by
  simp only [stage, stageF, lamAt, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hp,
    lams_lt p a.size k hp, dite_true, Option.getD_some]
  rfl

/-- **A stage of `E` entries is `stageF`**, below the array's size. -/
theorem stage_getD_E (fwd : Bool) (od : List K) (k : ℕ) (a : Array E) (p : ℕ) (hp : p < a.size) :
    (stage fwd od k a).getD p 0 = stageF fwd (lamAt od k) k (fun i ↦ a.getD i 0) p := by
  simp only [stage, stageF, lamAt, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hp,
    lams_lt p a.size k hp, dite_true, Option.getD_some]
  rfl

/-! ### The folds, for `K` -/

theorem foldr_stage_K (fwd : Bool) (od : List K) {m : ℕ} :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ (c : Array K), c.size = 2 ^ m →
      ∀ p < 2 ^ m, (l.foldr (fun k a ↦ stage fwd od k a) c).getD p 0 =
        l.foldr (fun k a ↦ stageF fwd (lamAt od k) k a) (fun i ↦ c.getD i 0) p
  | [], _, _, _ => fun _ _ ↦ rfl
  | k :: l, hl, c, hc => fun p hp ↦ by
    have hs : (l.foldr (fun k a ↦ stage fwd od k a) c).size = 2 ^ m := by
      rw [foldr_stage_size, hc]
    simp only [List.foldr_cons]
    rw [stage_getD_K _ _ _ _ _ (hs ▸ hp)]
    exact stageF_congr (hl k List.mem_cons_self) _ _
      (foldr_stage_K fwd od l (fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)) c hc) hp

theorem foldl_stage_K (fwd : Bool) (od : List K) {m : ℕ} :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ (c : Array K), c.size = 2 ^ m →
      ∀ p < 2 ^ m, (l.foldl (fun a k ↦ stage fwd od k a) c).getD p 0 =
        l.foldl (fun a k ↦ stageF fwd (lamAt od k) k a) (fun i ↦ c.getD i 0) p
  | [], _, _, _ => fun _ _ ↦ rfl
  | k :: l, hl, c, hc => fun p hp ↦ by
    simp only [List.foldl_cons]
    have hl' : ∀ k ∈ l, k < m := fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)
    rw [foldl_stage_K fwd od l hl' (stage fwd od k c) (by rw [stage_size, hc]) p hp]
    exact foldl_congr fwd (lamAt od) l hl'
      (fun i hi ↦ stage_getD_K fwd od k c i (hc ▸ hi)) p hp

theorem values_getD_K' (m : ℕ) (offset : K) (c : Array K) (hc : c.size = 2 ^ m) (p : ℕ)
    (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 =
      valuesF (lamAt (chain offset m)) m (fun i ↦ c.getD i 0) p :=
  foldr_stage_K true (chain offset m) (List.range m) (fun _ hk ↦ List.mem_range.mp hk) c hc p hp

theorem coefficients_getD_K' (m : ℕ) (offset : K) (v : Array K) (hv : v.size = 2 ^ m) (p : ℕ)
    (hp : p < 2 ^ m) :
    (coefficients m offset v).getD p 0 =
      coefficientsF (lamAt (chain offset m)) m (fun i ↦ v.getD i 0) p :=
  foldl_stage_K false (chain offset m) (List.range m) (fun _ hk ↦ List.mem_range.mp hk) v hv p hp

theorem array_ext_getD_K {a b : Array K} (hs : a.size = b.size)
    (h : ∀ p < a.size, a.getD p 0 = b.getD p 0) : a = b := by
  refine Array.ext hs fun i h1 h2 ↦ ?_
  have := h i h1
  simpa [Array.getD_eq_getD_getElem?, h1, h2] using this

/-- **`values` inverts `coefficients`** on `2^m` entries of `K`, at every offset. -/
theorem values_coefficients_K (m : ℕ) (offset : K) (v : Array K) (hv : v.size = 2 ^ m) :
    values m offset (coefficients m offset v) = v := by
  have hs : (coefficients m offset v).size = 2 ^ m := by rw [coefficients_size, hv]
  refine array_ext_getD_K (by rw [values_size, hs, hv]) fun p hp ↦ ?_
  rw [values_size, hs] at hp
  rw [values_getD_K' m offset _ hs p hp]
  unfold valuesF
  rw [foldr_congr true (lamAt (chain offset m)) (List.range m) (fun _ hk ↦ List.mem_range.mp hk)
      (b := coefficientsF (lamAt (chain offset m)) m (fun i ↦ v.getD i 0))
      (fun i hi ↦ coefficients_getD_K' m offset v hv i hi) p hp]
  exact congrFun (valuesF_coefficientsF _ m _) p

/-- **`coefficients` inverts `values`** on `2^m` entries of `K`, at every offset. -/
theorem coefficients_values_K (m : ℕ) (offset : K) (c : Array K) (hc : c.size = 2 ^ m) :
    coefficients m offset (values m offset c) = c := by
  have hs : (values m offset c).size = 2 ^ m := by rw [values_size, hc]
  refine array_ext_getD_K (by rw [coefficients_size, hs, hc]) fun p hp ↦ ?_
  rw [coefficients_size, hs] at hp
  rw [coefficients_getD_K' m offset _ hs p hp]
  unfold coefficientsF
  rw [foldl_congr false (lamAt (chain offset m)) (List.range m) (fun _ hk ↦ List.mem_range.mp hk)
      (b := valuesF (lamAt (chain offset m)) m (fun i ↦ c.getD i 0))
      (fun i hi ↦ values_getD_K' m offset c hc i hi) p hp]
  exact congrFun (coefficientsF_valuesF _ m _) p

/-! ### The folds, for `E` -/

theorem foldr_stage_E (fwd : Bool) (od : List K) {m : ℕ} :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ (c : Array E), c.size = 2 ^ m →
      ∀ p < 2 ^ m, (l.foldr (fun k a ↦ stage fwd od k a) c).getD p 0 =
        l.foldr (fun k a ↦ stageF fwd (lamAt od k) k a) (fun i ↦ c.getD i 0) p
  | [], _, _, _ => fun _ _ ↦ rfl
  | k :: l, hl, c, hc => fun p hp ↦ by
    have hs : (l.foldr (fun k a ↦ stage fwd od k a) c).size = 2 ^ m := by
      rw [foldr_stage_size, hc]
    simp only [List.foldr_cons]
    rw [stage_getD_E _ _ _ _ _ (hs ▸ hp)]
    exact stageF_congr (hl k List.mem_cons_self) _ _
      (foldr_stage_E fwd od l (fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)) c hc) hp

theorem foldl_stage_E (fwd : Bool) (od : List K) {m : ℕ} :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ (c : Array E), c.size = 2 ^ m →
      ∀ p < 2 ^ m, (l.foldl (fun a k ↦ stage fwd od k a) c).getD p 0 =
        l.foldl (fun a k ↦ stageF fwd (lamAt od k) k a) (fun i ↦ c.getD i 0) p
  | [], _, _, _ => fun _ _ ↦ rfl
  | k :: l, hl, c, hc => fun p hp ↦ by
    simp only [List.foldl_cons]
    have hl' : ∀ k ∈ l, k < m := fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)
    rw [foldl_stage_E fwd od l hl' (stage fwd od k c) (by rw [stage_size, hc]) p hp]
    exact foldl_congr fwd (lamAt od) l hl'
      (fun i hi ↦ stage_getD_E fwd od k c i (hc ▸ hi)) p hp

theorem values_getD_E' (m : ℕ) (offset : K) (c : Array E) (hc : c.size = 2 ^ m) (p : ℕ)
    (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 =
      valuesF (lamAt (chain offset m)) m (fun i ↦ c.getD i 0) p :=
  foldr_stage_E true (chain offset m) (List.range m) (fun _ hk ↦ List.mem_range.mp hk) c hc p hp

theorem coefficients_getD_E' (m : ℕ) (offset : K) (v : Array E) (hv : v.size = 2 ^ m) (p : ℕ)
    (hp : p < 2 ^ m) :
    (coefficients m offset v).getD p 0 =
      coefficientsF (lamAt (chain offset m)) m (fun i ↦ v.getD i 0) p :=
  foldl_stage_E false (chain offset m) (List.range m) (fun _ hk ↦ List.mem_range.mp hk) v hv p hp

theorem array_ext_getD_E {a b : Array E} (hs : a.size = b.size)
    (h : ∀ p < a.size, a.getD p 0 = b.getD p 0) : a = b := by
  refine Array.ext hs fun i h1 h2 ↦ ?_
  have := h i h1
  simpa [Array.getD_eq_getD_getElem?, h1, h2] using this

/-- **`values` inverts `coefficients`** on `2^m` entries of `E`, at every offset. -/
theorem values_coefficients_E (m : ℕ) (offset : K) (v : Array E) (hv : v.size = 2 ^ m) :
    values m offset (coefficients m offset v) = v := by
  have hs : (coefficients m offset v).size = 2 ^ m := by rw [coefficients_size, hv]
  refine array_ext_getD_E (by rw [values_size, hs, hv]) fun p hp ↦ ?_
  rw [values_size, hs] at hp
  rw [values_getD_E' m offset _ hs p hp]
  unfold valuesF
  rw [foldr_congr true (lamAt (chain offset m)) (List.range m) (fun _ hk ↦ List.mem_range.mp hk)
      (b := coefficientsF (lamAt (chain offset m)) m (fun i ↦ v.getD i 0))
      (fun i hi ↦ coefficients_getD_E' m offset v hv i hi) p hp]
  exact congrFun (valuesF_coefficientsF _ m _) p

/-- **`coefficients` inverts `values`** on `2^m` entries of `E`, at every offset. -/
theorem coefficients_values_E (m : ℕ) (offset : K) (c : Array E) (hc : c.size = 2 ^ m) :
    coefficients m offset (values m offset c) = c := by
  have hs : (values m offset c).size = 2 ^ m := by rw [values_size, hc]
  refine array_ext_getD_E (by rw [coefficients_size, hs, hc]) fun p hp ↦ ?_
  rw [coefficients_size, hs] at hp
  rw [coefficients_getD_E' m offset _ hs p hp]
  unfold coefficientsF
  rw [foldl_congr false (lamAt (chain offset m)) (List.range m) (fun _ hk ↦ List.mem_range.mp hk)
      (b := valuesF (lamAt (chain offset m)) m (fun i ↦ c.getD i 0))
      (fun i hi ↦ values_getD_E' m offset c hc i hi) p hp]
  exact congrFun (coefficientsF_valuesF _ m _) p

end Ntt

end Bridge
