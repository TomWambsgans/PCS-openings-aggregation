-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.FlockBase
import RecGraph.Sim.Pure

/-!
# Flock's pure parts, simulated: the Lagrange weights, the row weights, the known weights

* `lagrangeWeights_ph`: the program's prefix and suffix products (two arrays, filled from both ends) against
  `UniStatement`'s two pushed arrays (the suffix's reversed), through the products `prodSeq`;
* `lagrangeInterpolate_ph` (`Sim.Pure`'s `dot_psim`);
* `rowLowWeights_ph`: the skip's weights and their products with `eq(low, ·)` (`eqKernel_psim`), the nested loops
  against `flatMap`;
* `knownWeights_ph`: the constant's bits, `α²`, `α³` (`pow_psim`), the two `eq` evaluations (`eqEval_psim`).
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-- `Π_{k < n} f k`, left to right from `1`. -/
def prodSeq (f : ℕ → E) : ℕ → E
  | 0 => 1
  | k + 1 => prodSeq f k * f k

theorem prodSeq_congr {f g : ℕ → E} {n : ℕ} (h : ∀ i < n, f i = g i) : prodSeq f n = prodSeq g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prodSeq]; rw [ih (fun i hi ↦ h i (by omega)), h n (by omega)]

theorem foldl_prod_push (f : ℕ → E) (n : ℕ) :
    ((List.range n).foldl (fun acc i ↦ acc.push (acc.back?.getD 1 * f i)) #[1]).size = n + 1 ∧
    ∀ k ≤ n, ((List.range n).foldl (fun acc i ↦ acc.push (acc.back?.getD 1 * f i)) #[1]).getD k 1 =
      prodSeq f k := by
  induction n with
  | zero =>
    refine ⟨rfl, fun k hk ↦ ?_⟩
    have : k = 0 := by omega
    subst this; rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hA : (List.range n).foldl (fun acc i ↦ acc.push (acc.back?.getD 1 * f i)) #[1] = A at ih ⊢
    obtain ⟨h1, h2⟩ := ih
    have hback : A.back?.getD 1 = prodSeq f n := by
      rw [Array.back?_eq_getElem?, h1, Nat.add_sub_cancel, ← h2 n le_rfl, Array.getD_eq_getD_getElem?]
    refine ⟨by simp [h1], fun k hk ↦ ?_⟩
    rw [getD_pushB, hback, h1]
    by_cases hk' : k < n + 1
    · rw [iteT hk']; exact h2 k (by omega)
    · have : k = n + 1 := by omega
      rw [iteF hk', iteT this, this]; rfl

theorem getD_reverseB (A : Array E) (k : ℕ) (hk : k < A.size) : A.reverse.getD k 1 = A.getD (A.size - 1 - k) 1 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_reverse hk]

/-- **`UniStatement`'s Lagrange weights**, as products: weight `i` is `Π_{k<i} d_k · Π_{k>i} d_k · den`. -/
theorem lagrangeWeights_eq (count : ℕ) (x : E) :
    Flock.lagrangeWeights count x = (List.range count).map fun i ↦
      prodSeq (fun k ↦ x + Flock.phi k) i * prodSeq (fun k ↦ x + Flock.phi (count - 1 - k)) (count - (i + 1)) *
        Flock.windowDenominator count := by
  unfold Flock.lagrangeWeights
  dsimp only
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' : i < count := List.mem_range.mp hi
  have hd : ∀ k < count, (Array.ofFn (n := count) fun node ↦ x + Flock.phi node.val).getD k 0 = x + Flock.phi k := by
    intro k hk
    simp [Array.getD_eq_getD_getElem?, hk]
  obtain ⟨p1, p2⟩ := foldl_prod_push (fun k ↦ (Array.ofFn (n := count) fun node ↦ x + Flock.phi node.val).getD k 0) count
  obtain ⟨q1, q2⟩ := foldl_prod_push
    (fun k ↦ (Array.ofFn (n := count) fun node ↦ x + Flock.phi node.val).getD (count - 1 - k) 0) count
  rw [p2 i (by omega), getD_reverseB _ _ (by omega), q2 _ (by omega), q1]
  congr 2
  · exact prodSeq_congr fun k hk ↦ hd k (by omega)
  · rw [show count + 1 - 1 - (i + 1) = count - (i + 1) by omega]
    exact prodSeq_congr fun k hk ↦ hd _ (by omega)

section Pure

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "RpA'" => RpA π iv publicInput stream
local notation "PZ" => PH.zero (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)
local notation "PO" => PH.one (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)
local notation "PC" => PH.const (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)

/-- Pushing a node onto an array that represents a function's first `j` values. -/
theorem push_rp {st : RecState} {D : Array Sym} {f : ℕ → E} {j : ℕ} (hD : D.size = j)
    (hv : ∀ k < j, Rp' st (D.getD k 0) (f k)) {n : Sym} (hn : Rp' st n (f j)) :
    (D.push n).size = j + 1 ∧ ∀ k < j + 1, Rp' st ((D.push n).getD k 0) (f k) := by
  refine ⟨by simp [hD], fun k hk ↦ ?_⟩
  rw [getD_pushB]
  by_cases hk' : k < D.size
  · rw [iteT hk']; exact hv k (by omega)
  · have : k = D.size := by omega
    rw [iteF hk', iteT this, this, hD]; exact hn

theorem rpL_of_fn {st : RecState} {D : Array Sym} {f : ℕ → E} {n : ℕ} (hD : D.size = n)
    (hv : ∀ k < n, Rp' st (D.getD k 0) (f k)) : RpL' st D.toList ((List.range n).map f) := by
  rw [RpL, List.forall₂_iff_get]
  refine ⟨by simp [hD], fun i h1 h2 ↦ ?_⟩
  have hi : i < n := by simpa [hD] using h1
  have := hv i hi
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (hD ▸ hi : i < D.size),
    Option.getD_some] at this
  simpa using this

/-- **`lagrange_weights(count, point)`**: the differences, the prefix and suffix products, the denominator. -/
theorem lagrangeWeights_ph {st : RecState} (hg : Good st) {pt : Sym} {x : E} (hp : Rp' st pt x) (count : ℕ) :
    PH (Pi1.lagrangeWeights count pt) st (fun st' r ↦ RpL' st' r (Flock.lagrangeWeights count x)) := by
  rw [lagrangeWeights_eq]
  unfold Pi1.lagrangeWeights
  dsimp only
  refine PH.bind' (PH.forIn_range 0 count #[] _ st
    (fun j st' D ↦ D.size = j ∧ ∀ k < j, Rp' st' (D.getD k 0) (x + Flock.phi k)) hg ⟨rfl, by simp⟩ ?_) ?_
  · intro j hj st' D hs' ⟨hD, hDv⟩
    grow_all hg hs'
    simp only [Nat.zero_add]
    phg (PC hg (Flock.phi j)) as st1 c hs1 hc
    phg (PH.add hg hp hc) as st2 d hs2 hd
    exact PH.ret hg ⟨_, rfl, push_rp hD hDv hd⟩
  rintro st1 D hs1 ⟨hD, hDv⟩
  grow_all hg hs1
  rw [Nat.sub_zero] at hD hDv
  phg (PO hg) as st2 o1 hs2 ho1
  phg (PO hg) as st3 o2 hs3 ho2
  refine PH.bind' (PH.forIn_range 0 count _ _ st3
    (fun j st' (b : Array Sym × Array Sym) ↦ b.1.size = count + 1 ∧ b.2.size = count + 1 ∧
      (∀ k ≤ j, Rp' st' (b.1.getD k 0) (prodSeq (fun k ↦ x + Flock.phi k) k)) ∧
      (∀ k, count - j ≤ k → k ≤ count →
        Rp' st' (b.2.getD k 0) (prodSeq (fun k ↦ x + Flock.phi (count - 1 - k)) (count - k)))) hg
    ⟨by simp, by simp, fun k hk ↦ ?_, fun k hk1 hk2 ↦ ?_⟩ ?_) ?_
  · have : k = 0 := by omega
    subst this
    simpa [Array.getD_eq_getD_getElem?, prodSeq] using ho1
  · have : k = count := by omega
    subst this
    simpa [Array.getD_eq_getD_getElem?, prodSeq] using ho2
  · intro i hi st' b hs' ⟨hP, hS, hPv, hSv⟩
    grow_all hg hs'
    simp only [Nat.zero_add, Nat.sub_zero] at hi ⊢
    phg (PH.mul hg (hPv i le_rfl) (hDv i hi)) as st4 p hs4 hpv
    phg (PH.mul hg (hSv (count - i) (by omega) (by omega)) (hDv (count - 1 - i) (by omega))) as st5 q hs5 hqv
    refine PH.ret hg ⟨_, rfl, by simp [hP], by simp [hS], fun k hk ↦ ?_, fun k hk1 hk2 ↦ ?_⟩
    · rw [getD_setB]
      by_cases hk' : i + 1 = k ∧ k < b.1.size
      · rw [iteT hk', ← hk'.1]; exact hpv
      · rw [iteF hk']; exact hPv k (by omega)
    · rw [getD_setB]
      by_cases hk' : count - 1 - i = k ∧ k < b.2.size
      · rw [iteT hk', ← hk'.1, show count - (count - 1 - i) = i + 1 by omega,
          show count - (count - i) = i by omega] at *
        exact hqv
      · rw [iteF hk']; exact hSv k (by omega) hk2
  rintro st4 b hs4 ⟨hP, hS, hPv, hSv⟩
  grow_all hg hs4
  rw [Nat.sub_zero] at hPv hSv
  phg (PC hg (Flock.windowDenominator count)) as st5 den hs5 hden
  refine PH.bind' (PH.forIn_range 0 count #[] _ st5
    (fun j st' D ↦ D.size = j ∧ ∀ k < j, Rp' st' (D.getD k 0)
      (prodSeq (fun k ↦ x + Flock.phi k) k * prodSeq (fun k ↦ x + Flock.phi (count - 1 - k)) (count - (k + 1)) *
        Flock.windowDenominator count)) hg ⟨rfl, by simp⟩ ?_) ?_
  · intro j hj st' D hs' ⟨hD', hDv'⟩
    grow_all hg hs'
    simp only [Nat.zero_add, Nat.sub_zero] at hj ⊢
    phg (PH.mul hg (hPv j (by omega)) (hSv (j + 1) (by omega) (by omega))) as st6 p hs6 hpv
    phg (PH.mul hg hpv hden) as st7 o hs7 hov
    exact PH.ret hg ⟨_, rfl, push_rp hD' hDv' hov⟩
  rintro st6 D' hs6 ⟨hD', hDv'⟩
  rw [Nat.sub_zero] at hD' hDv'
  exact PH.ret hs6.good (rpL_of_fn hD' hDv')

/-- **`lagrange_interpolate(count, values, point)`**. -/
theorem lagrangeInterpolate_ph {st : RecState} (hg : Good st) {pt : Sym} {x : E} (hp : Rp' st pt x) (count : ℕ)
    {values : List Sym} {vs : List E} (hv : RpL' st values vs) :
    PH (Pi1.lagrangeInterpolate count values pt) st
      (fun st' r ↦ Rp' st' r (Flock.lagrangeInterpolate count vs x)) := by
  unfold Pi1.lagrangeInterpolate Flock.lagrangeInterpolate
  phg (lagrangeWeights_ph hg hp count) as st1 w hs1 hw
  exact PSim.ph (dot_psim st1 hg hw hv)

end Pure

end RecGraph.Sim
