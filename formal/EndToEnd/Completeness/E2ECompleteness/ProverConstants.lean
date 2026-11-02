-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`.
import E2ECompleteness.ProverDefs
import Bridge.Ntt
import Completeness
import Compose.Reduce

/-!
# The Statement's constants are the proof layers'

The Statement computes its constants (`Domain.lean`: `beta()` by a pivot search, `row_vanishing(24)`
by an elimination); `Constants` (`ProverDefs.lean`) says they have their defining properties. From
it:

* **`betaAt_eq_deployed`**: `beta()`'s first `24` vectors are F1's `deployedBasis` (`solve` clears
  each vector's low bit, so `deployedBasis_unique` applies);
* `stmtConsts`: the constants as `Compose.Reduce.Consts` (`beta()`, `row_vanishing(24)`);
  `rowVanishing_stmt`: they solve `row_vanishing`'s system (`Compose.Reduce.RowVanishing`);
* `coordinateWeight_deployed`: `coordinate_weight` (Compose's transcription) is the deployed
  instance's weights (`coordWeight G Y`, by F0c's `rustCoordinateWeight_eq`);
* **`matches_deployed`**: F1's deployed instance matches `reduce` at these constants
  (`Compose.Reduce.Matches`, by `matches_params`).
-/

open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain Finset
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness

/-! ## `beta()` -/

/-- Every vector `beta()` pushes is a `solve`'s. -/
theorem foldl_push_solve : ∀ (n : ℕ) (init : Array K),
    ∀ k, init.size ≤ k → k < ((List.range n).foldl (fun b _ ↦ b.push (solve (b.back?.getD 1)))
      init).size → ∃ x, ((List.range n).foldl (fun b _ ↦ b.push (solve (b.back?.getD 1))) init)[k]?
        = some (solve x)
  | 0, init, k, h1, h2 => by simp at h2; omega
  | n + 1, init, k, h1, h2 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h2 ⊢
    set b := (List.range n).foldl (fun b _ ↦ b.push (solve (b.back?.getD 1))) init
    rw [Array.size_push] at h2
    by_cases hk : k < b.size
    · obtain ⟨x, hx⟩ := foldl_push_solve n init k h1 hk
      refine ⟨x, ?_⟩
      rw [Array.getElem?_push_lt hk]
      rwa [Array.getElem?_eq_getElem hk] at hx
    · have : k = b.size := by omega
      subst this
      exact ⟨_, Array.getElem?_push_size⟩

theorem size_foldl_push : ∀ (n : ℕ) (init : Array K),
    ((List.range n).foldl (fun b _ ↦ b.push (solve (b.back?.getD 1))) init).size = init.size + n
  | 0, _ => rfl
  | n + 1, init => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_push,
      size_foldl_push n init]
    rfl

theorem beta_size : beta.size = basisSize := by
  unfold beta
  rw [size_foldl_push]
  rfl

/-- `solve` clears the low bit. -/
theorem lowBit_solve (x : K) : lowBit (solve x) = false := by
  unfold lowBit solve
  simp only [Primitives.F64.toU64, K.ofLane]
  rw [show (UInt64.ofBitVec (BF64.ofBitVec (UInt64.toBitVec
      (solveLoop 64 x.lane 0 &&& ~~~(1 : UInt64)))).toBitVec) =
      solveLoop 64 x.lane 0 &&& ~~~(1 : UInt64) from rfl]
  rw [UInt64.toNat_and, Nat.testBit_and]
  simp

/-- **`beta()`'s vectors past the first have their low bit clear.** -/
theorem lowBit_betaAt {k : ℕ} (h0 : 0 < k) (hk : k < basisSize) : lowBit (betaAt k) = false := by
  have hs : k < beta.size := by rw [beta_size]; exact hk
  obtain ⟨x, hx⟩ := foldl_push_solve (basisSize - 1) #[1] k (by simp; omega) (by
    rw [size_foldl_push]; simp [basisSize] at hk ⊢; omega)
  have hb : betaAt k = solve x := by
    unfold betaAt
    rw [Array.getD_eq_getD_getElem?]
    show (beta[k]?).getD 0 = solve x
    rw [show beta = (List.range (basisSize - 1)).foldl
      (fun b _ ↦ b.push (solve (b.back?.getD 1))) #[1] from rfl, hx]
    rfl
  rw [hb]
  exact lowBit_solve x

/-- The Statement's basis as F1's, its first `24` vectors. -/
def stmtBasis (hK : Constants) : CantorBasis K (22 + 2) :=
  Bridge.Ntt.cantorOf (Bridge.Ntt.cantorUpTo_of_isCantorBasis hK.cantor (by decide))

/-- **`beta()`'s first `24` vectors are `deployedBasis`'s.** -/
theorem betaAt_eq_deployed (hK : Constants) {k : ℕ} (hk : k < 22 + 2) :
    betaAt k = deployedBasis.β k :=
  deployedBasis_unique (stmtBasis hK) (fun k h0 hk ↦ lowBit_betaAt h0 (by
    unfold basisSize; omega)) k hk

/-! ## The constants of `reduce` -/

/-- **The Statement's constants** as `reduce`'s: `beta()` and `row_vanishing(24)`. -/
def stmtConsts : Compose.Reduce.Consts := ⟨betaAt, fun k ↦ (rowVanishing (22 + 2)).getD k 0⟩

theorem length_rowVanishing (m : ℕ) : (rowVanishing m).length = m - 2 + 1 := by
  simp [rowVanishing]

/-- `rowPolyAt` as a sum. -/
theorem rowPolyAt_eq_sum (x : K) :
    rowPolyAt (22 + 2) x = ∑ k ∈ range (22 + 1), (rowVanishing (22 + 2)).getD k 0 *
      (chain x (22 + 2 - 1)).getD k 0 := by
  unfold rowPolyAt
  have hl1 : (chain x (22 + 2 - 1)).length = 22 + 1 := by
    rw [chain, Bridge.Ntt.chain_foldl]
    simp
  have hl2 : (rowVanishing (22 + 2)).length = 22 + 1 := length_rowVanishing _
  generalize hc : chain x (22 + 2 - 1) = ws at hl1 ⊢
  generalize hr : rowVanishing (22 + 2) = ts at hl2 ⊢
  -- A fold of `acc + t · w` over a zip of two lists of length `n`.
  have key : ∀ (ws ts : List K) (n : ℕ), ws.length = n → ts.length = n → ∀ a : K,
      (ws.zip ts).foldl (fun acc (p : K × K) ↦ acc + p.2 * p.1) a =
        a + ∑ k ∈ range n, ts.getD k 0 * ws.getD k 0 := by
    intro ws
    induction ws with
    | nil => intro ts n h1 _ a; subst h1; simp
    | cons w ws ih =>
      intro ts n h1 h2 a
      rcases ts with _ | ⟨t, ts⟩
      · simp at h1 h2; omega
      · rcases n with _ | n
        · simp at h1
        simp only [List.zip_cons_cons, List.foldl_cons]
        rw [ih ts n (by simpa using h1) (by simpa using h2), sum_range_succ', add_assoc]
        simp [add_comm]
  rw [key ws ts (22 + 1) hl1 hl2 0, zero_add]

/-- **`row_vanishing(24)` solves its system.** -/
theorem rowVanishing_stmt (hK : Constants) : Compose.Reduce.RowVanishing stmtConsts 22 := by
  obtain ⟨hlast, hzero, -, -, -⟩ := hK.rows
  have hl : (rowVanishing (22 + 2)).length = 22 + 1 := length_rowVanishing _
  have hB := Bridge.Ntt.cantorUpTo_of_isCantorBasis hK.cantor (N := basisSize) le_rfl
  refine ⟨?_, fun j hj2 hj ↦ ?_⟩
  · simp only [stmtConsts]
    rw [List.getLast?_eq_getElem?, hl] at hlast
    rw [List.getD_eq_getElem?_getD, show (22 : ℕ) = 22 + 1 - 1 from rfl, hlast]
    rfl
  · simp only [stmtConsts]
    have h := hzero ⟨j, hj⟩ hj2
    rw [rowPolyAt_eq_sum] at h
    refine Eq.trans (sum_congr rfl fun k hk ↦ ?_) h
    have hk' := mem_range.mp hk
    rw [Bridge.Ntt.chain_getD _ (by omega), Bridge.Ntt.iterate_betaAt hB (by unfold basisSize; omega),
      mul_comm]

/-! ## The weights -/

theorem ofBits_shiftLeft (j : ℕ) (hj : j < 64) :
    K.ofBits (1 <<< j) = Primitives.F64.ofU64 ((1 : UInt64) <<< j.toUInt64) := by
  rw [one_shiftLeft_toUInt64 j hj]
  rfl

/-- `bit_weight`, transcribed twice. -/
theorem bitWeight_eq (j : ℕ) (hj : j < 128) : Compose.Reduce.bitWeight j = rustBitWeight j := by
  unfold Compose.Reduce.bitWeight rustBitWeight
  by_cases h : j < 64
  · rw [if_pos h, if_pos h, ofBits_shiftLeft j h]
    rfl
  · rw [if_neg h, if_neg h, ofBits_shiftLeft (j - 64) (by omega)]
    rfl

/-- **`coordinate_weight` is the deployed instance's weights** below `8`. -/
theorem coordinateWeight_deployed (k : ℕ) (hk : k < 8) :
    Compose.Reduce.coordinateWeight k = some (Completeness.deployedInstanceE.c k) := by
  rw [show Completeness.deployedInstanceE.c k = coordWeight Primitives.F192.G Primitives.F192.Y k
    from rfl, ← rustCoordinateWeight_eq k hk]
  unfold Compose.Reduce.coordinateWeight rustCoordinateWeight
  by_cases h0 : k = 0
  · rw [if_pos h0, if_pos h0, bitWeight_eq 1 (by norm_num)]
  by_cases h1 : k = 1
  · rw [if_neg h0, if_neg h0, if_pos h1, if_pos h1]
  rw [if_neg h0, if_neg h0, if_neg h1, if_neg h1, if_pos hk, if_pos hk, bitWeight_eq _ ?_]
  rw [Nat.shiftLeft_eq, one_mul]
  calc 2 ^ (k - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < 128 := by norm_num

/-- **F1's deployed instance matches `reduce` at the Statement's constants.** -/
theorem matches_deployed (hK : Constants) :
    Compose.Reduce.Matches Completeness.deployedInstanceE.params stmtConsts 22 :=
  Compose.Reduce.matches_params Completeness.deployedInstanceE stmtConsts
    (fun k hk ↦ by
      show algebraMap K E (deployedBasis.β k) = ofK (betaAt k)
      rw [betaAt_eq_deployed hK hk]
      rfl)
    coordinateWeight_deployed (rowVanishing_stmt hK)

end E2ECompleteness

/-- info: 'E2ECompleteness.betaAt_eq_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.betaAt_eq_deployed

/-- info: 'E2ECompleteness.matches_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.matches_deployed
