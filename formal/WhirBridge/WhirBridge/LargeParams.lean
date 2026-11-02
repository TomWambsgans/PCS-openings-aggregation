/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

leanVM's WHIR at the stack sizes `2^24 ..= 2^28`, rate `1/2`: the ladders, the certified level-0
lists and the verifier's query count, read off leanerVM `mumbai`
(https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0):
`Statement/LeanVmVerifier.lean` (`Whir.ladder`, `queryTable`, `queryGrindingBits`),
`lean_vm/LeanVM/Protocol/Whir/Params/Deployed.lean` (`certTable`, `certOf`, `shapeOK`,
`shapeOK_all`), `lean_vm/LeanVM/Protocol/Verifier/Cost.lean` (`whirCost`, the cost calculus);
`costLE_large` follows this package's `costLE_variant` (`Variant.lean`).
-/
import WhirBridge.Verifier

/-!
# WHIR at `2^24 ..= 2^28`

The commitments of a univariate leanVM PIOP are stacks of `μ = 24 ..= 28` variables, opened by
leanVM's WHIR at rate `1/2` (`LOG_INV_RATE = 1`). Everything here is decided by kernel evaluation
(`decide +kernel`) on objects of a few hundred numbers (the ladders, the certificates' `Nat` bounds,
the cost of one run), never on a stack:

* `admissible_large`: the shapes `(μ, 1)` are admissible (`15 ≤ μ ≤ 28`, `1 ≤ R ≤ 4`), so
  mumbai's deployed codes and `shapeOK_all` cover them;
* `ladder_large`: the ladder `Whir.ladder μ 1` (`derive_config`, `WHIR_QUERIES`) is
  `largeLadder μ`: level 0 folds `6` at rate `1/2`, every later level `4`, the rate exponents
  `1, 4, 7, 10, 13 (, 16)`, the queries
  `224, 56, 32, 23, 17` (`μ = 24, 25`), `224, 56, 32, 23, 18` (`26`), `225, 56, 32, 23, 18` (`27`),
  `225, 56, 32, 23, 18, 14` (`28`), residuals of `2, 3, 4, 5, 2` variables; `17` bits of grinding
  before every level's queries (`grinding_large`);
* `shapeOK_large`: every group of each of these ladders escapes with probability at most `2^-128`
  under the certified codes, and not at most `2^-129` (the query counts are tuned to `128`);
* `listHi_large`, `listMax_large`, `candidates_large`: level 0's Johnson list `L₀` (the candidates
  a root binds to: WHIR takes no out-of-domain sample at level 0) has at most
  `9952, 7908, 6296, 4473, 3564` stacks at `μ = 24, 25, 26, 27, 28` (`largeList`);
* `largeQueries_eq`, `isTotalQueryBound_large`: `opening::verify` (`ourVerifier`) makes at most
  `QO = 7183, 7546, 7928, 8318, 9018` queries to the two oracles at these shapes (the IV's hash,
  the seed's permutation, and mumbai's cost of the program at the commitments' height
  `μ − 5`), below the uniform `10122` (`variantQueries`) of `openingBound`.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

/-- The smallest stack the leanVM PIOP commits here, `2^24` words. -/
def largeMin : ℕ := 24

/-- The largest, `2^28` words (mumbai's `maxLogStack`, the window's end). -/
def largeMax : ℕ := 28

/-- **The shapes are admissible** at rate `1/2`. -/
theorem admissible_large_all :
    ∀ μ, largeMin ≤ μ → μ ≤ largeMax → Whir.Admissible μ logInvRate := by
  decide +kernel

theorem admissible_large {μ : ℕ} (h1 : largeMin ≤ μ) (h2 : μ ≤ largeMax) :
    Whir.Admissible μ logInvRate :=
  admissible_large_all μ h1 h2

/-- **The ladders** at `μ = 24 ..= 28`, rate `1/2`: per level its fold, its rate exponent and its
queries (`⟨fold, logInvRate, queries⟩`). -/
def largeLadder : ℕ → List Whir.Level
  | 24 => [⟨6, 1, 224⟩, ⟨4, 4, 56⟩, ⟨4, 7, 32⟩, ⟨4, 10, 23⟩, ⟨4, 13, 17⟩]
  | 25 => [⟨6, 1, 224⟩, ⟨4, 4, 56⟩, ⟨4, 7, 32⟩, ⟨4, 10, 23⟩, ⟨4, 13, 17⟩]
  | 26 => [⟨6, 1, 224⟩, ⟨4, 4, 56⟩, ⟨4, 7, 32⟩, ⟨4, 10, 23⟩, ⟨4, 13, 18⟩]
  | 27 => [⟨6, 1, 225⟩, ⟨4, 4, 56⟩, ⟨4, 7, 32⟩, ⟨4, 10, 23⟩, ⟨4, 13, 18⟩]
  | 28 => [⟨6, 1, 225⟩, ⟨4, 4, 56⟩, ⟨4, 7, 32⟩, ⟨4, 10, 23⟩, ⟨4, 13, 18⟩, ⟨4, 16, 14⟩]
  | _ => []

/-- **The deployed ladder** (`derive_config`, `crates/verifier/src/whir.rs:34-60`, mumbai's
`Whir.ladder`) at `μ = 24 ..= 28`, rate `1/2`, is `largeLadder μ`. -/
theorem ladder_large :
    ∀ μ, largeMin ≤ μ → μ ≤ largeMax → Whir.ladder μ logInvRate = some (largeLadder μ) := by
  decide +kernel

/-- What is left after the folds, sent in the clear: `2, 3, 4, 5, 2` variables. -/
theorem residual_large :
    ∀ μ, largeMin ≤ μ → μ ≤ largeMax →
      μ - ((largeLadder μ).map (·.fold)).sum = [2, 3, 4, 5, 2].getD (μ - largeMin) 0 := by
  decide +kernel

/-- `QUERY_GRINDING_BITS = 17` (`whir.rs:17`, `whir_config.rs:70`): the proof of work before every
level's query positions. -/
theorem grinding_large : Whir.queryGrindingBits = 17 := rfl

/-- **The certified bound at these shapes**: mumbai's check of the deployed codes passes at
`2^-128` per group (`shapeOK_all`) and fails at `2^-129` (kernel evaluation): the query counts
are tuned to `128` bits. -/
theorem shapeOK_large :
    ∀ μ, largeMin ≤ μ → μ ≤ largeMax →
      Whir.Params.shapeOK 128 μ logInvRate = true ∧
        Whir.Params.shapeOK 129 μ logInvRate = false := by
  decide +kernel

/-! ## Level 0's list -/

/-- **`L₀`**: the certified level-0 list bound (`listHi` of level 0's certificate) at
`μ = 24 ..= 28`; mumbai's generic `2^18` elsewhere. -/
def largeList : ℕ → ℕ
  | 24 => 9952
  | 25 => 7908
  | 26 => 6296
  | 27 => 4473
  | 28 => 3564
  | _ => 2 ^ 18

/-- Level 0's certificate at `μ = 24 ..= 28` (`certTable`, slack `η = e/2^22`,
`e = 298, 375, 471, 663, 832`) has `listHi = ⌊2^62/(2 e s)⌋ = largeList μ`. -/
theorem listHi_large :
    ∀ μ, largeMin ≤ μ → μ ≤ largeMax →
      (Whir.Params.certOf μ logInvRate 0).listHi = largeList μ := by
  decide +kernel

/-- **Level 0's Johnson list at these shapes** has at most `L₀ = largeList μ` stacks. -/
theorem listMax_large {μ : ℕ} (h1 : largeMin ≤ μ) (h2 : μ ≤ largeMax) :
    (code₀ μ logInvRate).listMax ≤ largeList μ :=
  (listMax_le_listHi (admissible_large h1 h2)).trans (listHi_large μ h1 h2).le

/-- **The candidates a root binds to at these shapes**: for every word, the stacks within level
0's Johnson radius of the certified code number at most `L₀ = largeList μ`, the set the opening's
doom (`OpeningDoomed`) quantifies over. -/
theorem candidates_large {μ : ℕ} (h1 : largeMin ≤ μ) (h2 : μ ≤ largeMax) (W : Word) :
    (Candidates μ logInvRate (code₀ μ logInvRate).thr W).Finite ∧
      (Candidates μ logInvRate (code₀ μ logInvRate).thr W).ncard ≤ largeList μ :=
  ⟨(candidates_count (admissible_large h1 h2) W).1,
    (candidates_count (admissible_large h1 h2) W).2.trans (listMax_large h1 h2)⟩

/-! ## The verifier's queries -/

/-- The height of every commitment the opening reads at `μ` (rate `1/2`): level 0's,
`μ − 6 + 1` (`rootHeight`), the largest. -/
def largeHeight (μ : ℕ) : ℕ := rootHeight μ logInvRate

/-- The cost (mumbai's calculus, in quarters of a query) of the opening's program past its seed: the
root, the batching challenge and WHIR (`whirCost`) at the commitments' height. -/
def largeCost (μ : ℕ) : ℕ := 2 + (4 + (2 + whirCost (largeHeight μ) μ (largeLadder μ)))

/-- **`QO`**: the queries of `opening::verify` at a stack of `μ` variables: the IV's hash, the seed's
permutation, and the program's cost. -/
def largeQueries (μ : ℕ) : ℕ := 1 + 1 + largeCost μ / 4

theorem largeQueries_eq :
    largeQueries 24 = 7183 ∧ largeQueries 25 = 7546 ∧ largeQueries 26 = 7928 ∧
      largeQueries 27 = 8318 ∧ largeQueries 28 = 9018 := by
  decide +kernel

/-- `QO` is below the uniform bound `10122` that `openingBound` carries. -/
theorem largeQueries_le :
    ∀ μ, largeMin ≤ μ → μ ≤ largeMax → largeQueries μ ≤ variantQueries := by
  rw [variantQueries_eq]
  decide +kernel

/-- What mumbai's cost lemmas need of the ladder at the commitments' height (decided). -/
theorem ladder_heights_large :
    ∀ μ, largeMin ≤ μ → μ ≤ largeMax →
      whirHeightsLE (largeHeight μ) μ (largeLadder μ) = true ∧
        stackHeightLE (largeHeight μ) μ (largeLadder μ) = true ∧
        queryDepthsLE μ (largeLadder μ) = true := by
  decide +kernel

/-- **The opening's program costs at most `largeCost μ`** at the commitments' height (as
`costLE_variant`, with this shape's ladder in place of the largest admissible one). -/
theorem costLE_large (L : Stacking) (h1 : largeMin ≤ L.logN) (h2 : L.logN ≤ largeMax)
    (claims : List Claim) :
    (variantProg L logInvRate claims).CostLE (largeHeight L.logN) (largeCost L.logN) := by
  have hl := ladder_large L.logN h1 h2
  have hh := ladder_heights_large L.logN h1 h2
  have hW : ∀ levels, Whir.ladder L.logN logInvRate = some levels →
      whirHeightsLE (largeHeight L.logN) L.logN levels = true ∧
        queryDepthsLE L.logN levels = true ∧
        whirCost (largeHeight L.logN) L.logN levels ≤
          whirCost (largeHeight L.logN) L.logN (largeLadder L.logN) := by
    intro levels h
    rw [hl] at h
    cases h
    exact ⟨hh.1, hh.2.2, le_rfl⟩
  have hH : ∀ levels, Whir.ladder L.logN logInvRate = some levels →
      stackHeightLE (largeHeight L.logN) L.logN levels = true := by
    intro levels h
    rw [hl] at h
    cases h
    exact hh.2.1
  have hopen : Prog.Costs (largeHeight L.logN) (L.check logInvRate claims)
      (4 + (2 + whirCost (largeHeight L.logN) L.logN (largeLadder L.logN))) fun _ ↦ True := by
    refine Prog.Costs.seq (a := 0) (Prog.Costs.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
    exact (costs_verifyStackedOpening _ _ _ _ hW).mono (by omega) fun _ h ↦ h
  exact (Prog.Costs.bind' (costs_commitStack _ _ hH)
    fun _ _ ↦ Prog.Costs.bind' hopen fun _ _ ↦ Prog.Costs.pure0 true).mono
      (by unfold largeCost; omega) fun _ _ ↦ trivial

/-- **The query count of `opening::verify`** at these shapes: on every input (root, claims, proof),
`ourVerifier` makes at most `QO = largeQueries log_n` queries to Keccak-256 and Keccak-f[1600]:
none when it rejects first, else the IV's hash, the seed's permutation, and the program's. -/
theorem isTotalQueryBound_large (L : Layout) (h1 : largeMin ≤ L.logN) (h2 : L.logN ≤ largeMax)
    (w : (Digest × Stmt L.stacking) × Proof) :
    IsTotalQueryBound (ourVerifier L logInvRate w) (largeQueries L.logN) := by
  rw [ourVerifier_eq]
  by_cases hne : w.1.2.claims.isEmpty = false
  · rw [if_pos hne, seedComp, bind_assoc]
    have h : largeQueries L.logN = largeCost L.logN / 4 + 1 + 1 := by
      unfold largeQueries; omega
    rw [h]
    refine isTotalQueryBound_queryH_bind _ fun iv ↦ isTotalQueryBound_queryF_bind _ fun seed ↦ ?_
    by_cases hr : rootOf w.2 = some w.1.1
    · rw [if_pos hr]
      exact isTotalQueryBound_runProof (costLE_large L.stacking h1 h2 _) seed w.2
    · rw [if_neg hr]
      exact isTotalQueryBound_pure' _ _
  · rw [if_neg hne]
    exact isTotalQueryBound_pure' _ _

end WhirBridge
