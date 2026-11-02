-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- An example of `ListChainKDoom.lean`'s closed theorem: two proof commitments of `2^27` words
-- (WhirBridge's `exampleChunks`, at half the size) and a setup of `2^24 ..= 2^26` words, with the
-- numbers; of this repository.
import Compose.ListChainKDoom

/-!
# Two roots of `2^27` words and a setup: the bound, in bits

A protocol in the shape of the univariate leanVM PIOP's: the chain's rounds `exRounds` (`C1`'s
root then three challenges, `C2`'s root then one, five values then one), `C1` and `C2` two public
stacks of `2^27` words (`chunks27`: forty columns of `2^21` rows, one of `3 · 2^19`, one of `2^22`
over two chunks, `43` lanes; `NewOK` decided on the chunks' numbers), each opened by WHIR at
rate `1/2` with the computable decoder (level 0's list `L₀ = 4473`), and a setup of
`2^24 ..= 2^26` words (any public layout `Layout::new` accepts there), the Merkle tree of its
stack computed with the oracle (`stackSetupS`, at most `2^22` queries). The PIOP is abstract:
its rounds' errors are a toy `d / 2^192`, `d = 2^26`; what it must give is `hg₁`, `hg₂` (a table
satisfying `C_i`'s opening's claims is `good`), `hS` (the setup's stack satisfying its claims is
`goodS`), `hfit`, `hlink`.

**`knowledgeSoundness_twoRoots`**: the closed theorem's bound at this protocol,

`openingBoundAt 8318 x + openingBoundAt 8318 (x + 8318) + openingBoundAt QO_S (x + 2 · 8318)
  + N (4473² · 2^26 / 2^192 + 5 N / 2^256)`,   `x = QS + Q + 6`, `N = x + 2 · 8318 + QO_S`,

(`QO = largeQueries 27 = 8318`, `QO_S = largeQueries μ_S ≤ 7928`, `QS = 2^(μ_S − 4)`).

**`knowledgeSoundness_twoRoots_bits`**: at most `2^-62` for an adversary of at most `2^64`
queries. (Exactly: `2^-62.415` at `Q = 2^64`, `μ_S = 26`: the three doom terms are `≈ 2^-64`
each, `3 · 2^-64 = 2^-62.415`; the list term is `≈ 2^-77.75`.)
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The shapes -/

/-- The `2^27`-word stack of `C1` and `C2` (lanes of `2^21` words): forty columns of `2^21` rows,
one of `3 · 2^19` rows, one of `2^22` rows over two chunks of `2^21`. -/
def chunks27 : List (ℕ × ℕ) :=
  (List.range 40).map (fun i ↦ (i, 2 ^ 21)) ++ [(40, 3 * 2 ^ 19), (41, 2 ^ 21), (42, 2 ^ 21)]

/-- `Layout::new` accepts it (decided on the chunks' numbers, no stack built): `43` lanes. -/
theorem chunks27_ok : NewOK 27 21 27 chunks27 ∧
    (Layout.new 27 21 27 chunks27).lanes.length = 43 := by
  decide +kernel

/-- **`C1`'s and `C2`'s shape**: `2^27` words, rate `1/2`. -/
@[reducible] noncomputable def shape27 : WhirShape :=
  WhirShape.large 27 21 27 chunks27 chunks27_ok.1 (by decide) (by decide)

/-- **The setup's shape**: any public layout of `2^24 ..= 2^26` words. -/
@[reducible] noncomputable def shapeS (sv sl sμ : ℕ) (sch : List (ℕ × ℕ)) (hS : NewOK sv sl sμ sch)
    (hs1 : 24 ≤ sμ) (hs2 : sμ ≤ 26) : WhirShape :=
  WhirShape.large sv sl sμ sch hS hs1 (le_trans hs2 (by decide))

theorem largeQueries_27 : largeQueries 27 = 8318 := largeQueries_eq.2.2.2.1

theorem largeQueries_le_26 : ∀ μ, 24 ≤ μ → μ ≤ 26 → largeQueries μ ≤ 7928 := by
  intro μ h1 h2
  obtain ⟨e24, e25, e26, -, -⟩ := largeQueries_eq
  interval_cases μ <;> omega

theorem largeList_27 : largeList 27 = 4473 := rfl

/-! ## The protocol -/

/-- The chain's rounds: `C1`'s root and three challenges, `C2`'s root and one, five values and
one. -/
def exRounds : List RoundSpec := [⟨true, 0, 2⟩, ⟨true, 0, 0⟩, ⟨false, 5, 0⟩]

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]

/-- The two roots' decoders: the computable decoder of the `2^27`-word shape, read back by `rd₁`,
`rd₂`. -/
noncomputable def exTC (rd₁ rd₂ : Tab shape27.L → M) : ℕ → TableCode M
  | 1 => tableCode shape27.L shape27.R shape27.adm rd₂
  | _ => tableCode shape27.L shape27.R shape27.adm rd₁

theorem exTC_bound (rd₁ rd₂ : Tab shape27.L → M) (i : ℕ) :
    (exTC rd₁ rd₂ i).commit.bound = 4473 := by
  have h : ∀ rd : Tab shape27.L → M,
      (tableCode shape27.L shape27.R shape27.adm rd).commit.bound = 4473 := fun rd =>
    (tableCode_bound_large 27 21 27 chunks27 chunks27_ok.1 (by decide) (by decide) rd).trans
      largeList_27
  rcases i with _ | _ | i
  · exact h rd₁
  · exact h rd₂
  · exact h rd₁

/-- **The openings**: `C1`'s at round `0`'s root, `C2`'s at round `1`'s, the setup's at the root
the proof carries. -/
noncomputable def twoOps (cl₁ cl₂ : Pf → List (List F) → Stmt shape27.L.stacking)
    (prf₁ prf₂ : Pf → Proof) (rd₁ rd₂ : Tab shape27.L → M) (S : WhirShape)
    (clS : Pf → List (List F) → Stmt S.L.stacking) (prfS : Pf → Proof) (rootS : Pf → Bytes32)
    (q₀ : Column S.L.logN) : List (WhirOp Pf F M) :=
  [⟨shape27, cl₁, prf₁, .round 0 (fun q => rd₁ (tabOf shape27.L q))⟩,
    ⟨shape27, cl₂, prf₂, .round 1 (fun q => rd₂ (tabOf shape27.L q))⟩,
    ⟨S, clS, prfS, .setup rootS q₀⟩]

/-! ## The numbers -/

theorem inv_two_pow_128 : (2 : ℝ≥0∞)⁻¹ ^ 128 = ((2 ^ 128 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 128 + 128 from rfl, two_pow_div_two_pow]

theorem div_192_eq (a : ℕ) :
    ((a : ℕ) : ℝ≥0∞) / 2 ^ 192 = ((a * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 192 + 64 from rfl, pow_add,
    ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]

theorem cast_div_le {a b : ℕ} (h : a ≤ b) :
    ((a : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((b : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr h) _

/-- An opening's term at most `(X 2^128 + 5 X²) / 2^256` for `QA + QO ≤ X`. -/
theorem openingBoundAt_le {QV QA X : ℕ} (h : QA + QV ≤ X) :
    openingBoundAt QV QA ≤ ((X * 2 ^ 128 + 5 * X * X : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold openingBoundAt
  rw [inv_two_pow_128, ENNReal.div_add_div_same, ← mul_div_assoc, ← Nat.cast_add, ← Nat.cast_mul]
  refine cast_div_le ?_
  calc (QA + QV) * (2 ^ 128 + 5 * (QA + QV)) ≤ X * (2 ^ 128 + 5 * X) :=
        Nat.mul_le_mul h (by omega)
    _ = X * 2 ^ 128 + 5 * X * X := by ring

/-- The list term at most `(X c + 5 X²) / 2^256` for `N ≤ X` and an error at most `c / 2^256`. -/
theorem listTerm_le {N X c : ℕ} {m : ℝ≥0∞} (hN : N ≤ X) (hm : m ≤ ((c : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    ((N : ℕ) : ℝ≥0∞) * (m + 5 * ((N : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤
      ((X * c + 5 * X * X : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have e5 : 5 * ((N : ℕ) : ℝ≥0∞) = ((5 * N : ℕ) : ℝ≥0∞) := by rw [Nat.cast_mul, Nat.cast_ofNat]
  calc ((N : ℕ) : ℝ≥0∞) * (m + 5 * ((N : ℕ) : ℝ≥0∞) / 2 ^ 256)
      ≤ ((N : ℕ) : ℝ≥0∞) * (((c : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((5 * N : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
        rw [e5]
        exact mul_le_mul' le_rfl (add_le_add hm le_rfl)
    _ = ((N * (c + 5 * N) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        rw [ENNReal.div_add_div_same, ← mul_div_assoc, ← Nat.cast_add, ← Nat.cast_mul]
    _ ≤ _ := by
        refine cast_div_le ?_
        calc N * (c + 5 * N) ≤ X * (c + 5 * X) := Nat.mul_le_mul hN (by omega)
          _ = X * c + 5 * X * X := by ring

/-! ## The theorem -/

/-- **Knowledge soundness of a two-root protocol with WHIR openings** (`C1`, `C2` of `2^27`
words, the setup of `2^24 ..= 2^26`), every opening's doom discharged, the rounds' errors
`2^26 / 2^192`: the closed theorem's bound at this protocol. -/
theorem knowledgeSoundness_twoRoots (K : ChainSpec F St) (hK : K.rounds = exRounds)
    (R : Piop K M) (herr : ∀ j, R.err j ≤ ((2 ^ 26 : ℕ) : ℝ≥0∞) / 2 ^ 192)
    (view : Pf → St × List (RMsg F))
    (cl₁ cl₂ : Pf → List (List F) → Stmt shape27.L.stacking) (prf₁ prf₂ : Pf → Proof)
    (rd₁ rd₂ : Tab shape27.L → M)
    (sv sl sμ : ℕ) (sch : List (ℕ × ℕ)) (hsS : NewOK sv sl sμ sch) (hs1 : 24 ≤ sμ) (hs2 : sμ ≤ 26)
    (clS : Pf → List (List F) → Stmt (shapeS sv sl sμ sch hsS hs1 hs2).L.stacking)
    (prfS : Pf → Proof) (rootS : Pf → Bytes32) (q₀ : Column sμ)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (fix : Bytes32 → Pf → Pf)
    (hfix : ∀ s p, rootS (fix s p) = s)
    (A₀ : Bytes32 → OracleComp KeccakCalls Pf) (Q : ℕ) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q)
    (hg₁ : ∀ π ch (t : Tab shape27.L),
      (∀ cl ∈ (cl₁ π ch).claims, tabEval shape27.L t cl.point = cl.value) →
        good 0 π ch (some (rd₁ t)))
    (hg₂ : ∀ π ch (t : Tab shape27.L),
      (∀ cl ∈ (cl₂ π ch).claims, tabEval shape27.L t cl.point = cl.value) →
        good 1 π ch (some (rd₂ t)))
    (hS : ∀ π ch, (∀ cl ∈ (clS π ch).claims,
      (shapeS sv sl sμ sch hsS hs1 hs2).L.tableEval q₀ cl.point = cl.value) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → good i π ch cs[i]) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c) :
    Pr{let z ← (simulateQ randomOracle (expK K view
        (withSetupG (stackSetupS (shapeS sv sl sμ sch hsS hs1 hs2) q₀) fix A₀)
        (opsRun view (twoOps cl₁ cl₂ prf₁ prf₂ rd₁ rd₂ (shapeS sv sl sμ sch hsS hs1 hs2) clS prfS
          rootS q₀)))).run' ∅}[
        BreaksOK K (fun i => (exTC rd₁ rd₂ i).commit) R view check
          (fun bs => ∀ k < 3, bs.getD k false = true) z] ≤
      openingBoundAt 8318 (2 ^ (sμ - 4) + Q + 6) +
        openingBoundAt 8318 (2 ^ (sμ - 4) + Q + 6 + 8318) +
        openingBoundAt (largeQueries sμ) (2 ^ (sμ - 4) + Q + 6 + 8318 + 8318) +
        ((2 ^ (sμ - 4) + Q + 6 + 8318 + 8318 + largeQueries sμ : ℕ) : ℝ≥0∞) *
          (((4473 ^ 2 * 2 ^ 26 : ℕ) : ℝ≥0∞) / 2 ^ 192 +
            5 * ((2 ^ (sμ - 4) + Q + 6 + 8318 + 8318 + largeQueries sμ : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set ops := twoOps cl₁ cl₂ prf₁ prf₂ rd₁ rd₂ (shapeS sv sl sμ sch hsS hs1 hs2) clS prfS rootS q₀
    with hops
  -- The openings' matches.
  have hok : ∀ o ∈ ops,
      WhirOp.OK (exTC rd₁ rd₂) good (stackSetupS (shapeS sv sl sμ sch hsS hs1 hs2) q₀) fix o := by
    intro o ho
    simp only [hops, twoOps, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact whirOp_ok_tableCode shape27 cl₁ prf₁ 0 rd₁ (exTC rd₁ rd₂) rfl good hg₁ _ _
    · exact whirOp_ok_tableCode shape27 cl₂ prf₂ 1 rd₂ (exTC rd₁ rd₂) rfl good hg₂ _ _
    · exact whirOp_ok_stack (shapeS sv sl sμ sch hsS hs1 hs2) clS prfS rootS q₀ _ good fix hfix
  have hcov : ∀ i < K.rounds.length, (K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd := by
    intro i hi hr
    rw [hK] at hi
    simp only [exRounds, List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact ⟨_, List.mem_cons_self, _, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, _, rfl⟩
    · simp [ChainSpec.spec, hK, exRounds] at hr
  have hS' : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHolds o π ch) → goodS π ch := fun π ch h =>
    hS π ch (h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hQS : IsTotalQueryBound (stackSetupS (shapeS sv sl sμ sch hsS hs1 hs2) q₀)
      (2 ^ (sμ - 4)) := by
    have h := isTotalQueryBound_stackSetupS (shapeS sv sl sμ sch hsS hs1 hs2) q₀
    have e : rootHeight (shapeS sv sl sμ sch hsS hs1 hs2).L.logN
        (shapeS sv sl sμ sch hsS hs1 hs2).R + 1 = sμ - 4 := by
      simp only [Layout.new_logN, rootHeight, laneFold,
        logInvRate]
      omega
    rwa [e] at h
  have h := knowledgeSoundness_listChainK_closed K R view ops (exTC rd₁ rd₂) check good goodS
    (stackSetupS (shapeS sv sl sμ sch hsS hs1 hs2) q₀) fix A₀ (2 ^ (sμ - 4)) Q hQS hQ hok hcov
    hS' hfit hlink
  have hnQ : K.nQ = 6 := by simp [ChainSpec.nQ, hK, exRounds, nSteps]
  have hn : 2 ^ (sμ - 4) + Q + K.nQ + (ops.map fun o => o.S.QO).sum =
      2 ^ (sμ - 4) + Q + 6 + 8318 + 8318 + largeQueries sμ := by
    simp only [hops, twoOps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, shape27,
      shapeS, WhirShape.large, hnQ, largeQueries_27]
    omega
  have hd : doomSum ops (2 ^ (sμ - 4) + Q + K.nQ) =
      openingBoundAt 8318 (2 ^ (sμ - 4) + Q + 6) +
        openingBoundAt 8318 (2 ^ (sμ - 4) + Q + 6 + 8318) +
        openingBoundAt (largeQueries sμ) (2 ^ (sμ - 4) + Q + 6 + 8318 + 8318) := by
    simp only [hops, twoOps, doomSum, shape27, shapeS, WhirShape.large, hnQ,
      largeQueries_27, add_zero, add_assoc]
  have hlen : ops.length = 3 := rfl
  rw [hn, hd, hlen] at h
  refine h.trans ?_
  gcongr
  -- The list term: two roots of `4473` candidates.
  unfold maxErrK
  refine Finset.sup_le fun j hj => ?_
  rw [hK] at hj
  simp only [exRounds, List.length_cons, List.length_nil, Finset.mem_range] at hj
  have hfac : facL (fun i => (exTC rd₁ rd₂ i).commit) 0 (K.rounds.take (j + 1)) ≤ 4473 ^ 2 := by
    rw [hK]
    interval_cases j <;> simp [facL, exRounds, exTC_bound]
  calc (facL (fun i => (exTC rd₁ rd₂ i).commit) 0 (K.rounds.take (j + 1)) : ℝ≥0∞) * R.err j
      ≤ ((4473 ^ 2 : ℕ) : ℝ≥0∞) * (((2 ^ 26 : ℕ) : ℝ≥0∞) / 2 ^ 192) := by
        exact mul_le_mul' (by exact_mod_cast hfac) (herr j)
    _ = ((4473 ^ 2 * 2 ^ 26 : ℕ) : ℝ≥0∞) / 2 ^ 192 := by
        rw [← mul_div_assoc, ← Nat.cast_mul]

/-- **The bits**: at most `2^-62` for an adversary of at most `2^64` queries (the setup's `2^22`
more). -/
theorem knowledgeSoundness_twoRoots_bits (K : ChainSpec F St) (hK : K.rounds = exRounds)
    (R : Piop K M) (herr : ∀ j, R.err j ≤ ((2 ^ 26 : ℕ) : ℝ≥0∞) / 2 ^ 192)
    (view : Pf → St × List (RMsg F))
    (cl₁ cl₂ : Pf → List (List F) → Stmt shape27.L.stacking) (prf₁ prf₂ : Pf → Proof)
    (rd₁ rd₂ : Tab shape27.L → M)
    (sv sl sμ : ℕ) (sch : List (ℕ × ℕ)) (hsS : NewOK sv sl sμ sch) (hs1 : 24 ≤ sμ) (hs2 : sμ ≤ 26)
    (clS : Pf → List (List F) → Stmt (shapeS sv sl sμ sch hsS hs1 hs2).L.stacking)
    (prfS : Pf → Proof) (rootS : Pf → Bytes32) (q₀ : Column sμ)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (fix : Bytes32 → Pf → Pf)
    (hfix : ∀ s p, rootS (fix s p) = s)
    (A₀ : Bytes32 → OracleComp KeccakCalls Pf) (Q : ℕ) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q)
    (hQ64 : Q ≤ 2 ^ 64)
    (hg₁ : ∀ π ch (t : Tab shape27.L),
      (∀ cl ∈ (cl₁ π ch).claims, tabEval shape27.L t cl.point = cl.value) →
        good 0 π ch (some (rd₁ t)))
    (hg₂ : ∀ π ch (t : Tab shape27.L),
      (∀ cl ∈ (cl₂ π ch).claims, tabEval shape27.L t cl.point = cl.value) →
        good 1 π ch (some (rd₂ t)))
    (hS : ∀ π ch, (∀ cl ∈ (clS π ch).claims,
      (shapeS sv sl sμ sch hsS hs1 hs2).L.tableEval q₀ cl.point = cl.value) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → good i π ch cs[i]) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c) :
    Pr{let z ← (simulateQ randomOracle (expK K view
        (withSetupG (stackSetupS (shapeS sv sl sμ sch hsS hs1 hs2) q₀) fix A₀)
        (opsRun view (twoOps cl₁ cl₂ prf₁ prf₂ rd₁ rd₂ (shapeS sv sl sμ sch hsS hs1 hs2) clS prfS
          rootS q₀)))).run' ∅}[
        BreaksOK K (fun i => (exTC rd₁ rd₂ i).commit) R view check
          (fun bs => ∀ k < 3, bs.getD k false = true) z] ≤ (2 : ℝ≥0∞)⁻¹ ^ 62 := by
  refine (knowledgeSoundness_twoRoots K hK R herr view cl₁ cl₂ prf₁ prf₂ rd₁ rd₂ sv sl sμ sch hsS
    hs1 hs2 clS prfS rootS q₀ check good goodS fix hfix A₀ Q hQ hg₁ hg₂ hS hfit hlink).trans ?_
  -- Every count at most `X = 2^64 + 2^22 + 2^15`.
  have hq := largeQueries_le_26 sμ hs1 hs2
  have hs : 2 ^ (sμ - 4) ≤ 4194304 :=
    (Nat.pow_le_pow_right (by norm_num) (by omega) : 2 ^ (sμ - 4) ≤ 2 ^ 22).trans (by norm_num)
  have hQ' : Q ≤ 18446744073709551616 := hQ64.trans (by norm_num)
  -- `X = 2^64 + 2^22 + 2^15`.
  have b1 := openingBoundAt_le (QV := 8318) (QA := 2 ^ (sμ - 4) + Q + 6)
    (X := 18446744073713778688) (by omega)
  have b2 := openingBoundAt_le (QV := 8318) (QA := 2 ^ (sμ - 4) + Q + 6 + 8318)
    (X := 18446744073713778688) (by omega)
  have b3 := openingBoundAt_le (QV := largeQueries sμ) (QA := 2 ^ (sμ - 4) + Q + 6 + 8318 + 8318)
    (X := 18446744073713778688) (by omega)
  have b4 := listTerm_le (N := 2 ^ (sμ - 4) + Q + 6 + 8318 + 8318 + largeQueries sμ)
    (X := 18446744073713778688) (c := 4473 ^ 2 * 2 ^ 26 * 2 ^ 64)
    (m := ((4473 ^ 2 * 2 ^ 26 : ℕ) : ℝ≥0∞) / 2 ^ 192) (by omega) (le_of_eq (div_192_eq _))
  refine (add_le_add (add_le_add (add_le_add b1 b2) b3) b4).trans ?_
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  calc _ ≤ ((2 ^ 194 : ℕ) : ℝ≥0∞) / 2 ^ 256 := cast_div_le (by norm_num)
    _ = (2 : ℝ≥0∞)⁻¹ ^ 62 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 194 + 62 from rfl, two_pow_div_two_pow]

end Compose
