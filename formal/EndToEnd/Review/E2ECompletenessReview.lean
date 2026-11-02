-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import E2ECompleteness.Done
import Soundness.Final

/-!
# Review: `E2ECompleteness.completeness_end` (adversarial review of the completeness headline)

Not part of any library: checked with `lake env lean Review/E2ECompletenessReview.lean` from
`formal/EndToEnd` (h1, `review-cpl`, after `lake build E2ECompleteness Soundness.Final`). What it
checks:

1. **Axioms** of the end theorem and of every definition its statement names (`#print axioms`), and
   the statement as elaborated (`#print`).
2. **The statement's definitional closure** (`#review_sweep`, the sweep of `E2ESoundness.lean`):
   axioms, `opaque`, `@[implemented_by]`, `@[extern]` constants reachable from `Completeness`, the
   experiment, the prover, the coins and `deltaDeployed`.
3. **Non-vacuity of the statement**: `Relation` holds for every secret and its own statement
   (`relation_self`), so for an explicit secret (`w₀`); the experiment has no failure mass, so
   acceptance is at least `1 - deltaDeployed` (`accepted_ge`, `w₀_accepted`).
4. **The coins do not matter**: for **every** value of the coins (masks and both paddings), not only
   uniform ones, the experiment with those coins fixed is rejected with probability at most
   `deltaDeployed` (`completeness_every_coins`). So the uniform-coins model (the deployed prover
   derives its masks and padding by a Keccak-256 KDF and ChaCha12) changes nothing for completeness,
   as long as the coins are independent of `π`.
   The block count of the staged run is the docstring's exact `114 098 677 826 653 < 2^47`
   (`hcost_exact`; `hcost_deployed` states `2^48`).
5. **One verifier for both end theorems; knowledge soundness is not vacuous**: the honest prover,
   run as an adversary in the knowledge-soundness experiment (same setup, same verifier), is accepted
   with probability at least `1 - deltaDeployed` (`honest_accepted_in_soundness`; the chain of
   `E2ESoundness.lean`'s section 4, copied here since that file is in no library).
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

-- Never evaluate the membership circuit (a closed term of `2^22` rows).
attribute [local irreducible] PcsQuotient.membershipBuilder PcsQuotient.secretOfStack

open OracleSpec OracleComp
open scoped ENNReal

/-! ## 1. Axioms and the statement -/

/-- info: 'E2ECompleteness.completeness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_end

#print axioms PcsQuotient.Completeness
#print axioms PcsQuotient.completenessExperiment
#print axioms PcsQuotient.prover
#print axioms PcsQuotient.sampleCoins
#print axioms PcsQuotient.verifier
#print axioms PcsQuotient.setupWith
#print axioms PcsQuotient.Relation
#print axioms E2ECompleteness.deltaDeployed

#print PcsQuotient.Completeness
#print PcsQuotient.completenessExperiment
#print PcsQuotient.prover
#print PcsQuotient.sampleCoins
#print PcsQuotient.nonceFuel
#print E2ECompleteness.deltaDeployed
#print LeanVM.rpmError

-- The deployed WHIR's query grinding is 17 bits (`crates/pcs/src/whir_config.rs`:
-- `QUERY_GRINDING_BITS = 17`), the fuel `2^25`.
open LeanVM LeanVM.Parameters LeanVM.Protocol in
example : Whir.queryGrindingBits = 17 := rfl
example : PcsQuotient.nonceFuel = 2 ^ 25 := rfl

/-! ## 2. The definitional closure -/

namespace Review.E2ECompleteness

open Lean Elab Command

/-- The module a constant comes from (`current` for this file's). -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `current

/-- Lean's own modules (`Init`, `Std`, `Lean`, `Lake`). -/
def isCore (m : Name) : Bool :=
  m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean || m.getRoot == `Lake

/-- The constants a constant's type and (for a definition, an opaque, an inductive) body use; a
theorem's proof is not entered. -/
def depsOf (ci : ConstantInfo) : Array Name :=
  match ci with
  | .thmInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  | .ctorInfo v => v.type.getUsedConstants.push v.induct
  | .recInfo v => v.type.getUsedConstants
  | .axiomInfo v => v.type.getUsedConstants
  | .quotInfo v => v.type.getUsedConstants

/-- **The sweep** (as `E2ESoundness.lean`'s): the closure of the given constants through types and
definitions' bodies, with its axioms, opaques, `implemented_by` and `extern` constants, and whether
each root is `noncomputable`. -/
elab "#review_sweep " ids:ident* : command => do
  let env ← getEnv
  let roots := ids.map (·.getId)
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots
  let mut axs : Array Name := #[]
  let mut opq : Array Name := #[]
  let mut impl : Array (Name × Name) := #[]
  let mut ext : Array Name := #[]
  let mut nThm : Nat := 0
  let mut nAll : Nat := 0
  let mut fuel : Nat := 2000000
  while fuel > 0 do
    fuel := fuel - 1
    match todo.back? with
    | none => fuel := 0
    | some n =>
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      nAll := nAll + 1
      let some ci := env.find? n | continue
      if let some i := Lean.Compiler.getImplementedBy? env n then impl := impl.push (n, i)
      if Lean.isExtern env n then ext := ext.push n
      match ci with
      | .axiomInfo _ => axs := axs.push n
      | .opaqueInfo _ => opq := opq.push n
      | .thmInfo _ => nThm := nThm + 1
      | _ => pure ()
      for d in depsOf ci do
        unless seen.contains d do todo := todo.push d
  let nonCore (n : Name) : Bool := !isCore (moduleOf env n)
  logInfo m!"roots: {roots}\nconstants reached: {nAll} ({nThm} theorems, proofs not entered)\naxioms: {axs}\nopaque outside core: {(opq.filter nonCore).map fun n => (n, moduleOf env n)}\nopaque in core: {(opq.filter (!nonCore ·)).size}\nimplemented_by outside core: {(impl.filter (nonCore ·.1)).map fun p => (p.1, p.2, moduleOf env p.1)}\nimplemented_by in core: {(impl.filter (!nonCore ·.1)).size}\nextern outside core: {(ext.filter nonCore).map fun n => (n, moduleOf env n)}\nextern in core: {(ext.filter (!nonCore ·)).size}\nnoncomputable roots: {roots.filter (Lean.isNoncomputable env ·)}"

end Review.E2ECompleteness

#review_sweep PcsQuotient.Completeness E2ECompleteness.deltaDeployed
#review_sweep PcsQuotient.prover PcsQuotient.sampleCoins PcsQuotient.Relation

namespace Review.E2ECompleteness

open PcsQuotient Common

/-! ## 3. Non-vacuity of the statement -/

/-- **`Relation` is satisfiable**: every secret is a witness of its own statement. -/
theorem relation_self (w : Secret) : Relation w.statement w := rfl

/-- An explicit secret: `x = 0^32`, every sibling `0^32`, every direction `false`. -/
def w₀ : Secret :=
  ⟨Vector.replicate 32 0, Vector.replicate depth (Vector.replicate 32 0), Vector.replicate depth false⟩

/-- **No failure mass**: the honest proof is accepted with probability at least `1 - δ`. -/
theorem accepted_ge (stmt : Statement) (w : Secret) (hrel : Relation stmt w) :
    1 - E2ECompleteness.deltaDeployed ≤ Pr{let v ← completenessExperiment stmt w}[v = true] := by
  have hδ := E2ECompleteness.completeness_end stmt w hrel
  have hf : Pr{let v ← completenessExperiment stmt w}[v = false] =
      1 - Pr{let v ← completenessExperiment stmt w}[v = true] := by
    have := prEvent_not_eq_one_sub (completenessExperiment stmt w) (fun v => v = true)
    simpa using this
  rw [hf] at hδ
  exact tsub_le_iff_tsub_le.mp hδ

/-- **An explicit instance**: `w₀`'s statement, honestly proved, is accepted with probability at
least `1 - deltaDeployed > 1 - 2^-162`. -/
theorem w₀_accepted :
    1 - E2ECompleteness.deltaDeployed ≤ Pr{let v ← completenessExperiment w₀.statement w₀}[v = true] :=
  accepted_ge _ _ (relation_self w₀)

theorem one_sub_delta_pos : 0 < 1 - E2ECompleteness.deltaDeployed := by
  have h := E2ECompleteness.deltaDeployed_lt
  have h1 : (2 : ℝ≥0∞)⁻¹ ^ 162 < 1 := pow_lt_one₀ (by simp) (by
    rw [ENNReal.inv_lt_one]; norm_num) (by norm_num)
  exact tsub_pos_of_lt (h.trans h1)

end Review.E2ECompleteness

/-! ## 4. Every value of the coins -/

namespace Review.E2ECompleteness

open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open LeanVM.Prover (Tree findNonceM powStepM Script)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open _root_.E2ECompleteness
open Common (runWithRandomPermutation queryPermutation lazyRandomPermutationOracles)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-- `RejectGood` (`Grinding.lean`'s `rejectGood_of_tail`, copied) for **any** coins, not only those
of raw words: in the two-call random-oracle model the staged run with these coins is rejected at
non-degenerate challenges with probability at most `3 · 2^-277`. -/
theorem rejectGood_coins (stmt : Statement) (w : Secret) (hrel : Relation stmt w)
    (coins : Masks × Padding × Padding) :
    Pr{let z ← (simulateQ ro (stagedRun stmt w coins)).run' ∅}[
      z.1 = false ∧ z.2 ∉ badSet w coins.1] ≤ 3 * (2 : ℝ≥0∞)⁻¹ ^ 277 := by
  have hacc := tailAccepts constants claimsMatch circuitMatch tablesMatch
  have hred := tailReduces constants claimsMatch circuitMatch tablesMatch
  have hfuel : nonceFuel ≤ 2 ^ 64 := by norm_num [nonceFuel]
  have hfuel0 : nonceFuel ≠ 0 := by norm_num [nonceFuel]
  have hstep : LogFreshStepBound (powPot Whir.queryGrindingBits nonceFuel)
      (missProb Whir.queryGrindingBits ^ nonceFuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF (by decide) (by decide) hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have e : Pr{let z ← (simulateQ ro (stagedRun stmt w coins)).run' ∅}[
      z.1 = false ∧ z.2 ∉ badSet w coins.1] =
      Pr{let z ← (simulateQ loggedRO (stagedRun stmt w coins)).run []}[
        z.1.1 = false ∧ z.1.2 ∉ badSet w coins.1] := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_run_randomOracle_eq_loggedRO _
      (fun (z : Bool × (E × E × E)) _ ↦ z.1 = false ∧ z.2 ∉ badSet w coins.1)
  rw [e]
  refine (prEvent_run_loggedRO_le_of_freshStepBound hstep _ (2 ^ 48)
    (isTotalQueryBound_of_queryCostAtMost (hcost_deployed stmt w coins)) []
    (fun (z : Bool × (E × E × E)) _ ↦ z.1 = false ∧ z.2 ∉ badSet w coins.1)
    fun z hz hev ↦ ?_).trans ?_
  · have hlook := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
    exact one_le_powPot_of_rejected _ _ _ _ _ _ _ _ _ hfuel hfuel0
      (hacc stmt w hrel coins) (hred stmt w hrel coins) hlook hev.1 hev.2
  · rw [powPot_nil, zero_add]
    calc ((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ nonceFuel
        ≤ (2 : ℝ≥0∞)⁻¹ ^ 304 := grinding_le
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 277 := inv_pow_le_inv_pow (by norm_num)
      _ ≤ 3 * (2 : ℝ≥0∞)⁻¹ ^ 277 := le_mul_of_one_le_left bot_le (by norm_num)

/-- The staged run with fixed coins, in the random-permutation model: rejected with probability at
most `deltaDeployed` (`End.lean`'s `prEvent_run_false_le`, its pieces at fixed coins). -/
theorem reject_rpm_coins (stmt : Statement) (w : Secret) (hrel : Relation stmt w)
    (coins : Masks × Padding × Padding) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation (stagedRun stmt w coins)).run' []}[
      z.1 = false] ≤ deltaDeployed := by
  refine rpm_le_rom (stagedRun stmt w coins) (duplexVm_stagedRun stmt w coins)
    (hcost_deployed stmt w coins) (fun z ↦ z.1 = false) ?_
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _
    (fun z : Bool × (E × E × E) ↦ z.2 ∈ badSet w coins.1)).trans ?_
  refine add_le_add ?_ (rejectGood_coins stmt w hrel coins)
  have hc : Pr{let z ← (simulateQ ro (stagedRun stmt w coins)).run' ∅}[z.2 ∈ badSet w coins.1] =
      Pr{let z ← (simulateQ ro (stagedRun stmt w coins)).run ∅}[z.1.2 ∈ badSet w coins.1] := by
    rw [StateT.run'_eq, prEvent_map]
  rw [hc]
  refine (prEvent_staged_le _ challengeOf_regular _ _ _ _
    (hashOK_stageAG _ hashOK_setupWithH _ _ _ _ _)
    (fun a s₁ s₂ s₃ ↦ hashOK_stageBG _ _ _ a s₁ s₂ s₃) ∅ fun m hm ↦ absurd rfl hm).trans ?_
  rw [add_comm]
  exact add_le_add (badSet_density w coins.1) le_rfl

/-- **The completeness experiment with the coins fixed** (the Statement's, with `sampleCoins`
replaced by `coins`). -/
noncomputable def experimentAt (stmt : Statement) (w : Secret) (coins : Masks × Padding × Padding) :
    ProbComp Bool :=
  runWithRandomPermutation do
    let indexRoot ← setupWith queryPermutation
    match ← prover queryPermutation stmt w coins with
    | none => return false
    | some proof => verifier queryPermutation indexRoot stmt proof

theorem experimentAt_eq (stmt : Statement) (w : Secret) (coins : Masks × Padding × Padding) :
    experimentAt stmt w coins = (fun z ↦ z.1) <$>
      (simulateQ keccakCallsOverRandomPermutation (stagedRun stmt w coins)).run' [] := by
  have h : experimentAt stmt w coins =
      runWithRandomPermutation (setupWith queryPermutation >>= fun idx ↦ body stmt w idx coins) :=
    rfl
  rw [h, runWithRandomPermutation, experimentBody_eq,
    simulateQ_lazy_keccakCallsOverQueryPermutation, expH_eq_staged, simulateQ_map, StateT.run'_eq,
    StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

/-- **Completeness for every value of the coins**: whatever the masks and the two paddings (uniform,
ChaCha12's, a constant), the honest proof is rejected with probability at most `deltaDeployed` over
the random permutation. -/
theorem completeness_every_coins (stmt : Statement) (w : Secret) (hrel : Relation stmt w)
    (coins : Masks × Padding × Padding) :
    Pr{let v ← experimentAt stmt w coins}[v = false] ≤ deltaDeployed := by
  rw [experimentAt_eq, prEvent_map]
  exact reject_rpm_coins stmt w hrel coins

/-- The all-zero coins (masks `0`, padding `0`): still complete. -/
theorem completeness_zero_coins (stmt : Statement) (w : Secret) (hrel : Relation stmt w) :
    Pr{let v ← experimentAt stmt w (fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ _ ↦ 0)}[v = false] ≤
      deltaDeployed :=
  completeness_every_coins stmt w hrel _

end Review.E2ECompleteness

/-! ## 4b. The block count, as the docstring states it -/

namespace Review.E2ECompleteness

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open PcsQuotient _root_.E2ECompleteness _root_.E2ECompleteness.Cost

/-- **The deployed staged run makes at most `114 098 677 826 653 < 2^47` block calls** (`Cost.lean`'s
docstring; its theorem `hcost_deployed` states `2^48`). -/
theorem hcost_exact :
    ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) LeanVM.Rpm.hashBlocks
      114098677826653 := by
  intro stmt w coins
  have hm : (membership logRows).logRows = 22 := rfl
  refine (cost_stagedRunG _ _ cost_setupWithH (membership logRows) (by rw [hm]; decide)
    (cellsOf w) coins.1 coins.2.1 coins.2.2 nonceFuel logRows (by decide) stmt).mono ?_
  rw [hm]
  norm_num [treeCost, proverCost, verifierCost, vOpen, blockFactor, whirBound, costHeight,
    nonceFuel, cellVars]

example : (114098677826653 : ℕ) < 2 ^ 47 := by norm_num

end Review.E2ECompleteness

/-! ## 5. One verifier; the honest prover in the knowledge-soundness experiment -/

namespace Review.E2ECompleteness

open PcsQuotient Common

/-- The setup's root is its tree's root (`E2ESoundness.lean`'s `setupWith_eq`). -/
theorem setupWith_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) :
    setupWith F = (fun t => t.root) <$> setupTreeWith F := by
  unfold setupWith setupTreeWith Circuit.indexRootWith Circuit.indexTreeWith
  rw [map_eq_bind_pure_comp]
  rfl

theorem fst_run_logged {α : Type} (A : OracleComp RandomPermutationOracles α) :
    ∀ log : OracleQueryLog, Prod.fst <$> (simulateQ loggedOracles A).run log = A := by
  induction A using OracleComp.inductionOn with
  | pure x => intro log; simp
  | query_bind t k ih =>
    intro log
    simp [loggedOracles, ih]

/-- The honest adversary: the Statement's prover with uniform coins, ignoring the commitment. -/
noncomputable def honestAdversary (stmt : Statement) (w : Secret) (dflt : Proof) : Adversary :=
  fun _ => do
    let coins ← sampleCoins
    let r ← prover queryPermutation stmt w coins
    return (stmt, r.getD dflt)

noncomputable def prefixH (stmt : Statement) (w : Secret) :
    OracleComp RandomPermutationOracles (LeanVM.Prover.Tree × Option Proof) :=
  setupTreeWith queryPermutation >>= fun t =>
    sampleCoins >>= fun c => prover queryPermutation stmt w c >>= fun r => pure (t, r)

noncomputable def contC (stmt : Statement) (a : LeanVM.Prover.Tree × Option Proof) :
    OracleComp RandomPermutationOracles Bool :=
  match a.2 with
  | none => pure false
  | some proof => verifier queryPermutation a.1.root stmt proof

theorem run'_map {β γ : Type} (V : OracleComp RandomPermutationOracles β) (g : β → γ)
    (s : PermutationEdges LeanVM.Semantics.KeccakState) :
    (simulateQ lazyRandomPermutationOracles (g <$> V)).run' s =
      g <$> (simulateQ lazyRandomPermutationOracles V).run' s := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Functor.map_map]

theorem accepted_eq (A : Adversary) :
    Pr{let z ← soundnessExperiment A}[z.accepted] =
      Pr{let b ← runWithRandomPermutation (setupTreeWith queryPermutation >>= fun t =>
          A t.root >>= fun z => verifier queryPermutation t.root z.1 z.2)}[b = true] := by
  have h1 : soundnessExperiment A = runWithRandomPermutation
      (setupTreeWith queryPermutation >>= fun t =>
        (simulateQ loggedOracles (A t.root)).run [] >>= fun p =>
          verifier queryPermutation t.root p.1.1 p.1.2 >>= fun acc =>
            pure (((p.1, acc), Tree.evaluations t, p.2) : Outcome)) := rfl
  have h2 : (setupTreeWith queryPermutation >>= fun t =>
        A t.root >>= fun z => verifier queryPermutation t.root z.1 z.2) =
      (fun z : Outcome => z.1.2) <$> (setupTreeWith queryPermutation >>= fun t =>
        (simulateQ loggedOracles (A t.root)).run [] >>= fun p =>
          verifier queryPermutation t.root p.1.1 p.1.2 >>= fun acc =>
            pure (((p.1, acc), Tree.evaluations t, p.2) : Outcome)) := by
    simp only [map_bind, map_pure]
    congr 1
    funext t
    conv_lhs => rw [← fst_run_logged (A t.root) []]
    rw [bind_map_left]
    simp only [bind_pure]
  rw [h1, h2]
  unfold runWithRandomPermutation
  rw [run'_map, prEvent_map]

theorem completeness_eq (stmt : Statement) (w : Secret) :
    completenessExperiment stmt w = runWithRandomPermutation (prefixH stmt w >>= fun a =>
      contC stmt a >>= fun v => pure v) := by
  unfold completenessExperiment prefixH contC
  rw [setupWith_eq]
  simp only [bind_map_left, bind_assoc, pure_bind, bind_pure]
  rfl

theorem honest_eq (stmt : Statement) (w : Secret) (dflt : Proof) :
    (setupTreeWith queryPermutation >>= fun t =>
        honestAdversary stmt w dflt t.root >>= fun z => verifier queryPermutation t.root z.1 z.2) =
      prefixH stmt w >>= fun a =>
        verifier queryPermutation a.1.root stmt (a.2.getD dflt) >>= fun v => pure v := by
  unfold honestAdversary prefixH
  simp only [bind_assoc, pure_bind, bind_pure]

theorem honest_accepted_ge (stmt : Statement) (w : Secret) (dflt : Proof) :
    Pr{let v ← completenessExperiment stmt w}[v = true] ≤
      Pr{let z ← soundnessExperiment (honestAdversary stmt w dflt)}[z.accepted] := by
  rw [accepted_eq, honest_eq, completeness_eq]
  refine Soundness.prEvent_le_of_continuations (prefixH stmt w) (contC stmt)
    (fun a => verifier queryPermutation a.1.root stmt (a.2.getD dflt))
    (fun _ v => v) (fun _ v => v) (· = true) (· = true) fun a s => ?_
  rcases a with ⟨t, _ | p⟩
  · exact le_of_eq_of_le (Soundness.zero_pure lazyRandomPermutationOracles false (· = true)
      Bool.false_ne_true s) bot_le
  · exact le_rfl

/-- **Knowledge soundness is not vacuous**: the honest prover of a true statement, run as an
adversary in `soundnessExperiment` (the same setup and verifier as `completenessExperiment`), is
accepted with probability at least `1 - deltaDeployed`. -/
theorem honest_accepted_in_soundness (stmt : Statement) (w : Secret) (hrel : Relation stmt w)
    (dflt : Proof) :
    1 - E2ECompleteness.deltaDeployed ≤
      Pr{let z ← soundnessExperiment (honestAdversary stmt w dflt)}[z.accepted] :=
  (accepted_ge stmt w hrel).trans (honest_accepted_ge stmt w dflt)

end Review.E2ECompleteness

/-- info: 'Review.E2ECompleteness.w₀_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Review.E2ECompleteness.w₀_accepted

/-- info: 'Review.E2ECompleteness.completeness_every_coins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Review.E2ECompleteness.completeness_every_coins

/-- info: 'Review.E2ECompleteness.hcost_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Review.E2ECompleteness.hcost_exact

/-- info: 'Review.E2ECompleteness.honest_accepted_in_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Review.E2ECompleteness.honest_accepted_in_soundness

/-! The explicit instance's statement, computed (interpreted Keccak-256, 33 hashes). -/
#eval (Review.E2ECompleteness.w₀.statement.y.toList, Review.E2ECompleteness.w₀.statement.root.toList)
