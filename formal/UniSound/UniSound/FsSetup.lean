-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows
-- `formal/EndToEnd/Soundness/TreeLog.lean` (`loggedKC_stackSetup`), `Soundness/Final.lean`
-- (`setupTree_eq`) and `Bridge/Setup.lean` (`commitWith_eq`) of this repository, for three trees.
import UniSound.FsWalk
import Bridge.Setup

/-!
# The setup bridge: the composed setup, logged, is the Statement's

**`uniSetupBridge`**: `UniSetupBridge D hs` (`FsCouple.lean`) for every deployment whose setup
stack has fewer than `256` variables (`hv`; `uniSetupBridge_of_small` from `FinalLink.lean`'s
`LayoutVarsSmall`). The composed setup (`uSetup`: the three trees of `stackSetupS` at the plain
shapes of the layout words' variables `wv D 2`, `wv D 3`, `wv D 4`), logged and answered over `π`,
is the Statement's `setupTreesWith π D`, its roots as bytes and its log the trees' evaluations.

* **One tree** (`simulateQ_loggedKC_stackSetupS`): the logged setup of `colOf a v` at the plain
  shape of `2^v` words is `PcsQuotient.commitWith π v a`'s tree, its root as bytes and its log
  `Soundness.treeTr` (TreeLog's `loggedKC_buildTree`, mumbai's `simulateQ_buildTreeM`; the
  Statement's NTT word is `stackWord` of `columnOf v a = colOf a v`, `Bridge.Setup.commitWith_eq`).
* **Three trees** (`loggedKC_bind`, `run_logImplKC`): logging a bind logs the first computation,
  then the second with its log appended.
* **The variables** (`wv_two`, `wv_three`, `wv_four`): the setup's layout word names the setup
  layout's variables (`layoutsOf`'s setup entry does not depend on `C2`'s columns, so it is
  `setupLayout`'s), `A0`'s and `B0`'s name `matrixVars`. `commitWith`'s `ℕ` argument is not
  dependent: the trees are rewritten after the setups are replaced by their commitments.

## Why the hypothesis `hv`

A layout word carries its stack's variables in one byte (`layoutWord`: `vars.toUInt8`), so
`wv D 2 = (setupLayout D.shape).vars % 256`. `UniShapes D` bounds this residue (`24 … 28`), not the
variables: nothing in `Deployment` bounds `logMemory` (`Shape.validate` checks only `1 ≤ logMemory`
and the heights), and the setup layout has `logMemory + 1` variables once `logMemory` exceeds
`logBytecode + 4`. The valid shape `⟨279, 1, [7, 7, 7, 7, 7, 7]⟩` (a program of `2` instructions)
has stacks of `282`, `284`, `280` variables (`C1`, `C2`, the setup; `#eval`, not in the build), so
its five words name `26, 28, 24, 28, 28` variables and `UniShapes` holds: `uSetup` commits the
setup stack at `24` variables (a tree of height `19`) while `setupTreesWith` commits it at `280`
(height `275`), and the two logs have different lengths. So `UniSetupBridge D hs` is false for such
a deployment; it holds when the setup layout's variables fit the byte,
`(setupLayout D.shape).vars < 256`, which `LayoutVarsSmall D` (already a hypothesis of `uniFinal`
and of the end theorem `uniKnowledgeSoundness_code`) implies.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## One tree -/

/-- **The logged setup of one plain tree**, answered over `π`, is the Statement's WHIR commitment
(`PcsQuotient.commitWith`) of the array, its root as bytes and its log the tree's evaluations. -/
theorem simulateQ_loggedKC_stackSetupS (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) (a : Array K) :
    simulateQ keccakCallsOverQueryPermutation
        (loggedKC (stackSetupS (plainShape v h1 h2) (colOf a v))) =
      (fun t : LeanVM.Prover.Tree => (toB t.root, Soundness.treeTr t)) <$>
        PcsQuotient.commitWith Common.queryPermutation v a := by
  unfold stackSetupS wiringSetup
  rw [Soundness.loggedKC_map, Soundness.loggedKC_buildTree,
    Functor.map_map, simulateQ_map, LeanVM.Protocol.Compile.simulateQ_buildTreeM,
    Bridge.Setup.commitWith_eq Common.queryPermutation v (by omega) (by omega) a]
  rfl

/-! ## Logging a bind -/

/-- **Logging from a log** appends to it the log from the empty one. -/
theorem run_logImplKC {α : Type} (oa : OracleComp KeccakCalls α) :
    ∀ l : Transcript, (simulateQ logImplKC oa).run l =
      (fun q => (q.1, l ++ q.2)) <$> (simulateQ logImplKC oa).run [] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro l; simp
  | query_bind t k ih =>
    intro l
    rw [loggedKC_run_query_bind, loggedKC_run_query_bind, map_bind]
    refine bind_congr fun u => ?_
    rw [ih u (l ++ (inlEntry ⟨t, u⟩).toList), ih u ([] ++ (inlEntry ⟨t, u⟩).toList),
      Functor.map_map]
    simp only [List.nil_append, List.append_assoc]

/-- **Logging a bind**: the first computation's log, then the second's appended. -/
theorem loggedKC_bind {α β : Type} (oa : OracleComp KeccakCalls α)
    (f : α → OracleComp KeccakCalls β) :
    loggedKC (oa >>= f) =
      loggedKC oa >>= fun p => (fun q => (q.1, p.2 ++ q.2)) <$> loggedKC (f p.1) := by
  unfold loggedKC
  rw [logImplKC_bind]
  exact bind_congr fun p => run_logImplKC (f p.1) p.2

theorem loggedKC_pure {α : Type} (a : α) :
    loggedKC (pure a : OracleComp KeccakCalls α) = pure (a, []) := by
  simp [loggedKC]

/-! ## The variables -/

/-- `layoutsOf`'s setup entry is `setupLayout`'s (it does not depend on `C2`'s columns). -/
theorem layoutOf_setup (s : UniStatement.Shape) :
    layoutOf (layoutsOf s) .setup = setupLayout s := rfl

/-- **The setup's layout word names the setup layout's variables**, when they fit its byte. -/
theorem wv_two (D : Deployment) (hv : (setupLayout D.shape).vars < 256) :
    wv D 2 = (setupLayout D.shape).vars := by
  rw [wv_eq, show (2 : ℕ) = wordIndex Commitment.setup from rfl, layoutWords_word,
    layoutOf_setup, layoutWordVars_layoutWord _ _ _ _ hv]

theorem wv_three (D : Deployment) : wv D 3 = matrixVars := by
  rw [wv_eq]
  exact (matrixWordVars D.shape).1

theorem wv_four (D : Deployment) : wv D 4 = matrixVars := by
  rw [wv_eq]
  exact (matrixWordVars D.shape).2

/-! ## The setup bridge -/

/-- **SETUP** (`UniSetupBridge`), for a setup stack of fewer than `256` variables (`hv`: the layout
word's byte; without it the statement fails, see the module docstring): the composed setup over
`π`, logged, is the Statement's `setupTreesWith` over `π`, its roots as bytes and its log the
trees' evaluations. -/
theorem uniSetupBridge (D : Deployment) (hs : UniShapes D)
    (hv : (setupLayout D.shape).vars < 256) : UniSetupBridge D hs := by
  have e2 : simulateQ keccakCallsOverQueryPermutation
      (loggedKC (stackSetupS (shapeK hs 2 (by decide)) (colF D))) =
        (fun t : LeanVM.Prover.Tree => (toB t.root, Soundness.treeTr t)) <$>
          PcsQuotient.commitWith Common.queryPermutation (wv D 2) (setupStack D.prog D.shape) :=
    simulateQ_loggedKC_stackSetupS (wv D 2) (hs.lo 2 (by decide)) (hs.hi 2 (by decide)) _
  have e3 : simulateQ keccakCallsOverQueryPermutation
      (loggedKC (stackSetupS (shapeK hs 3 (by decide)) (colA D))) =
        (fun t : LeanVM.Prover.Tree => (toB t.root, Soundness.treeTr t)) <$>
          PcsQuotient.commitWith Common.queryPermutation (wv D 3) (flockMatrixStack true) :=
    simulateQ_loggedKC_stackSetupS (wv D 3) (hs.lo 3 (by decide)) (hs.hi 3 (by decide)) _
  have e4 : simulateQ keccakCallsOverQueryPermutation
      (loggedKC (stackSetupS (shapeK hs 4 (by decide)) (colB D))) =
        (fun t : LeanVM.Prover.Tree => (toB t.root, Soundness.treeTr t)) <$>
          PcsQuotient.commitWith Common.queryPermutation (wv D 4) (flockMatrixStack false) :=
    simulateQ_loggedKC_stackSetupS (wv D 4) (hs.lo 4 (by decide)) (hs.hi 4 (by decide)) _
  unfold UniSetupBridge uSetup setupK3
  simp only [loggedKC_bind, loggedKC_pure, simulateQ_bind, simulateQ_map, simulateQ_pure]
  rw [e2, e3, e4, wv_two D hv, wv_three D, wv_four D]
  unfold setupTreesWith
  simp only [map_bind, map_pure, bind_map_left]
  refine bind_congr fun f => bind_congr fun a => bind_congr fun b => ?_
  simp only [rootsB, setupTr, SetupTrees.evaluations, Soundness.treeTr, List.map_append,
    List.append_nil, List.append_assoc]

/-- **SETUP** under `LayoutVarsSmall` (`FinalLink.lean`, a hypothesis of `uniFinal`). -/
theorem uniSetupBridge_of_small (D : Deployment) (hs : UniShapes D)
    (hsmall : LayoutVarsSmall D) : UniSetupBridge D hs :=
  uniSetupBridge D hs (layoutOf_setup D.shape ▸ hsmall .setup)

end UniSound

/-- info: 'UniSound.uniSetupBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniSetupBridge

/-- info: 'UniSound.uniSetupBridge_of_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniSetupBridge_of_small
