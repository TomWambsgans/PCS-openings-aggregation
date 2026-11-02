-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.RpmV
import Soundness.TreeLog
import Soundness.Extract
import Soundness.EarlyStop
import Bridge.Facts

/-!
# Knowledge soundness of the deployed membership proof

**`knowledgeSoundness : PcsQuotient.KnowledgeSoundness ksBound`**: the end statement of
`formal/Statement` (`PcsQuotient/Security.lean`), for the Statement's own extractor
(`PcsQuotient.extractor`: the setup tree's and the adversary's Keccak-256 evaluations, the witness
tree inverted, the word list-decoded, a candidate's input bits read as a secret satisfying the
relation), its own experiment (the setup over `π`, the adversary with its queries logged, the
verifier over `π`), with no hypothesis, at the bound `ksBound Q` (`RpmV.lean`): for an adversary of
at most `Q` calls of `π`, `π⁻¹`,

`ksBound Q = Σ_{i<3} openingBound (2^21 + Q + 6 + i · 10122) + N (2^-128 + 5 N / 2^256)
  + (2^52 + Q + (6 + 3 · 10122) · 2^32)² / 2^508`, `N = 2^21 + Q + 6 + 3 · 10122`,

`openingBound x = (x + 10122) (2^-128 + 5 (x + 10122) / 2^256)`: about `2^-62` for `Q ≤ 2^64`.

**The proof.** The Statement's experiment and Compose's random-permutation game (`rpmGame`, with
the Statement's adversary converted, `convAdv`) run the same setup (`setupTree_eq`: the Statement's
`setupTreeWith` is Compose's `stackSetup` of the wiring stack, `SetupBridge`) and the same adversary;
they differ only in the verifier, run last on the same state of the lazily sampled permutation
(`prEvent_le_of_continuations`). There, for each outcome of the setup and the adversary
(`step_le`):

* if the Statement's extractor finds a secret of the statement, the Statement's event fails;
* if the proof's roots are not digests, the Statement's verifier rejects (`verifier_malformed`);
* otherwise it is the composed verifier with early stops (`VerifierBridge`), which accepts at most
  as often as Compose's (`es_le`), and Compose's extractor's list holds no witness, or the
  Statement's extractor would find a secret (`extractor_of_mem`, with `ReadsSecret`).

Then Compose's theorem at the deployed claim maps (`knowledgeSoundness_rust_rpm`). The constants
are the Statement's (`Bridge.statementConsts`: `Domain.betaAt`, `Domain.rowVanishing 24`), a Cantor
basis and `row_vanishing`'s solution by the kernel (`isCantor_statementConsts`,
`rowVanishing_statementConsts`); the three bridge facts are `formal/EndToEnd/Bridge`'s.
-/

set_option linter.unusedSectionVars false
set_option simprocs false

open OracleSpec OracleComp
open scoped ENNReal

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge

/-! ## The experiments, a common prefix then the verifier -/

/-- **A comparison of the verifiers, run last, survives the common prefix** of two games against
the lazily sampled permutation. -/
theorem prEvent_le_of_continuations {α β₁ β₂ γ₁ γ₂ : Type}
    (X : OracleComp Common.RandomPermutationOracles α)
    (V₁ : α → OracleComp Common.RandomPermutationOracles β₁)
    (V₂ : α → OracleComp Common.RandomPermutationOracles β₂)
    (g₁ : α → β₁ → γ₁) (g₂ : α → β₂ → γ₂) (P₁ : γ₁ → Prop) (P₂ : γ₂ → Prop)
    (h : ∀ a s, Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (V₁ a)).run' s}[
        P₁ (g₁ a v)] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (V₂ a)).run' s}[P₂ (g₂ a v)]) :
    Pr{let z ← Common.runWithRandomPermutation (X >>= fun a => V₁ a >>= fun v => pure (g₁ a v))}[
        P₁ z] ≤
      Pr{let z ← Common.runWithRandomPermutation (X >>= fun a => V₂ a >>= fun v => pure (g₂ a v))}[
        P₂ z] := by
  unfold Common.runWithRandomPermutation
  refine mono_bind _ X _ _ _ _ (fun a s => ?_) []
  have e : ∀ {β γ : Type} (V : OracleComp Common.RandomPermutationOracles β) (g : β → γ),
      (simulateQ Common.lazyRandomPermutationOracles (V >>= fun v => pure (g v))).run' s =
        g <$> (simulateQ Common.lazyRandomPermutationOracles V).run' s := by
    intro β γ V g
    have hm : (V >>= fun v => pure (g v)) = g <$> V := by
      rw [map_eq_bind_pure_comp]
      rfl
    rw [hm, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map,
      Functor.map_map, Functor.map_map]
  rw [e, e, prEvent_map, prEvent_map]
  exact h a s

/-! ## The constants, the instance, the wire, the setup -/

/-- The Statement's constants (`Bridge.statementConsts`). -/
noncomputable abbrev cS : Consts := Bridge.statementConsts

/-- F1's instance at the Statement's constants. -/
noncomputable abbrev iS : Instance E := inst cS Bridge.isCantor_statementConsts

/-- The deployed wire for it. -/
noncomputable abbrev wS : Wire iS.params iS.bounds := deployedWire iS

/-- The deployed openings at the Statement's constants. -/
noncomputable abbrev dS : Deploy E := deployD cS 22

theorem hβ_iS : ∀ k < 22 + 2, iS.basis.β k = ofK (cS.beta k) := fun _ _ => rfl

theorem hc_iS : ∀ k < 8, coordinateWeight k = some (iS.c k) := coordinateWeight_eq

theorem matches_iS : Matches iS.params cS 22 :=
  matches_params iS cS hβ_iS hc_iS Bridge.rowVanishing_statementConsts

/-- The setup's tree, as Compose's setup computes it. -/
noncomputable abbrev buildS (q₀ : Column dS.Lσ.logN) :
    OracleComp KeccakCalls LeanVM.Prover.Tree :=
  LeanVM.Prover.buildTreeWithHash callKeccak256 (rootHeight dS.Lσ.logN dS.R)
    (LeanVM.Protocol.Whir.Complete.stackWord dS.Lσ.logN q₀)

/-- **The Statement's setup is Compose's**: its tree over `π` is the stack setup's tree of the
wiring stack `q₀` whose words are the Statement's wiring table. -/
theorem setupTree_eq (q₀ : Column dS.Lσ.logN)
    (hq : q₀.values.toArray = (PcsQuotient.membership PcsQuotient.logRows).wiringTable) :
    PcsQuotient.setupTreeWith (m := OracleComp Common.RandomPermutationOracles)
        Common.queryPermutation = simulateQ keccakCallsOverQueryPermutation (buildS q₀) := by
  unfold PcsQuotient.setupTreeWith PcsQuotient.Circuit.indexTreeWith PcsQuotient.commitWith
  have hs : LeanVM.Prover.stackWordFast (22 + 2) 1 q₀.values.toArray =
      LeanVM.Protocol.Whir.Complete.stackWord (22 + 2) q₀ :=
    LeanVM.Prover.Enc.stackWordFast_eq (by decide) 1 q₀
  rw [membership_logRows, ← hq, hs, LeanVM.Prover.buildTreeM_eq_withHash, simulateQ_buildTreeM]
  rfl

theorem simulateQ_loggedSetup (q₀ : Column dS.Lσ.logN) :
    simulateQ keccakCallsOverQueryPermutation (loggedKC (stackSetup dS q₀)) =
      (fun t => (toB t.root, treeTr t)) <$> simulateQ keccakCallsOverQueryPermutation (buildS q₀) := by
  rw [loggedKC_stackSetup, simulateQ_map]

theorem run_loggedConvAdv (A : PcsQuotient.Adversary) (ir : Bytes32) :
    (simulateQ Common.loggedOracles (convAdv A ir)).run [] =
      (fun p => (convP p.1, p.2)) <$> (simulateQ Common.loggedOracles A).run [] := by
  rw [convAdv, simulateQ_map, StateT.run_map]

/-! ## The two experiments -/

/-- The common prefix: the setup's tree, then the adversary with its queries logged. -/
noncomputable def prefixS (q₀ : Column dS.Lσ.logN) (A : PcsQuotient.Adversary) :
    OracleComp Common.RandomPermutationOracles
      (LeanVM.Prover.Tree × ((PcsQuotient.Statement × PcsQuotient.Proof) × Common.OracleQueryLog)) :=
  simulateQ keccakCallsOverQueryPermutation (buildS q₀) >>= fun t =>
    (simulateQ Common.loggedOracles A).run [] >>= fun p => pure (t, p)

theorem soundnessExperiment_eq (q₀ : Column dS.Lσ.logN)
    (hq : q₀.values.toArray = (PcsQuotient.membership PcsQuotient.logRows).wiringTable)
    (A : PcsQuotient.Adversary) :
    PcsQuotient.soundnessExperiment A = Common.runWithRandomPermutation (prefixS q₀ A >>= fun a =>
      PcsQuotient.verifier Common.queryPermutation a.1.root a.2.1.1 a.2.1.2 >>= fun acc =>
        pure (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2) : PcsQuotient.Outcome)) := by
  unfold PcsQuotient.soundnessExperiment prefixS
  rw [setupTree_eq q₀ hq]
  simp only [bind_assoc, pure_bind]

theorem rpmGame_eq (q₀ : Column dS.Lσ.logN) (A : PcsQuotient.Adversary) :
    Common.runWithRandomPermutation (rpmGame wS dS (stackSetup dS q₀) (convAdv A)) =
      Common.runWithRandomPermutation (prefixS q₀ A >>= fun a =>
        simulateQ keccakCallsOverQueryPermutation
          (verifyD wS dS (withIr (toB a.1.root) (convP a.2.1))) >>= fun v =>
          pure ((withIr (toB a.1.root) (convP a.2.1), v), treeTr a.1, a.2.2)) := by
  unfold rpmGame prefixS
  rw [simulateQ_loggedSetup q₀]
  simp only [run_loggedConvAdv, bind_map_left, bind_assoc, pure_bind]

/-! ## The verifiers, outcome by outcome -/

/-- Compose's extractor reads the proof's first root only, not the commitment `withIr` sets. -/
theorem adversaryExtractor_withIr {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F]
    [SampleableType F] {P : Params F} {B : P.Bounds} (c₁ : TableCode B.Msg₁) (tr : Transcript)
    (ir : Bytes32) (po : RootProof F × OpenProofs) :
    adversaryExtractor c₁ tr (withIr ir po).1 = adversaryExtractor c₁ tr po.1 := rfl

theorem trOf_append (t : LeanVM.Prover.Tree) (T : Common.OracleQueryLog) :
    trOf (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T)) =
      treeTr t ++ evalTr (permutationQueries T) := by
  simp only [trOf, treeTr, evalTr, List.map_append]

/-- **Compose's list holds no witness when the Statement's extractor finds no secret**, at a proof
whose witness root is a digest. -/
theorem rpmList_none (t : LeanVM.Prover.Tree) (stmt : PcsQuotient.Statement)
    (proof : PcsQuotient.Proof) (T : Common.OracleQueryLog) (d : Digest)
    (hw : digestOfScalars proof.reduction.witnessRoot = some d)
    (hext : ¬ ∃ w, PcsQuotient.extractor stmt (PcsQuotient.Tree.evaluations t) T proof = some w ∧
      PcsQuotient.Relation stmt w) :
    ∀ g ∈ rpmExtractor (witnessDecoder iS cS) (treeTr t) T
        (withIr (toB t.root) (convP (stmt, proof))).1,
      ¬ iS.params.Sat (wS.decode (withIr (toB t.root) (convP (stmt, proof))).1.stmt)
        (iS.params.cells g.1) := by
  intro g hg hs
  have hg' : g ∈ adversaryExtractor (witnessDecoder iS cS)
      (trOf (PcsQuotient.Tree.evaluations t ++ keccakEvaluationsOfTranscript (permutationQueries T)))
      (rootProofOf stmt proof) := by
    rw [trOf_append]
    unfold rpmExtractor at hg
    rw [adversaryExtractor_withIr] at hg
    exact hg
  exact hext (extractor_of_mem cS Bridge.isCantor_statementConsts Bridge.readsSecret_final stmt
    proof d hw (PcsQuotient.Tree.evaluations t) T g hg' hs)

/-- The Statement's event: the verifier accepts and the extractor finds no secret. -/
abbrev EvS (t : LeanVM.Prover.Tree) (stmt : PcsQuotient.Statement) (proof : PcsQuotient.Proof)
    (T : Common.OracleQueryLog) (acc : Bool) : Prop :=
  PcsQuotient.BreaksKnowledgeSoundness (((stmt, proof), acc), PcsQuotient.Tree.evaluations t, T)

/-- Compose's event. -/
abbrev EvC (t : LeanVM.Prover.Tree) (stmt : PcsQuotient.Statement) (proof : PcsQuotient.Proof)
    (T : Common.OracleQueryLog) (v : Verd E) : Prop :=
  BreaksRpm wS (witnessDecoder iS cS) ((withIr (toB t.root) (convP (stmt, proof)), v), treeTr t, T)

theorem evS_imp (t : LeanVM.Prover.Tree) (stmt : PcsQuotient.Statement) (proof : PcsQuotient.Proof)
    (T : Common.OracleQueryLog) (acc : Bool) (h : EvS t stmt proof T acc) :
    acc = true ∧ ¬ ∃ w, PcsQuotient.extractor stmt (PcsQuotient.Tree.evaluations t) T proof =
      some w ∧ PcsQuotient.Relation stmt w := h

/-- **One outcome of the setup and the adversary**: the Statement's event after the Statement's
verifier is at most as likely as Compose's after Compose's, from any state of the permutation. -/
theorem step_le (t : LeanVM.Prover.Tree) (stmt : PcsQuotient.Statement)
    (proof : PcsQuotient.Proof) (T : Common.OracleQueryLog) (s : _) :
    Pr{let acc ← (simulateQ Common.lazyRandomPermutationOracles
        (PcsQuotient.verifier Common.queryPermutation t.root stmt proof)).run' s}[
        EvS t stmt proof T acc] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation
            (verifyD wS dS (withIr (toB t.root) (convP (stmt, proof)))))).run' s}[
        EvC t stmt proof T v] := by
  -- the Statement's extractor finds a secret: no break
  by_cases hext : ∃ w, PcsQuotient.extractor stmt (PcsQuotient.Tree.evaluations t) T proof =
      some w ∧ PcsQuotient.Relation stmt w
  · rw [zero_of_support _ _ _ (fun acc _ hb => (evS_imp t stmt proof T acc hb).2 hext) s]
    exact bot_le
  -- a malformed proof: the Statement's verifier rejects
  have hrej : ∀ (hm : digestOfScalars proof.reduction.witnessRoot = none ∨
      digestOfScalars proof.reduction.quotientRoot = none),
      Pr{let acc ← (simulateQ Common.lazyRandomPermutationOracles
        (PcsQuotient.verifier Common.queryPermutation t.root stmt proof)).run' s}[
        EvS t stmt proof T acc] = 0 := fun hm =>
    zero_of_support _ _ _ (fun acc hacc hb => by
      have h1 := verifier_malformed t.root stmt proof hm acc hacc
      have h2 := (evS_imp t stmt proof T acc hb).1
      rw [h1] at h2
      exact Bool.false_ne_true h2) s
  rcases hw : digestOfScalars proof.reduction.witnessRoot with _ | d
  · rw [hrej (Or.inl hw)]; exact bot_le
  rcases hq : digestOfScalars proof.reduction.quotientRoot with _ | d'
  · rw [hrej (Or.inr hq)]; exact bot_le
  -- the verifier with early stops, and Compose's list holds no witness
  have hlist := rpmList_none t stmt proof T d hw hext
  rw [Bridge.verifierBridge_final t.root stmt proof d d' hw hq,
    simulateQ_lazy_keccakCallsOverQueryPermutation, simulateQ_lazy_keccakCallsOverQueryPermutation]
  calc _ ≤ Pr{let b ← (simulateQ kcLazy (verifyES wS cS
          (withIr (toB t.root) (convP (stmt, proof))))).run' s}[b = true] :=
        prEvent_mono _ _ _ fun b hb => (evS_imp t stmt proof T b hb).1
    _ ≤ Pr{let v ← (simulateQ kcLazy (verifyD wS dS
          (withIr (toB t.root) (convP (stmt, proof))))).run' s}[
          AcceptedV (P := iS.params) (withIr (toB t.root) (convP (stmt, proof)), v)] :=
        es_le cS wS matches_iS _ s
    _ ≤ _ := prEvent_mono _ _ _ fun v hv => ⟨hv, hlist⟩

/-! ## Knowledge soundness -/

/-- **Knowledge soundness of the deployed membership proof in the random-permutation model**, for
the Statement's extractor and experiment, with no hypothesis: an adversary of at most `Q` calls of
`π`, `π⁻¹` makes the verifier accept while the extractor (reading the setup's tree and the
adversary's transcript) outputs no secret of the statement with probability at most `ksBound Q`. -/
theorem knowledgeSoundness : PcsQuotient.KnowledgeSoundness ksBound := by
  intro A Q hQ
  obtain ⟨q₀, hq, hcarry⟩ := Bridge.setupBridge_final
  rw [soundnessExperiment_eq q₀ hq A]
  refine le_trans ?_ (knowledgeSoundness_rust_rpm iS cS hβ_iS hc_iS
    Bridge.rowVanishing_statementConsts wS (fun _ => rfl) q₀ hcarry (convAdv A) Q
    (fun _ => Common.isWeightBound_map _ hQ))
  rw [rpmGame_eq q₀ A]
  exact prEvent_le_of_continuations _ _ _ _ _ _ _ fun a s => step_le a.1 a.2.1.1 a.2.1.2 a.2.2 s

/-- info: 'Soundness.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.knowledgeSoundness

end Soundness
