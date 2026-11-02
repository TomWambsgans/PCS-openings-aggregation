-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Adapted from `formal/Compose/Compose/Rpm.lean` of this repository (its `rpm_le_wired`, with the
-- proof type, the verifier and the event made parameters), itself adapted from leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR
-- Apache-2.0): the relabelling of the adversary (`Rpm/RpmRelabel.lean`'s `adv_relabel`), the
-- experiment as a transfer game (`Rpm/Generic.lean`'s `detRun_evalDistEq`), the transcript's hashes
-- in the adversary's cache (`Rpm/Extract.lean`, `common/Common/Transfer2.lean`'s `pathsOf_ideal2`);
-- the transfer is `common`'s (`Common.keccak256_transfer2`), the derandomization `Rpm/Coins.lean`'s
-- (`LeanVM.Rpm.exists_det`).
import Compose.Rpm

/-!
# The random-permutation transfer, for any proof and any verifier

`Rpm.lean`'s `rpm_le_wired` moves the deployed composition from leanerVM's random-permutation
model to mumbai's two-oracle model. Nothing in its proof reads what the proof is, what the
verifier computes, or what the event says, beyond three facts: the verifier follows the duplex
discipline (`DuplexVm`), its calls of `π` are bounded, and the event reads the transcript only
through the answers it records (`lookTr`). Here these are the hypotheses:

* **the games**: `rpmGameG setup fix A V` (the setup over `π`, its Keccak-256 queries logged; the
  adversary, with coins, `π` and `π⁻¹`, given the setup's root, its queries logged; the verifier
  `V` on `fix ir proof`, Keccak-256 over `π`, Keccak-f `= π`) and `kcGameG setup fix A' V` (the
  same in the two-oracle model, the setup's and the adversary's Keccak-256 queries logged);
* **`rpm_le_kcG`**: for every event `E` of the proof, the verdict and a transcript that reads the
  transcript through `lookTr` only, the RPM game's event on the setup's log and the Keccak-256
  evaluations of the adversary's permutation transcript is bounded by the two-oracle game's on its
  log, for a deterministic adversary of at most `QS + Q` queries, plus
  `(QSπ + Q + QVπ)² / 2^508`.

`Rpm.lean`'s `rpm_le_wired` is the instance `Pf = RootProof F × OpenProofs`, `fix = withIr`,
`V = verifyD W D` (`7 + 3 QOπ` calls of `π`), `E` the event "accepted while the extractor's list
holds no witness"; `rpmGame_eq_rpmGameG` states that the games are the same.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open LeanVM.Rpm (HOnly DuplexVm DuplexP hashBlocks RSpec HFSpec HFS D2Spec CSpec RR toRHF ofRHF
  cmap projLog relP logRel)

variable {Pf β : Type}

/-! ## The games -/

/-- **The random-permutation game, for any proof type and verifier**: the setup with Keccak-256
over `π`, its queries logged; the adversary given its root, its queries logged (coins, `π`,
`π⁻¹`); the verifier on the proof `fix` makes of the adversary's with the setup's root. -/
def rpmGameG (setup : OracleComp KeccakCalls Bytes32) (fix : Bytes32 → Pf → Pf)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCalls β) :
    OracleComp Common.RandomPermutationOracles ((Pf × β) × Transcript × Common.OracleQueryLog) :=
  simulateQ keccakCallsOverQueryPermutation (loggedKC setup) >>= fun s =>
    (simulateQ Common.loggedOracles (A s.1)).run [] >>= fun p =>
      simulateQ keccakCallsOverQueryPermutation (V (fix s.1 p.1)) >>= fun v =>
        pure ((fix s.1 p.1, v), s.2, p.2)

/-- **The two-oracle game**: the setup then the adversary given its root, their Keccak-256
queries logged; then the verifier. -/
def kcGameG (setup : OracleComp KeccakCalls Bytes32) (fix : Bytes32 → Pf → Pf)
    (A' : Bytes32 → OracleComp KeccakCalls Pf) (V : Pf → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls ((Pf × β) × Transcript) :=
  loggedKC (setup >>= fun ir => fix ir <$> A' ir) >>= fun pt =>
    V pt.1 >>= fun v => pure ((pt.1, v), pt.2)

/-! ## The game with the model's answers threaded -/

/-- An outcome with the adversary's permutation transcript (coins left out). -/
abbrev RpmOutTG (Pf β : Type) := (Pf × β) × Transcript × PermutationTranscript

/-- **The game, the permutation's edges threaded** (as mumbai's `runAdversaryThen`). -/
noncomputable def rpmThreadedG (setup : OracleComp KeccakCalls Bytes32) (fix : Bytes32 → Pf → Pf)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCalls β) : ProbComp (RpmOutTG Pf β) :=
  (simulateQ keccakCallsOverRandomPermutation (loggedKC setup)).run [] >>= fun s =>
    (simulateQ loggedRandomPermutationOracles (A s.1.1)).run (s.2, []) >>= fun p =>
      (simulateQ keccakCallsOverRandomPermutation (V (fix s.1.1 p.1))).run' p.2.1 >>=
        fun v => pure ((fix s.1.1 p.1, v), s.1.2, p.2.2)

theorem map_rpmGameG (setup : OracleComp KeccakCalls Bytes32) (fix : Bytes32 → Pf → Pf)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCalls β) :
    (fun z : (Pf × β) × Transcript × Common.OracleQueryLog =>
        (z.1, z.2.1, permutationQueries z.2.2)) <$>
        Common.runWithRandomPermutation (rpmGameG setup fix A V) = rpmThreadedG setup fix A V := by
  have hA : ∀ ir E, (simulateQ loggedRandomPermutationOracles (A ir)).run (E, []) =
      (fun p => (p.1.1, p.2, permutationQueries p.1.2)) <$>
        (simulateQ Common.lazyRandomPermutationOracles
          ((simulateQ Common.loggedOracles (A ir)).run [])).run E := by
    intro ir E
    rw [logged_run (A ir) [] E]
    simp [permutationQueries_nil]
  simp only [rpmGameG, rpmThreadedG, Common.runWithRandomPermutation, simulateQ_bind,
    simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure, hA,
    bind_map_left, simulateQ_lazy_keccakCallsOverQueryPermutation]

theorem prEvent_rpmGameG (setup : OracleComp KeccakCalls Bytes32) (fix : Bytes32 → Pf → Pf)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCalls β) (E : (Pf × β) → Transcript → Prop) :
    Pr{let z ← Common.runWithRandomPermutation (rpmGameG setup fix A V)}[
        E z.1 (z.2.1 ++ evalTr (permutationQueries z.2.2))] =
      Pr{let z ← rpmThreadedG setup fix A V}[E z.1 (z.2.1 ++ evalTr z.2.2)] := by
  rw [← map_rpmGameG, prEvent_map]

/-! ## The transfer game -/

/-- The adversary on bytes, with its transcript. -/
def advBG (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (x : Bytes32 × Transcript) : OracleComp RSpec (Pf × PermutationTranscript) :=
  (simulateQ logRelC (A x.1)).run []

/-- The verifier on bytes. -/
def postBG (fix : Bytes32 → Pf → Pf) (V : Pf → OracleComp KeccakCalls β)
    (x : Bytes32 × Transcript) (a : Pf × PermutationTranscript) :
    OracleComp HFSpec (RpmOutTG Pf β) :=
  (fun v => ((fix x.1 a.1, v), x.2, a.2)) <$> simulateQ toRHF (V (fix x.1 a.1))

/-- **The transfer game** of the experiment: the setup, the adversary, the verifier. -/
def gameBG (setup : OracleComp KeccakCalls Bytes32) (fix : Bytes32 → Pf → Pf)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCalls β) : OracleComp D2Spec (RpmOutTG Pf β) :=
  Common.rpmGame2 (preB setup) (advBG A) (postBG fix V)

/-- **The game is the real world of the transfer game.** -/
theorem rpmThreadedG_evalDistEq (setup : OracleComp KeccakCalls Bytes32) (hS : HOnly setup)
    (fix : Bytes32 → Pf → Pf) (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCalls β) :
    rpmThreadedG setup fix A V =ᵈ
      Common.realGame2 Common.keccakPadding Common.KState.zero (gameBG setup fix A V) := by
  rw [LeanVM.Rpm.realGame2_eq, gameBG, Common.rpmGame2, preB,
    hEmbed2_toRH (loggedKC setup) (hOnly_loggedKC_run setup hS [])]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  simp only [postBG, simulateQ_map, StateT.run_map, Functor.map_map, RR,
    QueryImpl.simulateQ_compose]
  have hpre := (LeanVM.Rpm.post_relabel (loggedKC setup) []).symm
  simp only [projLog, LeanVM.Rpm.logMap, List.map_nil, RR, QueryImpl.simulateQ_compose] at hpre
  rw [rpmThreadedG]
  refine EvalDistEq.trans (EvalDistEq.bind_left hpre _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun x => ?_
  have hadv := (adv_relabelC (A x.1.1) x.2 []).symm
  simp only [RR, QueryImpl.simulateQ_compose] at hadv
  simp only [advBG]
  refine EvalDistEq.trans (EvalDistEq.bind_left hadv _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun p => ?_
  have h := (LeanVM.Rpm.post_relabel' (V (fix x.1.1 p.1.1)) p.2).symm.map
    fun v => ((fix x.1.1 p.1.1, v), x.1.2, p.1.2)
  simp only [StateT.run'_eq, Functor.map_map, RR, QueryImpl.simulateQ_compose] at h
  simp only [StateT.run'_eq, bind_pure_comp, Functor.map_map]
  exact h

/-! ## The transfer game's discipline and permutation calls -/

theorem duplex_postBG (fix : Bytes32 → Pf → Pf) (V : Pf → OracleComp KeccakCalls β)
    (hVd : ∀ π, DuplexVm (V π) []) (x : Bytes32 × Transcript)
    (a : Pf × PermutationTranscript) :
    Common.Duplex Common.KState.zero Common.keccakNF (postBG fix V x a) [] := by
  have h := LeanVM.Rpm.duplex_toRHF _ [] (hVd (fix x.1 a.1))
  exact LeanVM.Rpm.duplex_map _ _ [] (by simpa using h)

theorem cost_advBG (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (x : Bytes32 × Transcript) : Common.QueryCostAtMost (advBG A x) LeanVM.Rpm.advCost Q := by
  refine Common.isWeightBound_run_simulateQ logRelC Common.permutationCallCost LeanVM.Rpm.advCost
    (fun t T => ?_) (hA x.1) []
  rcases t with n | q
  · exact Common.isWeightBound_map _ (Common.isWeightBound_query LeanVM.Rpm.advCost (.inl n))
  · simp only [logRelC, logRel, StateT.run_mk, relP]
    exact Common.isWeightBound_map _ (Common.isWeightBound_map _
      (Common.isWeightBound_query LeanVM.Rpm.advCost (.inr (.inr (permQueryToRpm q)))))

/-- **The permutation calls of the transfer game**: the setup's `QSπ`, the adversary's `Q`, the
verifier's `QVπ`. -/
theorem cost_gameBG (setup : OracleComp KeccakCalls Bytes32) (hS : HOnly setup) (QSπ : ℕ)
    (hSπ : Common.QueryCostAtMost setup hashBlocks QSπ) (fix : Bytes32 → Pf → Pf)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (V : Pf → OracleComp KeccakCalls β) (QVπ : ℕ)
    (hVπ : ∀ π, Common.QueryCostAtMost (V π) hashBlocks QVπ) :
    Common.QueryCostAtMost (gameBG setup fix A V)
      (Common.queryCost2 (Dg := Common.DigestBytes) Common.keccakPadding) (QSπ + Q + QVπ) := by
  have h : Common.QueryCostAtMost (gameBG setup fix A V) LeanVM.Rpm.gameCost
      (QSπ + (Q + QVπ)) := by
    rw [gameBG, Common.rpmGame2, preB,
      hEmbed2_toRH (loggedKC setup) (hOnly_loggedKC_run setup hS [])]
    refine (LeanVM.Rpm.isWeightBound_hfEmbed_toRHF (cost_loggedKC setup QSπ hSπ [])).bind
      fun x => ?_
    refine (LeanVM.Rpm.isWeightBound_advEmbed (cost_advBG A Q hA x)).bind fun a => ?_
    rw [postBG, simulateQ_map]
    exact Common.isWeightBound_map _
      (LeanVM.Rpm.isWeightBound_hfEmbed_toRHF (hVπ _))
  exact h.mono (by omega)

/-! ## The random-oracle side: the transcript's evaluations are the adversary's cache -/

/-- **The adversary with the simulator, on lanes, with its transcript.** -/
noncomputable def romAdvTG (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (x : Bytes32 × Transcript) : OracleComp CSpec (Pf × PermutationTranscript) :=
  simulateQ ofRHF (Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x))

/-- **The random-oracle adversary of the transfer**: the adversary with the indifferentiability
simulator (`Common.advS2`), with coins, its queries read on lanes. -/
noncomputable def romAdvCG (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (ir : Bytes32) : OracleComp CSpec Pf :=
  Prod.fst <$> romAdvTG A (ir, [])

/-- The verifier from the cache after the adversary, that cache kept. -/
noncomputable def gLG (fix : Bytes32 → Pf → Pf) (V : Pf → OracleComp KeccakCalls β)
    (p : (Bytes32 × Pf) × KeccakCalls.QueryCache) :
    ProbComp ((Pf × β) × KeccakCalls.QueryCache) :=
  (fun v => ((fix p.1.1 p.1.2, v), p.2)) <$>
    (simulateQ randomOracle (V (fix p.1.1 p.1.2))).run' p.2

/-- **The event on the cache after the adversary**: the event for every transcript recording that
cache's Keccak-256 answers. -/
def BreaksCG (E : (Pf × β) → Transcript → Prop)
    (z : (Pf × β) × KeccakCalls.QueryCache) : Prop :=
  ∀ tr, Consistent tr z.2 → E z.1 tr

/-- The transfer's adversary is the adversary with the simulator logging the byte queries, its
log read on lanes. -/
theorem advS2_advBG (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (x : Bytes32 × Transcript) :
    Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x) =
      (fun y ↦ (y.1, y.2.2.map LeanVM.Rpm.entryOfRpm)) <$>
        (simulateQ (Common.advImplLog2 Common.keccakPadding) (simulateQ relPC (A x.1))).run
          (Common.SimState.init Common.KState.zero, []) := by
  have h := advImpl2_logRelC (A x.1) [] (Common.SimState.init Common.KState.zero)
  rw [List.map_nil] at h
  rw [← h, Functor.map_map, Common.advS2, advBG, StateT.run'_eq]
  congr 1
  funext y
  simp only [List.map_map]
  have e : LeanVM.Rpm.entryOfRpm ∘ LeanVM.Rpm.entryToRpm = id :=
    funext LeanVM.Rpm.entryOfRpm_toRpm
  rw [e, List.map_id]

/-- **The adversary's cache** after the adversary with the simulator, from a cache `c₀`: it extends
`c₀`, holds every Keccak-256 evaluation of the adversary's transcript, and holds no other new
Keccak-256 answer. -/
theorem adv_cacheG (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (x : Bytes32 × Transcript) (c₀ : HFS.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HFS.romImpl
      (Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x))).run c₀)) :
    c₀ ≤ z.2 ∧ (∀ md ∈ LeanVM.Rpm.transcriptPathsB z.1.2, z.2 (.inl md.1) = some md.2) ∧
      (∀ m d, z.2 (.inl m) = some d → c₀ (.inl m) = some d ∨
        (m, d) ∈ LeanVM.Rpm.transcriptPathsB z.1.2) := by
  refine ⟨Common.le_of_mem_support_run _ c₀ hz, ?_⟩
  rw [advS2_advBG, simulateQ_map, StateT.run_map, Common.run_simulateQ_foldRO, Functor.map_map,
    support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have eT : (w.2.1.2.map LeanVM.Rpm.entryOfRpm).map
      (fun e ↦ (permQueryToRpm e.1, LeanVM.KState.toRpm e.2)) = w.2.1.2 := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w.2.1.2]
    exact List.map_congr_left fun e _ ↦ LeanVM.Rpm.entryToRpm_ofRpm e
  have hpaths : LeanVM.Rpm.transcriptPathsB (w.2.1.2.map LeanVM.Rpm.entryOfRpm) =
      Common.pathsOf Common.keccakPadding Common.KState.zero w.2.1.2 := by
    rw [LeanVM.Rpm.transcriptPathsB, eT]
  have hrep : w.2.1.1 = Common.replay Common.KState.zero w.2.1.2 := by
    have h1 := Common.run_simulateQ_foldRO
      (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding) (simulateQ relPC (A x.1))
      (Common.SimState.init Common.KState.zero, []) c₀
    have hz' : ((w.1, w.2.1), w.2.2) ∈ support ((simulateQ HFS.romImpl
        ((simulateQ (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding)
          (simulateQ relPC (A x.1))).run (Common.SimState.init Common.KState.zero, []))).run
            c₀) := by
      rw [h1, support_map]
      exact ⟨w, hw, rfl⟩
    exact Common.simulator2_state_eq_replay _ _ _
      (Common.fst_mem_support_of_mem_support_ro2 hz')
  have hrel := cacheRel_run c₀ (A x.1) ((Common.SimState.init Common.KState.zero, []), c₀)
    (fun m d hd => Or.inl hd) w hw
  refine ⟨?_, fun m d hd => ?_⟩
  · simp only [hpaths]
    exact pathsOf_ideal2C _ c₀ hw
  · simp only [hpaths]
    rcases hrel m d hd with h | h
    · exact Or.inl h
    · rw [hrep] at h
      exact Or.inr h

/-- The prefix of the transfer's random-oracle game: the setup, then the adversary with the
simulator. -/
noncomputable def romPrefixG (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf) :
    OracleComp HFSpec ((Bytes32 × Transcript) × (Pf × PermutationTranscript)) :=
  simulateQ (Common.hInF (E := Common.KRest) (C := Common.KCap)) (preB setup) >>= fun x =>
    (x, ·) <$> Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x)

/-- **After the setup and the adversary, the cache's Keccak-256 answers are those the setup's log
and the Keccak-256 evaluations of the adversary's transcript record.** -/
theorem consistent_romPrefixG (setup : OracleComp KeccakCalls Bytes32) (hS : HOnly setup)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    {p : ((Bytes32 × Transcript) × (Pf × PermutationTranscript)) × HFS.QueryCache}
    (hp : p ∈ support ((simulateQ HFS.romImpl (romPrefixG setup A)).run ∅)) :
    Consistent (p.1.1.2 ++ evalTr p.1.2.2) (cmap p.2) := by
  rw [romPrefixG, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨⟨x, c₁⟩, h1, hp⟩ := hp
  rw [simulateQ_map, StateT.run_map, support_map] at hp
  obtain ⟨⟨a, c₂⟩, h2, rfl⟩ := hp
  have hc1 : Consistent x.2 (cmap c₁) := consB_run setup hS [] ∅
    (by rw [LeanVM.Rpm.cmap_empty]; exact consistent_nil) (x, c₁) h1
  obtain ⟨hle, hpaths, hrel⟩ := adv_cacheG A x c₁ h2
  intro m
  show cmap c₂ (.inl m) = lookTr (x.2 ++ evalTr a.2) m
  rw [lookTr_append', lookTr_evalTr, LeanVM.Rpm.hashesOf_transcriptPaths, ← hc1 m,
    LeanVM.Rpm.cmap_inl, LeanVM.Rpm.cmap_inl]
  rcases h : c₁ (.inl m) with _ | d
  · simp only [Option.map_none]
    unfold LeanVM.Rpm.hashesOfB
    rcases hf : (LeanVM.Rpm.transcriptPathsB a.2).find? (·.1 = m) with _ | e
    · rw [hf]
      rcases h2' : c₂ (.inl m) with _ | d'
      · rfl
      · exfalso
        rcases hrel m d' h2' with h3 | h3
        · rw [h] at h3
          cases h3
        · rw [List.find?_eq_none] at hf
          exact hf _ h3 (by simp)
    · have he := List.find?_some hf
      have hmem := List.mem_of_find?_eq_some hf
      simp only [decide_eq_true_eq] at he
      rw [hf, ← he, hpaths e hmem]
      rfl
  · simp only [Option.map_some]
    rw [hle h]
    rfl

theorem romRun2_splitG (setup : OracleComp KeccakCalls Bytes32) (fix : Bytes32 → Pf → Pf)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCalls β) :
    Common.romRun2 (simulateQ (Common.hInF (E := Common.KRest) (C := Common.KCap)) (preB setup) >>=
      fun x => Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x) >>= fun a =>
        postBG fix V x a) =
      (simulateQ HFS.romImpl (romPrefixG setup A)).run ∅ >>= fun p =>
        (simulateQ HFS.romImpl (postBG fix V p.1.1 p.1.2)).run' p.2 := by
  simp only [Common.romRun2, romPrefixG, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, map_bind, bind_map_left, bind_assoc]

/-- **The transfer's random-oracle game, on lanes, with the event on the cache**: the verifier
from the cache after the adversary with the simulator (with coins), the event read on any
transcript of that cache's answers. -/
theorem rom_leG (setup : OracleComp KeccakCalls Bytes32) (hS : HOnly setup)
    (fix : Bytes32 → Pf → Pf) (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCalls β) (E : (Pf × β) → Transcript → Prop)
    (hE : ∀ z tr tr', (∀ x, lookTr tr x = lookTr tr' x) → E z tr → E z tr') :
    Pr{let z ← Common.romRun2 (simulateQ (Common.hInF (E := Common.KRest) (C := Common.KCap))
        (preB setup) >>= fun x => Common.advS2 Common.keccakPadding Common.KState.zero
          (advBG A x) >>= fun a => postBG fix V x a)}[E z.1 (z.2.1 ++ evalTr z.2.2)] ≤
      Pr{let y ← (simulateQ KeccakCalls.romImpl (simulateQ liftKC setup >>= fun ir =>
          (ir, ·) <$> romAdvCG A ir)).run ∅ >>= gLG fix V}[BreaksCG E y] := by
  rw [romRun2_splitG]
  have hpost : ∀ p : ((Bytes32 × Transcript) × (Pf × PermutationTranscript)) × HFS.QueryCache,
      Pr{let z ← (simulateQ HFS.romImpl (postBG fix V p.1.1 p.1.2)).run' p.2}[
          E z.1 (z.2.1 ++ evalTr z.2.2)] =
        Pr{let v ← (simulateQ randomOracle (V (fix p.1.1.1 p.1.2.1))).run' (cmap p.2)}[
          E (fix p.1.1.1 p.1.2.1, v) (p.1.1.2 ++ evalTr p.1.2.2)] := by
    intro p
    rw [postBG, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map]
    have h := (LeanVM.Rpm.run'_toRHF (V (fix p.1.1.1 p.1.2.1)) p.2).prEvent_eq
      (fun v => E (fix p.1.1.1 p.1.2.1, v) (p.1.1.2 ++ evalTr p.1.2.2))
    rw [StateT.run'_eq, prEvent_map] at h
    exact h
  have h := LeanVM.Rpm.run_ofRHF (romPrefixG setup A) ∅
  rw [LeanVM.Rpm.cmap_empty] at h
  have hX : (fun r => (r.1.1, r.2.1)) <$> simulateQ ofRHF (romPrefixG setup A) =
      simulateQ liftKC setup >>= fun ir => (ir, ·) <$> romAdvCG A ir := by
    rw [romPrefixG, simulateQ_bind, preB,
      ofRHF_hInF_toRH (loggedKC setup) (hOnly_loggedKC_run setup hS [])]
    conv_rhs => rw [← fst_loggedKC_run setup [], simulateQ_map, bind_map_left]
    simp only [simulateQ_map, map_bind, Functor.map_map]
    refine bind_congr fun x => ?_
    simp only [romAdvCG, romAdvTG, Functor.map_map]
    rfl
  have hJ : (fun p : ((Bytes32 × Transcript) × (Pf × PermutationTranscript)) × HFS.QueryCache =>
      ((p.1.1.1, p.1.2.1), cmap p.2)) <$> (simulateQ HFS.romImpl (romPrefixG setup A)).run ∅ =ᵈ
      (simulateQ KeccakCalls.romImpl (simulateQ liftKC setup >>= fun ir =>
        (ir, ·) <$> romAdvCG A ir)).run ∅ := by
    rw [← hX, simulateQ_map, StateT.run_map]
    refine EvalDistEq.trans ?_ (h.symm.map _)
    rw [Functor.map_map]
    exact EvalDistEq.rfl
  calc _ ≤ Pr{let y ← (simulateQ HFS.romImpl (romPrefixG setup A)).run ∅ >>= fun p =>
              gLG fix V ((p.1.1.1, p.1.2.1), cmap p.2)}[BreaksCG E y] := by
        refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp => ?_
        rw [hpost, gLG, prEvent_map]
        refine prEvent_mono _ _ _ fun v hv tr htr => ?_
        have hcons := consistent_romPrefixG setup hS A hp
        exact hE _ _ _ (fun x => (hcons x).symm.trans (htr x)) hv
    _ = _ := by
        rw [← bind_map_left]
        exact (EvalDistEq.bind_left hJ _).prEvent_eq _

/-! ## Coins do not help -/

theorem cost_advB_wRG (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf) (Q : ℕ)
    (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (x : Bytes32 × Transcript) : Common.QueryCostAtMost (advBG A x) LeanVM.Rpm.wR Q := by
  refine Common.isWeightBound_run_simulateQ logRelC Common.permutationCallCost LeanVM.Rpm.wR
    (fun t T => ?_) (hA x.1) []
  rcases t with n | q
  · exact Common.isWeightBound_map _ (Common.isWeightBound_query LeanVM.Rpm.wR (.inl n))
  · simp only [logRelC, logRel, StateT.run_mk, relP]
    exact Common.isWeightBound_map _ (Common.isWeightBound_map _
      (Common.isWeightBound_query LeanVM.Rpm.wR (.inr (.inr (permQueryToRpm q)))))

/-- **The random-oracle adversary makes at most one oracle query per call of `π` or `π⁻¹` of the
adversary**, coins free. -/
theorem cost_romAdvCG (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf) (Q : ℕ)
    (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q) (ir : Bytes32) :
    Common.QueryCostAtMost (romAdvCG A ir) LeanVM.Rpm.hashCalls Q := by
  refine Common.isWeightBound_map _ (LeanVM.Rpm.isWeightBound_simulateQ_ofRHF ?_)
  rw [Common.advS2, StateT.run'_eq]
  exact Common.isWeightBound_map _ (Common.isWeightBound_run_simulateQ _ LeanVM.Rpm.wR
    LeanVM.Rpm.wHF LeanVM.Rpm.isWeightBound_advImpl2 (cost_advB_wRG A Q hA (ir, [])) _)

/-! ## The deterministic adversary's game is `kcGameG` -/

/-- **The deterministic adversary's game, the event on its cache, is bounded by `kcGameG`'s**: the
log of the setup and the adversary records the cache (`consistent_run_loggedKC`). -/
theorem le_kcGameG (setup : OracleComp KeccakCalls Bytes32) (fix : Bytes32 → Pf → Pf)
    (A' : Bytes32 → OracleComp KeccakCalls Pf) (V : Pf → OracleComp KeccakCalls β)
    (E : (Pf × β) → Transcript → Prop) :
    Pr{let y ← (simulateQ randomOracle (setup >>= fun ir => (ir, ·) <$> A' ir)).run ∅ >>=
        gLG fix V}[BreaksCG E y] ≤
      Pr{let z ← (simulateQ randomOracle (kcGameG setup fix A' V)).run' ∅}[E z.1 z.2] := by
  set SA := setup >>= fun ir => fix ir <$> A' ir
  have hAw : (fun p : Bytes32 × Pf => fix p.1 p.2) <$>
      (setup >>= fun ir => (ir, ·) <$> A' ir) = SA := by
    simp only [SA, map_bind, Functor.map_map]
  have hL : (simulateQ randomOracle (setup >>= fun ir => (ir, ·) <$> A' ir)).run ∅ >>= gLG fix V =
      (simulateQ randomOracle SA).run ∅ >>= fun q =>
        (fun v => ((q.1, v), q.2)) <$> (simulateQ randomOracle (V q.1)).run' q.2 := by
    rw [← hAw, simulateQ_map, StateT.run_map, bind_map_left]
    rfl
  have hR : (simulateQ randomOracle (kcGameG setup fix A' V)).run' ∅ =
      (simulateQ randomOracle (loggedKC SA)).run ∅ >>= fun q =>
        (fun v => ((q.1.1, v), q.1.2)) <$> (simulateQ randomOracle (V q.1.1)).run' q.2 := by
    simp only [kcGameG, SA, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind,
      bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [hL, hR, ← map_run_loggedKC SA [] ∅, bind_map_left]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun q hq => ?_
  have hcons := consistent_run_loggedKC SA [] ∅ consistent_nil q hq
  rw [prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ fun v hv => hv q.1.2 hcons

/-! ## The transfer -/

/-- **From the random-permutation model to mumbai's two-oracle model, for any proof, verifier and
event that reads the transcript through its answers.** For a setup of Keccak-256 calls only (at
most `QS` of them, `QSπ` calls of `π`), an adversary with coins, `π` and `π⁻¹` (at most `Q` calls
given any root) and a verifier following the duplex discipline with at most `QVπ` calls of `π`:
some deterministic adversary of the two random oracles, of at most `QS + Q` queries given any root
(it recomputes the public setup), meets the event in the two-oracle game, on the log of the setup's
and its Keccak-256 queries, at least as often as the RPM game's adversary meets it on the setup's
log and the Keccak-256 evaluations of its permutation transcript, less
`(QSπ + Q + QVπ)² / 2^508`. -/
theorem rpm_le_kcG (setup : OracleComp KeccakCalls Bytes32) (hSH : HOnly setup) (QS QSπ : ℕ)
    (hS : IsTotalQueryBound setup QS) (hSπ : Common.QueryCostAtMost setup hashBlocks QSπ)
    (fix : Bytes32 → Pf → Pf) (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf)
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (V : Pf → OracleComp KeccakCalls β) (hVd : ∀ π, DuplexVm (V π) []) (QVπ : ℕ)
    (hVπ : ∀ π, Common.QueryCostAtMost (V π) hashBlocks QVπ)
    (E : (Pf × β) → Transcript → Prop)
    (hE : ∀ z tr tr', (∀ x, lookTr tr x = lookTr tr' x) → E z tr → E z tr') :
    ∃ A' : Bytes32 → OracleComp KeccakCalls Pf, (∀ ir, IsTotalQueryBound (A' ir) (QS + Q)) ∧
      Pr{let z ← Common.runWithRandomPermutation (rpmGameG setup fix A V)}[
          E z.1 (z.2.1 ++ evalTr (permutationQueries z.2.2))] ≤
        Pr{let z ← (simulateQ randomOracle (kcGameG setup fix A' V)).run' ∅}[E z.1 z.2] +
          ((QSπ + Q + QVπ : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 := by
  obtain ⟨A', hA', hle⟩ := exists_det_setup setup QS hS (romAdvCG A) Q (cost_romAdvCG A Q hA)
    (gLG fix V) (BreaksCG E)
  refine ⟨A', hA', ?_⟩
  rw [prEvent_rpmGameG]
  refine le_trans (le_of_eq ((rpmThreadedG_evalDistEq setup hSH fix A V).prEvent_eq
    (fun z => E z.1 (z.2.1 ++ evalTr z.2.2)))) ?_
  obtain ⟨ht, -⟩ := Common.keccak256_transfer2 (preB setup) (advBG A) (postBG fix V)
    (duplex_postBG fix V hVd) (QSπ + Q + QVπ) (cost_gameBG setup hSH QSπ hSπ fix A Q hA V QVπ hVπ)
    (fun z => E z.1 (z.2.1 ++ evalTr z.2.2))
  exact ht.trans (add_le_add ((rom_leG setup hSH fix A V E hE).trans
    (hle.trans (le_kcGameG setup fix A' V E))) le_rfl)

/-! ## `Rpm.lean`'s game is an instance -/

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds}

/-- **`Rpm.lean`'s random-permutation game is `rpmGameG`** at the deployed proof type, `withIr`
and the deployed verifier. -/
theorem rpmGame_eq_rpmGameG (W : Wire P B) (D : Deploy F) (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs)) :
    rpmGame W D setup A = rpmGameG setup withIr A (verifyD W D) := rfl

/-- `Rpm.lean`'s event `BreaksRpm` is the generic event on the setup's log and the Keccak-256
evaluations of the adversary's permutation transcript. -/
theorem breaksRpm_iff (W : Wire P B) (c₁ : TableCode B.Msg₁) (z : RpmOut F) :
    BreaksRpm W c₁ z ↔ (AcceptedV (P := P) z.1 ∧
      ∀ g ∈ adversaryExtractor c₁ (z.2.1 ++ evalTr (permutationQueries z.2.2)) z.1.1.1,
        ¬ P.Sat (W.decode z.1.1.1.stmt) (P.cells g.1)) := Iff.rfl

/-- The deployed event reads the transcript through its answers only (`adversaryExtractor_congr`):
`rpm_le_kcG`'s hypothesis `hE` at `Rpm.lean`'s event. -/
theorem breaksP_congr (W : Wire P B) (c₁ : TableCode B.Msg₁)
    (z : (RootProof F × OpenProofs) × Verd F) (tr tr' : Transcript)
    (h : ∀ x, lookTr tr x = lookTr tr' x)
    (hz : AcceptedV (P := P) z ∧ ∀ g ∈ adversaryExtractor c₁ tr z.1.1,
      ¬ P.Sat (W.decode z.1.1.stmt) (P.cells g.1)) :
    AcceptedV (P := P) z ∧ ∀ g ∈ adversaryExtractor c₁ tr' z.1.1,
      ¬ P.Sat (W.decode z.1.1.stmt) (P.cells g.1) := by
  refine ⟨hz.1, fun g hg => hz.2 g ?_⟩
  rwa [adversaryExtractor_congr c₁ h]

/-- info: 'Compose.rpm_le_kcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.rpm_le_kcG

/-- info: 'Compose.rpmGame_eq_rpmGameG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.rpmGame_eq_rpmGameG

/-- info: 'Compose.breaksP_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.breaksP_congr

end Compose
