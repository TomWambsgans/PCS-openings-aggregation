-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the relabelling of the adversary (`adv_relabelC`, from
-- `lean_vm/LeanVM/Protocol/Rpm/RpmRelabel.lean`'s `adv_relabel`, with coins), the experiment as a
-- transfer game (`rpmThreaded_evalDistEq`, from `Rpm/Generic.lean`'s `detRun_evalDistEq`), the
-- transcript's hashes in the adversary's cache (`CacheRel`, `cacheRel_run`, `pathsOf_ideal2C`,
-- from `Rpm/Extract.lean`'s `cacheInv_step`, `cacheInv_run`, `transcriptHashes_eq_of_mem_support`
-- and `common/Common/Transfer2.lean`'s `pathsOf_ideal2`, from a cache the setup filled, with
-- coins); the transfer is `common`'s (`Common.keccak256_transfer2`), the derandomization
-- `Rpm/Coins.lean`'s (`LeanVM.Rpm.exists_det`), the rerun `common/Common/Rerun.lean`'s idea.
import Compose.Deployed
import LeanVM.Protocol.Rpm.Generic
import LeanVM.Protocol.ExperimentBridge
import Common.Rerun

/-!
# The deployed composition in the random-permutation model

leanerVM's model (`Statement/RandomPermutation.lean`): one uniformly random permutation `π` of the
Keccak-f[1600] state, queried forward and inverse, lazily sampled; Keccak-256 is the sponge over
`π`, Keccak-f[1600] is `π`. Here:

* **the experiment** (`rpmGame`): the setup computes the circuit's commitment with Keccak-256 over
  `π` (`setup`, its Keccak-256 queries logged: `tS`); the adversary, with coins, `π` and `π⁻¹`,
  is given it (its queries logged: `T`); the verifier runs the chain and the three openings
  (`verifyD`) with Keccak-256 over `π` and Keccak-f `= π`;
* **the extractor** (`rpmExtractor`): `adversaryExtractor` on the setup's log and the Keccak-256
  evaluations of the adversary's permutation transcript (mumbai's `keccakEvaluationsOfTranscript`
  of `permutationQueries T`, the statement's own reading of a transcript);
* **`knowledgeSoundness_deployed_rpm`**: the verifier accepts while the extractor's list holds no
  witness with probability at most the two-oracle bound of `knowledgeSoundness_deployed_setup` for
  an adversary of `QS + Q` queries, plus `(QSπ + Q + 7 + 3 QOπ)² / 2^508`.

The proof: the experiment is the real world of `common`'s two-oracle transfer game, the setup its
honest part before the adversary (`rpmThreaded_evalDistEq`); `Common.keccak256_transfer2` moves it
to the two random oracles against the adversary with the indifferentiability simulator; there the
adversary's cache holds the setup's answers and exactly the Keccak-256 evaluations of its
transcript (`consistent_romPrefix`), so the extractor reads the cache; coins do not help, the
deterministic adversary recomputing the public setup to learn the cache it starts from
(`exists_det_setup`); and the experiment of that adversary is `deployedExp`'s, its log the cache
(`le_deployedExp`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open LeanVM.Rpm (HOnly DuplexVm DuplexP hashBlocks RSpec HFSpec HFS D2Spec CSpec RR toRHF ofRHF
  cmap projLog relP logRel)

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds}

/-! ## The experiment, the extractor, the event -/

/-- The proof the verifier reads: the adversary's, with the setup's commitment. -/
def withIr (ir : Bytes32) (po : RootProof F × OpenProofs) : RootProof F × OpenProofs :=
  ({ po.1 with ir := ir }, po.2)

/-- The verifier's outputs: the chain's challenges and the three openings' verdicts. -/
abbrev Verd (F : Type) := Chals F × Bool × Bool × Bool

variable (W : Wire P B) (D : Deploy F)

/-- **The deployed verifier on a proof**: the chain, then `opening::verify` (F2's `ourVerifier`)
for the witness, wiring and quotient tables. -/
def verifyD (po : RootProof F × OpenProofs) : OracleComp KeccakCalls (Verd F) :=
  chainWith W hash256 po.1 >>= fun ch =>
    ourVerifier D.Lw D.R (wIn D (⟨po.1, po.2, [], ch⟩ : S0 F)) >>= fun bW =>
      ourVerifier D.Lσ D.R (σIn D (⟨po.1, po.2, [], ch⟩ : S0 F)) >>= fun bσ =>
        ourVerifier D.LQ D.R (qIn D (⟨po.1, po.2, [], ch⟩ : S0 F)) >>= fun bQ =>
          pure (ch, bW, bσ, bQ)

/-- An outcome of the experiment: the proof and the verdicts, the setup's log, the adversary's
transcript (coins, `π`, `π⁻¹`). -/
abbrev RpmOut (F : Type) :=
  ((RootProof F × OpenProofs) × Verd F) × Transcript × Common.OracleQueryLog

/-- **The experiment in the random-permutation model**, a game of the model's oracles (coins, `π`,
`π⁻¹`): the setup with Keccak-256 over `π` (`keccakCallsOverQueryPermutation`), its queries logged;
the adversary given its commitment, its queries logged (`Common.loggedOracles`); the verifier on
the adversary's proof with the setup's commitment, Keccak-256 over `π` and Keccak-f `= π`. -/
def rpmGame (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs)) :
    OracleComp Common.RandomPermutationOracles (RpmOut F) :=
  simulateQ keccakCallsOverQueryPermutation (loggedKC setup) >>= fun s =>
    (simulateQ Common.loggedOracles (A s.1)).run [] >>= fun p =>
      simulateQ keccakCallsOverQueryPermutation (verifyD W D (withIr s.1 p.1)) >>= fun v =>
        pure ((withIr s.1 p.1, v), s.2, p.2)

/-- The Keccak-256 evaluations a permutation transcript holds (mumbai's
`keccakEvaluationsOfTranscript`), as a transcript of inputs and 32-byte answers. -/
def evalTr (T : PermutationTranscript) : Transcript :=
  (keccakEvaluationsOfTranscript T).map fun e => (e.1, toB e.2)

/-- **The extractor in the random-permutation model**: `adversaryExtractor` on the setup's log and
the Keccak-256 evaluations of the adversary's permutation queries. An explicit, computable
function of the setup's log, the adversary's transcript and the proof. -/
def rpmExtractor (c₁ : TableCode B.Msg₁) (tS : Transcript) (T : Common.OracleQueryLog)
    (π : RootProof F) : List B.Msg₁ :=
  adversaryExtractor c₁ (tS ++ evalTr (permutationQueries T)) π

/-- The deployed verifier accepts: its own check and the three openings. -/
def AcceptedV (z : (RootProof F × OpenProofs) × Verd F) : Prop :=
  reductionCheck P z.2.1.α z.2.1.β z.2.1.t z.1.1.v.1 z.1.1.v.2 ∧ z.2.2.1 = true ∧
    z.2.2.2.1 = true ∧ z.2.2.2.2 = true

/-- **Knowledge soundness is broken**: the verifier accepts while the extractor's list holds no
witness of the statement. -/
def BreaksRpm (c₁ : TableCode B.Msg₁) (z : RpmOut F) : Prop :=
  AcceptedV (P := P) z.1 ∧ ∀ g ∈ rpmExtractor c₁ z.2.1 z.2.2 z.1.1.1,
    ¬ P.Sat (W.decode z.1.1.1.stmt) (P.cells g.1)

/-! ## The experiment with the model's answers threaded -/

/-- An outcome with the adversary's permutation transcript (coins left out). -/
abbrev RpmOutT (F : Type) :=
  ((RootProof F × OpenProofs) × Verd F) × Transcript × PermutationTranscript

/-- The event on an outcome with the permutation transcript. -/
def BreaksT (c₁ : TableCode B.Msg₁) (z : RpmOutT F) : Prop :=
  AcceptedV (P := P) z.1 ∧ ∀ g ∈ adversaryExtractor c₁ (z.2.1 ++ evalTr z.2.2) z.1.1.1,
    ¬ P.Sat (W.decode z.1.1.1.stmt) (P.cells g.1)

/-- **The experiment, the permutation's edges threaded** (as mumbai's `runAdversaryThen`): the
setup and the verifier's calls answered by `keccakCallsOverRandomPermutation`, the adversary by
`loggedRandomPermutationOracles`. -/
noncomputable def rpmThreaded (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs)) :
    ProbComp (RpmOutT F) :=
  (simulateQ keccakCallsOverRandomPermutation (loggedKC setup)).run [] >>= fun s =>
    (simulateQ loggedRandomPermutationOracles (A s.1.1)).run (s.2, []) >>= fun p =>
      (simulateQ keccakCallsOverRandomPermutation (verifyD W D (withIr s.1.1 p.1))).run' p.2.1 >>=
        fun v => pure ((withIr s.1.1 p.1, v), s.1.2, p.2.2)

theorem map_rpmGame (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs)) :
    (fun z : RpmOut F => (z.1, z.2.1, permutationQueries z.2.2)) <$>
        Common.runWithRandomPermutation (rpmGame W D setup A) = rpmThreaded W D setup A := by
  have hA : ∀ ir E, (simulateQ loggedRandomPermutationOracles (A ir)).run (E, []) =
      (fun p => (p.1.1, p.2, permutationQueries p.1.2)) <$>
        (simulateQ Common.lazyRandomPermutationOracles
          ((simulateQ Common.loggedOracles (A ir)).run [])).run E := by
    intro ir E
    rw [logged_run (A ir) [] E]
    simp [permutationQueries_nil]
  simp only [rpmGame, rpmThreaded, Common.runWithRandomPermutation, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure, hA, bind_map_left,
    simulateQ_lazy_keccakCallsOverQueryPermutation]

theorem prEvent_rpmGame (c₁ : TableCode B.Msg₁) (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs)) :
    Pr{let z ← Common.runWithRandomPermutation (rpmGame W D setup A)}[BreaksRpm W c₁ z] =
      Pr{let z ← rpmThreaded W D setup A}[BreaksT W c₁ z] := by
  rw [← map_rpmGame, prEvent_map]
  rfl

/-! ## The transfer game -/

/-- Keccak-256 calls read on bytes, as `common`'s honest part before the adversary (Keccak-f is
never called there: `HOnly`). -/
def toRH : QueryImpl KeccakCalls
    (OracleComp (unifSpec + Common.roSpec (List UInt8) Common.DigestBytes))
  | .inl m => LeanVM.Digest.ofRpm <$>
      (liftM ((unifSpec + Common.roSpec (List UInt8) Common.DigestBytes).query (.inr m)) :
        OracleComp _ Common.DigestBytes)
  | .inr s => pure s

/-- The setup on bytes, its log. -/
def preB (setup : OracleComp KeccakCalls Bytes32) :
    OracleComp (unifSpec + Common.roSpec (List UInt8) Common.DigestBytes) (Bytes32 × Transcript) :=
  simulateQ toRH (loggedKC setup)

/-- A query of the adversary (coins, `π`, `π⁻¹`), read on bytes. -/
def relPC : QueryImpl Common.RandomPermutationOracles (OracleComp RSpec)
  | .inl n => (liftM (RSpec.query (.inl n)) : OracleComp RSpec (Fin (n + 1)))
  | .inr q => relP q

/-- A query of the adversary read on bytes, a permutation query recorded in the transcript. -/
def logRelC : QueryImpl Common.RandomPermutationOracles
    (StateT PermutationTranscript (OracleComp RSpec))
  | .inl n => StateT.mk fun T =>
      (fun u => (u, T)) <$> (liftM (RSpec.query (.inl n)) : OracleComp RSpec (Fin (n + 1)))
  | .inr q => logRel q

/-- The adversary on bytes, with its transcript. -/
def advB (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs))
    (x : Bytes32 × Transcript) :
    OracleComp RSpec ((RootProof F × OpenProofs) × PermutationTranscript) :=
  (simulateQ logRelC (A x.1)).run []

/-- The verifier on bytes. -/
def postB (x : Bytes32 × Transcript)
    (a : (RootProof F × OpenProofs) × PermutationTranscript) : OracleComp HFSpec (RpmOutT F) :=
  (fun v => ((withIr x.1 a.1, v), x.2, a.2)) <$> simulateQ toRHF (verifyD W D (withIr x.1 a.1))

/-- **The transfer game** of the experiment: the setup, the adversary, the verifier. -/
def gameB (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs)) :
    OracleComp D2Spec (RpmOutT F) :=
  Common.rpmGame2 (preB setup) (advB A) (postB W D)

/-! ## The experiment is the transfer game's real world -/

theorem hOnly_loggedKC_run {α : Type} (v : OracleComp KeccakCalls α) (hv : HOnly v) :
    ∀ l : Transcript, HOnly ((simulateQ logImplKC v).run l) := by
  induction v using OracleComp.inductionOn with
  | pure a => intro l; trivial
  | query_bind t k ih =>
    intro l
    rw [LeanVM.Rpm.hOnly_query_bind] at hv
    rw [loggedKC_run_query_bind, LeanVM.Rpm.hOnly_query_bind]
    rcases t with x | s
    · exact fun u => ih u (hv u) _
    · exact hv

/-- A computation of Keccak-256 only, as the honest part before the adversary, is the
computation as the honest part after it. -/
theorem hEmbed2_toRH {α : Type} (X : OracleComp KeccakCalls α) (hX : HOnly X) :
    simulateQ (Common.hEmbed2 (E := Common.KRest) (C := Common.KCap)) (simulateQ toRH X) =
      simulateQ Common.hfEmbed (simulateQ toRHF X) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [LeanVM.Rpm.hOnly_query_bind] at hX
    rcases t with m | s
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, toRH, toRHF, bind_map_left]
      simp only [Common.hQuery, LeanVM.Rpm.hq_eq, simulateQ_spec_query, Common.hEmbed2,
        Common.hfEmbed]
      exact bind_congr fun u => ih _ (hX _)
    · exact hX.elim

theorem RR_advEmbed_coin (n : ℕ) :
    (RR ∘ₛ Common.advEmbed) (.inl n) =
      (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
        StateT (Common.PermutationEdges Common.KState) ProbComp (Fin (n + 1))) := by
  simp [Common.advEmbed, Common.toOne, Common.realImpl]

/-- **The adversary on bytes with its transcript, in the real world, is the adversary of the
experiment** (coins included), the permutation's edges read on lanes. -/
theorem adv_relabelC {α : Type} (A : OracleComp Common.RandomPermutationOracles α)
    (s : Common.PermutationEdges Common.KState) (T : PermutationTranscript) :
    (fun p ↦ (p.1.1, (projLog p.2, p.1.2))) <$>
        (simulateQ (RR ∘ₛ Common.advEmbed) ((simulateQ logRelC A).run T)).run s =ᵈ
      (simulateQ loggedRandomPermutationOracles A).run (projLog s, T) := by
  induction A using OracleComp.inductionOn generalizing s T with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact EvalDistEq.rfl
  | query_bind t k ih =>
    rcases t with n | q
    · simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query, logRelC,
        loggedRandomPermutationOracles, StateT.run_mk, bind_map_left, map_bind,
        RR_advEmbed_coin]
      simp only [liftM, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact EvalDistEq.bind_right _ fun u => ih u s T
    · have hq : LeanVM.Rpm.mapQ LeanVM.Rpm.stateEquiv q = permQueryToRpm q := by cases q <;> rfl
      have hrel : simulateQ (RR ∘ₛ Common.advEmbed) (relP q) =
          LeanVM.Rpm.KState.ofRpm <$> Common.lazyRandomPermutation (permQueryToRpm q) := by
        rw [relP, simulateQ_map, simulateQ_spec_query, LeanVM.Rpm.RR_advEmbed_perm]
      simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query, logRelC, logRel,
        loggedRandomPermutationOracles, StateT.run_mk, hrel, bind_map_left, map_bind]
      calc _ =ᵈ ((Common.lazyRandomPermutation (permQueryToRpm q)).run s >>= fun a ↦
              (simulateQ loggedRandomPermutationOracles (k (LeanVM.Rpm.KState.ofRpm a.1))).run
                (projLog a.2, T ++ [(q, LeanVM.Rpm.KState.ofRpm a.1)])) :=
            EvalDistEq.bind_right _ fun a ↦ ih _ _ _
        _ = ((Prod.map LeanVM.Rpm.KState.ofRpm projLog <$>
              (Common.lazyRandomPermutation (permQueryToRpm q)).run s) >>=
              fun a ↦ (simulateQ loggedRandomPermutationOracles (k a.1)).run
                (a.2, T ++ [(q, a.1)])) := by
            rw [bind_map_left]; rfl
        _ =ᵈ _ := EvalDistEq.bind_left
            (by rw [← hq]; exact LeanVM.Rpm.lazyPerm_relabel LeanVM.Rpm.stateEquiv q s) _

/-- **The experiment is the real world of the transfer game**: the setup its honest part before
the adversary, the adversary (with coins) on bytes, the verifier on bytes. -/
theorem rpmThreaded_evalDistEq (setup : OracleComp KeccakCalls Bytes32) (hS : HOnly setup)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs)) :
    rpmThreaded W D setup A =ᵈ
      Common.realGame2 Common.keccakPadding Common.KState.zero (gameB W D setup A) := by
  rw [LeanVM.Rpm.realGame2_eq, gameB, Common.rpmGame2, preB,
    hEmbed2_toRH (loggedKC setup) (hOnly_loggedKC_run setup hS [])]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  simp only [postB, simulateQ_map, StateT.run_map, Functor.map_map, RR,
    QueryImpl.simulateQ_compose]
  have hpre := (LeanVM.Rpm.post_relabel (loggedKC setup) []).symm
  simp only [projLog, LeanVM.Rpm.logMap, List.map_nil, RR, QueryImpl.simulateQ_compose] at hpre
  rw [rpmThreaded]
  refine EvalDistEq.trans (EvalDistEq.bind_left hpre _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun x => ?_
  have hadv := (adv_relabelC (A x.1.1) x.2 []).symm
  simp only [RR, QueryImpl.simulateQ_compose] at hadv
  simp only [advB]
  refine EvalDistEq.trans (EvalDistEq.bind_left hadv _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun p => ?_
  have h := (LeanVM.Rpm.post_relabel' (verifyD W D (withIr x.1.1 p.1.1)) p.2).symm.map
    fun v => ((withIr x.1.1 p.1.1, v), x.1.2, p.1.2)
  simp only [StateT.run'_eq, Functor.map_map, RR, QueryImpl.simulateQ_compose] at h
  simp only [StateT.run'_eq, bind_pure_comp, Functor.map_map]
  exact h

/-! ## The transfer game's discipline and permutation calls -/

theorem hOnly_hash256 (x : List UInt8) : HOnly (hash256 x) :=
  (LeanVM.Rpm.hOnly_queryH x).bind fun _ => trivial

theorem hOnly_chain (π : RootProof F) : HOnly (chainWith W hash256 π) := by
  simp only [chainWith]
  exact (hOnly_hash256 _).bind fun _ => (hOnly_hash256 _).bind fun _ =>
    (hOnly_hash256 _).bind fun _ => (hOnly_hash256 _).bind fun _ =>
      (hOnly_hash256 _).bind fun _ => (hOnly_hash256 _).bind fun _ => trivial

/-- **`opening::verify` follows the duplex discipline**: its one direct call before the program
is the seed, zero from lane `8` on. -/
theorem duplexVm_ourVerifier (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof) :
    DuplexVm (ourVerifier L R w) [] := by
  rw [LeanVM.Rpm.duplexVm_iff_duplexP]
  unfold ourVerifier openingVerifyWithHash
  split_ifs
  · refine ((LeanVM.Rpm.hOnly_queryH _).duplexP []).bind fun iv h' hh => ?_
    subst hh
    exact (LeanVM.Rpm.duplexP_queryF_bind _ _ _ _).mpr
      ⟨LeanVM.Rpm.admissibleVm_seedInput _ _ _, fun seed =>
        LeanVM.Rpm.duplexP_runProof _ List.mem_cons_self _⟩
  · refine ((LeanVM.Rpm.hOnly_queryH _).duplexP []).bind fun iv h' hh => ?_
    subst hh
    exact (LeanVM.Rpm.duplexP_queryF_bind _ _ _ _).mpr
      ⟨LeanVM.Rpm.admissibleVm_seedInput _ _ _, fun seed => trivial⟩
  · trivial

/-- **The deployed verifier follows the duplex discipline.** -/
theorem duplexVm_verifyD (po : RootProof F × OpenProofs) : DuplexVm (verifyD W D po) [] := by
  unfold verifyD
  refine LeanVM.Rpm.DuplexVm.bind ?_ fun ch => ?_
  · rw [LeanVM.Rpm.duplexVm_iff_duplexP]
    exact ((hOnly_chain W po.1).duplexP []).mono fun _ _ _ => trivial
  · exact LeanVM.Rpm.DuplexVm.bind (duplexVm_ourVerifier _ _ _) fun _ =>
      LeanVM.Rpm.DuplexVm.bind (duplexVm_ourVerifier _ _ _) fun _ =>
        LeanVM.Rpm.DuplexVm.bind (duplexVm_ourVerifier _ _ _) fun _ => trivial

theorem duplex_postB (x : Bytes32 × Transcript)
    (a : (RootProof F × OpenProofs) × PermutationTranscript) :
    Common.Duplex Common.KState.zero Common.keccakNF (postB W D x a) [] := by
  have h := LeanVM.Rpm.duplex_toRHF _ [] (duplexVm_verifyD W D (withIr x.1 a.1))
  exact LeanVM.Rpm.duplex_map _ _ [] (by simpa using h)

theorem cost_hash256_bind {β : Type} (x : List UInt8) (k : Bytes32 → OracleComp KeccakCalls β)
    (n : ℕ) (hx : x.length / 136 + 1 ≤ n)
    (hk : ∀ u, Common.QueryCostAtMost (k u) hashBlocks (n - (x.length / 136 + 1))) :
    Common.QueryCostAtMost (hash256 x >>= k) hashBlocks n := by
  rw [hash256, callKeccak256, bind_assoc]
  simp only [pure_bind]
  exact (Common.isWeightBound_query_bind_iff hashBlocks (.inl x) _ n).mpr ⟨hx, fun u => hk _⟩

/-- **The chain makes seven calls of `π`**: six hashes, of one block each but the last's two. -/
theorem cost_chain (π : RootProof F) :
    Common.QueryCostAtMost (chainWith W hash256 π) hashBlocks 7 := by
  simp only [chainWith]
  refine cost_hash256_bind _ _ 7 (by simp [length_labelOf]) fun _ => ?_
  refine cost_hash256_bind _ _ _ (by simp [length_labelOf]) fun _ => ?_
  refine cost_hash256_bind _ _ _ (by simp [length_labelOf]) fun _ => ?_
  refine cost_hash256_bind _ _ _ (by simp [length_labelOf]) fun _ => ?_
  refine cost_hash256_bind _ _ _ (by simp [length_labelOf]) fun _ => ?_
  refine cost_hash256_bind _ _ _ (by simp [length_labelOf]) fun _ => ?_
  exact Common.isWeightBound_pure _ _ _

theorem cost_verifyD (QOπ : ℕ)
    (hOπ : ∀ (L : Layout) w, Common.QueryCostAtMost (ourVerifier L D.R w) hashBlocks QOπ)
    (po : RootProof F × OpenProofs) :
    Common.QueryCostAtMost (verifyD W D po) hashBlocks (7 + (QOπ + (QOπ + (QOπ + 0)))) :=
  (cost_chain W po.1).bind fun _ => (hOπ _ _).bind fun _ => (hOπ _ _).bind fun _ =>
    (hOπ _ _).bind fun _ => Common.isWeightBound_pure _ _ 0

theorem cost_loggedKC {α : Type} (v : OracleComp KeccakCalls α) (n : ℕ)
    (hv : Common.QueryCostAtMost v hashBlocks n) (l : Transcript) :
    Common.QueryCostAtMost ((simulateQ logImplKC v).run l) hashBlocks n :=
  Common.isWeightBound_run_simulateQ logImplKC hashBlocks hashBlocks
    (fun t _ => Common.isWeightBound_map _ (Common.isWeightBound_query hashBlocks t)) hv l

theorem cost_advB (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs))
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (x : Bytes32 × Transcript) : Common.QueryCostAtMost (advB A x) LeanVM.Rpm.advCost Q := by
  refine Common.isWeightBound_run_simulateQ logRelC Common.permutationCallCost LeanVM.Rpm.advCost
    (fun t T => ?_) (hA x.1) []
  rcases t with n | q
  · exact Common.isWeightBound_map _ (Common.isWeightBound_query LeanVM.Rpm.advCost (.inl n))
  · simp only [logRelC, logRel, StateT.run_mk, relP]
    exact Common.isWeightBound_map _ (Common.isWeightBound_map _
      (Common.isWeightBound_query LeanVM.Rpm.advCost (.inr (.inr (permQueryToRpm q)))))

/-- **The permutation calls of the transfer game**: the setup's `QSπ`, the adversary's `Q`, the
chain's `7` and the three openings' `QOπ` each. -/
theorem cost_gameB (setup : OracleComp KeccakCalls Bytes32) (hS : HOnly setup) (QSπ : ℕ)
    (hSπ : Common.QueryCostAtMost setup hashBlocks QSπ)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof F × OpenProofs))
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q) (QOπ : ℕ)
    (hOπ : ∀ (L : Layout) w, Common.QueryCostAtMost (ourVerifier L D.R w) hashBlocks QOπ) :
    Common.QueryCostAtMost (gameB W D setup A)
      (Common.queryCost2 (Dg := Common.DigestBytes) Common.keccakPadding)
      (QSπ + Q + 7 + 3 * QOπ) := by
  have h : Common.QueryCostAtMost (gameB W D setup A) LeanVM.Rpm.gameCost
      (QSπ + (Q + (7 + (QOπ + (QOπ + (QOπ + 0)))))) := by
    rw [gameB, Common.rpmGame2, preB, hEmbed2_toRH (loggedKC setup) (hOnly_loggedKC_run setup hS [])]
    refine (LeanVM.Rpm.isWeightBound_hfEmbed_toRHF (cost_loggedKC setup QSπ hSπ [])).bind
      fun x => ?_
    refine (LeanVM.Rpm.isWeightBound_advEmbed (cost_advB A Q hA x)).bind fun a => ?_
    rw [postB, simulateQ_map]
    exact Common.isWeightBound_map _
      (LeanVM.Rpm.isWeightBound_hfEmbed_toRHF (cost_verifyD W D QOπ hOπ _))
  exact h.mono (by omega)

/-! ## The random-oracle side: the transcript's evaluations are the adversary's cache -/

/-- The two calls as queries of the two random oracles with coins. -/
def liftKC : QueryImpl KeccakCalls (OracleComp CSpec) := fun t => liftM (CSpec.query (.inr t))

theorem run_liftKC {α : Type} (X : OracleComp KeccakCalls α) (c : KeccakCalls.QueryCache) :
    (simulateQ KeccakCalls.romImpl (simulateQ liftKC X)).run c =
      (simulateQ randomOracle X).run c := by
  rw [← QueryImpl.simulateQ_compose]
  congr 2
  funext t
  simp [liftKC, QueryImpl.apply_compose]

/-- The setup on bytes, read back on lanes, is the setup. -/
theorem ofRHF_hInF_toRH {α : Type} (X : OracleComp KeccakCalls α) (hX : HOnly X) :
    simulateQ ofRHF (simulateQ (Common.hInF (E := Common.KRest) (C := Common.KCap))
      (simulateQ toRH X)) = simulateQ liftKC X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [LeanVM.Rpm.hOnly_query_bind] at hX
    rcases t with m | s
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, toRH, bind_map_left]
      simp only [Common.hInF, simulateQ_spec_query, ofRHF, liftKC, bind_map_left,
        LeanVM.Rpm.digestOfRpm_toRpm]
      exact bind_congr fun u => ih _ (hX _)
    · exact hX.elim

/-- Logging changes nothing of a computation. -/
theorem fst_loggedKC_run {α : Type} (v : OracleComp KeccakCalls α) :
    ∀ l : Transcript, Prod.fst <$> (simulateQ logImplKC v).run l = v := by
  induction v using OracleComp.inductionOn with
  | pure a => intro l; simp
  | query_bind t k ih =>
    intro l
    rw [loggedKC_run_query_bind, map_bind]
    exact bind_congr fun u => ih u _

/-- **The adversary with the simulator, on lanes, with its transcript.** -/
noncomputable def romAdvT (A : Bytes32 → OracleComp Common.RandomPermutationOracles
    (RootProof F × OpenProofs)) (x : Bytes32 × Transcript) :
    OracleComp CSpec ((RootProof F × OpenProofs) × PermutationTranscript) :=
  simulateQ ofRHF (Common.advS2 Common.keccakPadding Common.KState.zero (advB A x))

/-- **The random-oracle adversary of the transfer**: the adversary with the indifferentiability
simulator (`Common.advS2`), with coins, its queries read on lanes. -/
noncomputable def romAdvC (A : Bytes32 → OracleComp Common.RandomPermutationOracles
    (RootProof F × OpenProofs)) (ir : Bytes32) : OracleComp CSpec (RootProof F × OpenProofs) :=
  Prod.fst <$> romAdvT A (ir, [])

/-- The verifier from the cache after the adversary, that cache kept. -/
noncomputable def gL (p : (Bytes32 × (RootProof F × OpenProofs)) × KeccakCalls.QueryCache) :
    ProbComp (((RootProof F × OpenProofs) × Verd F) × KeccakCalls.QueryCache) :=
  (fun v => ((withIr p.1.1 p.1.2, v), p.2)) <$>
    (simulateQ randomOracle (verifyD W D (withIr p.1.1 p.1.2))).run' p.2

/-- **The event on the cache after the adversary**: the verifier accepts while, for every transcript
recording that cache's Keccak-256 answers, the extractor's list holds no witness. -/
def BreaksC (c₁ : TableCode B.Msg₁)
    (z : ((RootProof F × OpenProofs) × Verd F) × KeccakCalls.QueryCache) : Prop :=
  AcceptedV (P := P) z.1 ∧ ∀ tr, Consistent tr z.2 → ∀ g ∈ adversaryExtractor c₁ tr z.1.1.1,
    ¬ P.Sat (W.decode z.1.1.1.stmt) (P.cells g.1)

/-! ### The extractor reads the answers a transcript records -/

theorem lookTr_eq_map (tr : Transcript) (x : List UInt8) :
    lookTr tr x = ((tr.find? fun e => decide (e.1 = x)).map Prod.snd).map LeanVM.Digest.ofRpm := by
  simp [lookTr, Option.map_map, Function.comp_def]

theorem mem_histOfTr_iff (tr : Transcript) (x : List UInt8) :
    x ∈ histOfTr tr ↔ ((tr.find? fun e => decide (e.1 = x)).map Prod.snd).isSome := by
  simp only [histOfTr, List.mem_toFinset, List.mem_map, Option.isSome_map, List.find?_isSome,
    decide_eq_true_eq]

/-- **Two transcripts recording the same answers have the same extractor.** -/
theorem adversaryExtractor_congr (c₁ : TableCode B.Msg₁) {tr tr' : Transcript}
    (h : ∀ x, lookTr tr x = lookTr tr' x) (π : RootProof F) :
    adversaryExtractor c₁ tr π = adversaryExtractor c₁ tr' π := by
  have hs : ∀ x, (tr.find? fun e => decide (e.1 = x)).map Prod.snd =
      (tr'.find? fun e => decide (e.1 = x)).map Prod.snd := fun x => by
    have := h x
    rw [lookTr_eq_map, lookTr_eq_map] at this
    exact Option.map_injective (LeanVM.Rpm.digestEquiv.symm.injective) this
  have hH : histOfTr tr = histOfTr tr' := by
    ext x
    rw [mem_histOfTr_iff, mem_histOfTr_iff, hs x]
  have hT : tableOfTr tr = tableOfTr tr' := by
    funext x
    simp only [tableOfTr, hs x]
  simp only [adversaryExtractor, hH, hT]

theorem lookTr_append' (l₁ l₂ : Transcript) (x : List UInt8) :
    lookTr (l₁ ++ l₂) x = match lookTr l₁ x with
      | some d => some d
      | none => lookTr l₂ x := by
  unfold lookTr
  rw [List.find?_append]
  cases l₁.find? fun e => decide (e.1 = x) <;> rfl

theorem lookTr_evalTr (T : PermutationTranscript) (x : List UInt8) :
    lookTr (evalTr T) x = lookupEvaluation (keccakEvaluationsOfTranscript T) x := by
  simp [lookTr, evalTr, lookupEvaluation, List.find?_map, Function.comp_def,
    LeanVM.Rpm.digestOfRpm_toRpm]

/-! ### The adversary's cache (mumbai's `Rpm/Extract.lean`, from a filled cache, with coins) -/

/-- **The lane transcript is the byte log**, coins included (mumbai's `advImpl2_logRel`). -/
theorem advImpl2_logRelC {α : Type} (B : OracleComp Common.RandomPermutationOracles α)
    (T : PermutationTranscript) (σ : LeanVM.Rpm.KSim) :
    (fun x ↦ (x.1.1, (x.2, x.1.2.map LeanVM.Rpm.entryToRpm))) <$>
        (simulateQ (Common.advImpl2 Common.keccakPadding) ((simulateQ logRelC B).run T)).run σ =
      (simulateQ (Common.advImplLog2 Common.keccakPadding) (simulateQ relPC B)).run
        (σ, T.map LeanVM.Rpm.entryToRpm) := by
  induction B using OracleComp.inductionOn generalizing T σ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | q
    · simp only [StateT.run_bind, OracleQuery.input_query, relPC, logRelC,
        StateT.run_mk, bind_map_left, simulateQ_bind, simulateQ_query,
        OracleQuery.cont_query, id_map, map_bind]
      have h2 : (Common.advImplLog2 Common.keccakPadding (.inl n)).run
          (σ, T.map LeanVM.Rpm.entryToRpm) = (fun z ↦ (z.1, (z.2, T.map LeanVM.Rpm.entryToRpm)))
            <$> (Common.advImpl2 (Msg := Bytes) Common.keccakPadding (.inl n)).run σ := rfl
      rw [h2, bind_map_left]
      refine bind_congr fun z ↦ ?_
      rw [← ih]
    · simp only [StateT.run_bind, OracleQuery.input_query, relPC, relP, logRelC, logRel,
        StateT.run_mk, bind_map_left, simulateQ_bind, simulateQ_query,
        OracleQuery.cont_query, id_map, map_bind]
      have h1 : (Common.advImpl2 Common.keccakPadding (.inr (.inr (permQueryToRpm q)))).run σ =
          (Common.simulator2 (Msg := Bytes) Common.keccakPadding (permQueryToRpm q)).run σ := rfl
      have h2 : (Common.advImplLog2 Common.keccakPadding (.inr (.inr (permQueryToRpm q)))).run
          (σ, T.map LeanVM.Rpm.entryToRpm) = (fun z ↦ (z.1, (z.2, T.map LeanVM.Rpm.entryToRpm ++
            [(permQueryToRpm q, z.1)]))) <$>
              (Common.simulator2 (Msg := Bytes) Common.keccakPadding (permQueryToRpm q)).run σ :=
        rfl
      rw [h1, h2, bind_map_left]
      refine bind_congr fun z ↦ ?_
      have e : T.map LeanVM.Rpm.entryToRpm ++ [(permQueryToRpm q, z.1)] =
          (T ++ [(q, LeanVM.Rpm.KState.ofRpm z.1)]).map LeanVM.Rpm.entryToRpm := by
        simp [LeanVM.Rpm.entryToRpm, LeanVM.Rpm.toRpm_ofRpm]
      rw [e, ← ih]

/-- The transfer's adversary is the adversary with the simulator logging the byte queries, its
log read on lanes. -/
theorem advS2_advB (A : Bytes32 → OracleComp Common.RandomPermutationOracles
    (RootProof F × OpenProofs)) (x : Bytes32 × Transcript) :
    Common.advS2 Common.keccakPadding Common.KState.zero (advB A x) =
      (fun y ↦ (y.1, y.2.2.map LeanVM.Rpm.entryOfRpm)) <$>
        (simulateQ (Common.advImplLog2 Common.keccakPadding) (simulateQ relPC (A x.1))).run
          (Common.SimState.init Common.KState.zero, []) := by
  have h := advImpl2_logRelC (A x.1) [] (Common.SimState.init Common.KState.zero)
  rw [List.map_nil] at h
  rw [← h, Functor.map_map, Common.advS2, advB, StateT.run'_eq]
  congr 1
  funext y
  simp only [List.map_map]
  have e : LeanVM.Rpm.entryOfRpm ∘ LeanVM.Rpm.entryToRpm = id :=
    funext LeanVM.Rpm.entryOfRpm_toRpm
  rw [e, List.map_id]

/-- **Every Keccak-256 answer in the cache was there at the start or is a rooted path's.** -/
def CacheRel (c₀ : HFS.QueryCache) (σ : LeanVM.Rpm.KSim) (c : HFS.QueryCache) : Prop :=
  ∀ m d, c (.inl m) = some d → c₀ (.inl m) = some d ∨
    (m, d) ∈ Common.simPaths Common.keccakPadding σ

/-- **One step of the simulator keeps the relation** (mumbai's `cacheInv_step`). -/
theorem cacheRel_step (c₀ : HFS.QueryCache) (q : Common.PermutationQuery Common.KState)
    (σ : LeanVM.Rpm.KSim) (c : HFS.QueryCache) (h : CacheRel c₀ σ c)
    {v : (Common.KState × LeanVM.Rpm.KSim) × HFS.QueryCache}
    (hv : v ∈ support ((simulateQ HFS.romImpl
      ((Common.simulator2 (Msg := Bytes) Common.keccakPadding q).run σ)).run c)) :
    CacheRel c₀ v.1.2 v.2 := by
  cases q with
  | inverse y =>
    simp only [Common.simulator2, StateT.run_mk] at hv
    split at hv
    · simp at hv; subst hv; exact h
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM_run, simulateQ_pure,
        StateT.run_pure, bind_map_left, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hv
      obtain ⟨_, -, rfl⟩ := hv
      exact h
  | forward x =>
    simp only [Common.simulator2, StateT.run_mk] at hv
    split at hv
    · simp at hv; subst hv; exact h
    · split at hv
      · next s β hch =>
        simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        rcases hm : Common.keccakPadding.unpad (β ++ [Common.blockTo s x]) with _ | m
        · rw [Common.rootedAnswer2_run_none _ hm] at hw
          obtain ⟨-, -, hc⟩ := Common.roStep_support _ c hw
          intro m' d hd
          rw [hc _ (by simp)] at hd
          exact (h m' d hd).imp_right LeanVM.Rpm.mem_simPaths_cons
        · rw [Common.rootedAnswer2_run_some _ hm] at hw
          simp only [mem_support_bind_iff, support_uniformSample, Set.mem_univ, true_and,
            support_pure, Set.mem_singleton_iff] at hw
          obtain ⟨w', hw', ec, rfl⟩ := hw
          obtain ⟨-, hself, hc⟩ := Common.roStep_support _ c hw'
          intro m' d hd
          by_cases hmm : m' = m
          · subst hmm
            rw [hself, Option.some_inj] at hd
            subst hd
            exact Or.inr (by simp [Common.simPaths, hm])
          · rw [hc _ (by simpa using hmm)] at hd
            exact (h m' d hd).imp_right LeanVM.Rpm.mem_simPaths_cons
      · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          Common.fQuery_run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        obtain ⟨-, -, hc⟩ := Common.roStep_support _ c hw
        intro m' d hd
        rw [hc _ (by simp)] at hd
        exact h m' d hd

/-- A coin of the adversary changes neither the simulator's state nor the cache. -/
theorem foldRO_coin (n : ℕ)
    (s : (LeanVM.Rpm.KSim × LeanVM.Rpm.RLog) × HFS.QueryCache)
    {v : RSpec.Range (.inl n) × (LeanVM.Rpm.KSim × LeanVM.Rpm.RLog) × HFS.QueryCache}
    (hv : v ∈ support ((Common.foldRO (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding)
      (.inl n)).run s)) : v.2 = s := by
  rw [Common.foldRO_run] at hv
  simp only [Common.advImplLog2, Common.advImpl2, StateT.run_mk, support_map,
    Set.mem_image] at hv
  obtain ⟨y, hy, rfl⟩ := hv
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  simp only [StateT.run_monadLift, monadLift_self, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hy'
  obtain ⟨x, hx, rfl⟩ := hy'
  rw [simulateQ_romImpl_liftM_run, support_map] at hx
  obtain ⟨u, -, rfl⟩ := hx
  rfl

/-- **The relation along the adversary's run** (mumbai's `cacheInv_run`), coins included. -/
theorem cacheRel_run {α : Type} (c₀ : HFS.QueryCache)
    (B : OracleComp Common.RandomPermutationOracles α)
    (s : (LeanVM.Rpm.KSim × LeanVM.Rpm.RLog) × HFS.QueryCache) (hs : CacheRel c₀ s.1.1 s.2) :
    ∀ w ∈ support ((simulateQ (Common.foldRO
        (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding)) (simulateQ relPC B)).run s),
      CacheRel c₀ w.2.1.1 w.2.2 := by
  induction B using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro w hw
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hs
  | query_bind t k ih =>
    intro w hw
    rcases t with n | q
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, relPC, StateT.run_bind, mem_support_bind_iff] at hw
      obtain ⟨v, hv, hw⟩ := hw
      refine ih _ v.2 ?_ w hw
      rw [foldRO_coin n s hv]
      exact hs
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, relPC, relP, bind_map_left, StateT.run_bind, mem_support_bind_iff] at hw
      obtain ⟨v, hv, hw⟩ := hw
      refine ih _ v.2 ?_ w hw
      rw [Common.foldRO_run] at hv
      simp only [support_map, Set.mem_image] at hv
      obtain ⟨y, hy, rfl⟩ := hv
      have e : (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding
          (.inr (.inr (permQueryToRpm q)))).run s.1 =
          (fun z ↦ (z.1, (z.2, s.1.2 ++ [(permQueryToRpm q, z.1)]))) <$>
            (Common.simulator2 (Msg := Bytes) Common.keccakPadding (permQueryToRpm q)).run
              s.1.1 := rfl
      rw [e, simulateQ_map, StateT.run_map, support_map] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      exact cacheRel_step c₀ _ _ _ hs hu

/-- **The hash queries of the adversary's transcript are cached**, from any starting cache
(`common`'s `pathsOf_ideal2`, from a filled cache). -/
theorem pathsOf_ideal2C {α : Type} (X : OracleComp RSpec α) (c₀ : HFS.QueryCache) {z}
    (hz : z ∈ support ((simulateQ (Common.foldRO (Common.advImplLog2 (Msg := Bytes)
      Common.keccakPadding)) X).run ((Common.SimState.init Common.KState.zero, []), c₀))) :
    ∀ md ∈ Common.pathsOf Common.keccakPadding Common.KState.zero z.2.1.2,
      z.2.2 (.inl md.1) = some md.2 := by
  have hRO := Common.inv_of_mem_support_run (spec' := unifSpec)
    (Common.foldRO (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding))
    (fun s ↦ ∀ md ∈ Common.simPaths Common.keccakPadding s.1.1, s.2 (.inl md.1) = some md.2)
    (fun t s hs w hw ↦ Common.roOK2_step Common.keccakPadding t s hs hw) X
    (s := ((Common.SimState.init Common.KState.zero, []), c₀)) (by
      simp only [Common.simPaths, Common.SimState.init, List.filterMap_cons, List.filterMap_nil]
      rcases h : Common.keccakPadding.unpad [] with _ | a
      · simp
      · exact absurd ((Common.keccakPadding.unpad_eq_some_iff _ _).mp h)
          (Common.keccakPadding.pad_ne_nil a))
    z hz
  have h1 := Common.run_simulateQ_foldRO (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding)
    X (Common.SimState.init Common.KState.zero, []) c₀
  have hz' : ((z.1, z.2.1), z.2.2) ∈ support ((simulateQ HFS.romImpl
      ((simulateQ (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding) X).run
        (Common.SimState.init Common.KState.zero, []))).run c₀) := by
    rw [h1, support_map]
    exact ⟨z, hz, rfl⟩
  have hrep := Common.simulator2_state_eq_replay Common.keccakPadding Common.KState.zero X
    (Common.fst_mem_support_of_mem_support_ro2 hz')
  intro md hmd
  rw [Common.pathsOf, ← hrep] at hmd
  exact hRO md hmd

/-- **The adversary's cache** after the adversary with the simulator, from a cache `c₀`: it extends
`c₀`, holds every Keccak-256 evaluation of the adversary's transcript, and holds no other new
Keccak-256 answer. -/
theorem adv_cache (A : Bytes32 → OracleComp Common.RandomPermutationOracles
    (RootProof F × OpenProofs)) (x : Bytes32 × Transcript) (c₀ : HFS.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HFS.romImpl
      (Common.advS2 Common.keccakPadding Common.KState.zero (advB A x))).run c₀)) :
    c₀ ≤ z.2 ∧ (∀ md ∈ LeanVM.Rpm.transcriptPathsB z.1.2, z.2 (.inl md.1) = some md.2) ∧
      (∀ m d, z.2 (.inl m) = some d → c₀ (.inl m) = some d ∨
        (m, d) ∈ LeanVM.Rpm.transcriptPathsB z.1.2) := by
  refine ⟨Common.le_of_mem_support_run _ c₀ hz, ?_⟩
  rw [advS2_advB, simulateQ_map, StateT.run_map, Common.run_simulateQ_foldRO, Functor.map_map,
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

end Compose
