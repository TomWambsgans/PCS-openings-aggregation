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

end Compose
