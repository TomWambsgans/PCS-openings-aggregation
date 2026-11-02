-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Wiring

/-!
# The deployed composition, the wiring term discharged

`Deployed.lean` leaves the wiring opening's term `εσ` as a hypothesis. Here the run logs the wiring
opening's stage too (`wiredExp`), so that the wiring opening's doomed event at its end (`Eσw`) is an
event of `ours_sound`'s experiment (`prEvent_Eσw_le`), and an undoomed wiring opening gives the wiring
claim: the circuit's commitment is the setup's (`withSetup`), whose queries make its word the honest
encoding of the wiring stack (`WiringMatch.setupWord`), whose only candidate is that stack
(`candidates_honest`), whose table satisfies the wiring opening's claim only if F1's wiring claim
holds (`WiringMatch.claims`).

**`knowledgeSoundness_wired`**: the three openings' terms are F2's `ours_sound`, the bound
`openingBound (QS + Q + 6) + openingBound (QS + Q + 6 + QO) + openingBound (QS + Q + 6 + 2 QO) +
N (max L₁ (L₁ L₂) · roundError + 5 N / 2^256)`, `QO = 10122`, `N = QS + Q + 6 + 3 QO`. What stays:
the decoders and claims (`WitnessMatch`, `QuotientMatch`) and the wiring table's (`WiringMatch`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open LeanVM.Protocol.Rom (romExperiment romExperiment_map)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds}
variable (W : Wire P B) (D : Deploy F)

/-- The run through the wiring opening, logged: `((((a, bW), tW), bσ), tσ)`. -/
def innerσ (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) :
    OracleComp KeccakCalls ((((S0 F × Bool) × Transcript) × Bool) × Transcript) :=
  (simulateQ logImplKC (innerW W D A >>= fun x : (S0 F × Bool) × Transcript =>
    (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1))).run []

/-- **The deployed run, every opening's stage logged**: `(((((a, bW), tW), bσ), tσ), bQ), tQ)`. -/
def wiredExp (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) :
    OracleComp KeccakCalls ((((((S0 F × Bool) × Transcript) × Bool) × Transcript) × Bool) ×
      Transcript) :=
  (simulateQ logImplKC (innerσ W D A >>= fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
    (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1.1))).run []

/-- An outcome of the wired run. -/
abbrev WOut (F : Type) := (((((S0 F × Bool) × Transcript) × Bool) × Transcript) × Bool) × Transcript

/-! ## The events -/

/-- The witness opening accepts while doomed at its end. -/
def EWw (z : WOut F) : Prop :=
  z.1.1.1.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1.1.1.1.1) (cacheOfTr z.1.1.1.1.2)

/-- The wiring opening accepts while doomed at its end. -/
def Eσw (z : WOut F) : Prop :=
  z.1.1.1.2 = true ∧ OpeningDoomed D.Lσ D.R (σIn D z.1.1.1.1.1.1) (cacheOfTr z.1.1.2)

/-- The quotient opening accepts while doomed at its end. -/
def EQw (z : WOut F) : Prop :=
  z.1.2 = true ∧ OpeningDoomed D.LQ D.R (qIn D z.1.1.1.1.1.1) (cacheOfTr z.2)

/-- **Knowledge soundness is broken**: the verifier accepts (its own check and the three
openings) while the adversary's extractor's list holds no witness of the statement. -/
def BreaksW (c₁ : TableCode B.Msg₁) (z : WOut F) : Prop :=
  (reductionCheck P z.1.1.1.1.1.1.ch.α z.1.1.1.1.1.1.ch.β z.1.1.1.1.1.1.ch.t
    z.1.1.1.1.1.1.π.v.1 z.1.1.1.1.1.1.π.v.2 ∧ z.1.1.1.1.1.2 = true ∧ z.1.1.1.2 = true ∧
      z.1.2 = true) ∧
    ∀ g ∈ adversaryExtractor c₁ z.1.1.1.1.1.1.tA z.1.1.1.1.1.1.π,
      ¬ P.Sat (W.decode z.1.1.1.1.1.1.π.stmt) (P.cells g.1)

/-- **The wiring table**: the stack the setup commits to (`q₀`, its encoding `word`); the setup's
queries make the word the circuit's commitment commits to that encoding, on every history that
holds them without collision; and the stack's table satisfies the wiring opening's claim only if
F1's wiring claim holds. -/
structure WiringMatch (setup : OracleComp KeccakCalls Bytes32) where
  q₀ : Column D.Lσ.logN
  word : Word
  honest : HonestWord D.Lσ.logN D.R word q₀
  setupWord : ∀ (T : KTable) (H : Hist),
    (∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → x ∈ H) →
      Set.InjOn (viewT T) ↑H → ∀ p < 2 ^ rootHeight D.Lσ.logN D.R,
        Rom.extract (ansOf H (viewT T)) (ofB (evalWithAnswerFn (QueryImpl.ofFn T) setup))
          (rootHeight D.Lσ.logN D.R) (2 ^ laneFold) p = word p
  claims : ∀ (π : RootProof F) (ch : Chals F),
    (∀ cl ∈ (D.clσ π ch).claims, D.Lσ.tableEval q₀ cl.point = cl.value) →
      wiringClaim P ch.t π.v.2

/-! ## The three openings' terms are `ours_sound`'s -/

theorem isTotalQueryBound_innerW (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) : IsTotalQueryBound (innerW W D A) (Q + 6 + 10122) := by
  refine isTotalQueryBound_loggedKC_run _ _ _ ?_
  exact isTotalQueryBound_bind (ob := fun a : S0 F => (a, ·) <$> ourVerifier D.Lw D.R (wIn D a))
    (isTotalQueryBound_DA W A Q hQ) fun a =>
      (isQueryBound_map_iff (ourVerifier D.Lw D.R (wIn D a)) (fun b => (a, b)) 10122 _ _).mpr
        (ourVerifier_queryBound D.Lw D.R (wIn D a))

theorem isTotalQueryBound_innerσ (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) : IsTotalQueryBound (innerσ W D A) (Q + 6 + 10122 + 10122) := by
  refine isTotalQueryBound_loggedKC_run _ _ _ ?_
  exact isTotalQueryBound_bind
    (ob := fun x : (S0 F × Bool) × Transcript => (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1))
    (isTotalQueryBound_innerW W D A Q hQ) fun x =>
      (isQueryBound_map_iff (ourVerifier D.Lσ D.R (σIn D x.1.1)) (fun b => (x, b)) 10122 _
        _).mpr (ourVerifier_queryBound D.Lσ D.R _)

theorem isTotalQueryBound_wiredExp (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) :
    IsTotalQueryBound (wiredExp W D A) (Q + 6 + 10122 + 10122 + 10122) :=
  isTotalQueryBound_loggedKC_run _ _ _ (isTotalQueryBound_bind
    (ob := fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
      (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1.1))
    (isTotalQueryBound_innerσ W D A Q hQ) fun y =>
      (isQueryBound_map_iff (ourVerifier D.LQ D.R (qIn D y.1.1.1.1)) (fun b => (y, b)) 10122 _
        _).mpr (ourVerifier_queryBound D.LQ D.R _))

set_option maxHeartbeats 2000000 in
/-- **The witness opening's term.** -/
theorem prEvent_EWw_le (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows)
    (hLw : D.Lw = witnessLayout r ∨ D.Lw = wiringLayout r ∨ D.Lw = quotientLayout r)
    (hR : D.R = logInvRate) :
    Pr{let z ← (simulateQ randomOracle (wiredExp W D A)).run' ∅}[EWw D z] ≤
      openingBound (Q + 6) := by
  have hs := ours_sound r h1 h2 D.Lw hLw ((wIn D) <$> DA W A) (Q + 6)
    ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_DA W A Q hQ))
  rw [romExperiment_map, prEvent_map, ← hR] at hs
  calc Pr{let z ← (simulateQ randomOracle (wiredExp W D A)).run' ∅}[EWw D z]
      = Pr{let z ← (simulateQ randomOracle (innerσ W D A >>=
          fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1.1))).run' ∅}[
          z.1.1.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1.1.1.1) (cacheOfTr z.1.1.1.2)] :=
        prEvent_run'_loggedKC (innerσ W D A >>=
          fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1.1)) [] ∅
          fun w : ((((S0 F × Bool) × Transcript) × Bool) × Transcript) × Bool =>
            w.1.1.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D w.1.1.1.1.1) (cacheOfTr w.1.1.1.2)
    _ = Pr{let z ← (simulateQ randomOracle (innerσ W D A)).run' ∅}[
          z.1.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1.1.1) (cacheOfTr z.1.1.2)] :=
        prEvent_run'_bind_keep (innerσ W D A)
          (fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            ourVerifier D.LQ D.R (qIn D y.1.1.1.1)) ∅
          fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            y.1.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D y.1.1.1.1) (cacheOfTr y.1.1.2)
    _ = Pr{let z ← (simulateQ randomOracle (innerW W D A >>=
          fun x : (S0 F × Bool) × Transcript =>
            (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1))).run' ∅}[
          z.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1.1) (cacheOfTr z.1.2)] :=
        prEvent_run'_loggedKC (innerW W D A >>= fun x : (S0 F × Bool) × Transcript =>
            (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1)) [] ∅
          fun x' : ((S0 F × Bool) × Transcript) × Bool =>
            x'.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D x'.1.1.1) (cacheOfTr x'.1.2)
    _ = Pr{let z ← (simulateQ randomOracle (innerW W D A)).run' ∅}[
          z.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1) (cacheOfTr z.2)] :=
        prEvent_run'_bind_keep (innerW W D A)
          (fun x : (S0 F × Bool) × Transcript => ourVerifier D.Lσ D.R (σIn D x.1.1)) ∅
          fun x : (S0 F × Bool) × Transcript =>
            x.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D x.1.1) (cacheOfTr x.2)
    _ = Pr{let z ← romExperiment (DA W A) (fun a => ourVerifier D.Lw D.R (wIn D a))}[
          z.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1) z.2] :=
        prEvent_loggedPrefix (DA W A) (fun a => ourVerifier D.Lw D.R (wIn D a))
          (fun a b c => b = true ∧ OpeningDoomed D.Lw D.R (wIn D a) c)
          (readsInl_openingDoomed D.Lw D.R (wIn D))
    _ ≤ openingBound (Q + 6) := hs

set_option maxHeartbeats 2000000 in
/-- **The wiring opening's term.** -/
theorem prEvent_Eσw_le (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows)
    (hLσ : D.Lσ = witnessLayout r ∨ D.Lσ = wiringLayout r ∨ D.Lσ = quotientLayout r)
    (hR : D.R = logInvRate) :
    Pr{let z ← (simulateQ randomOracle (wiredExp W D A)).run' ∅}[Eσw D z] ≤
      openingBound (Q + 6 + 10122) := by
  have hs := ours_sound r h1 h2 D.Lσ hLσ
    ((fun x : (S0 F × Bool) × Transcript => σIn D x.1.1) <$> innerW W D A) (Q + 6 + 10122)
    ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_innerW W D A Q hQ))
  rw [romExperiment_map, prEvent_map, ← hR] at hs
  calc Pr{let z ← (simulateQ randomOracle (wiredExp W D A)).run' ∅}[Eσw D z]
      = Pr{let z ← (simulateQ randomOracle (innerσ W D A >>=
          fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1.1))).run' ∅}[
          z.1.1.2 = true ∧ OpeningDoomed D.Lσ D.R (σIn D z.1.1.1.1.1) (cacheOfTr z.1.2)] :=
        prEvent_run'_loggedKC (innerσ W D A >>=
          fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1.1)) [] ∅
          fun w : ((((S0 F × Bool) × Transcript) × Bool) × Transcript) × Bool =>
            w.1.1.2 = true ∧ OpeningDoomed D.Lσ D.R (σIn D w.1.1.1.1.1) (cacheOfTr w.1.2)
    _ = Pr{let z ← (simulateQ randomOracle (innerσ W D A)).run' ∅}[
          z.1.2 = true ∧ OpeningDoomed D.Lσ D.R (σIn D z.1.1.1.1) (cacheOfTr z.2)] :=
        prEvent_run'_bind_keep (innerσ W D A)
          (fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            ourVerifier D.LQ D.R (qIn D y.1.1.1.1)) ∅
          fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            y.1.2 = true ∧ OpeningDoomed D.Lσ D.R (σIn D y.1.1.1.1) (cacheOfTr y.2)
    _ = Pr{let z ← (romExperiment (innerW W D A)
          (fun x : (S0 F × Bool) × Transcript => ourVerifier D.Lσ D.R (σIn D x.1.1)))}[
          z.1.2 = true ∧ OpeningDoomed D.Lσ D.R (σIn D z.1.1.1.1) z.2] :=
        prEvent_loggedPrefix (innerW W D A)
          (fun x : (S0 F × Bool) × Transcript => ourVerifier D.Lσ D.R (σIn D x.1.1))
          (fun (x : (S0 F × Bool) × Transcript) b c =>
            b = true ∧ OpeningDoomed D.Lσ D.R (σIn D x.1.1) c)
          (readsInl_openingDoomed D.Lσ D.R fun x : (S0 F × Bool) × Transcript => σIn D x.1.1)
    _ ≤ openingBound (Q + 6 + 10122) := hs

set_option maxHeartbeats 2000000 in
/-- **The quotient opening's term.** -/
theorem prEvent_EQw_le (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows)
    (hLQ : D.LQ = witnessLayout r ∨ D.LQ = wiringLayout r ∨ D.LQ = quotientLayout r)
    (hR : D.R = logInvRate) :
    Pr{let z ← (simulateQ randomOracle (wiredExp W D A)).run' ∅}[EQw D z] ≤
      openingBound (Q + 6 + 10122 + 10122) := by
  have hs := ours_sound r h1 h2 D.LQ hLQ
    ((fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript => qIn D y.1.1.1.1) <$>
      innerσ W D A) (Q + 6 + 10122 + 10122)
    ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_innerσ W D A Q hQ))
  rw [romExperiment_map, prEvent_map, ← hR] at hs
  calc Pr{let z ← (simulateQ randomOracle (wiredExp W D A)).run' ∅}[EQw D z]
      = Pr{let z ← (romExperiment (innerσ W D A)
          (fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            ourVerifier D.LQ D.R (qIn D y.1.1.1.1)))}[
          z.1.2 = true ∧ OpeningDoomed D.LQ D.R (qIn D z.1.1.1.1.1.1) z.2] :=
        prEvent_loggedPrefix (innerσ W D A)
          (fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
            ourVerifier D.LQ D.R (qIn D y.1.1.1.1))
          (fun (y : (((S0 F × Bool) × Transcript) × Bool) × Transcript) b c =>
            b = true ∧ OpeningDoomed D.LQ D.R (qIn D y.1.1.1.1) c)
          (readsInl_openingDoomed D.LQ D.R
            fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript => qIn D y.1.1.1.1)
    _ ≤ openingBound (Q + 6 + 10122 + 10122) := hs

/-! ## The wired run reads as the deployed run -/

/-- The wired run asks what the deployed run asks, and gives the same outcome but for the wiring
stage's transcript. -/
theorem wired_deployed (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (T : KTable) :
    tableQueryLog (wiredExp W D A) T = tableQueryLog (deployedExp W D A) T ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D A)).1.1.1.1.1 =
        (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)).1.1.1.1 ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D A)).1.1.1.1.2 =
        (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)).1.1.1.2 ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D A)).1.1.1.2 =
        (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)).1.1.2 ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D A)).1.2 =
        (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)).1.2 ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D A)).2 =
        (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)).2 ∧
      tableQueryLog (deployedExp W D A) T = tableQueryLog (innerW W D A) T ++
        tableQueryLog (ourVerifier D.Lσ D.R
          (σIn D (evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A)).1.1)) T ++
        tableQueryLog (ourVerifier D.LQ D.R
          (qIn D (evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A)).1.1)) T ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D A)).1.1.2 =
        (tableQueryLog (innerW W D A) T ++ tableQueryLog (ourVerifier D.Lσ D.R
          (σIn D (evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A)).1.1)) T).filterMap inlEntry ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D A)).1.1.1.1.1 =
        (evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A)).1 := by
  set xI := evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A)
  -- The wiring stage, kept and logged.
  obtain ⟨hσl, hσe⟩ := run_keep (innerW W D A)
    (fun x : (S0 F × Bool) × Transcript => ourVerifier D.Lσ D.R (σIn D x.1.1)) T
  obtain ⟨hIσl, hIσe⟩ := run_logged (innerW W D A >>= fun x : (S0 F × Bool) × Transcript =>
    (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1)) T
  have hinnerσ_l : tableQueryLog (innerσ W D A) T = tableQueryLog (innerW W D A) T ++
      tableQueryLog (ourVerifier D.Lσ D.R (σIn D xI.1.1)) T := hIσl.trans hσl
  have hinnerσ_e : evalWithAnswerFn (QueryImpl.ofFn T) (innerσ W D A) =
      ((xI, evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier D.Lσ D.R (σIn D xI.1.1))),
        (tableQueryLog (innerW W D A) T ++
          tableQueryLog (ourVerifier D.Lσ D.R (σIn D xI.1.1)) T).filterMap inlEntry) := by
    show evalWithAnswerFn (QueryImpl.ofFn T) ((simulateQ logImplKC (innerW W D A >>=
      fun x : (S0 F × Bool) × Transcript => (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1))).run [])
        = _
    rw [hIσe, hσe, hσl]
  have hmid_l : tableQueryLog (midσ W D A) T = tableQueryLog (innerW W D A) T ++
      tableQueryLog (ourVerifier D.Lσ D.R (σIn D xI.1.1)) T := hσl
  have hmid_e : evalWithAnswerFn (QueryImpl.ofFn T) (midσ W D A) =
      (xI, evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier D.Lσ D.R (σIn D xI.1.1))) := hσe
  -- The quotient stage, kept and logged, after each.
  obtain ⟨hQwl, hQwe⟩ := run_keep (innerσ W D A)
    (fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
      ourVerifier D.LQ D.R (qIn D y.1.1.1.1)) T
  obtain ⟨hWl, hWe⟩ := run_logged (innerσ W D A >>=
    fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
      (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1.1)) T
  obtain ⟨hQdl, hQde⟩ := run_keep (midσ W D A)
    (fun y : ((S0 F × Bool) × Transcript) × Bool => ourVerifier D.LQ D.R (qIn D y.1.1.1)) T
  obtain ⟨hDl, hDe⟩ := run_logged (midσ W D A >>=
    fun y : ((S0 F × Bool) × Transcript) × Bool =>
      (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1)) T
  rw [hinnerσ_e] at hQwl hQwe
  rw [hmid_e] at hQdl hQde
  rw [hinnerσ_l] at hQwl
  rw [hmid_l] at hQdl
  have hlog : tableQueryLog (wiredExp W D A) T = tableQueryLog (deployedExp W D A) T := by
    show tableQueryLog ((simulateQ logImplKC (innerσ W D A >>=
      fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
        (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1.1))).run []) T =
      tableQueryLog ((simulateQ logImplKC (midσ W D A >>=
        fun y : ((S0 F × Bool) × Transcript) × Bool =>
          (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1))).run []) T
    rw [hWl, hDl, hQwl, hQdl]
  have hz : evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D A) =
      ((((xI, evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier D.Lσ D.R (σIn D xI.1.1))),
        (tableQueryLog (innerW W D A) T ++
          tableQueryLog (ourVerifier D.Lσ D.R (σIn D xI.1.1)) T).filterMap inlEntry),
        evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier D.LQ D.R (qIn D xI.1.1))),
        (tableQueryLog (innerW W D A) T ++ tableQueryLog (ourVerifier D.Lσ D.R (σIn D xI.1.1)) T ++
          tableQueryLog (ourVerifier D.LQ D.R (qIn D xI.1.1)) T).filterMap inlEntry) := by
    show evalWithAnswerFn (QueryImpl.ofFn T) ((simulateQ logImplKC (innerσ W D A >>=
      fun y : (((S0 F × Bool) × Transcript) × Bool) × Transcript =>
        (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1.1))).run []) = _
    rw [hWe, hQwe, hQwl]
  have hz' : evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A) =
      (((xI, evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier D.Lσ D.R (σIn D xI.1.1))),
        evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier D.LQ D.R (qIn D xI.1.1))),
        (tableQueryLog (innerW W D A) T ++ tableQueryLog (ourVerifier D.Lσ D.R (σIn D xI.1.1)) T ++
          tableQueryLog (ourVerifier D.LQ D.R (qIn D xI.1.1)) T).filterMap inlEntry) := by
    show evalWithAnswerFn (QueryImpl.ofFn T) ((simulateQ logImplKC (midσ W D A >>=
      fun y : ((S0 F × Bool) × Transcript) × Bool =>
        (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1))).run []) = _
    rw [hDe, hQde, hQdl]
  have hDlog : tableQueryLog (deployedExp W D A) T = tableQueryLog (innerW W D A) T ++
      tableQueryLog (ourVerifier D.Lσ D.R (σIn D xI.1.1)) T ++
      tableQueryLog (ourVerifier D.LQ D.R (qIn D xI.1.1)) T := by
    show tableQueryLog ((simulateQ logImplKC (midσ W D A >>=
      fun y : ((S0 F × Bool) × Transcript) × Bool =>
        (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1))).run []) T = _
    rw [hDl, hQdl]
  refine ⟨hlog, ?_⟩
  rw [hz, hz']
  exact ⟨rfl, rfl, rfl, rfl, rfl, hDlog, rfl, rfl⟩

/-! ## The trace, with the wiring opening -/

/-- The setup, then the adversary, against a table. -/
theorem withSetup_run (setup : OracleComp KeccakCalls Bytes32)
    (A₀ : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs)) (T : KTable) :
    tableQueryLog (withSetup setup A₀) T = tableQueryLog setup T ++
        tableQueryLog (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup)) T ∧
      (evalWithAnswerFn (QueryImpl.ofFn T) (withSetup setup A₀)).1.ir =
        evalWithAnswerFn (QueryImpl.ofFn T) setup := by
  constructor
  · rw [withSetup, tableQueryLog_bind, map_eq_bind_pure_comp, tableQueryLog_bind,
      Function.comp_apply, tableQueryLog_pure, List.append_nil]
  · simp only [withSetup, evalWithAnswerFn_bind, evalWithAnswerFn_map]

open Classical in
/-- **The trace of the wired run**: a run that breaks knowledge soundness while none of the
three openings is doomed at its end asks a bad fresh query. The wiring opening, undoomed, gives
F1's wiring claim (the setup's word, `candidates_honest`, `WiringMatch.claims`); then
`trace_deployed`. -/
theorem trace_wired (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) (mW : WitnessMatch D c₁)
    (mQ : QuotientMatch W D c₂) (setup : OracleComp KeccakCalls Bytes32)
    (A₀ : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs))
    (wm : WiringMatch (P := P) D setup) (hadm : Whir.Admissible D.Lσ.logN D.R) (T : KTable)
    (hev : BreaksW W c₁ (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D (withSetup setup A₀))) ∧
      ¬ EWw D (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D (withSetup setup A₀))) ∧
      ¬ Eσw D (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D (withSetup setup A₀))) ∧
      ¬ EQw D (evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D (withSetup setup A₀)))) :
    FreshBad (advBad W c₁.commit c₂.commit (withSetup setup A₀)) T ∅
      ((tableQueryLog (wiredExp W D (withSetup setup A₀)) T).map Sigma.fst) := by
  set A := withSetup setup A₀
  obtain ⟨hlog, e1, e2, e3, e4, e5, hDlog, htσ, ha⟩ := wired_deployed W D A T
  rw [hlog]
  set z := evalWithAnswerFn (QueryImpl.ofFn T) (wiredExp W D A)
  set z' := evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)
  set xI := evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A)
  obtain ⟨hB, hEW, hEσ, hEQ⟩ := hev
  have hza : z.1.1.1.1.1.1 = z'.1.1.1.1.1 := congrArg Prod.fst e1
  have hzbW : z.1.1.1.1.1.2 = z'.1.1.1.1.2 := congrArg Prod.snd e1
  -- The runs: the adversary's log holds the setup's, and the proof carries its root.
  obtain ⟨hLda, hEda⟩ := DA_run W A T
  obtain ⟨hsl, hsir⟩ := withSetup_run setup A₀ T
  obtain ⟨h1l, h1e⟩ := run_keep (DA W A) (fun a => ourVerifier D.Lw D.R (wIn D a)) T
  obtain ⟨h2l, h2e⟩ := run_logged (DA W A >>= fun a => (a, ·) <$> ourVerifier D.Lw D.R (wIn D a)) T
  have hIl : tableQueryLog (innerW W D A) T = tableQueryLog (DA W A) T ++
      tableQueryLog (ourVerifier D.Lw D.R (wIn D (evalWithAnswerFn (QueryImpl.ofFn T) (DA W A)))) T :=
    h2l.trans h1l
  have hIe : xI.1 = (evalWithAnswerFn (QueryImpl.ofFn T) (DA W A),
      evalWithAnswerFn (QueryImpl.ofFn T)
        (ourVerifier D.Lw D.R (wIn D (evalWithAnswerFn (QueryImpl.ofFn T) (DA W A))))) := by
    show (evalWithAnswerFn (QueryImpl.ofFn T) ((simulateQ logImplKC (DA W A >>= fun a =>
      (a, ·) <$> ourVerifier D.Lw D.R (wIn D a))).run [])).1 = _
    rw [h2e, h1e]
  -- The wiring stage's history.
  set lσ := tableQueryLog (ourVerifier D.Lσ D.R (σIn D xI.1.1)) T
  set lQ := tableQueryLog (ourVerifier D.LQ D.R (qIn D xI.1.1)) T
  set Hσ := (((tableQueryLog (innerW W D A) T ++ lσ).map Sigma.fst).filterMap Sum.getLeft?)
  set Lk := (tableQueryLog (deployedExp W D A) T).map Sigma.fst
  set L := Lk.filterMap Sum.getLeft?
  have hHσL : ∀ y ∈ Hσ, y ∈ L := fun y hy => by
    simp only [Hσ, L, Lk, hDlog, List.map_append, List.filterMap_append, List.mem_append] at hy ⊢
    tauto
  have hsetupσ : ∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → x ∈ Hσ.toFinset := by
    intro x hx
    refine List.mem_toFinset.mpr (mem_filterMap_getLeft?.mpr ?_)
    rw [List.map_append, hIl, List.map_append, hLda, hsl, List.map_append]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hx)))
  have hsndσ : ∀ q ∈ tableQueryLog (innerW W D A) T ++ lσ, q.2 = T q.1 := by
    have h := tableQueryLog_snd_dep T (innerW W D A >>= fun x : (S0 F × Bool) × Transcript =>
      (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1))
    rw [(run_keep (innerW W D A)
      (fun x : (S0 F × Bool) × Transcript => ourVerifier D.Lσ D.R (σIn D x.1.1)) T).1] at h
    exact h
  -- No bad fresh query, from here on.
  by_contra hnb
  have hk : ¬ FreshBad (kcBad W c₁.commit c₂.commit) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBad W c₁.commit c₂.commit) (viewT T) ∅ L := fun h =>
    hk (freshBad_kc W c₁.commit c₂.commit T ∅ Lk (by rw [viewH_empty]; exact h))
  have hinj := injOn_of_not_freshBad W hl
  have hinjσ : Set.InjOn (viewT T) ↑Hσ.toFinset := hinj.mono fun y hy =>
    List.mem_toFinset.mpr (hHσL y (List.mem_toFinset.mp hy))
  -- The wiring opening, undoomed: F1's wiring claim.
  have hbσ : z.1.1.1.2 = true := hB.1.2.2.1
  have hODσ : ¬ OpeningDoomed D.Lσ D.R (σIn D z.1.1.1.1.1.1) (cacheOfTr z.1.1.2) :=
    fun h => hEσ ⟨hbσ, h⟩
  unfold OpeningDoomed at hODσ
  push Not at hODσ
  obtain ⟨q, hq, hqc⟩ := hODσ
  rw [htσ, cacheOfTr_eq_ansOf T _ hsndσ] at hq
  have hroot : (σIn D z.1.1.1.1.1.1).1.1 = ofB (evalWithAnswerFn (QueryImpl.ofFn T) setup) := by
    show ofB z.1.1.1.1.1.1.π.ir = _
    rw [ha, hIe, hEda]
    show ofB (evalWithAnswerFn (QueryImpl.ofFn T) A).1.ir = _
    rw [hsir]
  rw [hroot] at hq
  have hword := candidates_congr (μ := D.Lσ.logN) (R := D.R)
    (A' := (code₀ D.Lσ.logN D.R).thr)
    (W₁ := Rom.extract (ansOf Hσ.toFinset (viewT T))
      (ofB (evalWithAnswerFn (QueryImpl.ofFn T) setup)) (rootHeight D.Lσ.logN D.R) (2 ^ laneFold))
    (W₂ := wm.word) fun v hv => wm.setupWord T Hσ.toFinset hsetupσ hinjσ v hv
  rw [hword] at hq
  have hq₀ := candidates_honest hadm wm.honest hq
  subst hq₀
  have hσc : wiringClaim P z.1.1.1.1.1.1.ch.t z.1.1.1.1.1.1.π.v.2 :=
    wm.claims _ _ fun cl hcl => hqc cl hcl
  rw [hza] at hσc
  -- The deployed run's trace.
  refine hnb (trace_deployed W D c₁ c₂ mW mQ A T ⟨?_, ?_, ?_, ?_⟩)
  · unfold BreaksW at hB
    rw [hza, hzbW, e3, e4] at hB
    exact hB
  · intro h
    refine hEW ?_
    unfold EWw
    rw [hza, hzbW, e2]
    exact h
  · rintro ⟨-, h⟩
    exact h hσc
  · intro h
    refine hEQ ?_
    unfold EQw
    rw [hza, e4, e5]
    exact h

/-! ## Knowledge soundness, every opening's term `ours_sound`'s -/

/-- **Knowledge soundness of the deployed verifier with the setup, in mumbai's two-oracle
model, the three openings' terms F2's `ours_sound`.** The setup (of at most `QS` queries)
computes the circuit's commitment with the oracle before the adversary (of at most `Q` queries)
runs; the chain's label and the wiring opening read it; the verifier runs the chain and
`opening::verify` for the witness, wiring and quotient tables. With the decoders and claims
matched to F1's (`WitnessMatch`, `QuotientMatch`) and the setup's wiring table
(`WiringMatch`), the verifier accepts while the adversary's extractor's list holds no witness of
the statement with probability at most
`openingBound (QS + Q + 6) + openingBound (QS + Q + 6 + QO) + openingBound (QS + Q + 6 + 2 QO) +
N (max L₁ (L₁ L₂) · roundError + 5 N / 2^256)`, `QO = 10122`, `N = QS + Q + 6 + 3 QO`. -/
theorem knowledgeSoundness_wired (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂)
    (mW : WitnessMatch D c₁) (mQ : QuotientMatch W D c₂)
    (setup : OracleComp KeccakCalls Bytes32)
    (A₀ : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs))
    (wm : WiringMatch (P := P) D setup) (QS Q : ℕ)
    (hS : IsTotalQueryBound setup QS) (hQ : ∀ ir, IsTotalQueryBound (A₀ ir) Q)
    (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows)
    (hLw : D.Lw = witnessLayout r) (hLσ : D.Lσ = wiringLayout r) (hLQ : D.LQ = quotientLayout r)
    (hR : D.R = logInvRate) :
    Pr{let z ← (simulateQ randomOracle (wiredExp W D (withSetup setup A₀))).run' ∅}[
        BreaksW W c₁ z] ≤
      openingBound (QS + Q + 6) + openingBound (QS + Q + 6 + 10122) +
        openingBound (QS + Q + 6 + 10122 + 10122) +
        ((QS + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) *
          ((listFactor c₁.commit.bound c₂.commit.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) +
          5 * ((QS + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set A := withSetup setup A₀
  have hA : IsTotalQueryBound A (QS + Q) := isTotalQueryBound_withSetup setup A₀ QS Q hS hQ
  have hadm : Whir.Admissible D.Lσ.logN D.R := by
    rw [hLσ, hR]
    exact (layouts_ok r h1 h2).2.1
  set mx := (simulateQ randomOracle (wiredExp W D A)).run' ∅
  have hrest : Pr{let z ← mx}[BreaksW W c₁ z ∧ ¬ EWw D z ∧ ¬ Eσw D z ∧ ¬ EQw D z] ≤
      ((QS + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) *
        ((listFactor c₁.commit.bound c₂.commit.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) +
        5 * ((QS + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
    refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (wiredExp W D A)
      (QS + Q + 6 + 10122 + 10122 + 10122) (isTotalQueryBound_wiredExp W D A (QS + Q) hA)
      (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
      (Set.finite_range _) _ (advBad W c₁.commit c₂.commit A) _ (fun S hS c t ht hcard => ?_)
      (fun T h => trace_wired W D c₁ c₂ mW mQ setup A₀ wm hadm T h)
    have hS' : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
      fun v => hS _ ⟨v, rfl⟩
    refine (prob_advBad W c₁.commit c₂.commit A S hS' c t ht).trans ?_
    rw [add_comm]
    gcongr
    have : 4 * (cacheDom c).card + 5 ≤ 5 * (QS + Q + 6 + 10122 + 10122 + 10122) := by omega
    calc ((4 * (cacheDom c).card + 5 : ℕ) : ℝ≥0∞) ≤
          ((5 * (QS + Q + 6 + 10122 + 10122 + 10122) : ℕ) : ℝ≥0∞) := by exact_mod_cast this
      _ = 5 * ((QS + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) := by push_cast; ring
  have hsplit : ∀ z, BreaksW W c₁ z → EWw D z ∨ Eσw D z ∨ EQw D z ∨
      (BreaksW W c₁ z ∧ ¬ EWw D z ∧ ¬ Eσw D z ∧ ¬ EQw D z) := by
    intro z hb
    by_cases h1 : EWw D z
    · exact Or.inl h1
    by_cases h2 : Eσw D z
    · exact Or.inr (Or.inl h2)
    by_cases h3 : EQw D z
    · exact Or.inr (Or.inr (Or.inl h3))
    exact Or.inr (Or.inr (Or.inr ⟨hb, h1, h2, h3⟩))
  refine (prEvent_mono mx _ _ hsplit).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add (prEvent_EWw_le W D A (QS + Q) hA r h1 h2 (Or.inl hLw) hR)
    ((prEvent_or_le _ _ _).trans (add_le_add
      (prEvent_Eσw_le W D A (QS + Q) hA r h1 h2 (Or.inr (Or.inl hLσ)) hR)
      ((prEvent_or_le _ _ _).trans (add_le_add
        (prEvent_EQw_le W D A (QS + Q) hA r h1 h2 (Or.inr (Or.inr hLQ)) hR) hrest))))).trans
    (le_of_eq ?_)
  simp only [add_assoc]

end Compose
