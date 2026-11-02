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

end Compose
