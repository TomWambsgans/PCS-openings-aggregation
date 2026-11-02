-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the two calls `KeccakCalls` and their simulation lemmas (`implH`, `implF`, `simulateQ_queryH`), and
-- `formal/EndToEnd/Completeness/E2ECompleteness/WithHash.lean`'s `simulateQ_openingWithH`, `simulateQ_commitWithH`.
import UniComplete.VerifierH

/-!
# The univariate verifier commutes with simulation

The H-copies of `VerifierH.lean` over the two calls (`m := OracleComp KeccakCalls`, `H := callKeccak256`,
`F := callKeccakF1600`) commute with any simulation `impl`: **`simulateQ_verifierWithH`**,
**`simulateQ_setupTreesWithH`**, as WithHash's `simulateQ_verifyWithH`, `simulateQ_commitWithH`.

The verifier runs in the channel's monad `ChanM m = ExceptT UniError (StateT Chan m)`, with loops (`forIn`) over
lists and ranges. So the commutation is proved once for **any monad morphism** (`Morph`: a map of computations
that keeps `pure` and `bind`), of which `simulateQ impl` is one (`Morph.sim`):

* `Morph.chan` lifts a morphism `m → n` to the channel's monads (the state and the error pass through), and keeps
  `pure`, `bind`, `get`, `set`, `modify`, `throw`, the lift of `m`, `<$>`, `if` and the loops (`chan_…`);
* every function of the verifier commutes with it, the hash `H` becoming `φ ∘ H` (`chan_sampleH`, …,
  `chan_reduceWithH`; the Statement's non-hashing helpers keep their form, `chan_nextScalar`, …);
* at the monad's level, the run, the IV and, given that the opening commutes (`hopen`, which WithHash proves for
  `simulateQ`), the verifier (`app_runWithH`, `app_verifyWithH`, **`app_verifierWithH`**).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open UniStatement

namespace UniComplete

/-- **A monad morphism**: a map of computations keeping `pure` and `bind`. -/
structure Morph (m n : Type → Type) [Monad m] [Monad n] where
  app : {α : Type} → m α → n α
  app_pure : ∀ {α : Type} (a : α), app (pure a) = pure a
  app_bind : ∀ {α β : Type} (x : m α) (f : α → m β), app (x >>= f) = app x >>= fun a ↦ app (f a)

namespace Morph

section Basic

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)

/-- **The morphism on the channel's monad**: the state and the error pass through. -/
def chan {α : Type} (x : ChanM m α) : ChanM n α :=
  ExceptT.mk fun c ↦ φ.app (x.run.run c)

omit [Monad n] [LawfulMonad n] in
theorem chan_ext {α : Type} {x y : ChanM n α} (h : ∀ c, x.run.run c = y.run.run c) : x = y := funext h

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_run {α : Type} (x : ChanM m α) (c : Chan) : (φ.chan x).run.run c = φ.app (x.run.run c) := rfl

theorem app_map {α β : Type} (f : α → β) (x : m α) : φ.app (f <$> x) = f <$> φ.app x := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, φ.app_bind]
  simp only [Function.comp_def, φ.app_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_ite {α : Type} (c : Prop) [Decidable c] (x y : m α) :
    φ.app (if c then x else y) = if c then φ.app x else φ.app y := by
  split <;> rfl

omit [LawfulMonad m] [LawfulMonad n] in
/-- A loop over a list. -/
theorem app_forIn_list {α β : Type} (l : List α) (b : β) (f : α → β → m (ForInStep β)) :
    φ.app (forIn l b f) = forIn l b fun a s ↦ φ.app (f a s) := by
  induction l generalizing b with
  | nil => exact φ.app_pure b
  | cons a l ih =>
    simp only [List.forIn_cons, φ.app_bind]
    congr 1
    funext s
    cases s with
    | done b => exact φ.app_pure b
    | yield b => exact ih b

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_pure {α : Type} (a : α) : φ.chan (pure a : ChanM m α) = pure a :=
  chan_ext fun c ↦ φ.app_pure (Except.ok a, c)

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_bind {α β : Type} (x : ChanM m α) (f : α → ChanM m β) :
    φ.chan (x >>= f) = φ.chan x >>= fun a ↦ φ.chan (f a) := by
  refine chan_ext fun c ↦ ?_
  simp only [chan_run, ExceptT.run_bind, StateT.run_bind, φ.app_bind]
  congr 1
  funext p
  obtain ⟨e, s⟩ := p
  cases e with
  | error e => exact φ.app_pure _
  | ok a => rfl

theorem chan_get : φ.chan (get : ChanM m Chan) = get := by
  refine chan_ext fun c ↦ ?_
  show φ.app ((Except.ok <$> (get : StateT Chan m Chan)).run c) =
    (Except.ok <$> (get : StateT Chan n Chan)).run c
  simp only [StateT.run_map, StateT.run_get, app_map, φ.app_pure]

theorem chan_set (s : Chan) : φ.chan (set s : ChanM m PUnit) = set s := by
  refine chan_ext fun c ↦ ?_
  show φ.app ((Except.ok <$> (set s : StateT Chan m PUnit)).run c) =
    (Except.ok <$> (set s : StateT Chan n PUnit)).run c
  simp only [StateT.run_map, StateT.run_set, app_map, φ.app_pure]

theorem chan_modify (f : Chan → Chan) : φ.chan (modify f : ChanM m PUnit) = modify f := by
  refine chan_ext fun c ↦ ?_
  show φ.app ((Except.ok <$> (modifyGet (fun s ↦ (PUnit.unit, f s)) : StateT Chan m PUnit)).run c) =
    (Except.ok <$> (modifyGet (fun s ↦ (PUnit.unit, f s)) : StateT Chan n PUnit)).run c
  simp only [StateT.run_map, StateT.run_modifyGet, app_map, φ.app_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_throw {α : Type} (e : UniError) : φ.chan (throw e : ChanM m α) = throw e := by
  refine chan_ext fun c ↦ ?_
  simp [chan_run, φ.app_pure]

theorem chan_lift {α : Type} (y : m α) : φ.chan (monadLift y : ChanM m α) = monadLift (φ.app y) := by
  refine chan_ext fun c ↦ ?_
  show φ.app ((Except.ok <$> (monadLift y : StateT Chan m α)).run c) =
    (Except.ok <$> (monadLift (φ.app y) : StateT Chan n α)).run c
  simp only [StateT.run_map, StateT.run_monadLift, monadLift_self, app_map, φ.app_bind, φ.app_pure]

theorem chan_map {α β : Type} (f : α → β) (x : ChanM m α) : φ.chan (f <$> x) = f <$> φ.chan x := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, chan_bind]
  simp only [Function.comp_def, chan_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem chan_ite {α : Type} (c : Prop) [Decidable c] (x y : ChanM m α) :
    φ.chan (if c then x else y) = if c then φ.chan x else φ.chan y := by
  split <;> rfl

omit [LawfulMonad m] [LawfulMonad n] in
/-- A loop over a list. -/
theorem chan_forIn_list {α β : Type} (l : List α) (b : β) (f : α → β → ChanM m (ForInStep β)) :
    φ.chan (forIn l b f) = forIn l b fun a s ↦ φ.chan (f a s) := by
  induction l generalizing b with
  | nil => exact chan_pure φ b
  | cons a l ih =>
    simp only [List.forIn_cons, chan_bind]
    congr 1
    funext s
    cases s with
    | done b => exact chan_pure φ b
    | yield b => exact ih b

omit [LawfulMonad m] [LawfulMonad n] in
/-- A loop over a range. -/
theorem chan_forIn_range {β : Type} (r : Std.Legacy.Range) (b : β) (f : ℕ → β → ChanM m (ForInStep β)) :
    φ.chan (forIn r b f) = forIn r b fun a s ↦ φ.chan (f a s) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range', chan_forIn_list]

/-! ### The Statement's channel helpers keep their form -/

theorem chan_takeBytes (k : ℕ) : φ.chan (takeBytes (m := m) k) = takeBytes k := by
  unfold takeBytes
  simp only [chan_bind, chan_get]
  congr 1; funext c
  split
  · simp only [chan_bind, chan_set, chan_pure]
  · exact chan_throw φ _

theorem chan_nextScalar : φ.chan (nextScalar (m := m)) = nextScalar := by
  simp only [nextScalar, chan_bind, chan_takeBytes, chan_pure]

theorem chan_nextInteger (bytes : ℕ) : φ.chan (nextInteger (m := m) bytes) = nextInteger bytes := by
  simp only [nextInteger, chan_bind, chan_takeBytes, chan_pure]

theorem chan_nextScalars (count : ℕ) : φ.chan (nextScalars (m := m) count) = nextScalars count := by
  simp only [nextScalars, chan_bind, chan_forIn_range, chan_nextScalar, chan_pure]

theorem chan_nextRoot : φ.chan (nextRoot (m := m)) = nextRoot := by
  simp only [nextRoot, chan_bind, chan_takeBytes, chan_pure]

theorem chan_requireZero (value : E) : φ.chan (requireZero (m := m) value) = requireZero value := by
  simp only [requireZero, chan_modify]

theorem chan_finish : φ.chan (finish (m := m)) = finish := by
  unfold finish
  simp only [chan_bind, chan_get]
  congr 1; funext c
  split
  · exact chan_pure φ _
  · exact chan_throw φ _

theorem chan_roundPoly (count : ℕ) (claim : E) (e : Option E) :
    φ.chan (roundPoly (m := m) count claim e) = roundPoly count claim e := by
  unfold roundPoly
  split <;> simp only [chan_bind, chan_nextScalar, chan_nextScalars, chan_pure]

theorem chan_countBits (heights : List ℕ) : φ.chan (countBits (m := m) heights) = countBits heights := by
  simp only [countBits, chan_bind, chan_forIn_list, chan_nextInteger, chan_requireZero, chan_pure]

theorem chan_tablePart (t : Table) (logHeight : ℕ) (weights : Array E) (beta : E) (w : List E) :
    φ.chan (tablePart (m := m) t logHeight weights beta w) = tablePart t logHeight weights beta w := by
  simp only [tablePart, chan_bind, chan_forIn_list, chan_nextScalar, chan_pure, chan_ite]

end Basic

/-! ### The verifier's functions -/

section Verifier

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest)

theorem chan_sampleH : φ.chan (sampleH H) = sampleH fun x ↦ φ.app (H x) := by
  simp only [sampleH, chan_bind, chan_get, chan_lift, chan_set, chan_pure]

theorem chan_samplesH (count : ℕ) :
    φ.chan (samplesH H count) = samplesH (fun x ↦ φ.app (H x)) count := by
  simp only [samplesH, chan_bind, chan_forIn_range, chan_sampleH, chan_pure]

theorem chan_sumcheckH (claim : E) (count : ℕ) (equalities : List (Option E)) :
    φ.chan (sumcheckH H claim count equalities) = sumcheckH (fun x ↦ φ.app (H x)) claim count equalities := by
  simp only [sumcheckH, chan_bind, chan_forIn_list, chan_roundPoly, chan_sampleH, chan_pure]

theorem chan_zerocheckH (logN k : ℕ) :
    φ.chan (Flock.zerocheckH H logN k) = Flock.zerocheckH (fun x ↦ φ.app (H x)) logN k := by
  simp only [Flock.zerocheckH, chan_bind, chan_samplesH, chan_ite, chan_nextScalars, chan_sampleH, chan_pure,
    chan_sumcheckH, chan_nextScalar]

theorem chan_reduceTerminalH (zSkip : Option E) (rowLow chiIn chiInPrime : List E) (alpha rLc : E)
    (s : Option (List E)) :
    φ.chan (Flock.reduceTerminalH H zSkip rowLow chiIn chiInPrime alpha rLc s) =
      Flock.reduceTerminalH (fun x ↦ φ.app (H x)) zSkip rowLow chiIn chiInPrime alpha rLc s := by
  cases s <;>
    simp only [Flock.reduceTerminalH, chan_bind, chan_sumcheckH, chan_nextScalar, chan_requireZero, chan_pure]

theorem chan_frontH (logN : ℕ) (variant : UniStatement.Flock.Variant) :
    φ.chan (Flock.frontH H logN variant) = Flock.frontH (fun x ↦ φ.app (H x)) logN variant := by
  simp only [Flock.frontH, chan_bind, chan_zerocheckH, chan_sampleH, chan_sumcheckH, chan_ite, chan_pure,
    chan_map, chan_nextScalars]

theorem chan_ringEndH (variant : UniStatement.Flock.Variant) (s : List E) :
    φ.chan (Flock.ringEndH H variant s) = Flock.ringEndH (fun x ↦ φ.app (H x)) variant s := by
  simp only [Flock.ringEndH, chan_bind, chan_samplesH, chan_pure]

theorem chan_flockVerifyH (logN : ℕ) (variant : UniStatement.Flock.Variant) :
    φ.chan (Flock.verifyH H logN variant) = Flock.verifyH (fun x ↦ φ.app (H x)) logN variant := by
  simp only [Flock.verifyH, chan_bind, chan_frontH, chan_reduceTerminalH]
  congr 1; funext fr; congr 1; funext x
  split <;> simp only [chan_bind, chan_ringEndH, chan_pure]

theorem chan_verifyDeferredH (logN : ℕ) (variant : UniStatement.Flock.Variant) :
    φ.chan (Flock.verifyDeferredH H logN variant) = Flock.verifyDeferredH (fun x ↦ φ.app (H x)) logN variant := by
  simp only [Flock.verifyDeferredH, chan_bind, chan_frontH]
  congr 1; funext fr
  split <;> simp only [chan_bind, chan_map, chan_ringEndH, chan_pure]

theorem chan_batchH (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (pending : Option (Flock.Pending × List E)) :
    φ.chan (batchH H combined layouts bitSlice ringMap pending) =
      batchH (fun x ↦ φ.app (H x)) combined layouts bitSlice ringMap pending := by
  rcases pending with _ | ⟨p, flockPoint⟩ <;>
    simp only [batchH, chan_bind, chan_sampleH, chan_sumcheckH, chan_nextScalars, chan_nextScalar, chan_pure,
      pure_bind, chan_ite, chan_requireZero]

/-- The walk, Flock deferred and point claims (the main line): Flock's end, then the batch. -/
theorem chan_reduceWithH_flockPoint (shape : Shape) (publicWords : List E) (variant : UniStatement.Flock.Variant) :
    φ.chan (reduceWithH H shape publicWords (.flock variant) .point) =
      reduceWithH (fun x ↦ φ.app (H x)) shape publicWords (.flock variant) .point := by
  simp only [reduceWithH, chan_bind, chan_ite, chan_throw, chan_pure, chan_countBits, chan_nextRoot,
    chan_samplesH, chan_sampleH, chan_verifyDeferredH, chan_forIn_list, chan_tablePart, chan_nextScalar,
    pure_bind]
  split <;>
  · repeat (with_reducible refine bind_congr fun _ ↦ ?_)
    split
    · split <;> simp only [chan_bind, chan_ite, chan_pure, chan_sampleH, chan_batchH]
    · simp only [chan_bind, chan_ite, chan_pure, chan_sampleH, chan_batchH]

/-- The walk, Flock and weighted claims. -/
theorem chan_reduceWithH_flockWeighted (shape : Shape) (publicWords : List E)
    (variant : UniStatement.Flock.Variant) :
    φ.chan (reduceWithH H shape publicWords (.flock variant) .weighted) =
      reduceWithH (fun x ↦ φ.app (H x)) shape publicWords (.flock variant) .weighted := by
  simp only [reduceWithH, chan_bind, chan_ite, chan_throw, chan_pure, chan_countBits, chan_nextRoot,
    chan_samplesH, chan_sampleH, chan_flockVerifyH, chan_forIn_list, chan_tablePart, chan_nextScalar, pure_bind]
  split <;>
  · repeat (with_reducible refine bind_congr fun _ ↦ ?_)
    split
    · simp only [chan_ite, chan_bind, chan_sampleH]
      split <;>
      · repeat (with_reducible refine bind_congr fun _ ↦ ?_)
        split <;> simp only [chan_pure]
    · simp only [chan_bind, chan_sampleH]
      repeat (with_reducible refine bind_congr fun _ ↦ ?_)
      split <;> simp only [chan_pure]

/-- The walk without Flock, point claims. -/
theorem chan_reduceWithH_omittedPoint (shape : Shape) (publicWords : List E) :
    φ.chan (reduceWithH H shape publicWords .omitted .point) =
      reduceWithH (fun x ↦ φ.app (H x)) shape publicWords .omitted .point := by
  simp only [reduceWithH, chan_bind, chan_ite, chan_throw, chan_pure, chan_countBits, chan_nextRoot,
    chan_samplesH, chan_sampleH, chan_forIn_list, chan_tablePart, chan_nextScalar, chan_batchH, pure_bind]

/-- The walk without Flock, weighted claims. -/
theorem chan_reduceWithH_omittedWeighted (shape : Shape) (publicWords : List E) :
    φ.chan (reduceWithH H shape publicWords .omitted .weighted) =
      reduceWithH (fun x ↦ φ.app (H x)) shape publicWords .omitted .weighted := by
  simp only [reduceWithH, chan_bind, chan_ite, chan_throw, chan_pure, chan_countBits, chan_nextRoot,
    chan_samplesH, chan_sampleH, chan_forIn_list, chan_tablePart, chan_nextScalar, pure_bind]
  split <;>
  · repeat (with_reducible refine bind_congr fun _ ↦ ?_)
    split <;> simp only [chan_pure]

theorem chan_reduceWithH (shape : Shape) (publicWords : List E) (blake2s : Blake2s) (mode : ClaimsMode) :
    φ.chan (reduceWithH H shape publicWords blake2s mode) =
      reduceWithH (fun x ↦ φ.app (H x)) shape publicWords blake2s mode := by
  rcases blake2s with variant | _ <;> cases mode
  · exact chan_reduceWithH_flockPoint φ H shape publicWords variant
  · exact chan_reduceWithH_flockWeighted φ H shape publicWords variant
  · exact chan_reduceWithH_omittedPoint φ H shape publicWords
  · exact chan_reduceWithH_omittedWeighted φ H shape publicWords


/-! ### The run, the IV, the verifier -/

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_seedWithH (iv publicInput : List UInt8) :
    φ.app (seedWithH H iv publicInput) = seedWithH (fun x ↦ φ.app (H x)) iv publicInput := rfl

theorem app_runWithH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) :
    φ.app (runWithH H shape iv publicInput stream blake2s mode) =
      runWithH (fun x ↦ φ.app (H x)) shape iv publicInput stream blake2s mode := by
  simp only [runWithH, φ.app_bind, app_seedWithH, φ.app_pure, ← chan_run φ, chan_bind, chan_reduceWithH,
    chan_finish, chan_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_contractIvWithH (s : Shape) (programIv : List UInt8) (roots : SetupRoots) :
    φ.app (contractIvWithH H s programIv roots) = contractIvWithH (fun x ↦ φ.app (H x)) s programIv roots := by
  simp only [contractIvWithH, φ.app_bind, φ.app_pure]

omit [LawfulMonad m] [LawfulMonad n] in
theorem app_ivWithH (D : Deployment) (roots : SetupRoots) :
    φ.app (Deployment.ivWithH H D roots) = Deployment.ivWithH (fun x ↦ φ.app (H x)) D roots :=
  app_contractIvWithH φ H _ _ _

variable (F : KeccakState → m KeccakState)

/-- **The verifier commutes with a monad morphism that commutes with the opening** (`hopen`, WithHash's
`simulateQ_openingWithH` for `simulateQ`). -/
theorem app_verifyWithH
    (hopen : ∀ (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (E2ECompleteness.openingWithH H F L root claims proof) =
        E2ECompleteness.openingWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) L root claims proof)
    (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32) (proof : UniProof) :
    φ.app (verifyWithH H F shape iv roots publicInput proof) =
      verifyWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) shape iv roots publicInput proof := by
  simp only [verifyWithH, φ.app_bind, app_runWithH]
  congr 1; funext o
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · simp only [φ.app_bind, app_forIn_list]
      congr 1
      · congr 1; funext x s
        split
        · simp only [φ.app_bind, φ.app_pure, pcsOpenWithH, hopen]
        · exact φ.app_pure _
      · funext s
        split
        · simp only [φ.app_bind, φ.app_pure, pcsOpenWithH, hopen]
        · exact φ.app_pure _

/-- **The deployed verifier commutes with a monad morphism that commutes with the opening.** -/
theorem app_verifierWithH
    (hopen : ∀ (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (E2ECompleteness.openingWithH H F L root claims proof) =
        E2ECompleteness.openingWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) L root claims proof)
    (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32) (proof : UniProof) :
    φ.app (Deployment.verifierWithH H F D roots input proof) =
      Deployment.verifierWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D roots input proof := by
  simp only [Deployment.verifierWithH, φ.app_bind, app_ivWithH, app_verifyWithH φ H F hopen]

end Verifier

end Morph

end UniComplete

/-! ## Over the two calls: `simulateQ` -/

namespace UniComplete

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- **`simulateQ impl` is a monad morphism.** -/
def Morph.sim : Morph (OracleComp KeccakCalls) r :=
  ⟨fun x ↦ simulateQ impl x, fun a ↦ simulateQ_pure impl a, fun x f ↦ simulateQ_bind impl x f⟩

theorem Morph.sim_H : (fun x ↦ (Morph.sim impl).app (callKeccak256 x)) = implH impl :=
  funext fun x ↦ simulateQ_queryH impl x

theorem Morph.sim_F : (fun s ↦ (Morph.sim impl).app (callKeccakF1600 s)) = implF impl :=
  funext fun s ↦ simulateQ_queryF impl s

/-- **The deployed verifier over the two calls commutes with any simulation.** -/
theorem simulateQ_verifierWithH (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniProof) :
    simulateQ impl (Deployment.verifierWithH callKeccak256 callKeccakF1600 D roots input proof) =
      Deployment.verifierWithH (implH impl) (implF impl) D roots input proof := by
  have h := Morph.app_verifierWithH (Morph.sim impl) callKeccak256 callKeccakF1600
    (fun L root claims proof ↦ by
      rw [Morph.sim_H, Morph.sim_F]
      exact E2ECompleteness.simulateQ_openingWithH impl L root claims proof) D roots input proof
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

/-- **The setup over the two calls commutes with any simulation.** -/
theorem simulateQ_setupTreesWithH (D : Deployment) :
    simulateQ impl (setupTreesWithH callKeccak256 callKeccakF1600 D) =
      setupTreesWithH (implH impl) (implF impl) D := by
  simp only [setupTreesWithH, simulateQ_bind, E2ECompleteness.simulateQ_commitWithH, simulateQ_pure]

end Commute

end UniComplete

/-- info: 'UniComplete.simulateQ_verifierWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.simulateQ_verifierWithH

/-- info: 'UniComplete.simulateQ_setupTreesWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.simulateQ_setupTreesWithH

/-- info: 'UniComplete.Morph.app_verifierWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Morph.app_verifierWithH
