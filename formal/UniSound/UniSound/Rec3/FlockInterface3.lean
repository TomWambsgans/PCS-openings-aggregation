-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The interface is `UniSound.FlockSound`'s
-- (`FlockInterface.lean`) for π1-rec3's Flock phase, `formal/UniStatement`'s `Flock.verifyWalkedFs` at `.rec3`
-- (`crates/leanvm_flock_gas/src/flock_min.rs`'s `verify_walked` at `FLOCK_REC3`).
import UniSound.Prog
import UniSound.FlockInterface
import UniStatement.RecSecurity

/-!
# Flock's interface at π1-rec3

π1-rec3's verifier runs Flock as `Flock.verifyWalkedFs F (14 + κ) flockMain .rec3` (`UniStatement.Rec`): the main
line's front, but

* the zerocheck's coordinates after the seven fixed ones are `c, c², c⁴, …` of **one** challenge `c`
  (`drawRun .rec3`, `squares`): the first round draws one challenge instead of `4 + κ`;
* the lincheck's terminal is **walked** (`walkedTerminal`, leanVM's forward walk of the BLAKE2s circuit on the sent
  slices): a zero the verifier collects after the slices, before the ring map's challenges; there is no pending
  matrices' reduction, the batching sumcheck has no `λ³` term;
* it returns the slices' point and the ring switch's end.

**`FlockSound3 κ`** is the one hypothesis about it, the analog of `FlockSound κ`:

* `prog`, `link`: `Flock.verifyWalkedFs` is a chain program (no root, no tail; its one zero the walk's);
* **the main line's reading** `outM done` (point, end, pending): the transcript read as the main line's Flock with
  the zerocheck's squares written out. Its point and end are the program's result (`out_end`); its pending is the
  main line's `Pending.new` of the same front, whose claim is its sum exactly when the walk's zero vanishes
  (`walk`: the walk is the matrices' product sum, `formal/FlockSound/FlockSoundUni/Walk.lean`). The univariate
  identity model reads Flock through `outM`, so that the main line's identity model is reused as it is;
* `S`, `err`, `S_nil`, `step`, `finish`: round-by-round soundness from `FlockHolds`, as `FlockSound`'s, its last
  state from the ring claim and the pending claim (which the walk gives).
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Semantics UniStatement
open scoped ENNReal

/-- **π1-rec3's Flock hypothesis**, for `q_flock` of `2^(8 + κ)` cells. -/
structure FlockSound3 (κ : ℕ) where
  /-- Flock's walked front as a chain program: its rounds, its zero (the walk), its result. -/
  prog : ChainProg (List E × Flock.End)
  rounds_root : ∀ s ∈ prog.rounds, s.root = false
  tail_eq : prog.tail = 0
  /-- **The code-level link**: `Flock.verifyWalkedFs` at `14 + κ` variables, π1-rec3, is `prog`'s canonical
  channel program, for every lawful monad and permutation. -/
  link : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState),
    Flock.verifyWalkedFs F (blake2sR1csLogSize + κ) flockMain .rec3 = prog.run F
  /-- **The main line's reading** of a transcript: the point, the end and the pending reduction. -/
  outM : Done → List E × Option Flock.End × Flock.Pending
  /-- On a completed transcript, the reading's point and end are the program's result. -/
  out_end : ∀ (done : Done) (tl : List E), DoneFits prog.rounds done →
    (outM done).1 = (prog.out done tl).1 ∧ (outM done).2.1 = some (prog.out done tl).2
  /-- **The walk**: on a completed transcript whose zeros vanish, the pending claim is its sum. -/
  walk : ∀ (done : Done) (tl : List E), DoneFits prog.rounds done → prog.ZerosVanish done tl →
    PendingHolds (outM done).2.2
  /-- Flock's state after its completed rounds `done`, for the column `qf`. -/
  S : LeanVM.Protocol.Column (8 + κ) → Done → Prop
  /-- Round `j`'s error. -/
  err : ℕ → ℝ≥0∞
  /-- At the start the state holds only if the column satisfies Flock's predicate. -/
  S_nil : ∀ qf, S qf [] → FlockHolds κ qf
  /-- **Round by round**, as `FlockSound.step`. -/
  step : ∀ (j : ℕ) (hj : j < prog.rounds.length) (qf : LeanVM.Protocol.Column (8 + κ))
    (done : Done) (msg : UMsg), DoneFits (prog.rounds.take j) done →
      msg.Fits (prog.rounds[j]'hj) →
        Pr{let c ← Compose.draws E ((prog.rounds[j]'hj).ns + 1)}[
          ¬ S qf done ∧ S qf (done ++ [(msg, c)])] ≤ err j
  /-- **At the end**: the ring switch's claim on `qf` holds and the pending claim is its sum, so the state
  holds. -/
  finish : ∀ (qf : LeanVM.Protocol.Column (8 + κ)) (done : Done), DoneFits prog.rounds done →
    FlockEndHolds qf (outM done) → PendingHolds (outM done).2.2 → S qf done

/-- **Flock's error per candidate**: the sum of its rounds' errors. -/
noncomputable def FlockSound3.flockError {κ : ℕ} (h : FlockSound3 κ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range h.prog.rounds.length, h.err j

end UniSound
