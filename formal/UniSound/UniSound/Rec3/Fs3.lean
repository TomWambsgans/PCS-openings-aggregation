-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The links' and the layer's form is `Fs.lean`'s (the main
-- line's), for π1-rec3's verifier (`formal/UniStatement`'s `reduceWithFs`, `verifyWithFs` at `.rec3` with the walk).
import UniSound.Fs
import UniSound.Rec3.PiopSound3

/-!
# π1-rec3: the code-level link, the last link and the Fiat–Shamir layer

The three hypotheses of π1-rec3's end theorem that speak of `UniStatement`'s verifier, as `Fs.lean`'s:

* **`UniCode3`** (the code-level link): after the row counts, `reduceWithFs … (.flock flockMain) .point .rec3 true`
  is a chain program on `rec3Rounds`, its Flock rounds `F3`'s, its tail the three stacks' values at the batch's
  point (no `a`, `b`).
* **`UniFinal3`** (the last link): on a completed transcript whose zeros vanish (the batch's terminal
  `sum + last = 0`, and Flock's walk) and whose three claims are true (`ClaimsHold`: no matrices' claim), the pending
  claim is its sum (the walk) and the batch's last state holds (`BR.St` at the batch's point), unless `t` is a root
  of the merge polynomial.
* **`FsLayer3`** (the Fiat–Shamir layer): every round-by-round sound protocol on π1-rec3's rounds, its errors at most
  `e`, whose first state is the relation and whose last follows from the checks with true claims, makes π1-rec3's
  deployed verifier knowledge sound for `uniExtractor` with the bound `uniBound3 e`.

**`uniBound3 e Q`**: `uniBound`'s, with **three** openings' doom terms instead of five (the setup still has three
trees, the IV hashing their roots: `Security.lean`'s setup is unchanged; the verifier opens `C1`, `C2` and the setup
only).
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement Finset WhirBridge
open scoped ENNReal

/-- **π1-rec3 as a chain program** (code-level link), for its Flock phase `F3`, with `nV` values at `t` and `np` pair
rounds: after the row counts, for each public input and counts, the chain program `prog input rows` on
`rec3Rounds F3.prog.rounds nV np`, with a tail of three (the stacks' values), runs as `reduceWithFs` at the
deployment's shape, π1-rec3 with the walk, point claims, up to what the verdict and the chain read (`obsOf`). -/
structure UniCode3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) where
  prog : Vector UInt8 32 → List ℕ → ChainProg Reduced
  rounds_eq : ∀ input rows, (prog input rows).rounds = rec3Rounds F3.prog.rounds nV np
  tail_eq : ∀ input rows, (prog input rows).tail = 3
  link : ∀ (input : Vector UInt8 32) {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) (c₀ : Chan),
    obsOf <$> ((reduceWithFs F D.shape (publicWordsOf input.toList) (.flock flockMain) .point .rec3
        true).run.run c₀) =
      obsOf <$> ((readCounts D.shape.heights >>= fun rows => (prog input rows).run F).run.run c₀)

/-- **π1-rec3's last link**: the verifier's checks with true claims make the pending claim its sum (the walk) and
the batch's last state hold at its point, unless `t` is a root of the merge polynomial. -/
def UniFinal3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) {np : ℕ} (I : UniIds3 D F3 np) (BR : PairBatch np)
    (C : UniCode3 D F3 I.nV np) : Prop :=
  ∀ (s : USt) done tl c1 c2, DoneFits (rec3Rounds F3.prog.rounds I.nV np) done → tl.length = 3 →
    (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2 →
      PendingHolds (F3.outM (fdOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done))).2.2 ∧
      ((I.zb (fdOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done))).eval
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 1)).2.headD 0) = 0 ∨
      BR.St (I.prod s c1 (rd (openedOf F3.prog.rounds.length c1 c2 done) 0).2
          (fdOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done)) c2
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 1)).2.headD 0)
          (rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).1.2
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).2.headD 0)
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).2.getD 1 0))
        (I.target s c1 (rd (openedOf F3.prog.rounds.length c1 c2 done) 0).2
          (fdOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done)) c2
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 1)).2.headD 0)
          (rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).1.2
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).2.headD 0)
          ((rd (openedOf F3.prog.rounds.length c1 c2 done) (F3.prog.rounds.length + 2)).2.getD 1 0))
        (brOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2 done)))

/-- **π1-rec3's bound** at `Q` adversary calls, rounds' errors at most `e`: `uniBound`'s with three openings. -/
noncomputable def uniBound3 (e : ℝ≥0∞) (Q : ℕ) : ℝ≥0∞ :=
  3 * openingBoundAt 10122 (uniN Q) +
    (uniN Q : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) * e + ((2 ^ 128 + 8 * uniN Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

/-- **π1-rec3's Fiat–Shamir layer**: every round-by-round sound protocol on π1-rec3's rounds, its errors at most `e`,
whose state before round `0` is the relation of `C1`'s candidate and whose last state follows from the verifier's
checks with true claims, makes π1-rec3's deployed verifier knowledge sound for `uniExtractor` with the bound
`uniBound3 e`. -/
def FsLayer3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np) : Prop :=
  ∀ (R : RbrPiop (rec3Rounds F3.prog.rounds nV np) USt Stk) (e : ℝ≥0∞), (∀ j, R.err j ≤ e) →
    (∀ s c m, R.pre s [] (some c, m) → Rel D s c) →
    (∀ (s : USt) done tl c1 c2, DoneFits (rec3Rounds F3.prog.rounds nV np) done → tl.length = 3 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf F3.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch) →
    UniKnowledgeSoundnessRec3 D (uniBound3 e)

end UniSound
