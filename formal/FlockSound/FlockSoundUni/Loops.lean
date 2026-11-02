-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The channel (`UniStatement.Transcript`)
-- and the chain programs (`UniSound.Prog`) are this repository's.
import UniSound.Prog

/-!
# The channel's loops as recursions

`nextScalars`, `samples` and `sumcheck` are `for` loops over an accumulating array; the chain
program reads round by round. Here each is a recursion (`repeatM`, `sumcheckR`), for every lawful
monad, the first step of the code-level link of `Flock.verifyDeferred` to its chain program:

* `nextScalars_eq`, `samples_eq`: `count` reads or draws, one after the other;
* `sumcheck_eq`: a round's message, its challenge, then the rounds after it;
* `runRounds_eq`: a chain program's rounds without roots or zeros are their reads and draws.
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- `n` runs of `act`, in order. -/
def repeatM {α : Type} (act : ChanM m α) : ℕ → ChanM m (List α)
  | 0 => pure []
  | n + 1 => do
    let a ← act
    let l ← repeatM act n
    pure (a :: l)

theorem forIn_push {α : Type} (act : ChanM m α) : ∀ (l : List ℕ) (arr : Array α),
    ((forIn l arr fun _ r ↦ do
        let a ← act
        pure (ForInStep.yield (r.push a))) >>= fun r ↦ pure r.toList) =
      (fun t ↦ arr.toList ++ t) <$> repeatM act l.length
  | [], arr => by simp [repeatM]
  | _ :: l, arr => by
    simp only [List.forIn_cons, bind_assoc, pure_bind, List.length_cons, repeatM, map_bind]
    congr 1
    funext a
    rw [forIn_push act l (arr.push a)]
    simp [Array.toList_push]

theorem forIn_range_eq {β : Type} (n : ℕ) (init : β) (f : ℕ → β → ChanM m (ForInStep β)) :
    forIn [:n] init f = forIn (List.range' 0 n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]

/-- **`nextScalars` is `count` reads.** -/
theorem nextScalars_eq (n : ℕ) : nextScalars (m := m) n = repeatM (nextScalar (m := m)) n := by
  have h := forIn_push (nextScalar (m := m)) (List.range' 0 n) #[]
  simp only [List.length_range', Array.toList_empty, List.nil_append, id_map'] at h
  rw [← h, nextScalars, forIn_range_eq]

/-- **`samples` is `count` draws.** -/
theorem samples_eq (F : KeccakState → m KeccakState) (n : ℕ) :
    samples F n = repeatM (sample F) n := by
  have h := forIn_push (sample F) (List.range' 0 n) #[]
  simp only [List.length_range', Array.toList_empty, List.nil_append, id_map'] at h
  rw [← h, samples, forIn_range_eq]

theorem repeatM_add {α : Type} (act : ChanM m α) (a b : ℕ) :
    repeatM act (a + b) = (do
      let x ← repeatM act a
      let y ← repeatM act b
      pure (x ++ y)) := by
  induction a with
  | zero => simp [repeatM]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [repeatM, ih, bind_assoc, pure_bind, List.cons_append]

/-- **The sumcheck as a recursion**: a round's message, its challenge, the rounds after. -/
def sumcheckR (F : KeccakState → m KeccakState) (count : ℕ) : E → List (Option E) →
    ChanM m (List E × E)
  | c, [] => pure ([], c)
  | c, e :: es => do
    let msg ← roundPoly (m := m) count c e
    let ch ← sample F
    let r ← sumcheckR F count (polyEval msg ch) es
    pure (ch :: r.1, r.2)

theorem forIn_sumcheck (F : KeccakState → m KeccakState) (count : ℕ) :
    ∀ (es : List (Option E)) (pt : Array E) (c : E),
      ((forIn es (pt, c) fun e (s : Array E × E) ↦ do
          let message ← roundPoly (m := m) count s.2 e
          let challenge ← sample F
          pure (ForInStep.yield (s.1.push challenge, polyEval message challenge))) >>=
        fun s ↦ pure (s.1.toList, s.2)) =
      (fun r ↦ (pt.toList ++ r.1, r.2)) <$> sumcheckR F count c es
  | [], pt, c => by simp [sumcheckR]
  | e :: es, pt, c => by
    simp only [List.forIn_cons, bind_assoc, pure_bind, sumcheckR, map_bind]
    congr 1
    funext msg
    congr 1
    funext ch
    rw [forIn_sumcheck F count es (pt.push ch) (polyEval msg ch)]
    simp [Array.toList_push]

/-- **`sumcheck` is `sumcheckR`.** -/
theorem sumcheck_eq (F : KeccakState → m KeccakState) (c : E) (count : ℕ) (es : List (Option E)) :
    sumcheck F c count es = sumcheckR F count c es := by
  have h := forIn_sumcheck F count es #[] c
  simp only [Array.toList_empty, List.nil_append, id_map'] at h
  rw [← h, sumcheck]

/-! ## Chain programs' rounds -/

/-- **A round without root or zeros**: its scalars, then its challenges. -/
def readRound (F : KeccakState → m KeccakState) (s : Compose.RoundSpec) : ChanM m (UMsg × List E) := do
  let vals ← nextScalars (m := m) s.nv
  let chs ← samples F (s.ns + 1)
  pure ((none, vals), chs)

/-- The rounds, read one after the other. -/
def readRounds (F : KeccakState → m KeccakState) : List Compose.RoundSpec → ChanM m Done
  | [] => pure []
  | s :: rs => do
    let r ← readRound F s
    let d ← readRounds F rs
    pure (r :: d)

theorem readRounds_append (F : KeccakState → m KeccakState) (a b : List Compose.RoundSpec) :
    readRounds F (a ++ b) = (do
      let x ← readRounds F a
      let y ← readRounds F b
      pure (x ++ y)) := by
  induction a with
  | nil => simp [readRounds]
  | cons s a ih => simp only [List.cons_append, readRounds, ih, bind_assoc, pure_bind]

/-- **A chain program's rounds without roots or zeros are their reads and draws.** -/
theorem runRounds_eq {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState)
    (hz : ∀ done msg, P.zeros done msg = []) :
    ∀ (rs : List Compose.RoundSpec), (∀ s ∈ rs, s.root = false) → ∀ done : Done,
      P.runRounds F rs done = (fun d ↦ done ++ d) <$> readRounds F rs
  | [], _, done => by simp [ChainProg.runRounds, readRounds]
  | s :: rs, hr, done => by
    have hs : s.root = false := hr s (List.mem_cons_self ..)
    simp only [ChainProg.runRounds, hs, Bool.false_eq_true, if_false, pure_bind, hz,
      ChainProg.requireZeros, readRounds, readRound, bind_assoc, map_bind]
    congr 1
    funext vals
    congr 1
    funext chs
    rw [runRounds_eq P F hz rs (fun s hs ↦ hr s (List.mem_cons_of_mem _ hs))]
    simp

end FlockSound.Uni
