-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.BatchProofSumcheck
import UniComplete.SyncBasic

/-!
# The batching sumcheck's rounds in step: `sumcheckH` reads `batchRounds`

At a pure Keccak-256 `H`, the verifier's `sumcheckH (pure ∘ H) target 3 (replicate vars none)` on a channel
synchronised with the prover's writer reads each round's two scalars (`roundPoly`: `c0`, then `[c2]`), draws the
prover's challenge, and ends synchronised with the prover's writer after `batchRounds`, returning the prover's point
and the claim `claimRun` reaches on the prover's messages (`syncs_sumcheck`). The challenges are the prover's
(`loopChallenges`: the round's message, then `Wr.sampled` at the writer after it); the prover's final state is
`batchRun` at them (`batchRounds_run`).
-/

open LeanVM.Parameters LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

namespace UniComplete

section Helpers

variable {α β : Type}

theorem Syncs.congr {v : ChanM Id α} {p : WrM Id β} {w : Wr} {a a' : α} {zs zs' : List E} (h : Syncs v p w a zs)
    (ha : a = a') (hz : zs = zs') : Syncs v p w a' zs' := by
  subst ha hz; exact h

theorem Syncs.congr_v {v v' : ChanM Id α} {p : WrM Id β} {w : Wr} {a : α} {zs : List E} (h : Syncs v p w a zs)
    (hv : v = v') : Syncs v' p w a zs := by
  subst hv; exact h

theorem Syncs.congr_p {v : ChanM Id α} {p p' : WrM Id β} {w : Wr} {a : α} {zs : List E} (h : Syncs v p w a zs)
    (hp : p = p') : Syncs v p' w a zs := by
  subst hp; exact h

theorem syncs_pure (a : α) (b : β) (w : Wr) : Syncs (Pure.pure a : ChanM Id α) (Pure.pure b : WrM Id β) w a [] :=
  (Steps.pure a b w.stream.size w).syncs

end Helpers

variable (H : List UInt8 → Digest)

/-! ## One round -/

/-- `sumcheckH`'s loop body. -/
def vbody (equality : Option E) (s : Array E × E) : ChanM Id (ForInStep (Array E × E)) := do
  let message ← UniStatement.roundPoly (m := Id) 3 s.2 equality
  let challenge ← sampleH (m := Id) (Pure.pure ∘ H)
  Pure.pure (ForInStep.yield (s.1.push challenge, UniStatement.polyEval message challenge))

/-- `batchRounds`'s loop body. -/
def pbody (lambda : E) (j : ℕ) (st : BatchState) : WrM Id (ForInStep BatchState) := do
  let st ← batchRound (m := Id) (Pure.pure ∘ H) lambda j st
  Pure.pure (ForInStep.yield st)

/-- The writer after round `j`'s message. -/
def msgWriter (lambda : E) (j : ℕ) (st : BatchState) (w : Wr) : Wr :=
  (w.append (scalarWire (batchMsg lambda j st).1)).append (scalarWire (batchMsg lambda j st).2)

theorem sendScalar_run (x : E) (w : Wr) : (sendScalar (m := Id) x).run w = ((), w.append (scalarWire x)) := rfl

/-- **One round in step**: the verifier reads `c0`, `[c2]`, draws the prover's challenge. -/
theorem syncs_round (lambda : E) (j : ℕ) (pa : Array E) (c : E) (st : BatchState) (w : Wr) :
    Syncs (vbody H none (pa, c)) (pbody H lambda j st) w
      (ForInStep.yield (pa.push (Wr.sampled H (msgWriter lambda j st w)).1,
        claimStep c (batchMsg lambda j st).1 (batchMsg lambda j st).2 (Wr.sampled H (msgWriter lambda j st w)).1)) [] := by
  have hv : vbody H none (pa, c) = (UniStatement.nextScalar (m := Id) >>= fun q0 ↦
      UniStatement.nextScalars (m := Id) 1 >>= fun tail ↦ sampleH (m := Id) (Pure.pure ∘ H) >>= fun ch ↦
        Pure.pure (ForInStep.yield (pa.push ch,
          UniStatement.polyEval ([q0, c + UniStatement.esum tail] ++ tail) ch))) := by
    simp only [vbody, UniStatement.roundPoly, bind_assoc, pure_bind]
  have hp : pbody H lambda j st = (sendScalar (m := Id) (batchMsg lambda j st).1 >>= fun _ ↦
      sendScalar (m := Id) (batchMsg lambda j st).2 >>= fun _ ↦ sampleW (m := Id) (Pure.pure ∘ H) >>= fun r ↦
        Pure.pure (ForInStep.yield (batchNext j st r))) := by
    simp only [pbody, batchRound_eq, bind_assoc, pure_bind]
  refine (Syncs.congr_p (Syncs.congr_v ?_ hv.symm) hp.symm)
  set q0 := (batchMsg lambda j st).1
  set q2 := (batchMsg lambda j st).2
  have h2 : Syncs (UniStatement.nextScalars (m := Id) 1) (sendScalar (m := Id) q2) (w.append (scalarWire q0)) [q2] [] :=
    Syncs.congr_p (syncs_scalars [q2] _) (by simp [sendScalars, sendScalar])
  refine Syncs.congr (Syncs.bind (syncs_scalar q0 w) (Syncs.bind h2 (Syncs.bind (syncs_sample H _)
    (syncs_pure _ _ _)))) rfl (by simp)

/-- The prover's round from the writer `w`: the next state at the challenge, the writer after it. -/
theorem pbody_run (lambda : E) (j : ℕ) (st : BatchState) (w : Wr) :
    (pbody H lambda j st).run w =
      (ForInStep.yield (batchNext j st (Wr.sampled H (msgWriter lambda j st w)).1),
        (Wr.sampled H (msgWriter lambda j st w)).2) := rfl

/-! ## The rounds -/

/-- **The prover's challenges** through `n` rounds from round `j`: each the hash at the writer after the round's
message. -/
def loopChallenges (lambda : E) : ℕ → ℕ → BatchState → Wr → List E
  | 0, _, _, _ => []
  | n + 1, j, st, w =>
    (Wr.sampled H (msgWriter lambda j st w)).1 ::
      loopChallenges lambda n (j + 1) (batchNext j st (Wr.sampled H (msgWriter lambda j st w)).1)
        (Wr.sampled H (msgWriter lambda j st w)).2

theorem loopChallenges_length (lambda : E) : ∀ (n j : ℕ) (st : BatchState) (w : Wr),
    (loopChallenges H lambda n j st w).length = n
  | 0, _, _, _ => rfl
  | n + 1, j, st, w => by simp [loopChallenges, loopChallenges_length lambda n]

/-- **The loops in step**: `n` rounds from round `j`, the verifier at `(pa, c)`. -/
theorem syncs_loop (lambda : E) : ∀ (n j : ℕ) (pa : Array E) (c : E) (st : BatchState) (w : Wr),
    Syncs (forIn (List.replicate n (none : Option E)) (pa, c) (vbody H))
      (forIn (List.range' j n) st (pbody H lambda)) w
      (pa ++ (loopChallenges H lambda n j st w).toArray, claimRun lambda j (loopChallenges H lambda n j st w) st c) []
  | 0, j, pa, c, st, w => by
    simp only [List.replicate_zero, List.range'_zero, List.forIn_nil, loopChallenges, claimRun]
    exact Syncs.congr (syncs_pure _ _ _) (by simp) rfl
  | n + 1, j, pa, c, st, w => by
    rw [List.replicate_succ, List.range'_succ, List.forIn_cons, List.forIn_cons]
    have h2 := syncs_loop lambda n (j + 1) (pa.push (Wr.sampled H (msgWriter lambda j st w)).1)
      (claimStep c (batchMsg lambda j st).1 (batchMsg lambda j st).2 (Wr.sampled H (msgWriter lambda j st w)).1)
      (batchNext j st (Wr.sampled H (msgWriter lambda j st w)).1) (Wr.sampled H (msgWriter lambda j st w)).2
    refine Syncs.congr (Syncs.bind (syncs_round H lambda j pa c st w) h2) ?_ (by simp)
    simp [loopChallenges, claimRun]

/-- The prover's loop's final state is `batchRun` at its challenges. -/
theorem loop_run (lambda : E) : ∀ (n j : ℕ) (st : BatchState) (w : Wr),
    ((forIn (List.range' j n) st (pbody H lambda)).run w).1 = batchRun j (loopChallenges H lambda n j st w) st
  | 0, _, _, _ => rfl
  | n + 1, j, st, w => by
    rw [List.range'_succ, List.forIn_cons, wr_run_bind, pbody_run]
    exact loop_run lambda n (j + 1) _ _

theorem batchRun_point : ∀ (rs : List E) (j : ℕ) (st : BatchState), (batchRun j rs st).point = st.point ++ rs
  | [], _, st => by simp [batchRun]
  | r :: rs, j, st => by
    rw [batchRun, batchRun_point rs]
    simp [batchNext]

theorem sumcheckH_eq (target : E) (vars : ℕ) :
    sumcheckH (m := Id) (Pure.pure ∘ H) target 3 (List.replicate vars none) =
      (forIn (List.replicate vars (none : Option E)) ((#[] : Array E), target) (vbody H) >>= fun s ↦
        Pure.pure (s.1.toList, s.2)) := rfl

theorem batchRounds_eq (lambda : E) (vars : ℕ) (st : BatchState) :
    batchRounds (m := Id) (Pure.pure ∘ H) lambda vars st =
      (forIn (List.range' 0 vars) st (pbody H lambda) >>= fun s ↦ Pure.pure s.point) := by
  unfold batchRounds
  rw [List.range_eq_range']
  rfl

/-- **The prover's point** after the rounds: its challenges (the state's point empty before). -/
theorem batchRounds_run (lambda : E) (vars : ℕ) (st : BatchState) (hst : st.point = []) (w : Wr) :
    ((batchRounds (m := Id) (Pure.pure ∘ H) lambda vars st).run w).1 = loopChallenges H lambda vars 0 st w := by
  rw [batchRounds_eq, wr_run_bind, wr_run_pure, loop_run, batchRun_point, hst, List.nil_append]

/-- **`sumcheckH` reads `batchRounds`**: the prover's point, and the claim the verifier reaches on the prover's
messages. -/
theorem syncs_sumcheck (lambda target : E) (vars : ℕ) (st : BatchState) (w : Wr) :
    Syncs (sumcheckH (m := Id) (Pure.pure ∘ H) target 3 (List.replicate vars none))
      (batchRounds (m := Id) (Pure.pure ∘ H) lambda vars st) w
      (loopChallenges H lambda vars 0 st w, claimRun lambda 0 (loopChallenges H lambda vars 0 st w) st target) [] := by
  rw [sumcheckH_eq, batchRounds_eq]
  exact Syncs.congr (Syncs.bind (syncs_loop H lambda vars 0 #[] target st w) (syncs_pure _ _ _)) (by simp) rfl

/-- **The honest sumcheck, read**: from the target `Σ_k λ^k Σ_u W_k C_k + λ^n Σ G L̂ ŝ` (`targetOf`), on the batch's
tables (`BatchWF`), the verifier's `sumcheckH` against the prover's `batchRounds` ends at the prover's point `rs` and
the terminal `Σ_k λ^k W̃_k(r) C̃_k(r) Π_{j ≥ d_k} (1 + r_j)² + λ^n G̃ L̃ S̃(r) Π_{j ≥ k+6} (1 + r_j)` (`terminalOf`). -/
theorem syncs_sumcheck_terminal (lambda : E) (k vars : ℕ) (pairs : List (Array E × Array E × ℕ))
    (tables : Option PendingTables) (hwf : BatchWF k vars pairs tables) (w : Wr) :
    Syncs (sumcheckH (m := Id) (Pure.pure ∘ H) (targetOf lambda pairs tables) 3 (List.replicate vars none))
      (batchRounds (m := Id) (Pure.pure ∘ H) lambda vars (initState pairs tables)) w
      (loopChallenges H lambda vars 0 (initState pairs tables) w,
        terminalOf lambda pairs tables (loopChallenges H lambda vars 0 (initState pairs tables) w)) [] := by
  refine Syncs.congr (syncs_sumcheck H lambda _ vars _ w) ?_ rfl
  rw [batch_rounds lambda k vars pairs tables hwf _ (loopChallenges_length H lambda vars 0 _ w)]

end UniComplete

/-- info: 'UniComplete.syncs_sumcheck_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.syncs_sumcheck_terminal

/-- info: 'UniComplete.syncs_sumcheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.syncs_sumcheck
