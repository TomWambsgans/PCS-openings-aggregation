-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's verifier reads its honest prover's stream:
-- `SyncVerifier.lean`'s `reduce_steps`, `runWithH_syncs`, `runWithH_accepts` for `Rec3VerifierH.lean`'s
-- `reduceWithFsH … .rec3 true` and `Rec3Prover.lean`'s `proveStreamRec3With`.
import UniComplete.Rec3BatchZero
import UniComplete.Rec3FlockDefs
import UniComplete.SyncVerifier

/-!
# π1-rec3's verifier reads back the honest prover's stream

At a pure Keccak-256 `H`, `reduceWithFsH … (.flock flockMain) .point .rec3 true` run on the stream
`proveStreamRec3With` writes from the seed reads every message and draws the same challenges, in the verifier's
order: the counts, `C1`'s root, `α = squares c 4` (`steps_drawRun`), `β`, `γ`, Flock (the hypothesis `FlockSyncs3`,
its walk's zero collected: `0` on the honest transcript; its end is a ring switch's, `verifyWalkedFsH_end`), `C2`'s
root, `t`, the values at `t` (the main line's `tablesLoop_reads`, `atTOf_values`), `ρ`, the paired batch (the
hypothesis `BatchSyncsAt3`: `BatchSyncs3` at the prover's state when the batch starts, `frontOf3`), `finish`.

* **`reduce_steps3`**: the joint steps, with the run's ends (the openings the prover's point claims, no matrices'
  claim, the roots its halves, the collected values the counts' checks, Flock's walk's zero `0`, the batch's
  terminal);
* **`runWithFsH_syncs3`**, **`runWithFsH_accepts3`**: the run returns `.ok R` at the end of the prover's stream, and
  accepts when the batch's terminal vanishes.

The proof is `SyncVerifier.lean`'s `reduce_steps` with π1-rec3's steps in place: the bus's draw, Flock's walked
verifier, the paired batch (and no pending matrices).
-/

namespace UniComplete.Rec3

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## Flock's end, the bus's draw -/

/-- **`verifyWalkedFsH`'s end is a ring switch's.** -/
theorem verifyWalkedFsH_end (H : List UInt8 → Digest) (logN : ℕ) (variant : Flock.Variant) (c : Chan)
    {pt : List E} {e : Flock.End} {c' : Chan}
    (h : (verifyWalkedFsH (m := Id) (Pure.pure ∘ H) logN variant .rec3).run.run c = (.ok (pt, e), c')) :
    ∃ map target, e = .ring map target := by
  unfold verifyWalkedFsH at h
  rw [chan_run_bind] at h
  generalize (frontFsH (m := Id) (Pure.pure ∘ H) logN variant .rec3).run.run c = r at h
  rcases r with ⟨r, c1⟩
  cases r with
  | error err => exact absurd h err_ne_ok
  | ok fr =>
    dsimp only at h
    rw [chan_run_bind] at h
    generalize (requireZero (m := Id) _).run.run c1 = r1 at h
    rcases r1 with ⟨r1, c2⟩
    cases r1 with
    | error err => exact absurd h err_ne_ok
    | ok u =>
      dsimp only at h
      rw [chan_run_bind] at h
      generalize hr : (Flock.ringEndH (m := Id) (Pure.pure ∘ H) variant (fr.slices.getD [])).run.run c2 = r2 at h
      rcases r2 with ⟨r2, c3⟩
      cases r2 with
      | error err => exact absurd h err_ne_ok
      | ok e' =>
        cases h
        exact ringEndH_ring H variant _ c2 _ _ hr

/-- **The bus's draw in step**: `drawRunH .rec3 4` draws the prover's `drawRunW 4`, one challenge and its squares. -/
theorem steps_drawRun (H : List UInt8 → Digest) (w : Wr) :
    Steps (drawRunH (m := Id) (Pure.pure ∘ H) .rec3 4) (drawRunW (m := Id) (Pure.pure ∘ H) 4) w.stream.size w
      (squares (Wr.sampled H w).1 4) (squares (Wr.sampled H w).1 4) w.stream.size (Wr.sampled H w).2 [] :=
  Steps.congr ((Steps.sample H w).bind (f := fun c ↦ Pure.pure (squares c 4))
    (g := fun c ↦ Pure.pure (squares c 4)) (Steps.pure _ _ _ _)) rfl rfl (by simp)

/-- `batchFsH`'s inputs, rewritten. -/
theorem batchFsH_congr (H : List UInt8 → Digest) {c1 c2 : List (Commitment × Combined)}
    {l1 l2 : List (Commitment × StackLayout)} {b1 b2 : Option Combined} (r : Option (List E))
    (p : Option (Flock.Pending × List E)) (hc : c1 = c2) (hl : l1 = l2) (hb : b1 = b2) :
    batchFsH (m := Id) (Pure.pure ∘ H) .rec3 c1 l1 b1 r p = batchFsH (m := Id) (Pure.pure ∘ H) .rec3 c2 l2 b2 r p := by
  subst hc hl hb; rfl

/-! ## The prover's state when the batch starts -/

section Front

variable (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed) (flock : FlockProver Id)

/-- **π1-rec3's prover's run up to `ρ`** (`proveStreamRec3With`'s steps 0–8, at `Id` with `pure ∘ H`), from the writer
`w0`: its state, and the writer when the batching sumcheck starts. -/
def frontOf3 (tr : Trace) (w0 : Wr) : FrontOut × Wr :=
  let shape := tr.shape
  let w1 := w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)
  let stack1 := c1Stack tr
  let committed1 : Committed := commit .c1 (c1Layout shape).vars stack1
  let w2 := w1.append (rootWord committed1.halves)
  let alphas := squares (Wr.sampled H w2).1 4
  let w3 := (Wr.sampled H w2).2
  let beta := (Wr.sampled H w3).1
  let w4 := (Wr.sampled H w3).2
  let gamma := (Wr.sampled H w4).1
  let w5 := (Wr.sampled H w4).2
  let logN := blake2sR1csLogSize + shape.heights.getD opBlake2s 0
  let flockOut : Option FlockOut := some ((flock logN flockMain tr.qflock).run w5).1
  let w6 := ((flock logN flockMain tr.qflock).run w5).2
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 : Committed := commit .c2 (((layoutsOf shape).lookup .c2).getD default).vars c2.stack
  let w7 := w6.append (rootWord committed2.halves)
  let t := (Wr.sampled H w7).1
  let w8 := (Wr.sampled H w7).2
  let a := atTOf tr c2 alphas beta gamma t flockOut
  let w9 := w8.append (a.values.flatMap scalarWire)
  let rho := (Wr.sampled H w9).1
  let w10 := (Wr.sampled H w9).2
  let combined := commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layouts shape a.c2Columns
  (⟨stack1, committed1, alphas, beta, gamma, flockOut, c2, committed2, t, a, rho, combined, stackLayouts,
    setupStackOf tr⟩, w10)

/-- **The paired batch's hypothesis at the prover's state** (`BatchSyncs3` at `frontOf3`'s). -/
def BatchSyncsAt3 (tr : Trace) (seed : Digest) (terminal : Wr → E) : Prop :=
  BatchSyncs3 H (frontOf3 H commit flock tr (Wr.start seed)).1.combined
    (frontOf3 H commit flock tr (Wr.start seed)).1.stackLayouts
    (frontOf3 H commit flock tr (Wr.start seed)).1.stackOf
    (frontOf3 H commit flock tr (Wr.start seed)).1.atT.ringMap terminal

end Front

/-! ## The joint steps -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **π1-rec3's verifier on its honest prover's stream**: the joint steps from the seed, with the run's ends. -/
theorem reduce_steps3 (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (seed : Digest) (hvalid : tr.shape.validate true = true)
    (hlen : tr.rows.length = tr.shape.heights.length) (h32 : ∀ n ∈ tr.rows, n < 2 ^ 32)
    (hflock : FlockSyncs3 H flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock
      (fun _ ↦ 0))
    (terminal : Wr → E) (hbatch : BatchSyncsAt3 H commit flock tr seed terminal) :
    StepsE (reduceWithFsH (m := Id) (Pure.pure ∘ H) tr.shape (publicWordsOf tr.publicInput) (.flock flockMain) .point
        .rec3 true)
      (proveStreamRec3With (m := Id) (Pure.pure ∘ H) commit flock tr) 0 (Wr.start seed)
      (fun R out posF wF zs ↦ posF = wF.stream.size ∧ out.stream = wF.stream ∧
        R.openings = out.claims.map pointOpening ∧ R.matrices = none ∧
        R.roots = (rootRead out.c1.2.halves, rootRead out.c2.2.halves) ∧
        zs = countChecks tr.rows tr.shape.heights ++ [0] ++
          [terminal (frontOf3 H commit flock tr (Wr.start seed)).2]) := by
  have hb : (Blake2s.flock flockMain != Blake2s.omitted) = true := by decide
  unfold reduceWithFsH proveStreamRec3With
  simp only [hb, hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  apply StepsE.pbind (rows_writes tr.rows _ (fun _ _ ↦ rfl) _)
  apply StepsE.plift
  apply StepsE.pbind (sendRoot_writes _ _)
  apply StepsE.vread (P := []) (Q := rootWord (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves)
    (countBits_reads hlen h32)
  · simp [Wr.start]
  apply StepsE.pos_start (pos0 := (tr.rows.flatMap fun n ↦ integerWire n 4).length) (by simp)
  apply StepsE.vread (Q := []) (nextRoot_reads (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves)
  · simp [Wr.start]
  apply StepsE.bind_pos (h1 := steps_drawRun H _)
  case e => simp [Wr.start]
  set w2 := ((Wr.start seed).append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
    (rootWord (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves) with hw2
  set alphas := squares (Wr.sampled H w2).1 4 with halphas
  set w3 := (Wr.sampled H w2).2 with hw3
  apply StepsE.bind_pos (h1 := Steps.sample H w3)
  case e => rfl
  set beta := (Wr.sampled H w3).1 with hbeta
  set w4 := (Wr.sampled H w3).2 with hw4
  apply StepsE.bind_pos (h1 := Steps.sample H w4)
  case e => rfl
  set gamma := (Wr.sampled H w4).1 with hgamma
  set w5 := (Wr.sampled H w4).2 with hw5
  apply StepsE.bind_pos (h1 := Steps.pmap (g := some) (hflock w5).steps)
  case e => rfl
  set fo := ((flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock).run w5).1 with hfo
  set w6 := ((flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock).run w5).2 with hw6
  apply StepsE.vpure
  apply StepsE.plift
  apply StepsE.pbind (sendRoot_writes _ _)
  apply StepsE.vreadEnd (nextRoot_reads _)
  set c2 := c2DataOf tr (eqKernel alphas) beta gamma with hc2
  set committed2 := commit .c2 (((layoutsOf tr.shape).lookup .c2).getD default).vars c2.stack with hcm2
  apply StepsE.bind_pos (h1 := Steps.sample H _)
  case e => simp
  set w7 := w6.append (rootWord committed2.halves) with hw7
  set t := (Wr.sampled H w7).1 with ht
  set w8 := (Wr.sampled H w7).2 with hw8
  set a := atTOf tr c2 alphas beta gamma t (some fo) with ha
  have hvals := atTOf_values tr c2 alphas beta t gamma (some fo)
  apply StepsE.pbind (sendScalars_writes _ _)
  apply StepsE.vreadD (R := (tailAtT tr c2 alphas beta t).flatMap scalarWire)
    (tablesLoop_reads tr (eqKernel alphas) beta (wOf tr t) _ ?hb tables (#[], #[]))
  case hb => intro _ _; rfl
  case hpos => simp [hw8, ha, hvals]
  case hd => simp [hw8, ha, hvals, List.flatMap_append]
  intro hd0
  unfold tailAtT at hd0
  apply StepsE.vscalarD hd0; intro hd1
  apply StepsE.vscalarD hd1; intro hd2
  apply StepsE.vscalarD hd2; intro hd3
  apply StepsE.vscalarD hd3; intro hd4
  apply StepsE.vscalarD hd4; intro hd5
  apply StepsE.vscalarD hd5; intro hd6
  apply StepsE.vscalarD hd6; intro _
  obtain ⟨map, target, hend⟩ : ∃ map target, fo.end_ = .ring map target :=
    verifyWalkedFsH_end H _ _ _ (((hflock w5).steps).2.2 w6.stream #[] (List.prefix_refl _))
  have hcond : (flockMain.slices == Flock.Slices.tower && ClaimsMode.point == ClaimsMode.point) = true := by decide
  simp only [hend, hcond, ↓reduceIte]
  apply StepsE.bind_pos (h1 := Steps.sample H _)
  case e => simp [hw8, ha, hvals, tailAtT, List.flatMap_append]; omega
  set w9 := w8.append (a.values.flatMap scalarWire) with hw9
  set rho := (Wr.sampled H w9).1 with hrho
  set w10 := (Wr.sampled H w9).2 with hw10
  have hring : a.ringMap = some map := atTOf_ringMap tr c2 alphas beta t gamma fo hend
  simp only [hring]
  have hB := hbatch w10
  generalize hF : (frontOf3 H commit flock tr (Wr.start seed)).1 = F at hB
  have hFr : F.atT.ringMap = some map := by rw [← hF]; exact hring
  have hFc : F.combined = commitments.filterMap (fun c ↦ (combine a.relations c rho).map (c, ·)) := by
    rw [← hF]; rfl
  have hFl : F.stackLayouts = layouts tr.shape a.c2Columns := by rw [← hF]; rfl
  have hFs : F.stackOf = stacksOf (c1Stack tr) c2.stack (setupStackOf tr) := by rw [← hF]; rfl
  rw [hFr, hFc, hFl, hFs] at hB
  apply StepsE.prog_eq (p' := batchProver3 (Pure.pure ∘ H)
    (commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)) (layouts tr.shape a.c2Columns)
    (stacksOf (c1Stack tr) c2.stack (setupStackOf tr)) (some map) >>=
      fun cm ↦ (get : WrM Id Wr) >>= fun c ↦ Pure.pure ⟨c.stream, (c1Stack tr, commit .c1 (c1Layout tr.shape).vars
        (c1Stack tr)), (c2.stack, committed2), setupStackOf tr, cm, none,
        commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·), c2.heapVals⟩)
  case e =>
    simp only [batchProver3, bind_assoc, pure_bind]
    rfl
  apply StepsE.bind_veq (h1 := hB.steps)
  case e =>
    refine batchFsH_congr H _ _ ?_ ?_ (by simp [combine])
    · refine congrArg (fun rels ↦ commitments.filterMap fun c ↦ (combine rels c rho).map (c, ·)) ?_
      rw [ha, countBits_zip_map _ _ _ hlen]
      unfold atTOf
      dsimp only
      rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
      case hb => intro _ _; rfl
      rw [pure_bind, hend, atTFold_snd]
      rfl
    · refine congrArg (layouts tr.shape) ?_
      rw [ha, countBits_zip_map _ _ _ hlen]
      unfold atTOf
      dsimp only
      rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
      case hb => intro _ _; rfl
      rw [pure_bind, hend, atTFold_snd]
      rfl
  apply StepsE.pget
  apply StepsE.vite
  apply StepsE.pure
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append]
    rfl

/-! ## The run on calldata -/

/-- **π1-rec3's honest prover's run** from the seed (`proveStreamRec3With` at `pure ∘ H`): its output and its final
writer. -/
def proverRun3 (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed) (flock : FlockProver Id)
    (tr : Trace) (iv : List UInt8) : CoreOut × Wr :=
  (proveStreamRec3With (m := Id) (Pure.pure ∘ H) commit flock tr).run (Wr.start (seedAt H iv tr.publicInput))

/-- `runWithFsH` at `pure ∘ H`: the walk and `finish` from the seed. -/
theorem runWithFsH_eq (H : List UInt8 → Digest) (shape : UniStatement.Shape) (iv publicInput : List UInt8)
    (stream : Array UInt8) (blake2s : Blake2s) (mode : ClaimsMode) (fs : FsShape) (walk : Bool) :
    runWithFsH (m := Id) (Pure.pure ∘ H) shape iv publicInput stream blake2s mode fs walk =
      ⟨((reduceWithFsH (m := Id) (Pure.pure ∘ H) shape (publicWordsOf publicInput) blake2s mode fs walk >>= fun r ↦
          finish (m := Id) >>= fun _ ↦ Pure.pure r).run.run (Chan.start (seedAt H iv publicInput) stream)).1,
        ((reduceWithFsH (m := Id) (Pure.pure ∘ H) shape (publicWordsOf publicInput) blake2s mode fs walk >>= fun r ↦
          finish (m := Id) >>= fun _ ↦ Pure.pure r).run.run (Chan.start (seedAt H iv publicInput) stream)).2⟩ :=
  rfl

/-- **π1-rec3's verifier on the honest prover's stream**: the run returns `R` (its openings the prover's point
claims, no matrices' claim, its roots the prover's halves), the channel at the end of the stream, synchronised with
the prover's final writer, having collected the counts' checks, Flock's walk's zero and the batch's terminal. -/
theorem runWithFsH_syncs3 (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (iv : List UInt8) (hvalid : tr.shape.Valid)
    (hfit : tr.shape.RowsFit tr.rows)
    (hflock : FlockSyncs3 H flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock
      (fun _ ↦ 0))
    (terminal : Wr → E) (hbatch : BatchSyncsAt3 H commit flock tr (seedAt H iv tr.publicInput) terminal) :
    ∃ R : Reduced,
      runWithFsH (m := Id) (Pure.pure ∘ H) tr.shape iv tr.publicInput (proverRun3 H commit flock tr iv).1.stream
          (.flock flockMain) .point .rec3 true =
        ⟨.ok R, chanAt (proverRun3 H commit flock tr iv).1.stream (proverRun3 H commit flock tr iv).1.stream.size
          (proverRun3 H commit flock tr iv).2
          (countChecks tr.rows tr.shape.heights ++ [0] ++
            [terminal (frontOf3 H commit flock tr (Wr.start (seedAt H iv tr.publicInput))).2]).toArray⟩ ∧
      R.openings = (proverRun3 H commit flock tr iv).1.claims.map pointOpening ∧ R.matrices = none ∧
      R.roots = (rootRead (proverRun3 H commit flock tr iv).1.c1.2.halves,
        rootRead (proverRun3 H commit flock tr iv).1.c2.2.halves) := by
  have hlen : tr.rows.length = tr.shape.heights.length := by rw [hfit.1, hvalid.1]
  obtain ⟨R, out, posF, wF, zs, hs, hpos, hstr, hop, hmat, hroot, hzs⟩ :=
    reduce_steps3 H commit flock tr _ hvalid.2 hlen (rows_lt_32 hvalid.1 hvalid.2 hfit) hflock terminal hbatch
  have hP : proverRun3 H commit flock tr iv = (out, wF) := hs.1
  rw [hP]
  refine ⟨R, ?_, hop, hmat, hroot⟩
  dsimp only
  rw [hstr, runWithFsH_eq, walk_finish hs hpos, hzs]

/-- **π1-rec3's verifier accepts** when the batch's terminal vanishes: no error, every collected value zero. -/
theorem runWithFsH_accepts3 (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (iv : List UInt8) (hvalid : tr.shape.Valid)
    (hfit : tr.shape.RowsFit tr.rows)
    (hflock : FlockSyncs3 H flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock
      (fun _ ↦ 0))
    (terminal : Wr → E) (hbatch : BatchSyncsAt3 H commit flock tr (seedAt H iv tr.publicInput) terminal)
    (hterm : terminal (frontOf3 H commit flock tr (Wr.start (seedAt H iv tr.publicInput))).2 = 0) :
    (runWithFsH (m := Id) (Pure.pure ∘ H) tr.shape iv tr.publicInput (proverRun3 H commit flock tr iv).1.stream
      (.flock flockMain) .point .rec3 true).accepts = true := by
  obtain ⟨R, hrun, -⟩ := runWithFsH_syncs3 H commit flock tr iv hvalid hfit hflock terminal hbatch
  rw [hrun]
  simp only [Outcome.accepts, chanAt, Bool.true_and, Array.all_eq_true', beq_iff_eq]
  intro z hz
  rw [List.mem_toArray, List.mem_append, List.mem_append, List.mem_singleton, List.mem_singleton] at hz
  rcases hz with (hz | rfl) | rfl
  · exact countChecks_zero _ _ (rowsFit_zip hvalid.1 hvalid.2 hfit) z hz
  · rfl
  · exact hterm

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.reduce_steps3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.reduce_steps3

/-- info: 'UniComplete.Rec3.runWithFsH_accepts3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.runWithFsH_accepts3
