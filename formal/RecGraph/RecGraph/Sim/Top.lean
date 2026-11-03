-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Calls
import RecGraph.Pi1.Main

/-!
# `Pi1Sim` from reduce's lockstep

`pi1Sim_of_reduce`: if `Pi1.reduce` simulates `reduceWithFs` (`SimE`, off the hazard at challenges `42` and `49`,
the outputs related by `RedR`) from any state like the one the statement words leave, then `Pi1Sim`:

* the seed and the statement words (`start_couple`, `statementWords_psim`) couple the recorder with `Chan.start`;
* on a run that succeeds, `finish` accepts exactly the stream of the record's length (`finish_run`, the coupling's
  cursor): the zeros are the coupling's, the nonzeros none, the calls `pcsCalls` (`calls_eq`);
* on a run that fails, the stream is shorter than the record (`SimE`'s failure clause), so both sides are `none`;
* `MergeHazard` reads the final channel, which `finish` does not change (`walk_chan`).
-/

-- The judgment is `RecGraph.Sim.Sim`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph.Pi1

/-- `pi1Rec3`: the statement words, then `reduce`. -/
theorem pi1Rec3_eq : pi1Rec3 = statementWords >>= Pi1.reduce reference := by
  unfold pi1Rec3
  exact statementWords_bind _

theorem start_chIds : chIds RecState.start = [] := by
  unfold chIds
  rw [start_nodes]
  rfl

/-- The verifier's walk: reduce, then `finish`. -/
abbrev walkU (π : KeccakState → KeccakState) (publicInput : List UInt8) : ChanM Id Reduced :=
  reduceWithFs (Fp π) reference (publicWordsOf publicInput) (.flock flockMain) .point .rec3 true >>= fun r ↦
    UniStatement.finish (m := Id) >>= fun _ ↦ pure r

/-- The outputs of a walk's outcome. -/
def outcomeOutputs (x : Except UniError Reduced × Chan) : Option Outputs :=
  match x.1 with
  | .ok r => some ⟨pcsCalls reference referenceRoots r, x.2.zeros.toList, []⟩
  | .error _ => none

theorem verifierOutputs_eq (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) :
    verifierOutputsWith (m := Id) (fun s ↦ pure (π s)) reference referenceRoots iv publicInput stream .rec3 true =
      outcomeOutputs (((walkU π publicInput).run).run (Chan.start (Id.run (seedWith (Fp π) iv publicInput)) stream)) :=
  rfl

theorem mergeHazard_iff (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) :
    MergeHazard π iv publicInput stream ↔
      ¬ NoHazardAt (((walkU π publicInput).run).run (Chan.start (Id.run (seedWith (Fp π) iv publicInput)) stream)).2 := by
  unfold NoHazardAt
  rw [not_not]
  exact Iff.rfl

/-- `finish` keeps the channel. -/
theorem walk_chan (u : ChanM Id Reduced) (c : Chan) :
    (((u >>= fun r ↦ UniStatement.finish (m := Id) >>= fun _ ↦ pure r).run).run c).2 = ((u.run).run c).2 := by
  rw [run_bind]
  cases h : (u.run).run c with
  | mk r c' =>
    cases r with
    | error e => rfl
    | ok b =>
      show (((UniStatement.finish (m := Id) >>= fun _ ↦ pure b).run).run c').2 = c'
      rw [run_bind, finish_run]
      by_cases hc : c'.cursor = c'.data.size
      · simp only [hc, ↓reduceIte]; rfl
      · simp only [hc, ↓reduceIte]

/-- The run's values are the record's evaluation (`run_vals`). -/
theorem run_vals_record {α : Type} (π : KeccakState → KeccakState) (iv publicInput : List UInt8)
    (stream : Array UInt8) (p : Prog α) :
    (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2 =
      evalAll π iv publicInput stream (p.record RecState.start).2 := by
  obtain ⟨h1, h2, -⟩ := run_vals π iv publicInput stream p RecState.start start_kinv
  rw [h1, ← h2]

theorem streamLen_recordedGraph (p : Prog ReducedS) :
    (recordedGraph p).streamLen = (p.record RecState.start).2.cursor := by
  unfold recordedGraph RecState.graph
  rfl

theorem outputsOf_recordedGraph (p : Prog ReducedS) (stream : Array UInt8) (vals : Array Value) :
    outputsOf (recordedGraph p) stream vals =
      ⟨(callsOf (p.record RecState.start).2 (p.record RecState.start).1).map
          (·.flatMap (RecGraph.wordBytes stream vals)),
        (p.record RecState.start).2.zero.toList.map (valE vals), []⟩ := by
  unfold outputsOf recordedGraph RecState.graph
  rfl

theorem outcomeOutputs_ok (b : Reduced) (c : Chan) :
    outcomeOutputs (.ok b, c) = some ⟨pcsCalls reference referenceRoots b, c.zeros.toList, []⟩ := rfl

theorem outcomeOutputs_error (e : UniError) (c : Chan) : outcomeOutputs (.error e, c) = none := rfl

/-- The walk on a run of reduce that succeeds: `finish` accepts iff the cursor is at the stream's end. -/
theorem walk_ok {π : KeccakState → KeccakState} {publicInput : List UInt8} {c c' : Chan} {b : Reduced}
    (h : ((reduceWithFs (Fp π) reference (publicWordsOf publicInput) (.flock flockMain) .point .rec3
      true).run).run c = (.ok b, c')) :
    ((walkU π publicInput).run).run c =
      if c'.cursor = c'.data.size then (.ok b, c') else (.error .streamNotConsumed, c') := by
  unfold walkU
  rw [run_bind_ok _ h, run_bind, finish_run]
  by_cases hc : c'.cursor = c'.data.size
  · simp only [hc, ↓reduceIte]; rfl
  · simp only [hc, ↓reduceIte]

/-- `valE` of the evaluation, as a function, is `val` (rewritten so as not to unfold a record's zeros). -/
theorem valE_evalAll_fun (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)
    (st : RecState) : valE (evalAll π iv publicInput stream st) = val π iv publicInput stream st := rfl

/-- **`Pi1Sim` from reduce's lockstep.** -/
theorem pi1Sim_of_reduce
    (hred : ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
      (words : List Nat) (wordsE : List E), Good st → st.nodes[0]? = some Node.seed → st.cursor = 0 →
      chIds st = [] → RpL π iv publicInput stream st words wordsE → wordsE.length = 4 →
      SimE π iv publicInput stream NoHazardAt st (Pi1.reduce reference words)
        (reduceWithFs (Fp π) reference wordsE (.flock flockMain) .point .rec3 true) (RedR π iv publicInput stream)) :
    Pi1Sim := by
  intro π iv publicInput stream hz
  rw [mergeHazard_iff, not_not] at hz
  rw [verifierOutputs_eq, pi1Rec3_eq]
  generalize publicInput.toList = pub at hz ⊢
  obtain ⟨hp0, hw0⟩ := statementWords_psim π iv pub stream RecState.start start_good
  have hc0 := (start_couple π iv pub stream).pstep π iv pub stream hp0
  have hseed : (statementWords.record RecState.start).2.nodes[0]? = some Node.seed :=
    nodes_grow hp0.grows (by rw [start_nodes]; rfl)
  have hS := hred π iv pub stream _ _ _ hp0.good hseed (hp0.cursor.trans start_cursor)
    (hp0.chal.trans start_chIds) hw0 (by simp [publicWordsOf])
  have hb : InputsBelow ((Pi1.reduce reference (statementWords.record RecState.start).1).record
      (statementWords.record RecState.start).2).2 :=
    inputsBelow_record _ _ (inputsBelow_record _ _ inputsBelow_start)
  rw [run_vals_record, streamLen_recordedGraph, outputsOf_recordedGraph, record_bind]
  have hQ : NoHazardAt (((reduceWithFs (Fp π) reference (publicWordsOf pub) (.flock flockMain) .point .rec3
      true).run).run (Chan.start (Id.run (seedWith (Fp π) iv pub)) stream)).2 := by
    rw [← walk_chan]; exact hz
  rcases hS _ hc0 (Nat.zero_le _) hQ with ⟨b, c', hrun, hc', -, -, hR⟩ | ⟨⟨e, c', hrun⟩, hlt⟩
  · rw [walk_ok hrun]
    have hcd : c'.data.size = stream.size := by rw [hc'.data]
    by_cases hs : stream.size = ((Pi1.reduce reference (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor
    · have hcc : c'.cursor = c'.data.size := by rw [hc'.cursor, hcd, hs]
      rw [ite_eq_left hcc, ite_eq_left hs, outcomeOutputs_ok, calls_eq π iv pub stream hc'.good hR hb hs,
        hc'.zeros, valE_evalAll_fun]
    · have hcc : ¬ c'.cursor = c'.data.size := by rw [hc'.cursor, hcd]; exact fun h ↦ hs h.symm
      rw [ite_eq_right hcc, ite_eq_right hs, outcomeOutputs_error]
  · unfold walkU
    rw [run_bind_error _ hrun]
    have hlt' : stream.size < ((Pi1.reduce reference (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor := hlt
    have hs : ¬ stream.size = ((Pi1.reduce reference (statementWords.record RecState.start).1).record
        (statementWords.record RecState.start).2).2.cursor := by omega
    rw [ite_eq_right hs, outcomeOutputs_error]

end RecGraph.Sim
