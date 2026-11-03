-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsExtract.lean`
-- (`uniExtractBridge_of_c1`) at π1-rec3's view of the stream; the extractor (`uniExtractor`) is unchanged.
import UniSound.Rec3.FsWalk3
import UniSound.FsExtract

/-!
# π1-rec3: the Statement's extractor finds what the composed one lists

**`uniExtractBridge3`**: `UniExtractBridge3` under `LayoutVarsSmall` (only its `C1` instance is used,
`uniExtractBridge3_of_c1`). The proof is `FsExtract.lean`'s: round `0`'s message is `C1`'s root the stream names
(`msgK_uView3_c1`: π1-rec3's first round, `⟨true, 0, 2⟩`, has a root and no scalar), the composed candidate is a
stack of mumbai's decoder (`mem_uniTc_zero`), the Statement's word is mumbai's `committedLeaves`
(`c1Word_eq_committed`), the stack sizes agree below `256` variables (`c1Layout_vars`), and the row counts agree
(`rowsOfBytes_rowBytes`). The extractor's reading does not depend on the rounds after round `0`.
-/

-- The relation is `M3Holds` of a symbolic instance: no simprocs here, which would try to decide it.
set_option simprocs false

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-- **Round `0`'s message is `C1`'s root** the stream names, without scalars. -/
theorem msgK_uView3_c1 {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (π : UPf) :
    msgK (uView (uRounds3 F3 nV np)) π 0 = (some (toB (c1RootOf π.proof)), []) :=
  rfl

/-- **The extractor's reading at π1-rec3, with `C1`'s variables below `256`** (`uniExtractBridge_of_c1`'s proof). -/
theorem uniExtractBridge3_of_c1 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ)
    (hs : UniShapes D) (hc1 : (c1Layout D.shape).vars < 256) :
    UniExtractBridge3 D F3 nV np hs := by
  intro t T z q hq hrel
  -- the evaluations both extractors read
  have htr : setupTr t ++ evalTr (permutationQueries T) = Soundness.trOf
      (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T)) := by
    simp only [Soundness.trOf, setupTr, evalTr, List.map_append]
  -- the composed candidate: a stack of `C1`'s decoder under the stream's root
  have h0 : extractorK (fun i => (uniTc hs i).commit) (uView (uRounds3 F3 nV np))
      (z, setupTr t ++ evalTr (permutationQueries T)) =
      ((uniTc hs 0).commit.cands
        (histOfTr (Soundness.trOf
          (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (tableOfTr (Soundness.trOf
          (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (toB (c1RootOf z.1.proof))).map some := by
    rw [htr]
    show optC _ _ _ (msgK (uView (uRounds3 F3 nV np)) z.1 0) = _
    rw [msgK_uView3_c1]
    rfl
  rw [h0] at hq
  have hq' : q ∈ (uniTc hs 0).commit.cands
      (histOfTr (Soundness.trOf
        (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T))))
      (tableOfTr (Soundness.trOf
        (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T))))
      (toB (c1RootOf z.1.proof)) := by
    obtain ⟨q', hq', he⟩ := List.mem_map.mp hq
    rw [← Option.some.inj he]
    exact hq'
  obtain ⟨st, hst, rfl⟩ := mem_uniTc_zero hs _ _ _ q hq'
  -- the Statement's word agrees with the composed one on every column
  have hμ : (c1Layout D.shape).vars = wv D 0 := c1Layout_vars D hc1
  have hadm : Whir.Admissible (wv D 0) logInvRate := (shapeK hs 0 (by decide)).adm
  have hst2 : st ∈ LeanVM.Extraction.decodeStacks (wv D 0) 1
      (c1Word D (PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex
        (t.evaluations ++ PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths
          (permutationQueries T)))) z.1.proof) := by
    refine Soundness.mem_decodeStacks_congr hadm (fun p hp => ?_) st hst
    rw [c1Word_eq_committed, hμ]
    exact Soundness.wordOfMerkle_merkleWord_eq _ _ _ _ hp
  -- the relation, at the proof's row counts
  have hrel' : D.Relation (rowsOfBytes (rowBytes z.1.proof.stream)) z.1.input
      (lv42Stack D.prog (D.sizes (rowsOfBytes (rowBytes z.1.proof.stream))) D.shape
        fun i => st.toArray.getD i 0) := hrel
  rw [rowsOfBytes_rowBytes] at hrel'
  obtain ⟨st', hst', hP⟩ := exists_stack_cast hμ
    (fun f => D.Relation (rowsOf z.1.proof.stream) z.1.input
      (lv42Stack D.prog (D.sizes (rowsOf z.1.proof.stream)) D.shape f)) _ st hst2 hrel'
  exact extractFrom_spec D z.1.input _ z.1.proof st' hst' hP

/-- **The extractor's reading at π1-rec3** (`UniExtractBridge3`), under `LayoutVarsSmall`. -/
theorem uniExtractBridge3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ)
    (hs : UniShapes D) (hsmall : LayoutVarsSmall D) : UniExtractBridge3 D F3 nV np hs :=
  uniExtractBridge3_of_c1 D F3 nV np hs (hsmall .c1)

end UniSound

/-- info: 'UniSound.uniExtractBridge3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniExtractBridge3
