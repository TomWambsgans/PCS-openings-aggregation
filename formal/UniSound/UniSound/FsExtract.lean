-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows
-- `formal/EndToEnd/Soundness/Extract.lean` of this repository (`extractor_of_mem`,
-- `extractFrom_spec`, `mem_witnessDecoder_dec`), with its lemmas (`Soundness/Replay.lean`'s
-- `preimage_merkle`, `leavesUnder_preimage`, `leavesUnder_congr`; `Soundness/MerkleWord.lean`'s
-- `wordOfMerkle_merkleWord_eq`; `Extract.lean`'s `mem_decodeStacks_congr`, `orElse_spec`,
-- `findSome_spec`).
import UniSound.FsWalk

/-!
# The extractor's reading: the Statement's extractor finds what the composed one lists

**`uniExtractBridge`**: `UniExtractBridge` (`FsCouple.lean`), under `LayoutVarsSmall`
(`FinalLink.lean`, a named hypothesis of the end theorem `uniKnowledgeSoundness_code` already), or
only its `C1` instance (`uniExtractBridge_of_c1`). A candidate of `C1`'s root that the composed
extractor (`extractorK` at round `0`: `C1`'s `tableCode`, `uniTc hs 0`) reads off the setup's
evaluations and the adversary's permutation transcript, and that satisfies leanVM 42422001's
relation (`Rel`), makes the Statement's `uniExtractor` return a stack satisfying it, on the same
evaluations:

* **round `0`'s message is `C1`'s root** the stream names (`msgK_uView_c1`: the main line's first
  round has a root and no scalar, its halves at byte `24` are `c1RootOf`'s);
* **the composed candidate is a stack of mumbai's decoder** (`mem_uniTc_zero`): `C1`'s decoder lists
  the plain layout's tables of the stacks `decodeStacks` lists for the Merkle word (`merkleWord` at
  height `rootHeight (wv D 0) 1`), and a plain layout's table read back as a stack is the stack
  (`rdTab_tabOf_plain`: `plainL_table`, zero past its `2^v` words as the Statement's `getD`);
* **the Statement's word is mumbai's `committedLeaves`** (`c1Word_eq_committed`, as
  `Replay.witnessWord_eq_committed`: the hash-map replay and index are mumbai's lists at the
  lengths a Merkle tree hashes), and the two Merkle words agree on every column
  (`wordOfMerkle_merkleWord_eq`), so the Statement's list decoder lists the same stack
  (`mem_decodeStacks_congr`);
* **the stack sizes agree** (`c1Layout_vars`): the Statement decodes at `C1`'s layout's `vars`, the
  composed opening at its layout word's byte `wv D 0`; these are equal when `vars < 256`;
* **the row counts agree** (`rowsOfBytes_rowBytes`): the chain's statement carries the stream's
  first 24 bytes, all `rowsOf` reads;
* the Statement's extractor returns the first candidate satisfying the relation, the fast path's,
  the unique decoder's, then the list decoder's (`extractFrom_spec`, `orElse_spec`): the list
  decoder's list, last, holds one.

**Why a hypothesis beyond `UniShapes`** (decision recorded here): `UniShapes D` bounds the layout
words' variable bytes, `wv D 0 = (c1Layout D.shape).vars % 256` (`layoutWordVars` reads one byte,
`vars.toUInt8`), not `C1`'s variables themselves, and a valid shape may have more than `255`
(`Shape.validate` bounds the heights, not the memory): `logMemory = 279` gives `C1` `vars = 282`,
byte `26`, and the setup `vars = 280`, byte `24`, both in `UniShapes`' range. The composed opening
then decodes a stack of `2^26` words and the Statement's extractor one of `2^282`, and nothing
relates the two lists: the bridge with `hs` alone does not follow from the definitions (a
counterexample would also need a candidate satisfying the relation, not sought here). With
`(c1Layout D.shape).vars < 256` it is proved, and `LayoutVarsSmall D` (every stack below `256`
variables) gives that.
-/

-- The relation is `M3Holds` of a symbolic instance: no simprocs here, which would try to decide it.
set_option simprocs false

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## The row counts -/

theorem rowBytes_getD (b : Array UInt8) {n : ℕ} (hn : n < 24) :
    (rowBytes b).toArray.getD n 0 = b.getD n 0 := by
  simp [rowBytes, hn]

/-- **The row counts the chain's statement announces are the proof's**: `rowsOf` reads the stream's
bytes `0 … 23` only, which `rowBytes` keeps. -/
theorem rowsOfBytes_rowBytes (b : Array UInt8) : rowsOfBytes (rowBytes b) = rowsOf b := by
  unfold rowsOfBytes rowsOf
  refine List.map_congr_left fun k hk => List.foldl_ext _ _ _ fun acc j hj => ?_
  have hk' := List.mem_range.mp hk
  have hj' := List.mem_range.mp hj
  rw [rowBytes_getD b (by omega)]

/-! ## `C1`'s root and its variables -/

/-- **Round `0`'s message is `C1`'s root** the stream names, without scalars. -/
theorem msgK_uView_c1 {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (π : UPf) :
    msgK (uView (uRounds Fl nV V)) π 0 = (some (toB (c1RootOf π.proof)), []) :=
  rfl

/-- `C1`'s layout is the layouts' `C1` entry (it does not depend on `C2`'s columns). -/
theorem c1Layout_eq (s : UniStatement.Shape) : c1Layout s = layoutOf (layoutsOf s) .c1 :=
  rfl

/-- **`C1`'s variables are its layout word's**, when fewer than `256` (the word carries a byte). -/
theorem c1Layout_vars (D : Deployment) (h : (c1Layout D.shape).vars < 256) :
    (c1Layout D.shape).vars = wv D 0 := by
  rw [c1Layout_eq] at h ⊢
  show _ = layoutWordVars ((layoutWords D.shape).getD (wordIndex .c1) [])
  rw [layoutWords_word, layoutWordVars_layoutWord _ _ _ _ h]

/-! ## The composed candidates -/

/-- **A plain layout's table, read back as a stack, is the stack**: its `2^v` words, zero past
them. -/
theorem rdTab_tabOf_plain (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) (st : Vector K (2 ^ v)) :
    rdTab (tabOf (plainL v) ⟨st⟩) = fun i => st.toArray.getD i 0 := by
  funext i
  unfold rdTab
  by_cases hi : i < 2 ^ v
  · have hi' : i < 2 ^ (plainL v).vars := hi
    rw [dite_eq_left hi']
    simp only [tabOf, Vector.getElem_ofFn]
    exact plainL_table v h1 h2 ⟨st⟩ i hi
  · have hi' : ¬ i < 2 ^ (plainL v).vars := hi
    rw [dite_eq_right hi']
    have hs : st.toArray.size ≤ i := by
      rw [Vector.size_toArray]
      omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hs]
    rfl

/-- A table code's candidates under a root: its decoder on the Merkle word. -/
theorem cands_commit {M : Type} (c : TableCode M) (H : Hist) (T : QuotientRpm.Table)
    (r : Bytes32) : c.commit.cands H T r = c.dec (merkleWord H T c.height c.leafLen r) :=
  rfl

/-- **What a layout's table code lists under a root** (`mem_witnessDecoder_dec`'s, for any
layout): the tables of the stacks mumbai's `decodeStacks` lists for the Merkle word, read by
`read`. (Stated for a variable layout: `rfl` at `uniTc`'s would unfold the decoder.) -/
theorem mem_tableCode_cands {L : WhirBridge.Layout} {R : ℕ} {hw : Whir.Admissible L.logN R}
    {M : Type} (read : Tab L → M) (H : Hist) (T : QuotientRpm.Table) (r : Bytes32) (g : M)
    (hg : g ∈ (tableCode L R hw read).commit.cands H T r) :
    ∃ st ∈ LeanVM.Extraction.decodeStacks L.logN R
        (wordOfMerkle (rootHeight L.logN R) (2 ^ WhirBridge.laneFold)
          (merkleWord H T (rootHeight L.logN R) leafBytes r)),
      read (tabOf L ⟨st⟩) = g := by
  rw [cands_commit, tableCode_dec L R hw read
    (merkleWord H T (tableCode L R hw read).height (tableCode L R hw read).leafLen r)] at hg
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hg
  unfold merkleTables decodeTables decodeColumns at hX
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hX
  obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hc
  exact ⟨st, hst, rfl⟩

/-- **What `C1`'s decoder lists**: under a root, the stacks mumbai's `decodeStacks` lists for the
Merkle word, each read back (through the plain layout's table) as the stack itself. -/
theorem mem_uniTc_zero {D : Deployment} (hs : UniShapes D) (H : Hist) (T : QuotientRpm.Table)
    (r : Bytes32) (q : Stk) (hq : q ∈ (uniTc hs 0).commit.cands H T r) :
    ∃ st ∈ LeanVM.Extraction.decodeStacks (wv D 0) logInvRate
        (wordOfMerkle (rootHeight (wv D 0) logInvRate) (2 ^ WhirBridge.laneFold)
          (merkleWord H T (rootHeight (wv D 0) logInvRate) leafBytes r)),
      q = fun i => st.toArray.getD i 0 := by
  have e : uniTc hs 0 = tableCode (shapeK hs 0 (by decide)).L (shapeK hs 0 (by decide)).R
      (shapeK hs 0 (by decide)).adm rdTab := by
    unfold uniTc
    rw [ite_eq_left rfl]
  rw [e] at hq
  obtain ⟨st, hst, rfl⟩ := mem_tableCode_cands _ _ _ _ _ hq
  exact ⟨st, hst, rdTab_tabOf_plain (wv D 0) (hs.lo 0 (by decide)) (hs.hi 0 (by decide)) st⟩

/-! ## The Statement's extractor -/

/-- **The Statement's `C1` word is mumbai's `committedLeaves`** on the setup's evaluations and the
transcript's, under the root the stream names. -/
theorem c1Word_eq_committed (D : Deployment) (setupEvals : List (List UInt8 × Digest))
    (T : Common.OracleQueryLog) (proof : UniProof) :
    c1Word D (PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex
        (setupEvals ++ PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths
          (permutationQueries T)))) proof =
      LeanVM.Extraction.leafAt (LeanVM.Extraction.committedLeaves
        (lookupEvaluation (setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)))
        ((setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)).map (·.1))
        (c1RootOf proof) ((c1Layout D.shape).vars - 6 + 1) 64)
        ((c1Layout D.shape).vars - 6 + 1) 64 := by
  unfold c1Word
  show LeanVM.Extraction.leafAt (PcsQuotient.Replay.leavesUnder _ 64 _ _) _ 64 =
    LeanVM.Extraction.leafAt (LeanVM.Extraction.subtreeLeaves _ 64 _ _) _ 64
  rw [← Soundness.Replay.leavesUnder_preimage]
  congr 1
  refine Soundness.Replay.leavesUnder_congr _ _ 64 (fun d' => ?_) (fun d' => ?_) _ _
  · exact Soundness.Replay.preimage_merkle setupEvals _ d' 64 (by decide)
  · exact Soundness.Replay.preimage_merkle setupEvals _ d' (8 * 64) (by decide)

/-- **The Statement's extractor returns a stack satisfying the relation** when its list decoder
lists a stack whose Lv42 stack satisfies it. The fast path's and the unique decoder's candidates
are tried first; whatever they return satisfies the relation. -/
theorem extractFrom_spec (D : Deployment) (input : Vector UInt8 32)
    (pre : Digest → ℕ → Option (List UInt8)) (proof : UniProof)
    (st : Vector K (2 ^ (c1Layout D.shape).vars))
    (hst : st ∈ LeanVM.Extraction.decodeStacks (c1Layout D.shape).vars 1 (c1Word D pre proof))
    (hrel : D.Relation proof.rows input
      (lv42Stack D.prog (D.sizes proof.rows) D.shape fun i ↦ st.toArray.getD i 0)) :
    ∃ q, extractFrom D input pre proof = some q ∧ D.Relation proof.rows input q := by
  have hf : ∀ (a : Vector K (2 ^ (c1Layout D.shape).vars)) (b : D.Stack proof.rows),
      (if D.Relation proof.rows input
          (lv42Stack D.prog (D.sizes proof.rows) D.shape fun i ↦ a.toArray.getD i 0) then
        some (lv42Stack D.prog (D.sizes proof.rows) D.shape fun i ↦ a.toArray.getD i 0)
      else none) = some b → D.Relation proof.rows input b := fun a b hab => by
    by_cases hr : D.Relation proof.rows input
        (lv42Stack D.prog (D.sizes proof.rows) D.shape fun i ↦ a.toArray.getD i 0)
    · rw [ite_eq_left hr] at hab
      cases hab
      exact hr
    · rw [ite_eq_right hr] at hab
      cases hab
  unfold extractFrom
  exact Soundness.orElse_spec _ _ _ (Soundness.findSome_sat _ _ _ hf)
    (Soundness.orElse_spec _ _ _ (Soundness.findSome_sat _ _ _ hf)
      (Soundness.findSome_spec _ _ _ hf ⟨st, hst, by rw [ite_eq_left hrel]; rfl⟩))

/-- A stack of one size, at another equal size, with the decoder's membership and any property of
its reading. -/
theorem exists_stack_cast {μ ν R : ℕ} (h : μ = ν) (P : (ℕ → K) → Prop) (W : ℕ → List K)
    (st : Vector K (2 ^ ν)) (hst : st ∈ LeanVM.Extraction.decodeStacks ν R W)
    (hP : P fun i => st.toArray.getD i 0) :
    ∃ st' : Vector K (2 ^ μ), st' ∈ LeanVM.Extraction.decodeStacks μ R W ∧
      P fun i => st'.toArray.getD i 0 := by
  subst h
  exact ⟨st, hst, hP⟩

/-! ## The bridge -/

/-- **The extractor's reading, with `C1`'s variables below `256`**: a candidate of `C1`'s root that
the composed extractor lists, satisfying leanVM 42422001's relation, makes the Statement's
extractor find a stack satisfying it. The hypothesis `hc1` is needed: `UniShapes` bounds only
`C1`'s layout word's byte `wv D 0 = vars % 256`, and the Statement's extractor decodes at `vars`
(see the module's docstring). -/
theorem uniExtractBridge_of_c1 (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ)
    (hs : UniShapes D) (hc1 : (c1Layout D.shape).vars < 256) :
    UniExtractBridge D Fl nV V hs := by
  intro t T z q hq hrel
  -- the evaluations both extractors read
  have htr : setupTr t ++ evalTr (permutationQueries T) = Soundness.trOf
      (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T)) := by
    simp only [Soundness.trOf, setupTr, evalTr, List.map_append]
  -- the composed candidate: a stack of `C1`'s decoder under the stream's root
  have h0 : extractorK (fun i => (uniTc hs i).commit) (uView (uRounds Fl nV V))
      (z, setupTr t ++ evalTr (permutationQueries T)) =
      ((uniTc hs 0).commit.cands
        (histOfTr (Soundness.trOf
          (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (tableOfTr (Soundness.trOf
          (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (toB (c1RootOf z.1.proof))).map some := by
    rw [htr]
    show optC _ _ _ (msgK (uView (uRounds Fl nV V)) z.1 0) = _
    rw [msgK_uView_c1]
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

/-- **The extractor's reading** (`UniExtractBridge`), under `LayoutVarsSmall` (the stacks have
fewer than `256` variables: a hypothesis of the end theorem `uniKnowledgeSoundness_code` already).
The form with `hs` alone does not follow from the definitions: `UniShapes` bounds the layout words'
bytes, `vars % 256`, only, and the Statement's extractor decodes at `vars` (see the module's
docstring). -/
theorem uniExtractBridge (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ)
    (hs : UniShapes D) (hsmall : LayoutVarsSmall D) : UniExtractBridge D Fl nV V hs :=
  uniExtractBridge_of_c1 D Fl nV V hs (hsmall .c1)

end UniSound

/-- info: 'UniSound.uniExtractBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniExtractBridge

/-- info: 'UniSound.uniExtractBridge_of_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniExtractBridge_of_c1
