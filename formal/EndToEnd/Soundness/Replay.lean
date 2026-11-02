-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM `mumbai`'s lemmas on Keccak-256's padding (https://github.com/Verified-zkEVM/leanerVM,
-- commit 6175f1a0, MIT OR Apache-2.0: `lean_vm/LeanVM/Protocol/Rpm/Paths.lean`'s `length_padded`,
-- `padded_prefix`, `unpad_eq_some_iff`). The filter lemmas (`preimage_filter`, `filter_answerPairs`)
-- and the index's specification follow leanerVM's `mumbai-no-more-extractors-in-statements`
-- (`lean_vm/LeanVM/Protocol/Extraction/Fast/Transcript.lean`, `preimage_filter`,
-- `filter_answerPairs`, `hitsOf`), re-proved here on `Std.HashMap`.
import Soundness.Defs
import LeanVM.Protocol.Rpm.Paths

/-!
# The extractor's hash maps compute mumbai's lists

The Statement's extractor (`PcsQuotient.transcriptExtractorFor`) replays the transcript and inverts
the Merkle tree with hash maps (`PcsQuotient/Replay.lean`); the proof (`Extract.lean`) reasons about
mumbai's list versions (`keccakEvaluationsOfTranscript`, `lookupEvaluation`, `answerPairs`, `preimage`,
`committedLeaves`). Here the two are equal where the extractor reads them:

* **`transcriptEvaluations_eq`**: the replay with hash maps gives mumbai's evaluations of the lengths
  `lens` (each of padding at most `maxAbsorbed`): the two replays' states correspond step by step
  (`Rel`, `rel_step`), and a chain's message of a length in `lens` is mumbai's unpadding of its bytes
  (`evaluationOf_capPath`);
* **`preimageIn_preimageIndex`**: the index's unique preimage is mumbai's `preimage` of the answered
  pairs (`firstAnswers_get`: the first answers are `lookupEvaluation`'s; `preimageIn_indexOf`);
* **`preimage_merkle`**: at the lengths the tree hashes, the preimages through the setup's
  evaluations and the transcript's of those lengths are the preimages through all of them
  (`preimage_filter`, `filter_answerPairs`);
* **`witnessWord_eq_committed`**: the Statement's witness word is mumbai's `committedLeaves` on the
  setup's and the transcript's evaluations.
-/

set_option linter.unusedSectionVars false

namespace Soundness.Replay

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Extraction Common PcsQuotient.Replay

/-! ## The replay -/

/-- A chain as the replay with hash maps keeps it: its bytes while at most `maxAbsorbed`. -/
def capPath (p : KeccakState × Bytes) : KeccakState × Option Bytes := (p.1, capBytes p.2)

/-- **The two replays' states correspond**: the hash sets hold the edges' inputs and outputs, the
hash map the newest chain of each capacity, and the chains are mumbai's, their bytes capped. -/
structure Rel (σ : TranscriptReplay) (φ : State) : Prop where
  inputs : ∀ x : KeccakState, φ.inputs.contains x.toArray = (forwardLookup σ.edges x).isSome
  outputs : ∀ y : KeccakState, φ.outputs.contains y.toArray = (inverseLookup σ.edges y).isSome
  chains : ∀ c : List UInt64, φ.chains[c]? =
    (σ.spongePaths.find? fun p ↦ decide (p.1.toList.drop 17 = c)).map capPath
  paths : φ.paths = σ.spongePaths.map capPath

theorem toArray_beq (x z : KeccakState) : (x.toArray == z.toArray) = decide (x = z) := by
  by_cases h : x = z
  · subst h
    simp
  · simp [h]

theorem list_beq (a b : List UInt64) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem forwardLookup_cons (x y z : KeccakState) (E : PermutationEdges KeccakState) :
    (forwardLookup ((x, y) :: E) z).isSome = (decide (x = z) || (forwardLookup E z).isSome) := by
  by_cases h : x = z <;> simp [forwardLookup, h]

theorem inverseLookup_cons (x y z : KeccakState) (E : PermutationEdges KeccakState) :
    (inverseLookup ((x, y) :: E) z).isSome = (decide (y = z) || (inverseLookup E z).isSome) := by
  by_cases h : y = z <;> simp [inverseLookup, h]

/-- A new edge that extends no chain, in both replays. -/
theorem rel_edge {σ : TranscriptReplay} {φ : State} (h : Rel σ φ) (x y : KeccakState) :
    Rel ⟨(x, y) :: σ.edges, σ.spongePaths⟩
      ⟨φ.inputs.insert x.toArray, φ.outputs.insert y.toArray, φ.chains, φ.paths⟩ where
  inputs z := by
    show (φ.inputs.insert x.toArray).contains z.toArray = _
    rw [Std.HashSet.contains_insert, toArray_beq, h.inputs z, forwardLookup_cons]
  outputs z := by
    show (φ.outputs.insert y.toArray).contains z.toArray = _
    rw [Std.HashSet.contains_insert, toArray_beq, h.outputs z, inverseLookup_cons]
  chains := h.chains
  paths := h.paths

theorem capBytes_bind_append (bs c : Bytes) :
    (capBytes bs).bind (fun b ↦ capBytes (b ++ c)) = capBytes (bs ++ c) := by
  unfold capBytes
  by_cases h : bs.length ≤ maxAbsorbed
  · simp [h]
  · have h' : ¬ (bs ++ c).length ≤ maxAbsorbed := by
      rw [List.length_append]
      omega
    rw [ite_eq_right h, ite_eq_right h']
    rfl

/-- A new edge that extends a chain, in both replays. -/
theorem rel_chain {σ : TranscriptReplay} {φ : State} (h : Rel σ φ) (x y s : KeccakState)
    (bs : Bytes) :
    Rel ⟨(x, y) :: σ.edges, (y, bs ++ blockBytes s x) :: σ.spongePaths⟩
      ⟨φ.inputs.insert x.toArray, φ.outputs.insert y.toArray,
        φ.chains.insert (y.toList.drop 17) (y, capBytes (bs ++ blockBytes s x)),
        (y, capBytes (bs ++ blockBytes s x)) :: φ.paths⟩ where
  inputs z := (rel_edge h x y).inputs z
  outputs z := (rel_edge h x y).outputs z
  chains c := by
    show (φ.chains.insert (y.toList.drop 17) (y, capBytes (bs ++ blockBytes s x)))[c]? = _
    rw [Std.HashMap.getElem?_insert, list_beq, h.chains c, List.find?_cons]
    by_cases hc : y.toList.drop 17 = c <;> simp [hc, capPath]
  paths := by
    show (y, capBytes (bs ++ blockBytes s x)) :: φ.paths = _
    rw [h.paths]
    rfl

/-- **One query, both replays.** -/
theorem rel_step {σ : TranscriptReplay} {φ : State} (h : Rel σ φ)
    (q : PermutationQuery KeccakState × KeccakState) : Rel (σ.step q) (φ.step q) := by
  rcases q with ⟨x | y, a⟩
  · rcases hf : forwardLookup σ.edges x with _ | b
    · have hc : φ.inputs.contains x.toArray = false := by rw [h.inputs x, hf]; rfl
      have hch := h.chains (x.toList.drop 17)
      rcases hp : σ.spongePaths.find? (fun p ↦ decide (p.1.toList.drop 17 = x.toList.drop 17))
        with _ | ⟨s, bs⟩
      · rw [hp, Option.map_none] at hch
        simp only [TranscriptReplay.step, State.step, hf, hp, hc, hch, Bool.false_eq_true,
          ↓reduceIte]
        exact rel_edge h x a
      · rw [hp, Option.map_some, capPath] at hch
        simp only [TranscriptReplay.step, State.step, hf, hp, hc, hch, Bool.false_eq_true,
          ↓reduceIte, capBytes_bind_append]
        exact rel_chain h x a s bs
    · have hc : φ.inputs.contains x.toArray = true := by rw [h.inputs x, hf]; rfl
      simp only [TranscriptReplay.step, State.step, hf, hc, ↓reduceIte]
      exact h
  · rcases hf : inverseLookup σ.edges y with _ | b
    · have hc : φ.outputs.contains y.toArray = false := by rw [h.outputs y, hf]; rfl
      simp only [TranscriptReplay.step, State.step, hf, hc, Bool.false_eq_true, ↓reduceIte]
      exact rel_edge h a y
    · have hc : φ.outputs.contains y.toArray = true := by rw [h.outputs y, hf]; rfl
      simp only [TranscriptReplay.step, State.step, hf, hc, ↓reduceIte]
      exact h

/-- The zero state, both replays. -/
theorem rel_init : Rel ⟨[], [(Vector.replicate 25 0, [])]⟩ State.init where
  inputs x := by simp [State.init, forwardLookup]
  outputs y := by simp [State.init, inverseLookup]
  chains c := by
    show ((∅ : Std.HashMap (List UInt64) (KeccakState × Option Bytes)).insert _ _)[c]? = _
    rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty, list_beq, List.find?_cons,
      List.find?_nil]
    by_cases hc : (Vector.replicate 25 (0 : UInt64) : KeccakState).toList.drop 17 = c
    · rw [decide_eq_true hc]
      rfl
    · rw [decide_eq_false hc]
      rfl
  paths := by simp [State.init, capPath, capBytes]

theorem rel_foldl (T : List (PermutationQuery KeccakState × KeccakState)) :
    ∀ {σ : TranscriptReplay} {φ : State}, Rel σ φ →
      Rel (T.foldl TranscriptReplay.step σ) (T.foldl State.step φ) := by
  induction T with
  | nil => exact fun h ↦ h
  | cons q T ih => exact fun h ↦ ih (rel_step h q)

/-! ## The evaluations -/

/-- **A chain's message of a length in `lens`** is mumbai's unpadding of its bytes, kept when its
length is in `lens`. -/
theorem findSome_unpad (lens : List ℕ) (bs : Bytes) :
    (lens.findSome? fun ℓ ↦ if keccakPadded (bs.take ℓ) = bs then some (bs.take ℓ) else none) =
      (keccakUnpadded bs).filter fun m ↦ decide (m.length ∈ lens) := by
  rcases hu : keccakUnpadded bs with _ | m
  · rw [Option.filter_none, List.findSome?_eq_none_iff]
    intro ℓ _
    split_ifs with hp
    · have := (Rpm.unpad_eq_some_iff bs _).mpr hp
      rw [hu] at this
      cases this
    · rfl
  · have hm := (Rpm.unpad_eq_some_iff bs m).mp hu
    have hit : ∀ ℓ, keccakPadded (bs.take ℓ) = bs → bs.take ℓ = m := fun ℓ hp ↦ by
      have := (Rpm.unpad_eq_some_iff bs _).mpr hp
      rw [hu] at this
      exact (Option.some.inj this).symm
    by_cases hl : m.length ∈ lens
    · rw [Option.filter_some, ite_eq_left (by simpa using hl)]
      rcases hF : lens.findSome? (fun ℓ ↦
          if keccakPadded (bs.take ℓ) = bs then some (bs.take ℓ) else none) with _ | v
      · rw [List.findSome?_eq_none_iff] at hF
        have h1 := hF m.length hl
        have hpre : bs.take m.length = m := by rw [← hm]; exact Rpm.padded_prefix m
        rw [hpre, ite_eq_left hm] at h1
        cases h1
      · obtain ⟨ℓ, -, hv⟩ := List.exists_of_findSome?_eq_some hF
        split_ifs at hv with hp
        · rw [← Option.some.inj hv, hit ℓ hp]
    · rw [Option.filter_some, ite_eq_right (by simpa using hl), List.findSome?_eq_none_iff]
      intro ℓ hℓ
      split_ifs with hp
      · exfalso
        have e := hit ℓ hp
        by_cases hle : ℓ ≤ bs.length
        · have : m.length = ℓ := by rw [← e, List.length_take]; omega
          exact hl (this ▸ hℓ)
        · rw [List.take_of_length_le (by omega)] at hp
          have := congrArg List.length hp
          rw [Rpm.length_padded] at this
          omega
      · rfl

/-- **A chain's evaluation** of a length in `lens` (each of padding at most `maxAbsorbed`) is mumbai's,
kept when its length is in `lens`. -/
theorem evaluationOf_capPath (lens : List ℕ)
    (hlens : ∀ ℓ ∈ lens, 136 * (ℓ / 136 + 1) ≤ maxAbsorbed) (p : KeccakState × Bytes) :
    evaluationOf lens (capPath p) =
      ((keccakUnpadded p.2).map fun m ↦ (m, #v[p.1[0], p.1[1], p.1[2], p.1[3]])).filter
        fun e ↦ decide (e.1.length ∈ lens) := by
  obtain ⟨s, bs⟩ := p
  simp only [evaluationOf, capPath, capBytes]
  split_ifs with hb
  · rw [Option.bind_some, findSome_unpad]
    cases keccakUnpadded bs <;> simp [Option.filter]
  · rw [Option.bind_none]
    rcases hu : keccakUnpadded bs with _ | m
    · rfl
    · have hm := (Rpm.unpad_eq_some_iff bs m).mp hu
      have hlen : m.length ∉ lens := fun hl ↦ hb (by
        have := hlens _ hl
        rw [← hm, Rpm.length_padded]
        exact this)
      rw [Option.map_some, Option.filter_some]
      simp [hlen]

/-- **The replay with hash maps gives mumbai's evaluations** of the lengths `lens`, newest first. -/
theorem transcriptEvaluations_eq (lens : List ℕ)
    (hlens : ∀ ℓ ∈ lens, 136 * (ℓ / 136 + 1) ≤ maxAbsorbed)
    (T : List (PermutationQuery KeccakState × KeccakState)) :
    transcriptEvaluations lens T =
      (keccakEvaluationsOfTranscript T).filter fun e ↦ decide (e.1.length ∈ lens) := by
  have hr := (rel_foldl T rel_init).paths
  unfold transcriptEvaluations PcsQuotient.Replay.replay keccakEvaluationsOfTranscript
  rw [hr, List.filterMap_map, List.filter_filterMap]
  congr 1
  funext p
  exact evaluationOf_capPath lens hlens p

/-! ## The answered pairs and the index -/

theorem lookupEvaluation_cons (e : Bytes × Digest) (P : List (Bytes × Digest)) (x : Bytes) :
    lookupEvaluation (e :: P) x = if e.1 = x then some e.2 else lookupEvaluation P x := by
  unfold lookupEvaluation
  rw [List.find?_cons]
  by_cases h : e.1 = x <;> simp [h]

theorem firstAnswers_foldl (P : List (Bytes × Digest)) (x : Bytes) :
    ∀ m : Std.HashMap Bytes Digest,
      (P.foldl (fun m e ↦ m.insertIfNew e.1 e.2) m)[x]? = m[x]?.or (lookupEvaluation P x) := by
  induction P with
  | nil => intro m; simp [lookupEvaluation]
  | cons e P ih =>
    intro m
    rw [List.foldl_cons, ih, Std.HashMap.getElem?_insertIfNew, lookupEvaluation_cons]
    by_cases h : e.1 = x
    · subst h
      by_cases hm : e.1 ∈ m
      · simp [hm]
      · rw [Std.HashMap.getElem?_eq_none hm]
        simp [hm]
    · simp [h]

/-- **The first answers are `lookupEvaluation`'s.** -/
theorem firstAnswers_get (P : List (Bytes × Digest)) (x : Bytes) :
    (firstAnswers P)[x]? = lookupEvaluation P x := by
  rw [firstAnswers, firstAnswers_foldl]
  simp

/-- **The answered pairs are mumbai's `answerPairs` of `lookupEvaluation`.** -/
theorem answeredPairs_eq (P : List (Bytes × Digest)) :
    answeredPairs P = answerPairs (lookupEvaluation P) (P.map (·.1)) := by
  unfold answeredPairs answerPairs
  simp only [firstAnswers_get, List.filterMap_map, Function.comp_def]

/-- The key of a pair `(x, d)` is `(d, |x|)`. -/
def keyHit (d : Digest) (len : ℕ) (p : Bytes × Digest) : Bool :=
  decide ((p.2.toList, p.1.length) = (d.toList, len))

/-- The unique input of the hits, if they have one. -/
def uniqueHit : List (Bytes × Digest) → Option Bytes
  | [] => none
  | p :: rest => if rest.all (fun p' ↦ decide (p'.1 = p.1)) then some p.1 else none

/-- The first hit's input if every hit has it: the unique input of the hits. -/
theorem find_all_uniqueHit (f : Bytes × Digest → Bool) :
    ∀ l : List (Bytes × Digest),
      (match l.find? f with
        | none => none
        | some p => if l.all (fun p' ↦ !f p' || decide (p'.1 = p.1)) then some p.1 else none) =
        uniqueHit (l.filter f)
  | [] => rfl
  | a :: l => by
    by_cases ha : f a = true
    · rw [List.find?_cons, ha, List.filter_cons_of_pos ha]
      show (if (a :: l).all (fun p' ↦ !f p' || decide (p'.1 = a.1)) then some a.1 else none) =
        uniqueHit (a :: l.filter f)
      rw [List.all_cons, ha]
      simp only [uniqueHit, List.all_filter, Bool.not_true, Bool.false_or, decide_true,
        Bool.true_and]
    · have hfa : f a = false := by simpa using ha
      have ih := find_all_uniqueHit f l
      simp only [List.find?_cons, hfa, List.filter_cons_of_neg ha, List.all_cons, Bool.not_false,
        Bool.true_or, Bool.true_and]
      exact ih

/-- **mumbai's `preimage` reads the hits only**: the pairs whose digest is `d` and input `len` bytes
long, through their unique input. -/
theorem preimage_eq_uniqueHit (pairs : List (Bytes × Digest)) (d : Digest) (len : ℕ) :
    preimage pairs d len = uniqueHit (pairs.filter (keyHit d len)) := by
  have hk : ∀ p : Bytes × Digest,
      (decide (p.2.toList = d.toList) && decide (p.1.length = len)) = keyHit d len p := by
    intro p
    simp [keyHit, Prod.mk.injEq]
  unfold preimage
  simp only [hk]
  exact find_all_uniqueHit (keyHit d len) pairs

/-- The index's step on one key's inputs. -/
def hstep (h : Option Hits) (x : Bytes) : Option Hits := some (Hits.add h x)

theorem indexOf_foldl (pairs : List (Bytes × Digest)) (k : List UInt64 × ℕ) :
    ∀ idx : Std.HashMap (List UInt64 × ℕ) Hits, (pairs.foldl indexStep idx)[k]? =
      ((pairs.filter fun p ↦ decide ((p.2.toList, p.1.length) = k)).map (·.1)).foldl hstep
        idx[k]? := by
  induction pairs with
  | nil => intro idx; rfl
  | cons p pairs ih =>
    intro idx
    rw [List.foldl_cons, ih, indexStep, Std.HashMap.getElem?_insert]
    by_cases hk : (p.2.toList, p.1.length) = k
    · subst hk
      simp [hstep]
    · simp [hk]

theorem foldl_hstep_many (xs : List Bytes) : xs.foldl hstep (some .many) = some .many := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

theorem foldl_hstep_one (xs : List Bytes) (x : Bytes) :
    xs.foldl hstep (some (.one x)) =
      some (if xs.all (fun z ↦ decide (z = x)) then .one x else .many) := by
  induction xs with
  | nil => simp
  | cons z xs ih =>
    rw [List.foldl_cons]
    by_cases h : x = z
    · subst h
      have e : hstep (some (.one x)) x = some (.one x) := by simp [hstep, Hits.add]
      rw [e, ih]
      simp
    · have e : hstep (some (.one x)) z = some .many := by simp [hstep, Hits.add, h]
      rw [e, foldl_hstep_many]
      simp [Ne.symm h]

/-- **The index's unique preimage is mumbai's `preimage`.** -/
theorem preimageIn_indexOf (pairs : List (Bytes × Digest)) (d : Digest) (len : ℕ) :
    preimageIn (indexOf pairs) d len = preimage pairs d len := by
  rw [preimage_eq_uniqueHit]
  unfold preimageIn indexOf
  rw [indexOf_foldl, Std.HashMap.getElem?_empty]
  have hk : (fun p : Bytes × Digest ↦ decide ((p.2.toList, p.1.length) = (d.toList, len))) =
      keyHit d len := rfl
  rw [hk]
  rcases pairs.filter (keyHit d len) with _ | ⟨p, rest⟩
  · rfl
  · rw [List.map_cons, List.foldl_cons]
    have e : hstep none p.1 = some (.one p.1) := rfl
    rw [e, foldl_hstep_one, List.all_map]
    by_cases ha : rest.all (fun p' ↦ decide (p'.1 = p.1)) = true
    · have ha' : (rest.all ((fun z ↦ decide (z = p.1)) ∘ fun x ↦ x.1)) = true := ha
      simp only [ha', ↓reduceIte, uniqueHit, ha]
    · have ha' : (rest.all ((fun z ↦ decide (z = p.1)) ∘ fun x ↦ x.1)) = false := by
        simpa using ha
      simp only [ha', Bool.false_eq_true, ↓reduceIte, uniqueHit, ha]

/-- **The preimage index is mumbai's `preimage` of the answered pairs.** -/
theorem preimageIn_preimageIndex (P : List (Bytes × Digest)) (d : Digest) (len : ℕ) :
    preimageIn (preimageIndex P) d len =
      preimage (answerPairs (lookupEvaluation P) (P.map (·.1))) d len := by
  rw [preimageIndex, preimageIn_indexOf, answeredPairs_eq]

/-! ## The lengths the tree hashes -/

/-- `preimage` of a length reads the pairs of that length only. -/
theorem preimage_filter (pairs : List (Bytes × Digest)) (q : Bytes → Bool) (d : Digest) (len : ℕ)
    (hq : ∀ x : Bytes, x.length = len → q x = true) :
    preimage (pairs.filter fun e ↦ q e.1) d len = preimage pairs d len := by
  rw [preimage_eq_uniqueHit, preimage_eq_uniqueHit, List.filter_filter]
  congr 1
  refine List.filter_congr fun p _ ↦ ?_
  by_cases h : keyHit d len p = true
  · have hl : p.1.length = len := by
      simp only [keyHit, decide_eq_true_eq, Prod.mk.injEq] at h
      exact h.2
    rw [h, hq _ hl]
    rfl
  · simp only [Bool.not_eq_true] at h
    rw [h]
    rfl

theorem lookupEvaluation_filter (P : List (Bytes × Digest)) (q : Bytes → Bool) (x : Bytes)
    (hx : q x = true) :
    lookupEvaluation (P.filter fun e ↦ q e.1) x = lookupEvaluation P x := by
  unfold lookupEvaluation
  rw [List.find?_filter]
  congr 1
  apply congrArg (fun f ↦ List.find? f P)
  funext a
  by_cases ha : a.1 = x
  · simp [ha, hx]
  · simp [ha]

/-- The answered pairs of inputs `q` keeps are those of the evaluations `q` keeps. -/
theorem filter_answerPairs (P : List (Bytes × Digest)) (q : Bytes → Bool) :
    (answerPairs (lookupEvaluation P) (P.map (·.1))).filter (fun e ↦ q e.1) =
      answerPairs (lookupEvaluation (P.filter fun e ↦ q e.1))
        ((P.filter fun e ↦ q e.1).map (·.1)) := by
  unfold answerPairs
  rw [List.filterMap_map, List.filterMap_map, List.filter_filterMap, List.filterMap_filter]
  congr 1
  funext e
  by_cases he : q e.1 = true
  · simp only [Function.comp_apply, he, ↓reduceIte, lookupEvaluation_filter P q e.1 he]
    cases lookupEvaluation P e.1 <;> simp [he]
  · simp only [Function.comp_apply, he, Bool.false_eq_true, ↓reduceIte]
    cases lookupEvaluation P e.1 <;> simp [he]

/-- The witness tree's input lengths have paddings of at most `maxAbsorbed` bytes. -/
theorem merkleLengths_padded :
    ∀ ℓ ∈ PcsQuotient.merkleLengths, 136 * (ℓ / 136 + 1) ≤ maxAbsorbed := by
  decide

/-- **At the lengths the tree hashes, the index of the setup's and the transcript's evaluations of
those lengths gives mumbai's preimages through all the evaluations.** -/
theorem preimage_merkle (setupEvals : List (Bytes × Digest))
    (T : List (PermutationQuery KeccakState × KeccakState)) (d : Digest) (len : ℕ)
    (hlen : len ∈ PcsQuotient.merkleLengths) :
    preimageIn (preimageIndex
        (setupEvals ++ transcriptEvaluations PcsQuotient.merkleLengths T)) d len =
      preimage (answerPairs (lookupEvaluation (setupEvals ++ keccakEvaluationsOfTranscript T))
        ((setupEvals ++ keccakEvaluationsOfTranscript T).map (·.1))) d len := by
  set q : Bytes → Bool := fun x ↦ decide (x.length ∈ PcsQuotient.merkleLengths) with hqdef
  have hq : ∀ x : Bytes, x.length = len → q x = true := fun x hx ↦ by simp [hqdef, hx, hlen]
  have hP : (setupEvals ++ transcriptEvaluations PcsQuotient.merkleLengths T).filter
        (fun e ↦ q e.1) =
      (setupEvals ++ keccakEvaluationsOfTranscript T).filter (fun e ↦ q e.1) := by
    rw [transcriptEvaluations_eq _ merkleLengths_padded, List.filter_append, List.filter_append,
      List.filter_filter]
    congr 1
    refine List.filter_congr fun e _ ↦ ?_
    simp [hqdef]
  rw [preimageIn_preimageIndex, ← preimage_filter _ q d len hq, filter_answerPairs, hP,
    ← filter_answerPairs, preimage_filter _ q d len hq]

/-! ## The leaves and the word -/

/-- `leavesUnder` on mumbai's preimages is mumbai's `subtreeLeaves`. -/
theorem leavesUnder_preimage (pairs : List (Bytes × Digest)) (w : ℕ) :
    ∀ (h : ℕ) (d : Digest), leavesUnder (preimage pairs) w h d = subtreeLeaves pairs w h d
  | 0, d => rfl
  | h + 1, d => by
    simp only [leavesUnder, subtreeLeaves]
    rcases preimage pairs d 64 with _ | x
    · rfl
    · simp only [leavesUnder_preimage pairs w h]

/-- `leavesUnder` reads its preimages at `64` bytes and at a leaf's `8w`. -/
theorem leavesUnder_congr (pre₁ pre₂ : Digest → ℕ → Option Bytes) (w : ℕ)
    (h64 : ∀ d, pre₁ d 64 = pre₂ d 64) (hw : ∀ d, pre₁ d (8 * w) = pre₂ d (8 * w)) :
    ∀ (h : ℕ) (d : Digest), leavesUnder pre₁ w h d = leavesUnder pre₂ w h d
  | 0, d => by simp only [leavesUnder, hw d]
  | h + 1, d => by simp only [leavesUnder, h64 d, leavesUnder_congr pre₁ pre₂ w h64 hw h]

/-- **The Statement's witness word is mumbai's `committedLeaves`** on the setup's evaluations and the
transcript's, at a proof naming the witness root `d`. -/
theorem witnessWord_eq_committed (setupEvals : List (Bytes × Digest)) (T : OracleQueryLog)
    (proof : PcsQuotient.Proof) (d : Digest)
    (hd : digestOfScalars proof.reduction.witnessRoot = some d) :
    PcsQuotient.witnessWord 22 (preimageIn (preimageIndex
        (setupEvals ++ transcriptEvaluations PcsQuotient.merkleLengths (permutationQueries T))))
        proof =
      some (leafAt (committedLeaves
        (lookupEvaluation (setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)))
        ((setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)).map (·.1)) d 20
          (2 ^ WhirBridge.laneFold)) 20 (2 ^ WhirBridge.laneFold)) := by
  unfold PcsQuotient.witnessWord PcsQuotient.witnessRootOf
  rw [hd, Option.map_some]
  congr 1
  show leafAt (leavesUnder _ 64 20 d) 20 64 = leafAt (subtreeLeaves _ 64 20 d) 20 64
  rw [← leavesUnder_preimage]
  congr 1
  refine leavesUnder_congr _ _ 64 (fun d' ↦ ?_) (fun d' ↦ ?_) 20 d
  · exact preimage_merkle setupEvals _ d' 64 (by decide)
  · exact preimage_merkle setupEvals _ d' (8 * 64) (by decide)

/-- info: 'Soundness.Replay.witnessWord_eq_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.Replay.witnessWord_eq_committed

/-- info: 'Soundness.Replay.transcriptEvaluations_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.Replay.transcriptEvaluations_eq

end Soundness.Replay
