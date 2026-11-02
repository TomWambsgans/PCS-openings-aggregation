-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM `mumbai`'s lemmas on its extractor (https://github.com/Verified-zkEVM/leanerVM,
-- commit 6175f1a0, MIT OR Apache-2.0: `lean_vm/LeanVM/Protocol/Extraction/Merkle.lean`,
-- `preimage_eq_some_iff`, `descend`, `subtreeLeaves_getD`, `digestBytes_bytesDigest`).
import Soundness.Defs

/-!
# The Statement's committed word is Compose's

The Statement's extractor (`PcsQuotient.witnessWord`) reads the witness table's word with mumbai's
`committedLeaves` and `leafAt` (`Statement/Extractor.lean`) on a list of Keccak-256 evaluations
`paths` (inputs, digests): a node's children the halves of its unique answered 64-byte preimage, a
leaf the words of its unique answered preimage of `8 w` bytes, zeros under an unanswered node.
Compose's extractor (`adversaryExtractor`) reads it with `merkleWord` (`Compose/Merkle.lean`) on the
transcript of the same evaluations, the digests as 32 bytes (`toB`), then `wordOfMerkle`.

* **`wordOfMerkle_merkleWord_eq`**: at every position below `2^ht`, the two words are equal.
-/

set_option linter.unusedSectionVars false

namespace Soundness

open QuotientRpm Compose LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- The evaluations as Compose's transcript: the digests as their 32 bytes. -/
def trOf (paths : List (List UInt8 × Digest)) : Transcript := paths.map fun e => (e.1, toB e.2)

/-! ## The unique element -/

theorem uniqList_eq_some_iff {α : Type} {l : List α} {x : α} :
    uniqList l = some x ↔ l = [x] := by
  unfold uniqList
  constructor
  · intro h
    split at h
    · rename_i h1
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h1
      simp only [List.head?_cons, Option.some.injEq] at h
      rw [h]
    · exact absurd h (by simp)
  · rintro rfl
    rfl

/-- `uniq` reads the element of a one-element set, and only that. -/
theorem uniq_eq_some_iff {α : Type} {s : Finset α} {x : α} : uniq s = some x ↔ s = {x} := by
  obtain ⟨l, hl⟩ := Quot.exists_rep s.val
  have hu : uniq s = uniqList l := by
    show Quot.liftOn s.val uniqList _ = _
    rw [← hl]
  rw [hu, uniqList_eq_some_iff]
  constructor
  · rintro rfl
    apply Finset.val_injective
    rw [← hl]
    rfl
  · rintro rfl
    have hl' : (l : Multiset α) = ([x] : List α) := hl
    exact List.perm_singleton.mp (Multiset.coe_eq_coe.mp hl')

/-! ## The transcript's answers are the evaluations' -/

/-- The evaluations' inputs cover the inputs `lookupEvaluation` answers. -/
theorem keysCover_lookupEvaluation (paths : List (List UInt8 × Digest)) :
    LeanVM.Extraction.MerkleProofs.KeysCover (LeanVM.lookupEvaluation paths)
      (paths.map (·.1)) := by
  intro x d h
  unfold LeanVM.lookupEvaluation at h
  obtain ⟨e, he, -⟩ := Option.map_eq_some_iff.mp h
  have hx := List.find?_some he
  simp only [decide_eq_true_eq] at hx
  exact List.mem_map.mpr ⟨e, List.mem_of_find?_eq_some he, hx⟩

theorem mem_histOfTr_trOf (paths : List (List UInt8 × Digest)) (z : List UInt8) :
    z ∈ histOfTr (trOf paths) ↔ z ∈ paths.map (·.1) := by
  simp [histOfTr, trOf, List.map_map, Function.comp_def]

theorem tableOfTr_trOf (paths : List (List UInt8 × Digest)) (z : List UInt8) :
    tableOfTr (trOf paths) z =
      ((LeanVM.lookupEvaluation paths z).map toB).getD (Vector.replicate 32 0) := by
  simp [tableOfTr, trOf, LeanVM.lookupEvaluation, List.find?_map, Function.comp_def,
    Option.map_map]

/-- An input of the transcript whose answer has the bytes of `d` is one `lookupEvaluation`
answers with `d`. -/
theorem mem_histOfTr_table_iff (paths : List (List UInt8 × Digest)) (z : List UInt8)
    (d : Digest) :
    (z ∈ histOfTr (trOf paths) ∧ (tableOfTr (trOf paths) z).toList = digestBytes d) ↔
      LeanVM.lookupEvaluation paths z = some d := by
  rw [mem_histOfTr_trOf, tableOfTr_trOf]
  constructor
  · rintro ⟨hz, hzd⟩
    obtain ⟨d', hd'⟩ : ∃ d', LeanVM.lookupEvaluation paths z = some d' := by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
      apply Option.isSome_iff_exists.mp
      unfold LeanVM.lookupEvaluation
      rw [Option.isSome_map, List.find?_isSome]
      exact ⟨e, he, by simp⟩
    rw [hd', Option.map_some, Option.getD_some, ← toList_toB] at hzd
    rw [hd', toB_injective (Vector.toList_inj.mp hzd)]
  · intro h
    refine ⟨keysCover_lookupEvaluation paths z d h, ?_⟩
    rw [h, Option.map_some, Option.getD_some, toList_toB]

/-- **The unique preimages are mumbai's**: `below` on the transcript is `preimage` on the
evaluations' answered pairs. -/
theorem below_eq_preimage (paths : List (List UInt8 × Digest)) (d : Digest) (n : ℕ) :
    Compose.below (histOfTr (trOf paths)) (tableOfTr (trOf paths)) (digestBytes d) n =
      LeanVM.Extraction.preimage
        (LeanVM.Extraction.answerPairs (LeanVM.lookupEvaluation paths) (paths.map (·.1))) d n := by
  apply Option.ext
  intro x
  rw [LeanVM.Extraction.MerkleProofs.preimage_eq_some_iff (keysCover_lookupEvaluation paths),
    Compose.below, uniq_eq_some_iff, Finset.eq_singleton_iff_unique_mem]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx, hxd, hxn⟩, hu⟩
    refine ⟨(mem_histOfTr_table_iff paths x d).mp ⟨hx, hxd⟩, hxn, fun y hy hyn => ?_⟩
    obtain ⟨hyH, hyd⟩ := (mem_histOfTr_table_iff paths y d).mpr hy
    exact hu y ⟨hyH, hyd, hyn⟩
  · rintro ⟨hx, hxn, hu⟩
    obtain ⟨hxH, hxd⟩ := (mem_histOfTr_table_iff paths x d).mpr hx
    exact ⟨⟨hxH, hxd, hxn⟩, fun y ⟨hyH, hyd, hyn⟩ =>
      hu y ((mem_histOfTr_table_iff paths y d).mp ⟨hyH, hyd⟩) hyn⟩

/-! ## The descents -/

/-- **Compose's descent is mumbai's**: from the bytes of `d`, `k` levels up, along the bits of
`p`, the leaf `Compose.leafAt` reaches, as words, is mumbai's `descend`. -/
theorem leafAt_map_eq_descend (paths : List (List UInt8 × Digest)) (w : ℕ) :
    ∀ (k : ℕ) (d : Digest) (p : ℕ),
      (Compose.leafAt (histOfTr (trOf paths)) (tableOfTr (trOf paths)) (8 * w) k (digestBytes d)
          (posBits k p)).map (LeanVM.Extraction.bytesWords w) =
        LeanVM.Extraction.MerkleProofs.descend
          (LeanVM.Extraction.answerPairs (LeanVM.lookupEvaluation paths) (paths.map (·.1))) w k d p
  | 0, d, p => by
    show (Compose.below _ _ (digestBytes d) (8 * w)).map _ = _
    rw [below_eq_preimage]
    rfl
  | k + 1, d, p => by
    rw [posBits_succ]
    show ((Compose.below _ _ (digestBytes d) 64).bind fun y => Compose.leafAt _ _ (8 * w) k
      (if p.testBit k then (y.drop 32).take 32 else y.take 32) (posBits k p)).map _ = _
    rw [below_eq_preimage, LeanVM.Extraction.MerkleProofs.descend]
    cases hx : LeanVM.Extraction.preimage
        (LeanVM.Extraction.answerPairs (LeanVM.lookupEvaluation paths) (paths.map (·.1))) d 64 with
    | none => rfl
    | some y =>
      obtain ⟨-, hylen, -⟩ := (LeanVM.Extraction.MerkleProofs.preimage_eq_some_iff
        (keysCover_lookupEvaluation paths)).mp hx
      simp only [Option.bind_some]
      have ha : digestBytes (LeanVM.Extraction.splitNode y).1 = y.take 32 :=
        LeanVM.Extraction.MerkleProofs.digestBytes_bytesDigest y (by omega)
      have hb : digestBytes (LeanVM.Extraction.splitNode y).2 = (y.drop 32).take 32 :=
        LeanVM.Extraction.MerkleProofs.digestBytes_bytesDigest _ (by simp [hylen])
      cases p.testBit k
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← ha]
        exact leafAt_map_eq_descend paths w k _ p
      · simp only [↓reduceIte]
        rw [← hb]
        exact leafAt_map_eq_descend paths w k _ p

/-- **The Statement's committed word is Compose's**: at every position `p < 2^ht`, the word
`merkleWord` reads under the root `toB d` through the transcript of the evaluations `paths`, as
words of `K` (`wordOfMerkle`), is the word mumbai's `committedLeaves` reads under `d` through
`paths` (`leafAt`). -/
theorem wordOfMerkle_merkleWord_eq (paths : List (List UInt8 × Digest)) (d : Digest) (ht w : ℕ)
    {p : ℕ} (hp : p < 2 ^ ht) :
    wordOfMerkle ht w (merkleWord (histOfTr (trOf paths)) (tableOfTr (trOf paths)) ht (8 * w)
        (toB d)) p =
      LeanVM.Extraction.leafAt
        (LeanVM.Extraction.committedLeaves (LeanVM.lookupEvaluation paths) (paths.map (·.1)) d ht w)
        ht w p := by
  unfold wordOfMerkle
  simp only [hp, ↓reduceDIte]
  rw [LeanVM.Extraction.leafAt, LeanVM.Extraction.committedLeaves, Nat.mod_eq_of_lt hp,
    LeanVM.Extraction.MerkleProofs.subtreeLeaves_getD _ _ _ _ hp]
  show ((Compose.leafAt _ _ (8 * w) ht (toB d).toList (posBits ht p)).map _).getD _ = _
  rw [toList_toB, leafAt_map_eq_descend]

/-- info: 'Soundness.wordOfMerkle_merkleWord_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.wordOfMerkle_merkleWord_eq

end Soundness
