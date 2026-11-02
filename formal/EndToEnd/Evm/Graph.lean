-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Field192

/-!
# The contract's words, exactly

F5's `graph_words` reads the words the contract writes for `PCS_OPEN` as elements (`elem`, their low
`192` bits) and states those elements. Here, on `Primitives.F192` (mumbai's `E`) with its Rust limbs
(`limbsEquiv`), the words themselves:

* `value_lt`: every node an output word names holds a number below `2^192` on every calldata (a
  product, a challenge, or a constant below `2^192`: `outputs_bounded`, by kernel evaluation of the
  graph), so it *is* the word of the element it stands for (`word`), not only read as it;
* **`run_words_formula`**: when the contract reaches its calls, its words are, back to back, the root
  words, layout ids and claim counts, and the words of the elements of `reduce`'s formulas
  (`Formula`, F5's transcription of `quotient::protocol::reduce`) at the leaves the calldata gives
  (`modelVals`): byte for byte what `Formula` computes.
-/

set_option linter.unusedSectionVars false

namespace Evm

open Implementation Implementation.Program Implementation.Emitted QuotientRpm

/-- Whether node `i` holds a number below `2^192` on every calldata: a product (`FIELD_MUL`), a
challenge (`low`), or a constant below `2^192`. -/
def boundedNode (i : ℕ) : Bool :=
  match nodes[i]? with
  | some (.mul _ _) => true
  | some (.low _) => true
  | some (.const c) => decide (c < B192)
  | _ => false

/-- **Every node an output word names is bounded** (kernel evaluation over the `122` words). -/
theorem outputs_bounded :
    outputs.all (fun w => match w with
      | .node i => boundedNode i
      | _ => true) = true := by
  decide +kernel

/-- A node an output word names holds a number below `2^192`. -/
theorem value_lt (H : List UInt8 → Vector UInt8 32) (idx cd : List UInt8) {i : ℕ}
    (h : Word.node i ∈ outputs) : (values H idx cd).getD i 0 < B192 := by
  have hb : boundedNode i = true := by
    have := List.all_eq_true.mp outputs_bounded _ h
    simpa using this
  unfold boundedNode at hb
  rcases hn : nodes[i]? with _ | n
  · rw [hn] at hb
    simp at hb
  · rw [hn] at hb
    cases n with
    | mul a b => rw [values_mul H idx cd hn]; exact mulE_lt _ _
    | low a => rw [values_low H idx cd hn]; exact Nat.mod_lt _ (by decide)
    | const c => rw [values_const H idx cd hn]; exact of_decide_eq_true hb
    | _ => simp at hb

variable (H : List UInt8 → Vector UInt8 32) (idx : Bytes32) (sb : Vector UInt8 64) (r₁ r₂ : Bytes32)
  (x0 x1 x2 x3 x4 : Primitives.F192)

local notation "CD" => calldataOf limbsEquiv sb r₁ r₂ [x0, x1, x2, x3, x4]

/-- **The words the contract writes for `PCS_OPEN`, exactly**: when it reaches its calls (on the
calldata of a statement's 64 bytes, two roots and five values), they are the root word of `r₁`, the
witness layout's id, one claim, the words of `Formula.witness`; the root word of the index root, the
wiring layout's id, one claim, the words of `Formula.wiring`; the root word of `r₂`, the quotient
layout's id, two claims, the words of `Formula.quotient`, `sum_point`'s words and the word of
`Formula.sum` — the formulas at the leaves the calldata gives (`modelVals`). -/
theorem run_words_formula (ws : List ℕ) (h : run H idx CD = some ws) :
    ws = [rootWord r₁.toList, 256 * 1 + 22, 1] ++
        (Formula.witness (modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4)).map
          (word limbsEquiv) ++
        [rootWord idx.toList, 256 * 2 + 22, 1] ++
        (Formula.wiring (modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4)).map
          (word limbsEquiv) ++
        [rootWord r₂.toList, 256 * 3 + 22, 2] ++
        (Formula.quotient limbsEquiv (modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4)).map
          (word limbsEquiv) ++
        sumPointWords ++
        [word limbsEquiv (Formula.sum limbsEquiv (modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4))] := by
  have hF := isF192_primitives
  have hfr := frobOK hF
  have hsome : (run H idx CD).isSome := by rw [h]; rfl
  have hnz := (run_isSome_iff hF H idx sb r₁ r₂ x0 x1 x2 x3 x4 hfr).mp hsome
  obtain ⟨o, ho, hwords⟩ := reduceIds_some
  have hspec := reduceIds_spec (H := H) (idx := idx.toList) (cd := CD) hF hfr
    (by rwa [leafVals_calldataOf]) o ho
  rw [leafVals_calldataOf] at hspec
  obtain ⟨hW, hF', hQ, hS⟩ := hspec
  unfold run at h
  rw [if_pos (wellFormed_calldataOf hF sb r₁ r₂ x0 x1 x2 x3 x4)] at h
  dsimp only at h
  split_ifs at h
  have hws := (Option.some.inj h).symm
  set vals := values H idx.toList CD with hvals
  have hmem : ∀ i, Word.node i ∈ wordsOf o →
      vals.getD i 0 = word limbsEquiv (val limbsEquiv H idx.toList CD i) := by
    intro i hi
    rw [val, word_elem, Nat.mod_eq_of_lt (value_lt H idx.toList CD (hwords ▸ hi))]
  have hmap : ∀ l : List ℕ, (∀ i ∈ l, Word.node i ∈ wordsOf o) →
      l.map (fun x => vals.getD x 0) =
        (l.map (val limbsEquiv H idx.toList CD)).map (word limbsEquiv) := by
    intro l hl
    rw [List.map_map]
    exact List.map_congr_left fun i hi => hmem i (hl i hi)
  have eW : o.witness.map (fun x => vals.getD x 0) =
      (Formula.witness (modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4)).map
        (word limbsEquiv) := by
    rw [hmap _ (fun i hi => by simp [wordsOf, hi]), hW]
  have eF : o.wiring.map (fun x => vals.getD x 0) =
      (Formula.wiring (modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4)).map
        (word limbsEquiv) := by
    rw [hmap _ (fun i hi => by simp [wordsOf, hi]), hF']
  have eQ : o.quotient.map (fun x => vals.getD x 0) =
      (Formula.quotient limbsEquiv (modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4)).map
        (word limbsEquiv) := by
    rw [hmap _ (fun i hi => by simp [wordsOf, hi]), hQ]
  have eS : vals.getD o.sum 0 =
      word limbsEquiv (Formula.sum limbsEquiv (modelVals H idx sb r₁ r₂ limbsEquiv x0 x1 x2 x3 x4)) := by
    rw [hmem _ (by simp [wordsOf]), hS]
  have h68 : cdWord CD (4 + 64) = rootWord r₁.toList := by
    rw [cdWord_slice _ _ (by rw [length_calldataOf]; omega),
      show 4 + 64 = 4 + 64 + 32 * 0 from rfl, drop_root sb r₁ r₂ x0 x1 x2 x3 x4 0 (by norm_num),
      rootWord_eq]
    rfl
  have h100 : cdWord CD (4 + 96) = rootWord r₂.toList := by
    rw [cdWord_slice _ _ (by rw [length_calldataOf]; omega),
      show 4 + 96 = 4 + 64 + 32 * 1 from rfl, drop_root sb r₁ r₂ x0 x1 x2 x3 x4 1 (by norm_num),
      rootWord_eq]
    rfl
  rw [hws, ← hwords]
  have e1 : (wordOf idx.toList CD vals ∘ Word.node) = fun x => vals.getD x 0 := by
    funext x; simp only [Function.comp, wordOf]
  have e2 : (wordOf idx.toList CD vals ∘ Word.const) = id := by
    funext x; simp only [Function.comp, wordOf, id]
  simp only [wordsOf, List.map_append, List.map_cons, List.map_nil, List.map_map, e1, e2,
    List.map_id]
  simp only [wordOf, h68, h100, eW, eF, eQ, eS, List.append_assoc, List.cons_append,
    List.nil_append]

end Evm

/-- info: 'Evm.outputs_bounded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Evm.outputs_bounded

/-- info: 'Evm.run_words_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Evm.run_words_formula
