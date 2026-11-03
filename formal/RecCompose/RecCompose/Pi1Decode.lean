-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The byte round trips go through `UInt64.toNat`, as
-- `formal/UniComplete/UniComplete/AlgCRun.lean`'s `run_fold_be64` (reused) and `SyncBasic.lean`'s do.
import RecCompose.Basic
import UniComplete.AlgCRun
import UniComplete.SyncBasic

/-!
# π1's own `PCS_OPEN` calls, decoded

`decodePi1Call` (`RecStatement.Security`) reads π1's contract's call bytes (`UniStatement.openingWords` of a point
claim: the root word, the layout word, the count `1`, the coordinates, the value) back into the opening's root, layout
word and claim (`decodePi1Call_point`), when the claim's point has the layout word's variables; the root is the setup's
digest by its code `0x5503`, else the root word read back (`rootOfWord`), which is `UniStatement.rootOf` of the halves
when their top limbs are zero (`rootOfWord_rootWord`).
-/

namespace RecCompose.Pi1Decode

open RecStatement UniStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## Words -/

theorem length_be64 (u : UInt64) : (be64 u).length = 8 := by simp [be64]

@[simp] theorem length_elementWord (x : E) : (elementWord x).length = 32 := by
  simp [elementWord]

@[simp] theorem length_numberWord (n : ℕ) : (numberWord n).length = 32 := by
  simp [numberWord]

/-- The big-endian fold of `be64 u` placed at `at'` is `u`. -/
theorem fold_be64_at (pre post : List UInt8) (u : UInt64) (at' : ℕ) (h : pre.length = at') :
    (List.range 8).foldl (fun (acc : UInt64) k ↦ (acc <<< 8) ||| ((pre ++ be64 u ++ post).getD (at' + k) 0).toUInt64)
      (0 : UInt64) = u := by
  apply UInt64.toNat_inj.mp
  rw [UniComplete.AlgC.run_fold_be64 u (fun k ↦ (pre ++ be64 u ++ post).getD (at' + k) 0) (fun k hk ↦ by
    rw [← h, List.append_assoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by rw [length_be64]; omega)]) 8 le_rfl]
  simp

/-- **An element word reads back its element.** -/
theorem elementOfWord_elementWord (x : E) : elementOfWord (elementWord x) = some x := by
  unfold elementOfWord
  have hz : ((elementWord x).take 8).all (· = 0) = true := by
    simp [elementWord]
  rw [ite_eq_left ⟨length_elementWord x, by simpa using hz⟩]
  have e : elementWord x = (List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane) ++
      be64 (x.limb 0).lane ++ [] := by simp [elementWord, List.append_assoc]
  have h24 := fold_be64_at (List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane) [] (x.limb 0).lane 24
    (by simp)
  have h16 := fold_be64_at (List.replicate 8 0 ++ be64 (x.limb 2).lane) (be64 (x.limb 0).lane) (x.limb 1).lane 16
    (by simp)
  have h8 := fold_be64_at (List.replicate 8 0) (be64 (x.limb 1).lane ++ be64 (x.limb 0).lane) (x.limb 2).lane 8
    (by simp)
  have e16 : elementWord x = List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane ++
      be64 (x.limb 0).lane := by simp [elementWord]
  have e8 : elementWord x = List.replicate 8 0 ++ be64 (x.limb 2).lane ++
      (be64 (x.limb 1).lane ++ be64 (x.limb 0).lane) := by simp [elementWord, List.append_assoc]
  rw [← e] at h24
  rw [show List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane ++ be64 (x.limb 0).lane =
    elementWord x from e16.symm] at h16
  rw [show List.replicate 8 0 ++ be64 (x.limb 2).lane ++ (be64 (x.limb 1).lane ++ be64 (x.limb 0).lane) =
    elementWord x from e8.symm] at h8
  simp only [h24, h16, h8]
  exact congrArg some (UniComplete.eNew_limbs x)

/-- The count word of `1`. -/
theorem countOfWord_numberWord_one : countOfWord (numberWord 1) = some 1 := by decide

/-! ## A root word read back -/

/-- Byte `k` of a word, little-endian, as a number. -/
theorem byte_toNat (u : UInt64) {k : ℕ} (hk : k < 8) :
    ((u >>> (8 * k).toUInt64).toUInt8).toNat = u.toNat / 2 ^ (8 * k) % 256 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have : (8 * k).toUInt64.toNat % 64 = 8 * k := by interval_cases k <;> rfl
  rw [this]

/-- The little-endian fold of a word's first `j` bytes is the word modulo `2^(8 j)`. -/
theorem le_fold_toNat (u : UInt64) (f : ℕ → UInt8) (hf : ∀ k < 8, f k = (u >>> (8 * k).toUInt64).toUInt8) :
    ∀ j ≤ 8, ((List.range j).foldl (fun (acc : UInt64) k ↦ acc ||| ((f k).toUInt64 <<< (8 * k).toUInt64))
      (0 : UInt64)).toNat = u.toNat % 2 ^ (8 * j)
  | 0, _ => by simp [Nat.mod_one]
  | j + 1, hj => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, UInt64.toNat_or,
      le_fold_toNat u f hf j (by omega), UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, hf j (by omega),
      byte_toNat u (by omega)]
    have h64 : (8 * j).toUInt64.toNat % 64 = 8 * j := by
      have : j < 8 := by omega
      interval_cases j <;> rfl
    rw [h64]
    have hlt : (u.toNat / 2 ^ (8 * j) % 256) <<< (8 * j) < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq]
      calc u.toNat / 2 ^ (8 * j) % 256 * 2 ^ (8 * j) < 256 * 2 ^ (8 * j) :=
            Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by norm_num)) (by positivity)
        _ = 2 ^ (8 * j + 8) := by rw [pow_add]; ring
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.mod_eq_of_lt hlt, Nat.lor_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by positivity)), Nat.shiftLeft_eq,
      show 8 * (j + 1) = 8 * j + 8 by ring, pow_add, Nat.mod_mul]
    ring_nf

/-- **The little-endian fold of a word's bytes is the word.** -/
theorem le_fold (u : UInt64) (f : ℕ → UInt8) (hf : ∀ k < 8, f k = (u >>> (8 * k).toUInt64).toUInt8) :
    (List.range 8).foldl (fun (acc : UInt64) k ↦ acc ||| ((f k).toUInt64 <<< (8 * k).toUInt64)) (0 : UInt64) = u := by
  apply UInt64.toNat_inj.mp
  rw [le_fold_toNat u f hf 8 le_rfl, Nat.mod_eq_of_lt (by simpa using u.toNat_lt)]

/-- Byte `k` of `be64 u` reversed is the word's byte `k`, little-endian. -/
theorem be64_reverse_getD (u : UInt64) {k : ℕ} (hk : k < 8) :
    (be64 u).reverse.getD k 0 = (u >>> (8 * k).toUInt64).toUInt8 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [length_be64]; exact hk), length_be64,
    ← List.getD_eq_getElem?_getD, UniComplete.be64_getD u (by omega)]
  congr 3
  omega

theorem getD_append_left {l r : List UInt8} {k : ℕ} (h : k < l.length) : (l ++ r).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (l r : List UInt8) (k : ℕ) : (l ++ r).getD (l.length + k) 0 = r.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left]

/-- **A root word read back** (`root_of_word` of `rootWord`) is the root of its halves (`rootOf`), when their top limbs
are zero (as `nextRoot` reads them). -/
theorem rootOfWord_rootWord (h : E × E) (h1 : h.1.limb 2 = 0) (h2 : h.2.limb 2 = 0) :
    rootOfWord (rootWord h) = rootOf h := by
  set a0 := (h.1.limb 0).lane
  set a1 := (h.1.limb 1).lane
  set b0 := (h.2.limb 0).lane
  set b1 := (h.2.limb 1).lane
  have hroot : rootOf h = #v[a0, a1, b0, b1] := by
    unfold rootOf digestOfScalars
    rw [ite_eq_left ⟨h1, h2⟩]
    rfl
  have hb : rootWordOfBytes (rootWord h) =
      (be64 a0).reverse ++ ((be64 a1).reverse ++ ((be64 b0).reverse ++ (be64 b1).reverse)) := by
    have e : rootWord h = (be64 a1 ++ be64 a0) ++ (be64 b1 ++ be64 b0) := by
      simp only [rootWord, List.append_assoc]; rfl
    unfold rootWordOfBytes
    rw [e, List.take_left' (by simp), List.drop_left' (by simp),
      List.take_of_length_le (by simp)]
    simp only [List.reverse_append, List.append_assoc]
  rw [hroot]
  unfold rootOfWord
  rw [hb]
  unfold digestOfBytes32
  have l8 : ∀ u : UInt64, (be64 u).reverse.length = 8 := fun u ↦ by simp
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  interval_cases j
  · refine le_fold a0 _ fun k hk ↦ ?_
    rw [show 8 * 0 + k = k by ring, getD_append_left (by rw [l8]; exact hk), be64_reverse_getD a0 hk]
  · refine le_fold a1 _ fun k hk ↦ ?_
    rw [show 8 * 1 + k = (be64 a0).reverse.length + k by rw [l8], getD_append_right,
      getD_append_left (by rw [l8]; exact hk), be64_reverse_getD a1 hk]
  · refine le_fold b0 _ fun k hk ↦ ?_
    rw [show 8 * 2 + k = (be64 a0).reverse.length + ((be64 a1).reverse.length + k) by rw [l8, l8]; ring,
      getD_append_right, getD_append_right, getD_append_left (by rw [l8]; exact hk), be64_reverse_getD b0 hk]
  · refine le_fold b1 _ fun k hk ↦ ?_
    rw [show 8 * 3 + k = (be64 a0).reverse.length + ((be64 a1).reverse.length +
        ((be64 b0).reverse.length + k)) by rw [l8, l8, l8]; ring,
      getD_append_right, getD_append_right, getD_append_right, be64_reverse_getD b1 hk]

/-! ## A call's words -/

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  have : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  rw [this, LeanVM.Rpm.length_lanesBytes]
  simp

theorem length_layoutWord (s : UniStatement.Shape) (code vars placed : ℕ) : (UniStatement.layoutWord s code vars placed).length = 32 := by
  simp [UniStatement.layoutWord, UniStatement.shapeBytes]

theorem layoutWord_getD_22 (s : UniStatement.Shape) (code vars placed : ℕ) :
    (UniStatement.layoutWord s code vars placed).getD 22 0 = (code >>> 8).toUInt8 := by
  have e : UniStatement.layoutWord s code vars placed = (shapeBytes s ++ List.replicate 14 (0 : UInt8)) ++
      ([(code >>> 8).toUInt8, code.toUInt8, vars.toUInt8] ++
        (List.range 7).map fun k ↦ (placed >>> (8 * (6 - k))).toUInt8) := by
    simp [UniStatement.layoutWord, List.append_assoc]
  rw [e, show 22 = (shapeBytes s ++ List.replicate 14 (0 : UInt8)).length + 0 by simp [shapeBytes],
    getD_append_right]
  rfl

theorem layoutWord_getD_23 (s : UniStatement.Shape) (code vars placed : ℕ) :
    (UniStatement.layoutWord s code vars placed).getD 23 0 = code.toUInt8 := by
  have e : UniStatement.layoutWord s code vars placed = (shapeBytes s ++ List.replicate 14 (0 : UInt8)) ++
      ([(code >>> 8).toUInt8, code.toUInt8, vars.toUInt8] ++
        (List.range 7).map fun k ↦ (placed >>> (8 * (6 - k))).toUInt8) := by
    simp [UniStatement.layoutWord, List.append_assoc]
  rw [e, show 23 = (shapeBytes s ++ List.replicate 14 (0 : UInt8)).length + 1 by simp [shapeBytes],
    getD_append_right]
  rfl

/-- The code a layout word names (bytes `22`, `23`). -/
def codeOf (word : List UInt8) : ℕ := (word.getD 22 0).toNat * 256 + (word.getD 23 0).toNat

theorem codeOf_layoutWord (s : UniStatement.Shape) (code vars placed : ℕ) :
    codeOf (UniStatement.layoutWord s code vars placed) = (code >>> 8).toUInt8.toNat * 256 + code.toUInt8.toNat := by
  unfold codeOf
  rw [layoutWord_getD_22, layoutWord_getD_23]

/-- π1's layout words: `C1`'s, `C2`'s, the setup's, each its code's. -/
theorem layoutWords_getD (s : UniStatement.Shape) :
    (∃ v p, (UniStatement.layoutWords s).getD 0 [] = UniStatement.layoutWord s 0x5501 v p) ∧
      (∃ v p, (UniStatement.layoutWords s).getD 1 [] = UniStatement.layoutWord s 0x5502 v p) ∧
      (∃ v p, (UniStatement.layoutWords s).getD 2 [] = UniStatement.layoutWord s 0x5503 v p) :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

/-- **Words of 32 bytes, concatenated, are cut back into them.** -/
theorem chunks_flatten : ∀ (W : List (List UInt8)), (∀ w ∈ W, w.length = 32) →
    (List.range (W.flatten.length / 32)).map (fun j ↦ (W.flatten.drop (32 * j)).take 32) = W
  | [], _ => by simp
  | a :: W, h => by
    have ha : a.length = 32 := h a (List.mem_cons_self ..)
    have hW : ∀ w ∈ W, w.length = 32 := fun w hw ↦ h w (List.mem_cons_of_mem _ hw)
    have hl : (a :: W).flatten.length / 32 = W.flatten.length / 32 + 1 := by
      rw [List.flatten_cons, List.length_append, ha]
      omega
    rw [hl, List.range_succ_eq_map, List.map_cons, List.map_map, List.flatten_cons]
    congr 1
    · simp [List.take_left' ha]
    · conv_rhs => rw [← chunks_flatten W hW]
      refine List.map_congr_left fun j _ ↦ ?_
      simp only [Function.comp_apply]
      rw [show 32 * (j + 1) = a.length + 32 * j by rw [ha]; ring, ← List.drop_drop, List.drop_left]

theorem mapM_map_succ {β : Type} (gf : ℕ → Option β) : ∀ (l : List ℕ),
    (l.map Nat.succ).mapM gf = l.mapM fun j ↦ gf (j + 1)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.mapM_cons, mapM_map_succ gf l, Nat.succ_eq_add_one]

/-- `n` reads that each give the list's entry give the list. -/
theorem mapM_range_eq_some {β : Type} (d : β) : ∀ (l : List β) (gf : ℕ → Option β),
    (∀ j < l.length, gf j = some (l.getD j d)) → (List.range l.length).mapM gf = some l
  | [], _, _ => rfl
  | a :: l, gf, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.mapM_cons, mapM_map_succ,
      mapM_range_eq_some d l (fun j ↦ gf (j + 1)) fun j hj ↦ by
        rw [h (j + 1) (by simp; omega)]; rfl, h 0 (by simp)]
    rfl

theorem length_flatten_32 : ∀ (W : List (List UInt8)), (∀ w ∈ W, w.length = 32) → W.flatten.length = 32 * W.length
  | [], _ => rfl
  | a :: W, h => by
    rw [List.flatten_cons, List.length_append, h a (List.mem_cons_self ..),
      length_flatten_32 W fun w hw ↦ h w (List.mem_cons_of_mem _ hw), List.length_cons]
    ring

theorem getD_append_left' {α : Type} {l r : List α} {k : ℕ} (d : α) (h : k < l.length) :
    (l ++ r).getD k d = l.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type} (l r : List α) (k : ℕ) (d : α) : (l ++ r).getD (l.length + k) d = r.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left]

/-- **π1's call of a point claim, decoded** (`decodePi1Call` of `openingWords`): its root (the digest the root word reads
back, the setup's by its code `0x5503`), its layout word and its claim, when the point has the layout word's variables. -/
theorem decodePi1Call_point (root word : List UInt8) (pt : List E) (v : E) (hr : root.length = 32)
    (hw : word.length = 32) (hpt : pt.length = layoutWordVars word) :
    decodePi1Call (openingWords root word (.point pt v none)) =
      some ((if codeOf word = 0x5503 then digestOfBytes32 root else rootOfWord root), word, [⟨pt, v⟩]) := by
  set W : List (List UInt8) := [root, word, numberWord 1] ++ (pt.map elementWord ++ [elementWord v]) with hW
  have hcall : openingWords root word (.point pt v none) = W.flatten := by
    simp [openingWords, hW, List.flatten_append, List.flatMap, List.append_assoc]
  have hlen : ∀ w ∈ W, w.length = 32 := by
    intro w hw'
    simp only [hW, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hw'
    rcases hw' with (rfl | rfl | rfl) | ⟨x, -, rfl⟩ | rfl <;> simp [hr, hw]
  have hWl : W.length = 3 + (pt.length + 1) := by simp [hW]; omega
  have hflen : W.flatten.length = 32 * W.length := length_flatten_32 W hlen
  have hWj : ∀ j < pt.length, W.getD (3 + j) [] = elementWord (pt.getD j 0) := by
    intro j hj
    rw [hW, show 3 + j = [root, word, numberWord 1].length + j from rfl, getD_append_right',
      getD_append_left' _ (by simpa using hj), List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  have hWv : W.getD (3 + pt.length) [] = elementWord v := by
    rw [hW, show 3 + pt.length = [root, word, numberWord 1].length + ((pt.map elementWord).length + 0) by simp,
      getD_append_right', getD_append_right']
    rfl
  have hclaims : claimsOfWords W 1 (layoutWordVars word) = some [⟨pt, v⟩] := by
    unfold claimsOfWords
    rw [← hpt]
    simp only [List.range_one, List.mapM_cons, List.mapM_nil, zero_mul, add_zero]
    rw [mapM_range_eq_some 0 pt _ fun j hj ↦ by rw [hWj j hj, elementOfWord_elementWord], hWv,
      elementOfWord_elementWord]
    rfl
  unfold decodePi1Call
  rw [hcall, ite_eq_right (by rw [hflen]; omega), chunks_flatten W hlen]
  have h0 : W.head? = some root := rfl
  have h1 : W[1]? = some word := rfl
  have h2 : W[2]? = some (numberWord 1) := rfl
  simp only [h0, h1, h2, Option.bind_eq_bind, Option.bind_some, countOfWord_numberWord_one, hWl, ← hpt]
  rw [hpt, hclaims]
  simp [codeOf]

end RecCompose.Pi1Decode

/-- info: 'RecCompose.Pi1Decode.elementOfWord_elementWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1Decode.elementOfWord_elementWord

/-- info: 'RecCompose.Pi1Decode.rootOfWord_rootWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1Decode.rootOfWord_rootWord

/-- info: 'RecCompose.Pi1Decode.decodePi1Call_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1Decode.decodePi1Call_point
