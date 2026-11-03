-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The contract's calls are `formal/RecStatement`'s
-- (`Calls.lean`: `pcsCalls`, `claimWords`; `Security.lean`: `decodeWith`, `registryOf`, `pcsOpenAt`); the words' read-backs
-- are `RecCompose.Pi1Decode`'s (`elementOfWord_elementWord`, `countOfWord_numberWord_one`, `rootOfWord_rootWord`,
-- `mapM_range_eq_some`).
import RecCompose.Pi1Decode
import RecCompose.OpeningsAgree
import RecCompose.Pi2Whir
import UniComplete.Core

/-!
# π2's three `PCS_OPEN` calls decoded

The contract's calls for `W`, the setup and `Q` (`pcsCalls`' last three: a root word, π2's layout word, the count, then
each claim's coordinates and value as element words) decode under the registry (`decodeWith`) to the root the word
names, π2's opener of the layout and the claims themselves (`decodeWith_claims`): the layout words are the registry's
first three entries, distinct by their codes (`registry_lookup_w`, `_q`, `_s`), every element word reads back
(`elementOfWord_elementWord`), the counts `1` and `2` too. A root the stream carries as its halves' word names the digest
(`rootOfWord_rootWord_digestScalars`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2C

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Pi1Decode (elementOfWord_elementWord getD_append_left' getD_append_right' mapM_range_eq_some)

/-! ## Claims' words -/

theorem length_claimWords (c : List E × E) : (claimWords c).length = c.1.length + 1 := by
  simp [claimWords]

theorem claimWords_getD_lt (x : List E × E) {j : ℕ} (hj : j < x.1.length) :
    (claimWords x).getD j [] = UniStatement.elementWord (x.1.getD j 0) := by
  have hj' : j < (x.1.map UniStatement.elementWord).length := by simpa using hj
  rw [claimWords, List.map_append, List.getD_eq_getElem?_getD, List.getElem?_append_left hj', List.getElem?_map,
    List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  rfl

theorem claimWords_getD_last (x : List E × E) : (claimWords x).getD x.1.length [] = UniStatement.elementWord x.2 := by
  simp [claimWords, List.getD_eq_getElem?_getD]

/-- Entry `c (v + 1) + j` of claims' words of `v + 1` words each is word `j` of claim `c`. -/
theorem getD_flatMap_claimWords (v : ℕ) : ∀ (cs : List (List E × E)), (∀ c ∈ cs, c.1.length = v) →
    ∀ c < cs.length, ∀ j < v + 1,
      (cs.flatMap claimWords).getD (c * (v + 1) + j) [] = (claimWords (cs.getD c ([], 0))).getD j []
  | [], _, c, hc, _, _ => absurd hc (by simp)
  | a :: cs, h, c, hc, j, hj => by
    have ha : (claimWords a).length = v + 1 := by rw [length_claimWords, h a List.mem_cons_self]
    rw [List.flatMap_cons]
    cases c with
    | zero =>
      rw [zero_mul, zero_add, getD_append_left' _ (by rw [ha]; exact hj)]
      rfl
    | succ c =>
      rw [show (c + 1) * (v + 1) + j = (claimWords a).length + (c * (v + 1) + j) by rw [ha]; ring,
        getD_append_right', getD_flatMap_claimWords v cs (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) c
          (by simpa using hc) j hj]
      rfl

theorem length_flatMap_claimWords (v : ℕ) : ∀ (cs : List (List E × E)), (∀ c ∈ cs, c.1.length = v) →
    (cs.flatMap claimWords).length = cs.length * (v + 1)
  | [], _ => by simp
  | a :: cs, h => by
    rw [List.flatMap_cons, List.length_append, length_claimWords, h a List.mem_cons_self,
      length_flatMap_claimWords v cs fun x hx ↦ h x (List.mem_cons_of_mem _ hx), List.length_cons]
    ring

/-- **The claims' words read back**: `claimsOfWords` of a call's words (three header words, then the claims' element
words) is the claims. -/
theorem claimsOfWords_eq (hd : List (List UInt8)) (hhd : hd.length = 3) (v : ℕ) (cs : List (List E × E))
    (hlen : ∀ c ∈ cs, c.1.length = v) :
    claimsOfWords (hd ++ cs.flatMap claimWords) cs.length v =
      some (cs.map fun c ↦ (⟨c.1, c.2⟩ : PcsQuotient.Claim)) := by
  unfold claimsOfWords
  rw [show cs.length = (cs.map fun c ↦ (⟨c.1, c.2⟩ : PcsQuotient.Claim)).length by simp]
  refine mapM_range_eq_some ⟨[], 0⟩ _ _ fun c hc ↦ ?_
  have hc' : c < cs.length := by simpa using hc
  have hcl : (cs.getD c ([], 0)).1.length = v := hlen _ (by
    rw [List.getD_eq_getElem _ _ hc']; exact List.getElem_mem hc')
  have hw : ∀ j < v + 1, (hd ++ cs.flatMap claimWords).getD (3 + c * (v + 1) + j) [] =
      (claimWords (cs.getD c ([], 0))).getD j [] := by
    intro j hj
    rw [show 3 + c * (v + 1) + j = hd.length + (c * (v + 1) + j) by rw [hhd]; ring, getD_append_right',
      getD_flatMap_claimWords v cs hlen c hc' j hj]
  have hpt : (List.range v).mapM (fun j ↦ elementOfWord ((hd ++ cs.flatMap claimWords).getD (3 + c * (v + 1) + j) []))
      = some (cs.getD c ([], 0)).1 := by
    have h := mapM_range_eq_some 0 (cs.getD c ([], 0)).1
      (fun j ↦ elementOfWord ((hd ++ cs.flatMap claimWords).getD (3 + c * (v + 1) + j) [])) fun j hj ↦ by
        have hjv : j < v := by rw [hcl] at hj; exact hj
        rw [hw j (by omega), claimWords_getD_lt _ hj, elementOfWord_elementWord]
    rw [hcl] at h
    exact h
  have hval : elementOfWord ((hd ++ cs.flatMap claimWords).getD (3 + c * (v + 1) + v) []) =
      some (cs.getD c ([], 0)).2 := by
    have e := claimWords_getD_last (cs.getD c ([], 0))
    rw [hcl] at e
    rw [hw v (by omega), e, elementOfWord_elementWord]
  simp only [hpt, hval, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc']

/-- **A call of claims, decoded**: its root word as the digest it names, the registered opener, the claims. -/
theorem decodeWith_claims (reg : List (List UInt8 × Opener)) (root lw : List UInt8) (op : Opener)
    (hl : reg.lookup lw = some op) (hr : root.length = 32) (cs : List (List E × E)) (hk : 1 ≤ cs.length)
    (hc : countOfWord (UniStatement.numberWord cs.length) = some cs.length)
    (hlen : ∀ c ∈ cs, c.1.length = op.vars) :
    decodeWith reg ([root, lw, UniStatement.numberWord cs.length] ++ cs.flatMap claimWords) =
      some (rootOfWord root, op, cs.map fun c ↦ (⟨c.1, c.2⟩ : PcsQuotient.Claim)) := by
  have hcl := claimsOfWords_eq [root, lw, UniStatement.numberWord cs.length] rfl op.vars cs hlen
  have hwl : ([root, lw, UniStatement.numberWord cs.length] ++ cs.flatMap claimWords).length =
      3 + cs.length * (op.vars + 1) := by
    rw [List.length_append, length_flatMap_claimWords op.vars cs hlen]; rfl
  unfold decodeWith
  simp only [List.cons_append, List.head?_cons, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.bind_eq_bind, Option.bind_some, hl, hc]
  rw [ite_eq_right (by simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not]; exact ⟨hk, by
    simpa using hwl, hr⟩)]
  simp only [List.cons_append, List.nil_append] at hcl
  simp [hcl]

theorem countOfWord_numberWord_two : countOfWord (UniStatement.numberWord 2) = some 2 := by decide

/-! ## The registry -/

theorem layoutWord_getD23 (code m : ℕ) (L : PcsQuotient.Layout) :
    (RecStatement.layoutWord code m L).getD 23 0 = code.toUInt8 := by
  have h : "pi2".toUTF8.toList = [112, 105, 50] := by decide +kernel
  unfold RecStatement.layoutWord
  rw [h]
  rfl

theorem layoutWord_ne {c c' m m' : ℕ} {L L' : PcsQuotient.Layout} (h : c.toUInt8 ≠ c'.toUInt8) :
    RecStatement.layoutWord c m L ≠ RecStatement.layoutWord c' m' L' := fun e ↦
  h (by rw [← layoutWord_getD23 c m L, ← layoutWord_getD23 c' m' L', e])

theorem registry_lookup_w (s : UniStatement.Shape) (m : ℕ) :
    (registryOf s m).lookup (layoutWords m).1 = some (.pi2 (layoutsOf m).1) := by
  simp [registryOf, layoutWords]

theorem registry_lookup_s (s : UniStatement.Shape) (m : ℕ) :
    (registryOf s m).lookup (layoutWords m).2.2 = some (.pi2 (layoutsOf m).2.2) := by
  have h1 : RecStatement.layoutWord setupCode m (layoutsOf m).2.2 ≠
      RecStatement.layoutWord witnessCode m (layoutsOf m).1 := layoutWord_ne (by decide)
  have h2 : RecStatement.layoutWord setupCode m (layoutsOf m).2.2 ≠
      RecStatement.layoutWord quotientCode m (layoutsOf m).2.1 := layoutWord_ne (by decide)
  simp only [registryOf, layoutWords, List.cons_append]
  rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2, lookup_cons_self]

theorem registry_lookup_q (s : UniStatement.Shape) (m : ℕ) :
    (registryOf s m).lookup (layoutWords m).2.1 = some (.pi2 (layoutsOf m).2.1) := by
  have h1 : RecStatement.layoutWord quotientCode m (layoutsOf m).2.1 ≠
      RecStatement.layoutWord witnessCode m (layoutsOf m).1 := layoutWord_ne (by decide)
  simp only [registryOf, layoutWords, List.cons_append]
  rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_self]

/-! ## Roots -/

/-- **A root the stream carries as its halves' word names the digest.** -/
theorem rootOfWord_rootWord_digestScalars (d : Digest) : rootOfWord (UniStatement.rootWord (digestScalars d)) = d := by
  have h := digestOfScalars_digestScalars d
  unfold digestOfScalars at h
  split at h
  · rename_i hc
    rw [Pi1Decode.rootOfWord_rootWord _ hc.1 hc.2, UniComplete.rootOf_digestScalars]
  · exact absurd h (by simp)

theorem length_rootWord (h : E × E) : (UniStatement.rootWord h).length = 32 := by
  simp [UniStatement.rootWord, UniStatement.be64]

/-- The stream's 32 bytes at the end of a prefix. -/
theorem streamWord_of (S : Array UInt8) (P B Q : List UInt8) (hS : S.toList = P ++ (B ++ Q)) (hB : B.length = 32) :
    streamWord S P.length = B := by
  unfold streamWord
  rw [Array.toList_extract, hS, List.extract_eq_take_drop, List.drop_left, Nat.add_sub_cancel_left]
  exact List.take_left' hB

end RecCompose.Pi2C

/-- info: 'RecCompose.Pi2C.decodeWith_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2C.decodeWith_claims

/-- info: 'RecCompose.Pi2C.registry_lookup_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2C.registry_lookup_q

/-- info: 'RecCompose.Pi2C.rootOfWord_rootWord_digestScalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2C.rootOfWord_rootWord_digestScalars
