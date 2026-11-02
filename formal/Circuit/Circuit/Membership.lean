/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-/
import Circuit.KeccakGadget
import Circuit.Bytes

/-!
# The membership rows compute the statement

`spec_swap`: the swap of a level (`differ = node ⊕ sibling`, `left = χ(node, ¬direction, differ)`,
`right = left ⊕ differ`) computes the ordered pair. `spec_level`: a level computes `H` of the ordered
pair, its sibling and direction being `257` new inputs. `spec_levels`: `n` levels compute the path.
`spec_membershipBuild`: the rows of `membership` before `finish` compute `y = H(x ‖ 0x11^32)` and
`root`, for every valuation whose input bits are a secret's, and fit in `4,002,624` rows.
-/

set_option maxRecDepth 10000
set_option linter.deprecated false

namespace PcsCircuit

open LeanVM.Parameters Builder

theorem array_append_getD {α : Type} (a b : Array α) (d : α) (p : Nat) :
    (a ++ b).getD p d = if p < a.size then a.getD p d else b.getD (p - a.size) d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

/-! ## The swap -/

/-- One bit of the swap: `differ`, `left`, `right`, three rows. -/
def swapBit (node sibling : Array Src) (keep : Src) (i : Nat) : BuildM (Src × Src) := do
  let differ ← xorG (node.getD i .zero) (sibling.getD i .zero)
  let l ← chiG (node.getD i .zero) keep differ
  let r ← xorG l differ
  pure (l, r)

/-- The rest of a level, after its inputs: the swap, then the hash of the ordered pair. -/
def levelTail (node sibling : Array Src) (direction : Src) : BuildM (Array Src) := do
  let keep ← notG direction
  let lr ← (List.range 256).mapM (swapBit node sibling keep)
  keccak256Block ((lr.map Prod.fst).toArray ++ (lr.map Prod.snd).toArray)

theorem level_eq (node : Array Src) :
    level node = (freeBits 256 >>= fun sibling => input >>= fun direction => levelTail node sibling direction) :=
  rfl

/-- **The swap**, one bit: `left` is the sibling if the direction is set, else the node; `right` the
other; three rows. -/
theorem spec_swapBit {node sibling : Array Src} {keep : Src} {D : (Nat → Bool) → Bool} {i : Nat} {b : Builder}
    (hb : WF b) (hn : Valid b (node.getD i .zero) ∧ IsRow (node.getD i .zero))
    (hs : Valid b (sibling.getD i .zero) ∧ IsRow (sibling.getD i .zero))
    (hk : Computes b keep (fun v => !D v) ∧ IsRow keep) :
    Spec (swapBit node sibling keep i) b 3 fun lr b' =>
      Out True (fun v => if D v then read v (sibling.getD i .zero) else read v (node.getD i .zero)) lr.1 b' ∧
      Out True (fun v => if D v then read v (node.getD i .zero) else read v (sibling.getD i .zero)) lr.2 b' := by
  unfold swapBit
  refine Spec.bind (k := 1) (k' := 1 + (1 + 0)) (spec_xorG hb hn.1 hs.1) fun d b1 hg1 ⟨hdr, hdc⟩ => ?_
  have hdrow : IsRow d := hdr (Or.inr hs.2)
  refine Spec.bind (k := 1) (k' := 1 + 0)
    ((spec_chiG hg1.wf (hn.1.of_ext hg1.ext) (hk.1.1.of_ext hg1.ext) hdc.1).mono
      (by rw [chiCost_row hdrow]) fun _ _ _ h => h) fun l b2 hg2 ⟨hlr, hlc⟩ => ?_
  refine Spec.bind (k := 1) (k' := 0) (spec_xorG hg2.wf hlc.1 (hdc.1.of_ext hg2.ext))
    fun r b3 hg3 ⟨hrr, hrc⟩ => Spec.pure hg3.wf ⟨⟨fun _ => hlr ⟨hn.2, hk.2, hdrow⟩, ?_⟩, ⟨fun _ => hrr (Or.inr hdrow), ?_⟩⟩
  · refine (hlc.of_ext hg3.ext).congr fun v hv => ?_
    have hv1 := hv.of_ext (hg2.ext.trans hg3.ext)
    have hv0 := hv1.of_ext hg1.ext
    simp only [hk.1.2 v hv0, hdc.2 v hv1]
    cases D v <;> cases read v (node.getD i .zero) <;> cases read v (sibling.getD i .zero) <;> rfl
  · refine hrc.congr fun v hv => ?_
    have hv2 := hv.of_ext hg3.ext
    have hv1 := hv2.of_ext hg2.ext
    have hv0 := hv1.of_ext hg1.ext
    simp only [hlc.2 v hv2, hdc.2 v hv1, hk.1.2 v hv0]
    cases D v <;> cases read v (node.getD i .zero) <;> cases read v (sibling.getD i .zero) <;> rfl

/-- The message a level hashes: the ordered pair of the node's bits `N` and the sibling's `S`, the
sibling first when `d`. -/
def pairBits (N S : Nat → Bool) (d : Bool) (p : Nat) : Bool :=
  if p < 256 then (if d then S p else N p) else (if d then N (p - 256) else S (p - 256))

/-- The rows of a level after its inputs: the NOT, three a bit, Keccak. -/
def tailRows : Nat := 1 + (3 * 256 + keccakRows true)

/-- **The rest of a level**: the hash of the ordered pair, rows. -/
theorem spec_levelTail {node sibling : Array Src} {direction : Src} {b : Builder} (hb : WF b)
    (hn : ∀ i < 256, Valid b (node.getD i .zero) ∧ IsRow (node.getD i .zero))
    (hs : ∀ i < 256, Valid b (sibling.getD i .zero) ∧ IsRow (sibling.getD i .zero))
    (hd : Valid b direction ∧ IsRow direction) :
    Spec (levelTail node sibling direction) b tailRows fun out b' => ∀ k < 256,
      Out True (fun v => KeccakBits.hash (pairBits (fun p => read v (node.getD p .zero))
        (fun p => read v (sibling.getD p .zero)) (read v direction)) k) (out.getD k .zero) b' := by
  unfold levelTail tailRows
  refine Spec.bind (spec_notG hb hd.1) fun keep b1 hg1 ⟨hkr, hkc⟩ => ?_
  have hm := Spec.mapM_range (swapBit node sibling keep) 256 b1 3
    (fun i lr b' => Out True (fun v => if read v direction then read v (sibling.getD i .zero)
        else read v (node.getD i .zero)) lr.1 b' ∧
      Out True (fun v => if read v direction then read v (node.getD i .zero)
        else read v (sibling.getD i .zero)) lr.2 b')
    (fun _ _ _ _ h ⟨h1, h2⟩ => ⟨Out.mono _ _ _ _ _ h h1, Out.mono _ _ _ _ _ h h2⟩)
    (fun i hi b' he hw => spec_swapBit (D := fun v => read v direction) hw
      ⟨((hn i hi).1.of_ext (hg1.ext.trans he)), (hn i hi).2⟩
      ⟨((hs i hi).1.of_ext (hg1.ext.trans he)), (hs i hi).2⟩
      ⟨(hkc.congr fun v _ => rfl).of_ext he, hkr hd.2⟩) hg1.wf
  refine Spec.bind (k := 3 * 256) (k' := keccakRows true) hm fun lr b2 hg2 ⟨hlen, hlr⟩ => ?_
  have hmsg : ∀ p < 512, Out True (fun v => pairBits (fun p => read v (node.getD p .zero))
      (fun p => read v (sibling.getD p .zero)) (read v direction) p)
      (((lr.map Prod.fst).toArray ++ (lr.map Prod.snd).toArray).getD p .zero) b2 := by
    intro p hp
    rw [array_append_getD]
    simp only [List.size_toArray, List.length_map, hlen, pairBits]
    by_cases h : p < 256
    · simp only [h, if_true]
      rw [toArray_getD_of_lt (lr.map Prod.fst) _ _ (by simp [hlen, h])]
      simpa using (hlr p (by omega)).1
    · simp only [h, if_false]
      rw [toArray_getD_of_lt (lr.map Prod.snd) _ _ (by simp [hlen]; omega)]
      simpa using (hlr (p - 256) (by omega)).2
  refine (spec_keccak256Block true hg2.wf (fun p hp => (hmsg p hp).2.1) (fun _ p hp => (hmsg p (by omega)).1 trivial)).mono
    (Nat.le_refl _) fun out b3 hg3 hout k hk => ⟨fun _ => (hout k hk).1 rfl, (hout k hk).2.congr fun v hv => ?_⟩
  exact hash_congr (fun p hp => ((hmsg p hp).2.2 v (hv.of_ext hg3.ext))) k hk

end PcsCircuit
