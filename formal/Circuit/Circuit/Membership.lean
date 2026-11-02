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

-- Facts about the sources a gadget returns must not be unfolded: reducing `IsRow a` or `Valid b a` by
-- its match would evaluate the gadget's run.
attribute [local irreducible] IsRow Below Valid

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

/-! ## A level -/

/-- The rows of a level: `257` inputs, then the rest. -/
def levelRows : Nat := 257 + tailRows

/-- **A level**: `257` new input rows from the current size `s` (the sibling's bits, then the
direction), and the hash of the ordered pair of the node and the sibling. -/
theorem spec_level {node : Array Src} {b : Builder} (hb : WF b)
    (hn : ∀ i < 256, Valid b (node.getD i .zero) ∧ IsRow (node.getD i .zero)) :
    RowsExt b (runB (level node) b).2 ∧ WF (runB (level node) b).2 ∧
    (runB (level node) b).2.rows.size ≤ b.rows.size + levelRows ∧
    (runB (level node) b).2.inputs = b.inputs ++ ((List.range 257).map (b.rows.size + ·)).toArray ∧
    ∀ k < 256, Valid (runB (level node) b).2 ((runB (level node) b).1.getD k .zero) ∧
      IsRow ((runB (level node) b).1.getD k .zero) ∧
      ∀ v, Sat v (runB (level node) b).2 → read v ((runB (level node) b).1.getD k .zero) =
        KeccakBits.hash (pairBits (fun p => read v (node.getD p .zero)) (fun p => v (b.rows.size + p))
          (v (b.rows.size + 256))) k := by
  have hfb : runB (freeBits 256) b = ((runB ((List.range 256).mapM fun _ => input) b).1.toArray,
      (runB ((List.range 256).mapM fun _ => input) b).2) := by
    unfold freeBits; rw [runB_bind, runB_pure]
  rw [level_eq, runB_bind, hfb, runB_bind, runB_input]
  obtain ⟨h1ext, h1size, h1wf, h1inp, h1res, h1sat⟩ := spec_freeBits_list (List.range 256) b hb
  generalize runB ((List.range 256).mapM fun _ => input) b = r1 at h1ext h1size h1wf h1inp h1res h1sat ⊢
  obtain ⟨l, b1⟩ := r1
  simp only at h1ext h1size h1wf h1inp h1res h1sat ⊢
  simp only [List.length_range] at h1size h1inp h1res
  subst h1res
  have hs := hb.size
  have hb2 := addInput_wf h1wf
  have h2ext : RowsExt b b1.addInput := h1ext.trans (addInput_rowsExt b1)
  have h2size := addInput_size b1
  have hsib : ∀ i < 256, Valid b1.addInput
      ((((List.range 256).map fun k => Src.row (b.rows.size + k)).toArray).getD i .zero) ∧
      IsRow ((((List.range 256).map fun k => Src.row (b.rows.size + k)).toArray).getD i .zero) := by
    intro i hi
    rw [map_range_getD _ _ _ _ hi]
    exact ⟨valid_row (by unfold publicRows at hs ⊢; omega) (by omega), isRow_row _⟩
  have hdir : Valid b1.addInput (.row b1.rows.size) ∧ IsRow (.row b1.rows.size) :=
    ⟨valid_row (by unfold publicRows at hs ⊢; omega) (by omega), isRow_row _⟩
  obtain ⟨hg, hout⟩ := spec_levelTail hb2 (fun i hi => ⟨((hn i hi).1.of_rowsExt h2ext), (hn i hi).2⟩) hsib hdir
  refine ⟨?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · exact h2ext.trans hg.ext.toRowsExt
  · exact hg.wf
  · have := hg.le; unfold levelRows; omega
  · rw [hg.ext.inputs_eq]
    simp only [Builder.addInput, h1inp, h1size]
    rw [show List.range 257 = List.range 256 ++ [256] from List.range_succ, List.map_append]
    apply Array.ext'
    simp only [Array.toList_push, Array.toList_append, List.map_cons, List.map_nil, List.append_assoc]
  · obtain ⟨hk1, hk2, hk3⟩ := hout k hk
    refine ⟨hk2, hk1 trivial, fun v hv => ?_⟩
    rw [hk3 v hv]
    refine hash_congr (fun p hp => ?_) k hk
    simp only [pairBits]
    have hread : ∀ q < 256, read v ((((List.range 256).map fun k => Src.row (b.rows.size + k)).toArray).getD q
        .zero) = v (b.rows.size + q) := fun q hq => by rw [map_range_getD _ _ _ _ hq]; rfl
    have hd : read v (Src.row b1.rows.size) = v (b.rows.size + 256) := by simp [h1size]
    rw [hd]
    split
    · split
      · exact hread p (by omega)
      · rfl
    · split
      · rfl
      · exact hread (p - 256) (by omega)

/-! ## The path -/

/-- `n` levels from `node`. -/
def levelsRun (n : Nat) (node : Array Src) (b : Builder) : Array Src × Builder :=
  runB ((List.range n).foldlM (fun node _ => level node) node) b

theorem levelsRun_zero (node : Array Src) (b : Builder) : levelsRun 0 node b = (node, b) := rfl

theorem levelsRun_succ (n : Nat) (node : Array Src) (b : Builder) :
    levelsRun (n + 1) node b = runB (level (levelsRun n node b).1) (levelsRun n node b).2 := by
  unfold levelsRun
  rewrite [List.range_succ, List.foldlM_append, runB_bind, List.foldlM_cons, runB_bind, List.foldlM_nil,
    runB_pure]
  exact Prod.mk.eta

/-- The input bits of levels `0 … n - 1`, from input index `I0`, are the secret's: level `i`'s
sibling bit `j`, then its direction. -/
def LevelInputs (s : Secret) (v : Nat → Bool) (ins : Array Nat) (I0 n : Nat) : Prop :=
  ∀ i < n, (∀ j < 256, v (ins.getD (I0 + 257 * i + j) 0) = bitOf (s.siblings.getD i []) j) ∧
    v (ins.getD (I0 + 257 * i + 256) 0) = s.directions.testBit i

theorem up_length (s : Secret) (node : List UInt8) (i : Nat) : (s.up node i).length = 32 := by
  unfold Secret.up; split <;> exact H_length _

theorem path_length (s : Secret) (h0 : List UInt8) (h0l : h0.length = 32) :
    ∀ n, ((List.range n).foldl s.up h0).length = 32
  | 0 => h0l
  | n + 1 => by rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]; exact up_length _ _ _

/-- **The path**: `n` levels compute `n` steps of `Secret.up` from the node's value, for every
valuation whose level inputs are the secret's; `257 n` inputs, at most `n` levels' rows. -/
theorem spec_levels (s : Secret) (hsib : ∀ i < depth, (s.siblings.getD i []).length = 32)
    (Q : (Nat → Bool) → Prop) :
    ∀ (n : Nat), n ≤ depth → ∀ (node : Array Src) (h0 : List UInt8) (b : Builder), WF b → h0.length = 32 →
      (∀ k < 256, Valid b (node.getD k .zero) ∧ IsRow (node.getD k .zero)) →
      (∀ v, Sat v b → Q v → ∀ k < 256, read v (node.getD k .zero) = bitOf h0 k) →
      RowsExt b (levelsRun n node b).2 ∧ WF (levelsRun n node b).2 ∧
      (levelsRun n node b).2.rows.size ≤ b.rows.size + n * levelRows ∧
      (∃ L : Array Nat, (levelsRun n node b).2.inputs = b.inputs ++ L ∧ L.size = 257 * n) ∧
      (∀ k < 256, Valid (levelsRun n node b).2 ((levelsRun n node b).1.getD k .zero) ∧
        IsRow ((levelsRun n node b).1.getD k .zero)) ∧
      ∀ v, Sat v (levelsRun n node b).2 → Q v → LevelInputs s v (levelsRun n node b).2.inputs b.inputs.size n →
        ∀ k < 256, read v ((levelsRun n node b).1.getD k .zero) = bitOf ((List.range n).foldl s.up h0) k := by
  intro n
  induction n with
  | zero =>
    intro _ node h0 b hb _ hnode hsem
    rw [levelsRun_zero]
    exact ⟨RowsExt.refl b, hb, by simp, ⟨#[], by simp, rfl⟩, hnode, fun v hv hq _ k hk => hsem v hv hq k hk⟩
  | succ n ih =>
    intro hn node h0 b hb hh0 hnode hsem
    obtain ⟨e1, w1, z1, ⟨L, hL, hLs⟩, val1, sem1⟩ := ih (by omega) node h0 b hb hh0 hnode hsem
    rw [levelsRun_succ]
    generalize levelsRun n node b = r at e1 w1 z1 hL val1 sem1 ⊢
    obtain ⟨nd, bn⟩ := r
    simp only at e1 w1 z1 hL val1 sem1 ⊢
    obtain ⟨e2, w2, z2, inp2, out2⟩ := spec_level w1 val1
    refine ⟨e1.trans e2, w2, ?_, ⟨L ++ ((List.range 257).map (bn.rows.size + ·)).toArray, ?_, ?_⟩,
      fun k hk => ⟨(out2 k hk).1, (out2 k hk).2.1⟩, fun v hv hq hin k hk => ?_⟩
    · have : (n + 1) * levelRows = n * levelRows + levelRows := Nat.succ_mul _ _
      omega
    · rw [inp2, hL, Array.append_assoc]
    · simp [hLs]; omega
    -- the inputs of the first `n` levels are where they were
    have hsize : bn.inputs.size = b.inputs.size + 257 * n := by rw [hL, Array.size_append, hLs]
    have hget : ∀ q < bn.inputs.size, (runB (level nd) bn).2.inputs.getD q 0 = bn.inputs.getD q 0 := by
      intro q hq; rw [inp2, array_append_getD, if_pos hq]
    have hnew : ∀ p < 257, (runB (level nd) bn).2.inputs.getD (b.inputs.size + 257 * n + p) 0 =
        bn.rows.size + p := by
      intro p hp
      rw [inp2, array_append_getD, if_neg (by omega), map_range_getD _ _ _ _ (by omega)]
      omega
    have hin' : LevelInputs s v bn.inputs b.inputs.size n := by
      intro i hi
      obtain ⟨h1, h2⟩ := hin i (by omega)
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [← hget _ (by omega)]; exact h1 j hj
      · rw [← hget _ (by omega)]; exact h2
    have hvn := hv.of_rowsExt e2
    have hnode' := sem1 v hvn hq hin'
    obtain ⟨hsibn, hdirn⟩ := hin n (by omega)
    rw [(out2 k hk).2.2 v hv, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hS : ∀ p < 256, v (bn.rows.size + p) = bitOf (s.siblings.getD n []) p := by
      intro p hp; rw [← hnew p (by omega)]; exact hsibn p hp
    have hD : v (bn.rows.size + 256) = s.directions.testBit n := by
      rw [← hnew 256 (by omega)]; exact hdirn
    have hpl := path_length s h0 hh0 n
    have hsl := hsib n (by unfold depth at hn ⊢; omega)
    unfold Secret.up
    rw [hD]
    split
    · rename_i hd
      refine pair_bits _ _ hsl hpl _ (fun p hp => ?_) k hk
      simp only [pairBits, hd, if_true]
      split
      · exact hS p (by omega)
      · exact hnode' _ (by omega)
    · rename_i hd
      refine pair_bits _ _ hpl hsl _ (fun p hp => ?_) k hk
      simp only [pairBits, hd, if_false]
      split
      · exact hnode' _ (by omega)
      · exact hS _ (by omega)

/-! ## The membership rows -/

-- From here on a run is opaque: unifying with a run must not evaluate it.
attribute [local irreducible] runB

/-- A secret of the statement's shape: `x` and the `32` siblings are `32` bytes each. -/
def Secret.WellFormed (s : Secret) : Prop :=
  s.x.length = 32 ∧ ∀ i < depth, (s.siblings.getD i []).length = 32

/-- The input bits of the circuit are the secret's: `x`'s `256` bits, then each level's sibling and
direction (`membership_inputs`). -/
def SecretInputs (s : Secret) (v : Nat → Bool) (ins : Array Nat) : Prop :=
  (∀ k < 256, v (ins.getD k 0) = bitOf s.x k) ∧ LevelInputs s v ins 256 depth

/-- The rows of `membership` before `finish`, at most: the public rows, `x`, two hashes, the path. -/
def buildRows : Nat := publicRows + 256 + 2 * keccakRows true + depth * levelRows

theorem buildRows_eq : buildRows = 4002624 := by decide

theorem wf_new : WF Builder.new :=
  ⟨by simp [Builder.new], by simp [Builder.new], fun r h => by simp [Builder.new] at h,
    fun r h => by simp [Builder.new] at h, fun r h1 h2 => by simp [Builder.new] at h2; omega⟩

theorem new_size : Builder.new.rows.size = publicRows := by simp [Builder.new]

theorem constantBlock_read (byte : UInt8) (v : Nat → Bool) (q : Nat) (hq : q < 256) :
    read v ((constantBlock byte).getD q .zero) = bitOf (List.replicate 32 byte) q := by
  simp only [constantBlock]
  rw [map_range_getD _ _ _ _ hq]
  simp only [bitOf, List.getD_eq_getElem?_getD, List.getElem?_replicate, show q / 8 < 32 by omega, if_true,
    Option.getD_some]
  split <;> simp_all

/-- The message `x ‖ pad^32` of the two hashes of `x`. -/
theorem msg_read {x : Array Src} (hx : x.size = 256) (byte : UInt8) (v : Nat → Bool) (X : List UInt8)
    (hX : ∀ k < 256, read v (x.getD k .zero) = bitOf X k) (p : Nat) (hp : p < 512) :
    read v ((x ++ constantBlock byte).getD p .zero) =
      if p < 256 then bitOf X p else bitOf (List.replicate 32 byte) (p - 256) := by
  rw [array_append_getD, hx]
  split
  · exact hX p (by assumption)
  · exact constantBlock_read byte v _ (by omega)

/-- The membership rows from any well-formed builder of `512` rows and no inputs. -/
theorem spec_membershipBuild_from (b0 : Builder) (hb0 : WF b0) (hs0 : b0.rows.size = publicRows)
    (hi0 : b0.inputs = #[]) :
    ∃ y root bf, runB membershipBuild b0 = ((y, root), bf) ∧
    WF bf ∧ bf.rows.size ≤ buildRows ∧ bf.inputs.size = 256 + 257 * depth ∧
    (∀ k < 256, Valid bf (y.getD k .zero) ∧ Valid bf (root.getD k .zero)) ∧
    ∀ s : Secret, s.WellFormed → ∀ v, Sat v bf → SecretInputs s v bf.inputs →
      ∀ k < 256, read v (y.getD k .zero) = bitOf s.y k ∧ read v (root.getD k .zero) = bitOf s.root k := by
  have hfb : runB (freeBits 256) b0 =
      ((runB ((List.range 256).mapM fun _ => input) b0).1.toArray,
        (runB ((List.range 256).mapM fun _ => input) b0).2) := by
    unfold freeBits; rewrite [runB_bind, runB_pure]; rfl
  obtain ⟨h1ext, h1size, h1wf, h1inp, h1res, h1sat⟩ := spec_freeBits_list (List.range 256) b0 hb0
  obtain ⟨⟨l, b1⟩, hr1⟩ : ∃ r, runB ((List.range 256).mapM fun _ => input) b0 = r := ⟨_, rfl⟩
  rw [hr1] at h1ext h1size h1wf h1inp h1res h1sat hfb
  simp only at h1ext h1size h1wf h1inp h1res h1sat hfb
  simp only [List.length_range, hs0] at h1size h1inp h1res
  subst h1res
  -- `x`: the input rows `512 … 767`
  have hxs : (((List.range 256).map fun k => Src.row (publicRows + k)).toArray).size = 256 := by simp
  have hxv : ∀ k < 256, (((List.range 256).map fun k => Src.row (publicRows + k)).toArray).getD k .zero =
      .row (publicRows + k) := fun k hk => map_range_getD _ _ _ _ hk
  obtain ⟨x, hxdef⟩ : ∃ x, ((List.range 256).map fun k => Src.row (publicRows + k)).toArray = x := ⟨_, rfl⟩
  rw [hxdef] at hxs hxv hfb
  have hmsg : ∀ (byte : UInt8) (b : Builder), RowsExt b1 b → ∀ p < 512,
      Valid b ((x ++ constantBlock byte).getD p .zero) ∧
      (p < 256 → IsRow ((x ++ constantBlock byte).getD p .zero)) := by
    intro byte b he p hp
    rw [array_append_getD, hxs]
    split
    · rw [hxv p (by assumption)]
      exact ⟨valid_row (by unfold publicRows; omega) (by have := he.size_le; omega), fun _ => isRow_row _⟩
    · refine ⟨?_, fun h => absurd h (by assumption)⟩
      simp only [constantBlock]
      rw [map_range_getD _ _ _ _ (by omega)]
      split
      · exact valid_one b
      · exact valid_zero b
  -- `y` and the leaf
  obtain ⟨hg2, hy⟩ := spec_keccak256Block (msg := x ++ constantBlock yPad) true h1wf
    (fun p hp => (hmsg yPad b1 (RowsExt.refl _) p hp).1) (fun _ p hp => (hmsg yPad b1 (RowsExt.refl _) p (by omega)).2 hp)
  obtain ⟨⟨y, b2⟩, hr2⟩ : ∃ r, runB (keccak256Block (x ++ constantBlock yPad)) b1 = r := ⟨_, rfl⟩
  rw [hr2] at hg2 hy
  simp only at hg2 hy
  obtain ⟨hg3, hleaf⟩ := spec_keccak256Block (msg := x ++ constantBlock leafPad) true hg2.wf
    (fun p hp => (hmsg leafPad b2 hg2.ext.toRowsExt p hp).1)
    (fun _ p hp => (hmsg leafPad b2 hg2.ext.toRowsExt p (by omega)).2 hp)
  obtain ⟨⟨leaf, b3⟩, hr3⟩ : ∃ r, runB (keccak256Block (x ++ constantBlock leafPad)) b2 = r := ⟨_, rfl⟩
  rw [hr3] at hg3 hleaf
  simp only at hg3 hleaf
  -- the path
  have heq : runB membershipBuild b0 =
      ((y, (levelsRun depth leaf b3).1), (levelsRun depth leaf b3).2) := by
    unfold membershipBuild
    rewrite [runB_bind_of hfb, runB_bind_of hr2, runB_bind_of hr3, runB_bind, runB_pure]
    rfl
  have hleafv : ∀ k < 256, Valid b3 (leaf.getD k .zero) ∧ IsRow (leaf.getD k .zero) :=
    fun k hk => ⟨(hleaf k hk).2.1, (hleaf k hk).1 trivial⟩
  have hdummy : ∀ i < depth, ((List.replicate 32 (List.replicate 32 (0 : UInt8))).getD i []).length = 32 :=
    fun i hi => by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, show i < 32 by unfold depth at hi; omega,
        if_true, Option.getD_some, List.length_replicate]
  obtain ⟨e4, w4, z4, ⟨L, hL, hLs⟩, val4, -⟩ := spec_levels ⟨[], List.replicate 32 (List.replicate 32 0), 0⟩
    hdummy (fun _ => False) depth (Nat.le_refl _) leaf (List.replicate 32 0) b3 hg3.wf (by simp) hleafv
    (fun _ _ h => h.elim)
  have hin3 : b3.inputs = ((List.range 256).map (publicRows + ·)).toArray := by
    rw [hg3.ext.inputs_eq, hg2.ext.inputs_eq, h1inp, hi0]; simp
  have hin3s : b3.inputs.size = 256 := by rw [hin3]; simp
  have e24 : RowsExt b2 (levelsRun depth leaf b3).2 := hg3.ext.toRowsExt.trans e4
  refine ⟨y, (levelsRun depth leaf b3).1, (levelsRun depth leaf b3).2, heq, w4, ?_, ?_,
    fun k hk => ⟨((hy k hk).2.1.of_rowsExt e24), (val4 k hk).1⟩, fun s hs v hv hin k hk => ?_⟩
  · have := hg2.le; have := hg3.le
    unfold buildRows; omega
  · rw [hL, Array.size_append, hLs, hin3s]
  -- the semantics
  have hx : ∀ k < 256, read v (x.getD k .zero) = bitOf s.x k := by
    intro k hk
    rw [hxv k hk, read_row, ← hin.1 k hk, hL, array_append_getD, if_pos (by omega), hin3,
      map_range_getD _ _ _ _ hk]
  have hpair : ∀ (byte : UInt8) (out : Array Src) (b : Builder), (∀ k < 256, Out True
      (fun v => KeccakBits.hash (fun p => read v ((x ++ constantBlock byte).getD p .zero)) k) (out.getD k .zero) b) →
      ∀ v, Sat v b → (∀ k < 256, read v (x.getD k .zero) = bitOf s.x k) →
      ∀ k < 256, read v (out.getD k .zero) = bitOf (H (s.x ++ List.replicate 32 byte)) k := by
    intro byte out b hout v hv hxv' k hk
    rw [(hout k hk).2.2 v hv]
    exact pair_bits _ _ hs.1 (by simp) _ (fun p hp => msg_read hxs byte v s.x hxv' p hp) k hk
  have hsat2 : Sat v b2 := hv.of_rowsExt e24
  have hlev := (spec_levels s hs.2 (fun v => ∀ k < 256, read v (x.getD k .zero) = bitOf s.x k) depth
    (Nat.le_refl _) leaf (H (s.x ++ List.replicate 32 leafPad)) b3 hg3.wf (H_length _) hleafv
    (fun v hv hq => hpair leafPad leaf b3 hleaf v hv hq)).2.2.2.2.2 v hv hx (by rw [hin3s]; exact hin.2) k hk
  exact ⟨hpair yPad y b2 hy v hsat2 hx k hk, hlev⟩
/-- **The membership rows** (`membership` before `finish`): well-formed, at most `4,002,624` rows,
`256 + 257 · 32` inputs, and, for every valuation satisfying them whose input bits are a well-formed
secret's, the wires of `y` and `root` hold the bits of `y = H(x ‖ 0x11^32)` and of the root. -/
theorem spec_membershipBuild :
    ∃ y root bf, runB membershipBuild Builder.new = ((y, root), bf) ∧
    WF bf ∧ bf.rows.size ≤ buildRows ∧ bf.inputs.size = 256 + 257 * depth ∧
    (∀ k < 256, Valid bf (y.getD k .zero) ∧ Valid bf (root.getD k .zero)) ∧
    ∀ s : Secret, s.WellFormed → ∀ v, Sat v bf → SecretInputs s v bf.inputs →
      ∀ k < 256, read v (y.getD k .zero) = bitOf s.y k ∧ read v (root.getD k .zero) = bitOf s.root k :=
  spec_membershipBuild_from Builder.new wf_new new_size rfl

end PcsCircuit
