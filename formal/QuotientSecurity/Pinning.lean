-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.CircuitLayout
import QuotientSecurity.SetupLemmas

/-!
# From the relation to the circuit's computation

`cells_determined` (`Circuit.lean`) is stated on the protocol's cells (`Params`: a cell is a
row's point and a role) and assumes the zero and the one pinned. This file connects it to an
instance whose wiring lays a circuit `C` (`Laid`, `CircuitLayout.lean`):

* **the bridge**: an instance's cells, named by 24 bits, are its parameters' cells
  (`Instance.cellEquiv`); its rows, numbered as `quotient::circuit` numbers them, are its
  parameters' rows (`Instance.rowEquivT`); its wiring is its parameters' (`sigma_pow_cellEquiv`);
  so a cell on the cycle of what it reads is `Wired` on the parameters (`wired_of_reads`) and
  `cells_determined` applies to the instance's cells (`Instance.cells_determined`);
* **the pinning**: with `coordinate_weight`'s weights, public word 5 being 0 pins the zero's
  cycle to 0 (`zero_pinned`: its 128 bits are on that cycle and their weights do not sum to
  zero), and then public word 4 being 1 pins the one's cycle to 1 (`one_pinned`: its bit 0, of
  weight 1, is the one's anchor, and its other bits are on the zero's cycle);
* `Instance.proves_of_relation`: cells that satisfy the relation for a statement whose words 4
  and 5 are 1 and 0 hold `C`'s computation, and its public words are the statement's.
-/

set_option linter.unusedSectionVars false

open Finset

namespace QuotientSecurity

section Copies

variable {F : Type*} [Field F] [CharP F 2]

/-- A cell on the cycle of an anchor holds what the anchor holds. -/
theorem reads_eq_anchor {σ : Equiv.Perm (Fin (22 + 2) → Bool)} {w : (Fin (22 + 2) → Bool) → F}
    (hcopy : ∀ z, w (σ z) = w z) {cell : Fin (22 + 2) → Bool} {s : Src (Fin (2 ^ 22))}
    (h : Reads σ cell s) : w cell = w (anchor s) := by
  obtain ⟨n, hn⟩ := h
  rw [← copy_iterate σ w hcopy n cell, hn]

/-- With the zero and the one pinned, a cell holds what it reads. -/
theorem reads_val {σ : Equiv.Perm (Fin (22 + 2) → Bool)} {w : (Fin (22 + 2) → Bool) → F}
    (hcopy : ∀ z, w (σ z) = w z) (hzero : w zeroCell = 0) (hone : w oneCell = 1)
    {cell : Fin (22 + 2) → Bool} {s : Src (Fin (2 ^ 22))} (h : Reads σ cell s) :
    w cell = s.val fun r => w (rowCell r 3) := by
  rw [reads_eq_anchor hcopy h]
  cases s with
  | zero => exact hzero
  | one => exact hone
  | row r => rfl

/-- **The zero is pinned by word 5.** If public word 5 is 0, the zero's cycle holds 0: the word's
128 bits are on it, so the word is that value times the sum of the bits' weights, which is not
zero when `x ≠ 1` and `Y ≠ 1` (`sum_bitWeight_ne_zero`). -/
theorem zero_pinned {σ : Equiv.Perm (Fin (22 + 2) → Bool)} {C : ChiCircuit (Fin (2 ^ 22))}
    (hC : Laid σ C) {x Y : F} (hx : x ≠ 1) (hY : Y ≠ 1) (w : (Fin (22 + 2) → Bool) → F)
    (hcopy : ∀ z, w (σ z) = w z) (h5 : ∑ z, regionWeight (coordWeight x Y) 5 z * w z = 0) :
    w zeroCell = 0 := by
  classical
  rw [sum_regionWeight _ (coordWeight_one x Y)] at h5
  have hj : ∀ j, w (pubCell 5 j) = w zeroCell := fun j => by
    have := reads_eq_anchor hcopy (hC.reads_pub 5 j)
    rw [hC.word5 j] at this
    exact this
  simp only [regionWeight_coordWeight, hj] at h5
  have := word_pins (fun j : Fin 128 => bitWeight x Y j) (w zeroCell) 0
    (sum_bitWeight_ne_zero hx hY) h5
  rwa [zero_div] at this

/-- **The one is pinned by word 4**, once the zero is. If public word 4 is 1: its bit 0 is the
one's anchor, of weight `bit_weight(0) = 1`, and its other bits are on the zero's cycle, so the
word is the one's value. -/
theorem one_pinned {σ : Equiv.Perm (Fin (22 + 2) → Bool)} {C : ChiCircuit (Fin (2 ^ 22))}
    (hC : Laid σ C) (x Y : F) (w : (Fin (22 + 2) → Bool) → F) (hcopy : ∀ z, w (σ z) = w z)
    (hzero : w zeroCell = 0) (h4 : ∑ z, regionWeight (coordWeight x Y) 4 z * w z = 1) :
    w oneCell = 1 := by
  classical
  rw [sum_regionWeight _ (coordWeight_one x Y), sum_eq_single (0 : Fin 128)] at h4
  · rw [regionWeight_coordWeight] at h4
    have h0 : bitWeight x Y ((0 : Fin 128) : ℕ) = 1 := bitWeight_zero x Y
    rw [h0, one_mul] at h4
    exact h4
  · intro j _ hj
    have := reads_eq_anchor hcopy (hC.reads_pub 4 j)
    rw [hC.word4 j hj] at this
    rw [this]
    show _ * w zeroCell = 0
    rw [hzero, mul_zero]
  · intro h
    exact absurd (mem_univ _) h

end Copies

namespace Instance

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] (I : Instance F)

/-! ## The bridge to the parameters' cells -/

/-- The rows of the instance's parameters, by their numbers. -/
noncomputable def rowEquivT : Fin (2 ^ 22) ≃ I.params.T :=
  rowEquiv.trans (cantorRows (n := 22) I.basis le24)

theorem cellEquiv_rowCell (r : Fin (2 ^ 22)) (role : Fin 4) :
    I.cellEquiv (rowCell r role) = (I.rowEquivT r, role) := by
  show (Equiv.prodCongr _ _) (cellBits.symm (cellBits (rowBits r, role))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem sigma_cellEquiv (x : Fin (22 + 2) → Bool) :
    I.params.σ (I.cellEquiv x) = I.cellEquiv (I.wiring x) := by
  show (I.cellEquiv.permCongr I.wiring) (I.cellEquiv x) = _
  simp [Equiv.permCongr_apply]

theorem sigma_pow_cellEquiv (n : ℕ) (x : Fin (22 + 2) → Bool) :
    (I.params.σ ^ n) (I.cellEquiv x) = I.cellEquiv ((I.wiring ^ n) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, sigma_cellEquiv, ih]

/-- **A cell on the cycle of what it reads is `Wired` on the parameters.** -/
theorem wired_of_reads {cell : Fin (22 + 2) → Bool} {s : Src (Fin (2 ^ 22))}
    (h : Reads I.wiring cell s) :
    Wired I.params (I.cellEquiv zeroCell) (I.cellEquiv oneCell) (I.cellEquiv cell)
      (s.map I.rowEquivT) := by
  obtain ⟨n, hn⟩ := h
  cases s with
  | zero => exact ⟨n, by rw [sigma_pow_cellEquiv, hn]; rfl⟩
  | one => exact ⟨n, by rw [sigma_pow_cellEquiv, hn]; rfl⟩
  | row r => exact ⟨n, by rw [sigma_pow_cellEquiv, hn]; exact I.cellEquiv_rowCell r 3⟩

/-- **`cells_determined` on an instance's cells.** Two assignments of the cells that satisfy the
gates and the copies of an instance whose wiring lays `C`, with the zero and the one pinned, and
that agree on `C`'s input rows, have the same output at every row, a bit. Proved by carrying the
cells, the rows and the wiring to the instance's parameters and applying `cells_determined`
there. -/
theorem cells_determined (C : ChiCircuit (Fin (2 ^ 22)))
    (hreads : ∀ r, Reads I.wiring (rowCell r 0) (C.x r) ∧ Reads I.wiring (rowCell r 1) (C.y r) ∧
      Reads I.wiring (rowCell r 2) (C.c r))
    (w w' : (Fin (22 + 2) → Bool) → F)
    (hgate : ∀ y : Fin 22 → Bool, gate (w (cellBits (y, 0))) (w (cellBits (y, 1)))
      (w (cellBits (y, 2))) (w (cellBits (y, 3))) = 0)
    (hgate' : ∀ y : Fin 22 → Bool, gate (w' (cellBits (y, 0))) (w' (cellBits (y, 1)))
      (w' (cellBits (y, 2))) (w' (cellBits (y, 3))) = 0)
    (hcopy : ∀ z, w (I.wiring z) = w z) (hcopy' : ∀ z, w' (I.wiring z) = w' z)
    (hzero : w zeroCell = 0) (hone : w oneCell = 1)
    (hzero' : w' zeroCell = 0) (hone' : w' oneCell = 1)
    (hin : ∀ r, C.isInput r → w (rowCell r 3) = w' (rowCell r 3)) (r : Fin (2 ^ 22)) :
    w (rowCell r 3) = w' (rowCell r 3) ∧ IsBit (w (rowCell r 3)) := by
  have hpull : ∀ (W : (Fin (22 + 2) → Bool) → F) (r : Fin (2 ^ 22)) (k : Fin 4),
      W (I.cellEquiv.symm (I.rowEquivT r, k)) = W (rowCell r k) := fun W r k => by
    rw [← I.cellEquiv_rowCell, Equiv.symm_apply_apply]
  have hwire : ∀ t : I.params.T,
      Wired I.params (I.cellEquiv zeroCell) (I.cellEquiv oneCell) (t, 0)
          ((C.map I.rowEquivT).x t) ∧
        Wired I.params (I.cellEquiv zeroCell) (I.cellEquiv oneCell) (t, 1)
          ((C.map I.rowEquivT).y t) ∧
        Wired I.params (I.cellEquiv zeroCell) (I.cellEquiv oneCell) (t, 2)
          ((C.map I.rowEquivT).c t) := by
    intro t
    obtain ⟨r, rfl⟩ := I.rowEquivT.surjective t
    obtain ⟨hx, hy, hc⟩ := hreads r
    rw [ChiCircuit.map_x, ChiCircuit.map_y, ChiCircuit.map_c, ← I.cellEquiv_rowCell,
      ← I.cellEquiv_rowCell, ← I.cellEquiv_rowCell]
    exact ⟨I.wired_of_reads hx, I.wired_of_reads hy, I.wired_of_reads hc⟩
  have hg : ∀ W : (Fin (22 + 2) → Bool) → F,
      (∀ y : Fin 22 → Bool, gate (W (cellBits (y, 0))) (W (cellBits (y, 1)))
        (W (cellBits (y, 2))) (W (cellBits (y, 3))) = 0) →
      ∀ t : I.params.T, gate (W (I.cellEquiv.symm (t, 0))) (W (I.cellEquiv.symm (t, 1)))
        (W (I.cellEquiv.symm (t, 2))) (W (I.cellEquiv.symm (t, 3))) = 0 := by
    intro W hW t
    obtain ⟨r, rfl⟩ := I.rowEquivT.surjective t
    rw [hpull W, hpull W, hpull W, hpull W]
    exact hW (rowBits r)
  have hc : ∀ W : (Fin (22 + 2) → Bool) → F, (∀ z, W (I.wiring z) = W z) →
      ∀ i, W (I.cellEquiv.symm (I.params.σ i)) = W (I.cellEquiv.symm i) := by
    intro W hW i
    obtain ⟨z, rfl⟩ := I.cellEquiv.surjective i
    rw [I.sigma_cellEquiv, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hW z
  have hin' : ∀ t, (C.map I.rowEquivT).isInput t →
      w (I.cellEquiv.symm (t, 3)) = w' (I.cellEquiv.symm (t, 3)) := by
    intro t ht
    obtain ⟨r, rfl⟩ := I.rowEquivT.surjective t
    rw [ChiCircuit.map_isInput] at ht
    rw [hpull w, hpull w']
    exact hin r ht
  have h := QuotientSecurity.cells_determined I.params (C.map I.rowEquivT)
    (I.cellEquiv zeroCell) (I.cellEquiv oneCell) hwire (fun i => w (I.cellEquiv.symm i))
    (fun i => w' (I.cellEquiv.symm i)) (hg w hgate) (hg w' hgate') (hc w hcopy) (hc w' hcopy')
    (by simpa using hzero) (by simpa using hone) (by simpa using hzero') (by simpa using hone')
    hin' (I.rowEquivT r)
  beta_reduce at h
  rw [hpull w, hpull w'] at h
  exact h

/-! ## The relation holds `C`'s computation -/

/-- **Cells satisfying the relation hold `C`'s computation.** For an instance whose wiring lays
`C` and whose weights are `coordinate_weight`'s (with `x ≠ 1`, `Y ≠ 1`), and a statement whose
words 4 and 5 are 1 and 0: cells that satisfy the relation hold a computation of `C` on bits, and
every public word of the statement is that computation's. -/
theorem proves_of_relation (C : ChiCircuit (Fin (2 ^ 22))) {x Y : F} (hx : x ≠ 1) (hY : Y ≠ 1)
    (hc : I.c = coordWeight x Y) (hC : Laid I.wiring C) (stmt : Fin 8 → F)
    (h4 : stmt 4 = 1) (h5 : stmt 5 = 0) (w : (Fin (22 + 2) → Bool) → F)
    (hrel : I.Relation stmt w) :
    ∃ v, C.Computes w v ∧ ∀ J, C.pubWord x Y v J = stmt J := by
  obtain ⟨hgate, hcopy, hword⟩ := hrel
  rw [hc] at hword
  have hzero := zero_pinned hC hx hY w hcopy ((hword 5).trans h5)
  have hone := one_pinned hC x Y w hcopy hzero ((hword 4).trans h4)
  have hbit : ∀ r, IsBit (w (rowCell r 3)) := fun r =>
    (I.cells_determined C hC.reads w w hgate hgate hcopy hcopy hzero hone hzero hone
      (fun _ _ => rfl) r).2
  let v : Fin (2 ^ 22) → Bool := fun r => decide (w (rowCell r 3) = 1)
  have hv : ∀ r, w (rowCell r 3) = bitF (v r) := fun r => eq_bitF_of_isBit (hbit r)
  have hval : ∀ s : Src (Fin (2 ^ 22)), (s.val fun r => w (rowCell r 3)) = bitF (s.bval v) := by
    intro s
    rw [show (fun r => w (rowCell r 3)) = fun r => bitF (v r) from funext hv]
    exact Src.val_bitF v s
  have hread : ∀ {cell : Fin (22 + 2) → Bool} {s : Src (Fin (2 ^ 22))},
      Reads I.wiring cell s → w cell = bitF (s.bval v) := fun h =>
    (reads_val hcopy hzero hone h).trans (hval _)
  have hcells : ∀ r, w (rowCell r 0) = bitF ((C.x r).bval v) ∧
      w (rowCell r 1) = bitF ((C.y r).bval v) ∧ w (rowCell r 2) = bitF ((C.c r).bval v) ∧
      w (rowCell r 3) = bitF (v r) := fun r =>
    ⟨hread (hC.reads r).1, hread (hC.reads r).2.1, hread (hC.reads r).2.2, hv r⟩
  refine ⟨v, ⟨fun r => ?_, hcells⟩, fun J => ?_⟩
  · have h := hgate (rowBits r)
    obtain ⟨h0, h1, h2, h3⟩ := hcells r
    change gate (w (rowCell r 0)) (w (rowCell r 1)) (w (rowCell r 2)) (w (rowCell r 3)) = 0 at h
    rw [h0, h1, h2, h3] at h
    exact (gate_bitF _ _ _ _).mp h
  · classical
    rw [← hword J, sum_regionWeight _ (coordWeight_one x Y)]
    unfold ChiCircuit.pubWord
    refine sum_congr rfl fun j _ => ?_
    rw [regionWeight_coordWeight, hread (hC.reads_pub J j)]
    rfl

/-- **For the statement `(y, root)`**: cells satisfying the relation for its eight words prove it
in `C`. -/
theorem proves_of_relation_statement (C : ChiCircuit (Fin (2 ^ 22))) {x Y : F} (hx : x ≠ 1)
    (hY : Y ≠ 1) (hc : I.c = coordWeight x Y) (hC : Laid I.wiring C) (y root : Fin 32 → UInt8)
    (w : (Fin (22 + 2) → Bool) → F) (hrel : I.Relation (statementWords x Y y root) w) :
    C.Proves x Y w y root := by
  obtain ⟨v, hv, hw⟩ := I.proves_of_relation C hx hY hc hC _ rfl rfl w hrel
  exact ⟨v, hv, fun J => (hw _).trans (statementWords_low x Y y root J)⟩

end Instance

end QuotientSecurity
