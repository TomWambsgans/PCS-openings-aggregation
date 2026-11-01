-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Circuit.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Protocol

/-!
# What the relation means for a circuit

The relation proved is "every gate, every copy, the public words". For a circuit of χ gates
(`V = X + C + Y·C`, that is `X ⊕ (C ∧ ¬Y)` on bits) with no loop this pins every cell: an input
row reads its own output three times, so its gate says `v + v + v + v·v = 0`, that is `v^2 = v`,
and it holds a bit; every other row reads constants or rows of lower rank, and the gate sends bits
to bits. So the rows' outputs are bits, determined by the input bits, whatever field the cells
live in, and a satisfying assignment is the circuit's computation on some input bits, and nothing
else.
-/

set_option linter.unusedSectionVars false

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2]

/-- A bit: `0` or `1`. -/
def IsBit (v : F) : Prop := v = 0 ∨ v = 1

/-- What the gate makes the `V` cell: `x + c + y·c`, which is `x ⊕ (c ∧ ¬y)` on bits. -/
def chiOf (x y c : F) : F := x + c + y * c

theorem gate_eq (x y c v : F) : gate x y c v = v + chiOf x y c := by
  unfold gate chiOf
  ring

theorem chiOf_bit {x y c : F} (hx : IsBit x) (hy : IsBit y) (hc : IsBit c) :
    IsBit (chiOf x y c) := by
  have one : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  unfold IsBit chiOf
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp [one]

/-- A gate whose inputs are bits has a bit for its output, and the output is a function of the
inputs. -/
theorem gate_output {x y c v : F} (hx : IsBit x) (hy : IsBit y) (hc : IsBit c)
    (h : gate x y c v = 0) : v = chiOf x y c ∧ IsBit v := by
  have hv : v = chiOf x y c := by
    rw [gate_eq] at h
    exact CharTwo.add_eq_zero.mp h
  refine ⟨hv, ?_⟩
  rw [hv]
  exact chiOf_bit hx hy hc

/-- **A row that reads its own output three times holds a bit**: its gate is `v + v + v + v·v`,
that is `v^2 + v`, which vanishes only at `0` and `1`. -/
theorem input_is_bit {v : F} (h : gate v v v v = 0) : IsBit v := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 : v * (v + 1) = 0 := by
    unfold gate at h
    linear_combination h - v * two
  rcases mul_eq_zero.mp h1 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (CharTwo.add_eq_zero.mp h0)

/-- What a cell reads: a constant, or the output of a row. -/
inductive Src (ρ : Type*)
  | zero
  | one
  | row (r : ρ)

/-- A circuit of χ gates with no loop: a row is an input, which reads its own output in its three
input cells, or it reads constants and rows of lower rank (`quotient::circuit`'s `Builder`). -/
structure ChiCircuit (ρ : Type*) where
  x : ρ → Src ρ
  y : ρ → Src ρ
  c : ρ → Src ρ
  rank : ρ → ℕ
  isInput : ρ → Prop
  hInput : ∀ r, isInput r → x r = .row r ∧ y r = .row r ∧ c r = .row r
  hOrder : ∀ r, ¬ isInput r → ∀ r', (x r = .row r' ∨ y r = .row r' ∨ c r = .row r') →
    rank r' < rank r

variable {ρ : Type*}

/-- The value a cell reads, the rows' outputs being `v`. -/
def Src.val (v : ρ → F) : Src ρ → F
  | .zero => 0
  | .one => 1
  | .row r => v r

/-- Every row's gate holds. -/
def ChiCircuit.Satisfies (C : ChiCircuit ρ) (v : ρ → F) : Prop :=
  ∀ r, gate ((C.x r).val v) ((C.y r).val v) ((C.c r).val v) (v r) = 0

/-- **A satisfying assignment is the circuit's computation.** Two assignments of the rows'
outputs, in any field of characteristic 2, that satisfy every gate and agree on the inputs agree
everywhere, and every output is a bit. -/
theorem ChiCircuit.determined (C : ChiCircuit ρ) (v v' : ρ → F)
    (hv : C.Satisfies v) (hv' : C.Satisfies v') (hin : ∀ r, C.isInput r → v r = v' r) :
    ∀ r, v r = v' r ∧ IsBit (v r) := by
  intro r
  induction hn : C.rank r using Nat.strong_induction_on generalizing r with
  | _ n ih =>
    by_cases hi : C.isInput r
    · obtain ⟨hx, hy, hc⟩ := C.hInput r hi
      have h := hv r
      rw [hx, hy, hc] at h
      exact ⟨hin r hi, input_is_bit (v := v r) h⟩
    · have hsrc : ∀ s : Src ρ, (∀ r', s = .row r' → C.rank r' < C.rank r) →
          s.val v = s.val v' ∧ IsBit (s.val v) := by
        intro s hs
        cases s with
        | zero => exact ⟨rfl, Or.inl rfl⟩
        | one => exact ⟨rfl, Or.inr rfl⟩
        | row r' => exact ih (C.rank r') (hn ▸ hs r' rfl) r' rfl
      obtain ⟨ex, mx⟩ := hsrc (C.x r) fun r' h => C.hOrder r hi r' (Or.inl h)
      obtain ⟨ey, my⟩ := hsrc (C.y r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inl h))
      obtain ⟨ec, mc⟩ := hsrc (C.c r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inr h))
      obtain ⟨e1, m1⟩ := gate_output mx my mc (hv r)
      have h' := hv' r
      rw [← ex, ← ey, ← ec] at h'
      obtain ⟨e2, -⟩ := gate_output mx my mc h'
      exact ⟨e1.trans e2.symm, m1⟩

/-- A value copied along the wiring is the same at every cell of its cycle. -/
theorem copy_iterate {ι : Type*} (σ : Equiv.Perm ι) (w : ι → F) (h : ∀ i, w (σ i) = w i)
    (n : ℕ) (i : ι) : w ((σ ^ n) i) = w i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, h, ih]

/-- A public word all of whose cells are one cell pins that cell: its weighted sum is the cell
times the sum of the weights. -/
theorem word_pins {ι : Type*} [Fintype ι] (μ : ι → F) (z target : F)
    (hμ : ∑ i, μ i ≠ 0) (h : ∑ i, μ i * z = target) : z = target / ∑ i, μ i := by
  rw [← Finset.sum_mul] at h
  rw [eq_div_iff hμ, mul_comm]
  exact h

/-! ## On the protocol's cells -/

section OnCells

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : Params F)

/-- A cell is wired to what it reads: some power of the wiring takes it to the output cell of
the row it reads, or to the cell that holds the constant. -/
def Wired (zeroCell oneCell : P.T × Fin 4) (cell : P.T × Fin 4) :
    Src P.T → Prop
  | .zero => ∃ n : ℕ, (P.σ ^ n) cell = zeroCell
  | .one => ∃ n : ℕ, (P.σ ^ n) cell = oneCell
  | .row r => ∃ n : ℕ, (P.σ ^ n) cell = (r, 3)

/-- Cells that satisfy the gates and the copies, with the zero and the one pinned, satisfy the
circuit: the outputs of the rows are an assignment of the circuit. -/
theorem satisfies_of_cells (C : ChiCircuit P.T) (zeroCell oneCell : P.T × Fin 4)
    (hwire : ∀ x : P.T, Wired P zeroCell oneCell (x, 0) (C.x x) ∧
      Wired P zeroCell oneCell (x, 1) (C.y x) ∧ Wired P zeroCell oneCell (x, 2) (C.c x))
    (w : P.T × Fin 4 → F)
    (hgate : ∀ x : P.T, gate (w (x, 0)) (w (x, 1)) (w (x, 2)) (w (x, 3)) = 0)
    (hcopy : ∀ i, w (P.σ i) = w i) (hzero : w zeroCell = 0) (hone : w oneCell = 1) :
    C.Satisfies fun r => w (r, 3) := by
  have hread : ∀ (cell : P.T × Fin 4) (s : Src P.T), Wired P zeroCell oneCell cell s →
      w cell = s.val fun r => w (r, 3) := by
    intro cell s hs
    cases s with
    | zero =>
      obtain ⟨n, hn⟩ := hs
      rw [← copy_iterate P.σ w hcopy n cell, hn, hzero]; rfl
    | one =>
      obtain ⟨n, hn⟩ := hs
      rw [← copy_iterate P.σ w hcopy n cell, hn, hone]; rfl
    | row r =>
      obtain ⟨n, hn⟩ := hs
      rw [← copy_iterate P.σ w hcopy n cell, hn]; rfl
  intro x
  obtain ⟨hx, hy, hc⟩ := hwire x
  rw [← hread _ _ hx, ← hread _ _ hy, ← hread _ _ hc]
  exact hgate x

/-- **The relation pins the computation.** Two assignments of the cells that satisfy the gates
and the copies of a wired loop-free circuit, with the zero and the one pinned, and that agree on
the input rows, have the same output at every row, a bit. -/
theorem cells_determined (C : ChiCircuit P.T) (zeroCell oneCell : P.T × Fin 4)
    (hwire : ∀ x : P.T, Wired P zeroCell oneCell (x, 0) (C.x x) ∧
      Wired P zeroCell oneCell (x, 1) (C.y x) ∧ Wired P zeroCell oneCell (x, 2) (C.c x))
    (w w' : P.T × Fin 4 → F)
    (hgate : ∀ x : P.T, gate (w (x, 0)) (w (x, 1)) (w (x, 2)) (w (x, 3)) = 0)
    (hgate' : ∀ x : P.T, gate (w' (x, 0)) (w' (x, 1)) (w' (x, 2)) (w' (x, 3)) = 0)
    (hcopy : ∀ i, w (P.σ i) = w i) (hcopy' : ∀ i, w' (P.σ i) = w' i)
    (hzero : w zeroCell = 0) (hone : w oneCell = 1)
    (hzero' : w' zeroCell = 0) (hone' : w' oneCell = 1)
    (hin : ∀ r, C.isInput r → w (r, 3) = w' (r, 3)) (x : P.T) :
    w (x, 3) = w' (x, 3) ∧ IsBit (w (x, 3)) :=
  C.determined _ _
    (satisfies_of_cells P C zeroCell oneCell hwire w hgate hcopy hzero hone)
    (satisfies_of_cells P C zeroCell oneCell hwire w' hgate' hcopy' hzero' hone') hin x

end OnCells

end QuotientSecurity
