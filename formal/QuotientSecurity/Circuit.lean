-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Circuit.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Protocol

/-!
# What the relation means for a circuit

The relation proved is "every gate, every copy, the public words". For a circuit of full adders
with no loop this pins every cell: the values of the rows' outputs are determined by the input
bits, and they are elements of `GF(4)`, whatever field the cells live in. So a satisfying
assignment is the circuit's computation on some input bits, and nothing else.
-/

set_option linter.unusedSectionVars false

namespace QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2]

/-- An element of `GF(4)`. -/
def InGF4 (θ v : F) : Prop := v = 0 ∨ v = 1 ∨ v = θ ∨ v = θ + 1

/-- The bit and the carry a cell holds. -/
def bitOf (θ v : F) : F := v * (θ * v + θ * θ)

def carryOf (v : F) : F := v * v + v

theorem gate_eq (θ x y c v : F) :
    gate θ x y c v = v + bitOf θ x + bitOf θ y + carryOf c
      + θ * (bitOf θ x * bitOf θ y + carryOf c * (bitOf θ x + bitOf θ y)) := rfl

variable {θ : F} (hθ : θ * θ + θ + 1 = 0)
include hθ

theorem bitOf_mem {v : F} (hv : InGF4 θ v) : bitOf θ v = 0 ∨ bitOf θ v = 1 := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  rcases hv with rfl | rfl | rfl | rfl
  · left; simp [bitOf]
  · right; unfold bitOf; linear_combination hθ - two
  · left; unfold bitOf; linear_combination (v * v * v) * two
  · right; unfold bitOf; linear_combination hθ + (θ ^ 3 + θ ^ 2 - 1) * two

theorem carryOf_mem {v : F} (hv : InGF4 θ v) : carryOf v = 0 ∨ carryOf v = 1 := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  rcases hv with rfl | rfl | rfl | rfl
  · left; simp [carryOf]
  · left; unfold carryOf; linear_combination two
  · right; unfold carryOf; linear_combination hθ - two
  · right; unfold carryOf; linear_combination hθ + (θ) * two

/-- A sum of a bit and `θ` times a bit is in `GF(4)`. -/
theorem inGF4_of_bits {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    InGF4 θ (a + θ * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left; simp
  · right; right; left; simp
  · right; left; simp
  · right; right; right; ring

theorem bit_add {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : a + b = 0 ∨ a + b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · left; exact CharTwo.add_self_eq_zero 1

theorem bit_mul {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : a * b = 0 ∨ a * b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-- A gate whose inputs are in `GF(4)` has its output there, and the output is a function of the
inputs. -/
theorem gate_output {x y c v : F} (hx : InGF4 θ x) (hy : InGF4 θ y) (hc : InGF4 θ c)
    (h : gate θ x y c v = 0) :
    v = bitOf θ x + bitOf θ y + carryOf c
        + θ * (bitOf θ x * bitOf θ y + carryOf c * (bitOf θ x + bitOf θ y)) ∧ InGF4 θ v := by
  have hv : v = bitOf θ x + bitOf θ y + carryOf c
      + θ * (bitOf θ x * bitOf θ y + carryOf c * (bitOf θ x + bitOf θ y)) := by
    rw [gate_eq] at h
    have h' : v + (bitOf θ x + bitOf θ y + carryOf c
        + θ * (bitOf θ x * bitOf θ y + carryOf c * (bitOf θ x + bitOf θ y))) = 0 := by
      rw [← h]; ring
    exact CharTwo.add_eq_zero.mp h'
  refine ⟨hv, ?_⟩
  rw [hv]
  have bx := bitOf_mem hθ hx
  have bY := bitOf_mem hθ hy
  have cc := carryOf_mem hθ hc
  exact inGF4_of_bits hθ (bit_add hθ (bit_add hθ bx bY) cc)
    (bit_add hθ (bit_mul hθ bx bY) (bit_mul hθ cc (bit_add hθ bx bY)))

/-- A row that reads its own output and two zeros holds a bit. -/
theorem input_is_bit {v : F} (h : gate θ v 0 0 v = 0) : v = 0 ∨ v = 1 := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    simp at hθ
  have h1 : θ * (v * (v + 1)) = 0 := by
    rw [gate_eq] at h
    simp only [bitOf, carryOf] at h
    linear_combination h - v * hθ + (θ * v) * two
  rcases mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hθ0) with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (CharTwo.add_eq_zero.mp h0)

omit hθ

/-- What a cell reads: a constant, or the output of a row. -/
inductive Src (ρ : Type*)
  | zero
  | one
  | row (r : ρ)

/-- A circuit of full adders with no loop: a row is an input, which reads its own output and two
zeros, or it reads constants and rows of lower rank. -/
structure AdderCircuit (ρ : Type*) where
  x : ρ → Src ρ
  y : ρ → Src ρ
  c : ρ → Src ρ
  rank : ρ → ℕ
  isInput : ρ → Prop
  hInput : ∀ r, isInput r → x r = .row r ∧ y r = .zero ∧ c r = .zero
  hOrder : ∀ r, ¬ isInput r → ∀ r', (x r = .row r' ∨ y r = .row r' ∨ c r = .row r') →
    rank r' < rank r

variable {ρ : Type*}

/-- The value a cell reads, the rows' outputs being `v`. -/
def Src.val (v : ρ → F) : Src ρ → F
  | .zero => 0
  | .one => 1
  | .row r => v r

/-- Every row's gate holds. -/
def AdderCircuit.Satisfies (C : AdderCircuit ρ) (θ : F) (v : ρ → F) : Prop :=
  ∀ r, gate θ ((C.x r).val v) ((C.y r).val v) ((C.c r).val v) (v r) = 0

include hθ

/-- **A satisfying assignment is the circuit's computation.** Two assignments of the rows'
outputs, in any field, that satisfy every gate and agree on the inputs agree everywhere, and
every output is an element of `GF(4)`. -/
theorem AdderCircuit.determined (C : AdderCircuit ρ) (v v' : ρ → F)
    (hv : C.Satisfies θ v) (hv' : C.Satisfies θ v') (hin : ∀ r, C.isInput r → v r = v' r) :
    ∀ r, v r = v' r ∧ InGF4 θ (v r) := by
  intro r
  induction hn : C.rank r using Nat.strong_induction_on generalizing r with
  | _ n ih =>
    by_cases hi : C.isInput r
    · obtain ⟨hx, hy, hc⟩ := C.hInput r hi
      have h := hv r
      rw [hx, hy, hc] at h
      rcases input_is_bit hθ h with h0 | h1
      · exact ⟨hin r hi, Or.inl h0⟩
      · exact ⟨hin r hi, Or.inr (Or.inl h1)⟩
    · have hsrc : ∀ s : Src ρ, (∀ r', s = .row r' → C.rank r' < C.rank r) →
          s.val v = s.val v' ∧ InGF4 θ (s.val v) := by
        intro s hs
        cases s with
        | zero => exact ⟨rfl, Or.inl rfl⟩
        | one => exact ⟨rfl, Or.inr (Or.inl rfl)⟩
        | row r' => exact ih (C.rank r') (hn ▸ hs r' rfl) r' rfl
      obtain ⟨ex, mx⟩ := hsrc (C.x r) fun r' h => C.hOrder r hi r' (Or.inl h)
      obtain ⟨ey, my⟩ := hsrc (C.y r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inl h))
      obtain ⟨ec, mc⟩ := hsrc (C.c r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inr h))
      obtain ⟨e1, m1⟩ := gate_output hθ mx my mc (hv r)
      have h' := hv' r
      rw [← ex, ← ey, ← ec] at h'
      obtain ⟨e2, -⟩ := gate_output hθ mx my mc h'
      exact ⟨e1.trans e2.symm, m1⟩

omit hθ

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
theorem satisfies_of_cells (C : AdderCircuit P.T) (zeroCell oneCell : P.T × Fin 4)
    (hwire : ∀ x : P.T, Wired P zeroCell oneCell (x, 0) (C.x x) ∧
      Wired P zeroCell oneCell (x, 1) (C.y x) ∧ Wired P zeroCell oneCell (x, 2) (C.c x))
    (w : P.T × Fin 4 → F)
    (hgate : ∀ x : P.T, gate P.θ (w (x, 0)) (w (x, 1)) (w (x, 2)) (w (x, 3)) = 0)
    (hcopy : ∀ i, w (P.σ i) = w i) (hzero : w zeroCell = 0) (hone : w oneCell = 1) :
    C.Satisfies P.θ fun r => w (r, 3) := by
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
the input rows, have the same output at every row, an element of `GF(4)`. -/
theorem cells_determined (C : AdderCircuit P.T) (zeroCell oneCell : P.T × Fin 4)
    (hwire : ∀ x : P.T, Wired P zeroCell oneCell (x, 0) (C.x x) ∧
      Wired P zeroCell oneCell (x, 1) (C.y x) ∧ Wired P zeroCell oneCell (x, 2) (C.c x))
    (w w' : P.T × Fin 4 → F)
    (hgate : ∀ x : P.T, gate P.θ (w (x, 0)) (w (x, 1)) (w (x, 2)) (w (x, 3)) = 0)
    (hgate' : ∀ x : P.T, gate P.θ (w' (x, 0)) (w' (x, 1)) (w' (x, 2)) (w' (x, 3)) = 0)
    (hcopy : ∀ i, w (P.σ i) = w i) (hcopy' : ∀ i, w' (P.σ i) = w' i)
    (hzero : w zeroCell = 0) (hone : w oneCell = 1)
    (hzero' : w' zeroCell = 0) (hone' : w' oneCell = 1)
    (hin : ∀ r, C.isInput r → w (r, 3) = w' (r, 3)) (x : P.T) :
    w (x, 3) = w' (x, 3) ∧ InGF4 P.θ (w (x, 3)) :=
  C.determined P.hθ _ _
    (satisfies_of_cells P C zeroCell oneCell hwire w hgate hcopy hzero hone)
    (satisfies_of_cells P C zeroCell oneCell hwire w' hgate' hcopy' hzero' hone') hin x

end OnCells

end QuotientSecurity
