-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Mathlib

/-!
# π2's circuit, generic

The circuit description of π2's PIOP (`crates/leanvm_rec/src/circuit/spec.rs`, the interface, and
`src/pi2/circuit.rs`, the PIOP's form; `PI2.md` §1), for **any** layout:

* `N = 2^logN` positions, rows of `W = 2^logW` cells: position `i` is role `i % W` of row `i / W`,
  and its row's cells are the positions `base i + c`, `c < W` (`base i = (i / W)·W`);
* **regions**: a row type, `W` role formulas each (`Role`): a **forward** (its push is its own pull),
  an **expression** (`Poly2`: a polynomial of degree at most two in the row's cells, coefficients in
  `F`, no constant term), or a **port** (`Limb`s: the cells of its limbs, each weighted by a
  polynomial in the challenge `γ`, the port's fingerprint);
* **blocks**: aligned runs of `2^logRows` rows of one region (`Block`); a row in no block is all
  forwards;
* the setup columns **σ** (each position's push tag, an index: a position `< N`, or `N + j`, port
  `j`'s outside tag) and **κ** (the constants, zero off the expression slots);
* the **ports**: the positions whose role is a port, in order; port `j` pushes to the outside tag
  `N + j`, and its position is a **hole**: it pulls nothing (`PI2.md` §4.1).

Every position `i` pushes `push w γ i = F_i + κ_i`, `F_i` its role's formula on its row's cells
(`Role.value`). **`Valid`** is `pi2::circuit::Circuit::validate` together with
`spec::Circuit::check_shape` (the regions `W` roles wide, the formulas reading their row, the
blocks aligned, in range and disjoint, `σ` a bijection from the positions onto the non-holes and the
ports' tags, the ports exactly the holes, **no formula reads a hole**, **`κ` only at expression
slots**); `validate` decides it (`validate_eq_true_iff`). **`Satisfies`** is the relation π2
proves: every non-hole position's pull is the push meant for it, and every port's limbs are the
public ones (`spec::Circuit::check`'s (1), (2), (4): not (3), the holes' values, which the PIOP
leaves free; REVIEW-REC.md N1).

Everything is a function of the position (`ℕ → ·`), so the description is generic; nothing about
a particular layout (D16v, D32v) is assumed.
-/

namespace RecPiop

/-! ## Formulas -/

/-- **A formula of degree at most two** in a row's cells (`spec::Poly`): linear terms
`(cell, coefficient)` and quadratic terms `(cell a, cell b, coefficient)`, no constant term (the
constants are `κ`). -/
structure Poly2 (F : Type) where
  linear : List (ℕ × F)
  quadratic : List (ℕ × ℕ × F)

/-- **A port's limb**: the cell it reads and its weight in the fingerprint, a polynomial in `γ`
(coefficients, the constant first). The three-limb ports weigh `1, Y, Y²` (the element itself), the
four-limb ones `1, Y, γ, γY` (`PI2.md` §4.2). -/
structure Limb (F : Type) where
  cell : ℕ
  coeff : List F

/-- **A role's formula** (`spec::Formula`). -/
inductive Role (F : Type) where
  /-- Its own pull. -/
  | forward
  /-- A formula of degree at most two of the row's cells: an expression slot. -/
  | expr (p : Poly2 F)
  /-- A port: its limbs' fingerprint, to its outside tag; the position is a hole. -/
  | port (limbs : List (Limb F))

/-- **A block**: `2^logRows` rows of region `region` from row `row` (a multiple of `2^logRows`). -/
structure Block where
  row : ℕ
  logRows : ℕ
  region : ℕ
deriving DecidableEq

/-- **π2's circuit**: the layout, the setup columns, the ports. -/
structure Circuit (F : Type) where
  logN : ℕ
  logW : ℕ
  regions : List (List (Role F))
  blocks : List Block
  /-- Each position's push tag, an index: a position `< N`, or `N + j` for port `j`. -/
  sigma : ℕ → ℕ
  /-- The constants, zero off the expression slots. -/
  kappa : ℕ → F
  /-- The ports' positions: port `j` pushes to the outside tag `N + j`. -/
  ports : List ℕ

section Eval

variable {F : Type} [Field F]

/-- A polynomial in `γ`, by Horner's rule. -/
def horner (c : List F) (γ : F) : F := c.foldr (fun a acc => a + γ * acc) 0

/-- A degree-two formula on cells in any `F`-algebra (`F` itself, or `F[X]`). -/
def Poly2.eval {R : Type} [CommRing R] [Algebra F R] (p : Poly2 F) (cell : ℕ → R) : R :=
  (p.linear.map fun t => algebraMap F R t.2 * cell t.1).sum +
    (p.quadratic.map fun t => algebraMap F R t.2.2 * (cell t.1 * cell t.2.1)).sum

/-- The cells a formula reads. -/
def Poly2.reads (p : Poly2 F) : List ℕ :=
  p.linear.map (·.1) ++ p.quadratic.flatMap fun t => [t.1, t.2.1]

/-- **A port's fingerprint** on cells in any `F`-algebra: `Σ_l coeff_l(γ) · cell_l`. -/
def fpEval {R : Type} [CommRing R] [Algebra F R] (ls : List (Limb F)) (γ : F) (cell : ℕ → R) : R :=
  (ls.map fun l => algebraMap F R (horner l.coeff γ) * cell l.cell).sum

/-- **The public side's fingerprint** of limbs `v`, with a port's weights: `Σ_l coeff_l(γ) v_l`. -/
def fpList (ls : List (Limb F)) (γ : F) (v : List F) : F :=
  ((ls.zip v).map fun p => horner p.1.coeff γ * p.2).sum

/-- The cells a role reads (a forward reads none: its push is its own pull). -/
def Role.reads : Role F → List ℕ
  | .forward => []
  | .expr p => p.reads
  | .port ls => ls.map (·.cell)

/-- Whether a role is a forward. -/
def Role.isForward : Role F → Bool
  | .forward => true
  | _ => false

/-- Whether a role is an expression slot. -/
def Role.isExpr : Role F → Bool
  | .expr _ => true
  | _ => false

/-- Whether a role is a port. -/
def Role.isPort : Role F → Bool
  | .port _ => true
  | _ => false

/-- **A role's push, without `κ`**, given the challenge `γ`, the position's own pull and its row's
cells, in any `F`-algebra. -/
def Role.value {R : Type} [CommRing R] [Algebra F R] (γ : F) (own : R) (cell : ℕ → R) :
    Role F → R
  | .forward => own
  | .expr p => p.eval cell
  | .port ls => fpEval ls γ cell

end Eval

namespace Circuit

variable {F : Type} [Field F] (G : Circuit F)

/-- The number of positions, `N = 2^logN`. -/
def N : ℕ := 2 ^ G.logN

/-- The row width, `W = 2^logW`. -/
def W : ℕ := 2 ^ G.logW

/-- The number of rows, `N / W`. -/
def rows : ℕ := 2 ^ (G.logN - G.logW)

/-- The first position of position `i`'s row. -/
def base (i : ℕ) : ℕ := i / G.W * G.W

/-- A block covers row `y`. -/
def Covers (b : Block) (y : ℕ) : Prop := b.row ≤ y ∧ y < b.row + 2 ^ b.logRows

instance (b : Block) (y : ℕ) : Decidable (Covers b y) := by unfold Covers; infer_instance

/-- The block covering row `y`, if any (the first: `Valid` makes it unique). -/
def blockAt (y : ℕ) : Option Block := G.blocks.find? fun b => decide (Covers b y)

/-- Role `k` of block `b`'s region. -/
def regionRole (b : Block) (k : ℕ) : Role F := (G.regions.getD b.region []).getD k .forward

/-- **Position `i`'s role**: its role in the region of the block covering its row, or a forward. -/
def role (i : ℕ) : Role F :=
  match G.blockAt (i / G.W) with
  | none => .forward
  | some b => G.regionRole b (i % G.W)

/-- **A hole**: a port's position. It pulls nothing. -/
def IsHole (i : ℕ) : Prop := (G.role i).isPort = true

instance (i : ℕ) : Decidable (G.IsHole i) := by unfold IsHole; infer_instance

/-- **Position `i`'s push** `F_i + κ_i`, for the witness `w` and the challenge `γ`. -/
def push (w : ℕ → F) (γ : F) (i : ℕ) : F :=
  (G.role i).value γ (w i) (fun c => w (G.base i + c)) + G.kappa i

/-- The number of ports. -/
def nP : ℕ := G.ports.length

/-- Port `j`'s position. -/
def port (j : ℕ) : ℕ := G.ports.getD j 0

/-- Port `j`'s limbs. -/
def limbs (j : ℕ) : List (Limb F) :=
  match G.role (G.port j) with
  | .port ls => ls
  | _ => []

/-- **Port `j`'s limbs' values** in the witness. -/
def limbVals (w : ℕ → F) (j : ℕ) : List F :=
  (G.limbs j).map fun l => w (G.base (G.port j) + l.cell)

/-- **Port `j`'s public fingerprint** `F_j`, of the public limbs `pub j`. -/
def pubFp (γ : F) (pub : ℕ → List F) (j : ℕ) : F := fpList (G.limbs j) γ (pub j)

/-! ## The layout's validity -/

/-- **The structure the protocol assumes** (`pi2::circuit::Circuit::validate` and
`spec::Circuit::check_shape`). -/
structure Valid : Prop where
  /-- At least two rows. -/
  logW_lt : G.logW < G.logN
  /-- Every region is `W` roles wide. -/
  width : ∀ r ∈ G.regions, r.length = G.W
  /-- Every formula reads its row. -/
  reads_lt : ∀ r ∈ G.regions, ∀ f ∈ r, ∀ c ∈ f.reads, c < G.W
  /-- The blocks are aligned. -/
  aligned : ∀ b ∈ G.blocks, 2 ^ b.logRows ∣ b.row
  /-- The blocks are in range. -/
  in_range : ∀ b ∈ G.blocks, b.row + 2 ^ b.logRows ≤ G.rows
  /-- The blocks' regions exist. -/
  region_lt : ∀ b ∈ G.blocks, b.region < G.regions.length
  /-- The blocks are disjoint. -/
  disjoint : G.blocks.Pairwise fun b b' => b.row + 2 ^ b.logRows ≤ b'.row ∨ b'.row + 2 ^ b'.logRows ≤ b.row
  /-- The ports are distinct. -/
  ports_nodup : G.ports.Nodup
  /-- The ports are exactly the holes. -/
  ports_holes : ∀ i, i ∈ G.ports ↔ i < G.N ∧ G.IsHole i
  /-- Port `j` pushes to its outside tag `N + j`. -/
  sigma_port : ∀ j < G.nP, G.sigma (G.port j) = G.N + j
  /-- A non-hole pushes to a non-hole. -/
  sigma_inside : ∀ i < G.N, ¬ G.IsHole i → G.sigma i < G.N ∧ ¬ G.IsHole (G.sigma i)
  /-- `σ` is injective. -/
  sigma_inj : ∀ i < G.N, ∀ i' < G.N, G.sigma i = G.sigma i' → i = i'
  /-- Every non-hole is pushed to. -/
  sigma_onto : ∀ j < G.N, ¬ G.IsHole j → ∃ i < G.N, G.sigma i = j
  /-- **No formula reads a hole** (REVIEW-REC.md L1). -/
  no_hole_read : ∀ i < G.N, ∀ c ∈ (G.role i).reads, ¬ G.IsHole (G.base i + c)
  /-- **`κ` only at expression slots.** -/
  kappa_expr : ∀ i < G.N, G.kappa i ≠ 0 → (G.role i).isExpr = true

/-- `Valid` as one proposition, to decide it. -/
def ValidProp : Prop :=
  G.logW < G.logN ∧
  (∀ r ∈ G.regions, r.length = G.W) ∧
  (∀ r ∈ G.regions, ∀ f ∈ r, ∀ c ∈ f.reads, c < G.W) ∧
  (∀ b ∈ G.blocks, 2 ^ b.logRows ∣ b.row) ∧
  (∀ b ∈ G.blocks, b.row + 2 ^ b.logRows ≤ G.rows) ∧
  (∀ b ∈ G.blocks, b.region < G.regions.length) ∧
  G.blocks.Pairwise (fun b b' => b.row + 2 ^ b.logRows ≤ b'.row ∨ b'.row + 2 ^ b'.logRows ≤ b.row) ∧
  G.ports.Nodup ∧
  (∀ i ∈ G.ports, i < G.N) ∧
  (∀ i < G.N, G.IsHole i → i ∈ G.ports) ∧
  (∀ i ∈ G.ports, G.IsHole i) ∧
  (∀ j < G.nP, G.sigma (G.port j) = G.N + j) ∧
  (∀ i < G.N, ¬ G.IsHole i → G.sigma i < G.N ∧ ¬ G.IsHole (G.sigma i)) ∧
  (∀ i < G.N, ∀ i' < G.N, G.sigma i = G.sigma i' → i = i') ∧
  (∀ j < G.N, ¬ G.IsHole j → ∃ i < G.N, G.sigma i = j) ∧
  (∀ i < G.N, ∀ c ∈ (G.role i).reads, ¬ G.IsHole (G.base i + c)) ∧
  (∀ i < G.N, G.kappa i ≠ 0 → (G.role i).isExpr = true)

theorem valid_iff : G.Valid ↔ G.ValidProp := by
  constructor
  · intro h
    exact ⟨h.logW_lt, h.width, h.reads_lt, h.aligned, h.in_range, h.region_lt, h.disjoint,
      h.ports_nodup, fun i hi => ((h.ports_holes i).mp hi).1,
      fun i hi hh => (h.ports_holes i).mpr ⟨hi, hh⟩, fun i hi => ((h.ports_holes i).mp hi).2,
      h.sigma_port, h.sigma_inside, h.sigma_inj, h.sigma_onto, h.no_hole_read, h.kappa_expr⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8,
      fun i => ⟨fun hi => ⟨h9 i hi, h11 i hi⟩, fun hi => h10 i hi.1 hi.2⟩,
      h12, h13, h14, h15, h16, h17⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance [DecidableEq F] : Decidable G.ValidProp := by unfold ValidProp; infer_instance

instance [DecidableEq F] : Decidable G.Valid := decidable_of_iff _ G.valid_iff.symm

/-- **`validate`**: the layout's checks, computed (`pi2::circuit::Circuit::validate`, asserted by
`Spec::of` and `Setup::new`). -/
def validate [DecidableEq F] : Bool := decide G.Valid

theorem validate_eq_true_iff [DecidableEq F] : G.validate = true ↔ G.Valid := by
  unfold validate
  exact decide_eq_true_iff

/-! ## The relation -/

/-- **The relation π2 proves** for the public limbs `pub` (port `j`'s limbs `pub j`): every
non-hole position's pull is the push meant for it (`w (σ i) = push w γ i`; a non-hole's push does
not read `γ`, `push_gamma`), and every port's limbs are the public ones. -/
structure Satisfies (pub : ℕ → List F) (w : ℕ → F) : Prop where
  copy : ∀ i < G.N, ¬ G.IsHole i → w (G.sigma i) = G.push w 0 i
  ports : ∀ j < G.nP, G.limbVals w j = pub j

/-- A non-hole's push does not read `γ`. -/
theorem push_gamma (w : ℕ → F) {i : ℕ} (hi : ¬ G.IsHole i) (γ γ' : F) :
    G.push w γ i = G.push w γ' i := by
  unfold push
  unfold IsHole at hi
  cases h : G.role i with
  | forward => rfl
  | expr p => rfl
  | port ls => rw [h] at hi; exact absurd rfl hi

end Circuit

end RecPiop
