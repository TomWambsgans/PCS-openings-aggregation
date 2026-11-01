-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Protocol.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.LogDerivative

/-!
# The reduction of `flock::quotient`, as polynomials

The protocol of `doc/quotient/main.tex` with its tables read as the polynomials they hold: a claim
on a table is an evaluation of those polynomials, and the claim at the fixed point is a sum over
the cells. This file defines the parameters, what the prover's two messages hold, the relation
proved, and the verifier's decision as a predicate on the transcript.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace QuotientSecurity

variable {F : Type*} [Field F]

/-- The gate: a full adder on the bits of `x`, `y` and the carry of `c`, packed in `v`. -/
def gate {R : Type*} [CommRing R] (θ x y c v : R) : R :=
  let bx := x * (θ * x + θ * θ)
  let bY := y * (θ * y + θ * θ)
  let cc := c * c + c
  v + bx + bY + cc + θ * (bx * bY + cc * (bx + bY))

/-- The offset of a cell from the `X` cell of its row: `0, 1, θ, θ + 1`. -/
def shift (θ : F) : Fin 4 → F := ![0, 1, θ, θ + 1]

/-- The digit basis of a cell inside its row: `1, X, X^2 + X, X^3 + X^2`. -/
noncomputable def digit : Fin 4 → F[X] := ![1, X, X ^ 2 + X, (X ^ 2 + X) * X]

/-- The row of a point: `X^4 + X`, which does not move under the four shifts. -/
noncomputable def rowPoly : F[X] := X ^ 4 + X

/-- The fixed data of the protocol. A cell is a row `x ∈ T` and a role, at the point
`x + shift θ role`. -/
structure Params (F : Type*) [Field F] [DecidableEq F] where
  θ : F
  hθ : θ * θ + θ + 1 = 0
  /-- The `X` cells. -/
  T : Finset F
  /-- Cells are distinct points. -/
  hT : ∀ x ∈ T, ∀ y ∈ T, ∀ c d : Fin 4, x + shift θ c = y + shift θ d → x = y ∧ c = d
  /-- A polynomial vanishing on the cells, and one vanishing on the `X` cells. -/
  vCells : F[X]
  vRows : F[X]
  hCells : ∀ x ∈ T, ∀ c : Fin 4, vCells.eval (x + shift θ c) = 0
  hRows : ∀ x ∈ T, vRows.eval x = 0
  /-- The wiring, as a permutation of the cells and as the polynomial that carries it. -/
  σ : Equiv.Perm (T × Fin 4)
  sigmaPoly : F[X]
  hσ : ∀ i : T × Fin 4, sigmaPoly.eval (i.1.1 + shift θ i.2) = (σ i).1.1 + shift θ (σ i).2
  /-- The public words: each is a weighted sum of cells that must equal its value. -/
  words : ℕ
  wordSum : Fin words → (T × Fin 4 → F) →ₗ[F] F
  /-- The public weight, a polynomial for each `γ`, which on the cells is `γ ^ J` times the weight
  of word `J`. -/
  pub : F → F[X]
  hPub : ∀ (γ : F) (w : T × Fin 4 → F),
    ∑ i : T × Fin 4, (pub γ).eval (i.1.1 + shift θ i.2) * w i = ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J w

variable [DecidableEq F] (P : Params F)

namespace Params

/-- The point of a cell. -/
def pt (i : P.T × Fin 4) : F := i.1.1 + shift P.θ i.2

theorem pt_injective : Function.Injective P.pt := by
  rintro ⟨⟨x, hx⟩, c⟩ ⟨⟨y, hy⟩, d⟩ h
  obtain ⟨rfl, rfl⟩ := P.hT x hx y hy c d h
  rfl

/-- What the statement's words must sum to, at `γ`. -/
def target (stmt : Fin P.words → F) (γ : F) : F := ∑ J : Fin P.words, γ ^ (J : ℕ) * stmt J

/-- The relation proved: cells that satisfy every gate, every copy, and the public words. -/
def Sat (stmt : Fin P.words → F) (w : P.T × Fin 4 → F) : Prop :=
  (∀ x : P.T, gate P.θ (w (x, 0)) (w (x, 1)) (w (x, 2)) (w (x, 3)) = 0) ∧
    (∀ i, w (P.σ i) = w i) ∧ ∀ J, P.wordSum J w = stmt J

/-- The prover's first message: four polynomials in the row. -/
abbrev Witness (F : Type*) [Field F] := Fin 4 → F[X]

/-- The polynomial of role `c`: at an `X` cell, the value of the cell of role `c` of its row. -/
noncomputable def cellPoly (g : Witness F) (c : Fin 4) : F[X] :=
  ∑ j, (digit j).comp (X + C (shift P.θ c)) * (g j).comp rowPoly

/-- The cells a first message holds. -/
noncomputable def cells (g : Witness F) (i : P.T × Fin 4) : F := (cellPoly P g i.2).eval i.1.1

/-- The prover's second message: the sum's polynomial as its part of degree below the number of
cells and the rest, the copy identity's quotient, the gate's, and what shares its claim. -/
structure Quotients (F : Type*) [Field F] where
  h₀ : F[X]
  hHigh : F[X]
  q : F[X]
  qGate : F[X]
  junk : F[X]

variable {P}

/-- The sum's polynomial. -/
noncomputable def Quotients.h (R : Quotients F) (P : Params F) : F[X] := R.h₀ + P.vCells * R.hHigh

/-- The claim at the fixed point: the sum of the low part over the cells. -/
noncomputable def Quotients.top (R : Quotients F) (P : Params F) : F :=
  ∑ i : P.T × Fin 4, R.h₀.eval (P.pt i)

variable (P)

/-- The two denominators, the gate and the copy identity's right side, as polynomials. -/
noncomputable def dPoly (g : Witness F) (α β : F) : F[X] := C α + cellPoly P g 0 + C β * X

noncomputable def dNextPoly (g : Witness F) (α β : F) : F[X] :=
  C α + cellPoly P g 0 + C β * P.sigmaPoly

noncomputable def gatePoly (g : Witness F) : F[X] :=
  gate (C P.θ) (cellPoly P g 0) (cellPoly P g 1) (cellPoly P g 2) (cellPoly P g 3)

noncomputable def copyPoly (g : Witness F) (α β γ : F) : F[X] :=
  dPoly P g α β + dNextPoly P g α β
    + P.pub γ * cellPoly P g 0 * (dPoly P g α β * dNextPoly P g α β)

/-- What the two identities leave when they fail: zero exactly when they hold. -/
noncomputable def copyDefect (g : Witness F) (R : Quotients F) (α β γ : F) : F[X] :=
  dPoly P g α β * dNextPoly P g α β * R.h P + P.vCells * R.q + copyPoly P g α β γ

noncomputable def gateDefect (g : Witness F) (R : Quotients F) (α β : F) : F[X] :=
  P.vRows * (dPoly P g α β * dNextPoly P g α β * R.qGate + P.vCells * R.junk)
    + dPoly P g α β * dNextPoly P g α β * gatePoly P g

/-- The second message is consistent with the first: both identities hold as polynomials, and
the sum is the target. -/
def Consistent (stmt : Fin P.words → F) (g : Witness F) (R : Quotients F) (α β γ : F) : Prop :=
  copyDefect P g R α β γ = 0 ∧ gateDefect P g R α β = 0 ∧ R.top P = P.target stmt γ

/-- The same at one point. -/
def ConsistentAt (stmt : Fin P.words → F) (g : Witness F) (R : Quotients F) (α β γ t : F) :
    Prop :=
  (copyDefect P g R α β γ).eval t = 0 ∧ (gateDefect P g R α β).eval t = 0 ∧
    R.top P = P.target stmt γ

/-- The four cells of the row of `t`, from the four values the prover sends. -/
noncomputable def cellAt (a : Fin 4 → F) (t : F) (c : Fin 4) : F :=
  ∑ j, (digit j).eval (t + shift P.θ c) * a j

/-- The weights of the four values in the witness claim. -/
def opening (ρ : F) : Fin 4 → F :=
  ![(1 + ρ) * (1 + ρ ^ 2), ρ * (1 + ρ ^ 2), (1 + ρ) * ρ ^ 2, ρ ^ 3]

/-- The verifier's decision, the four claims being checked against what the messages hold. -/
def Accepts (stmt : Fin P.words → F) (g : Witness F) (R : Quotients F)
    (α β γ t : F) (a : Fin 4 → F) (s ρ : F) : Prop :=
  let x := cellAt P a t 0
  let d := α + x + β * t
  let d' := α + x + β * s
  let gt := gate P.θ x (cellAt P a t 1) (cellAt P a t 2) (cellAt P a t 3)
  let copies := d + d' + (P.pub γ).eval t * x * (d * d')
  let den := d * d' + P.vCells.eval t
  let e := P.vCells.eval t / den
  -- The witness claim, the wiring claim, the nonzero product, the two quotient claims.
  (∑ j, opening ρ j * ((g j).comp rowPoly).eval t = ∑ j, opening ρ j * a j) ∧
    P.sigmaPoly.eval t = s ∧
    den * P.vRows.eval t ≠ 0 ∧
    (1 + ρ) * ((1 + e) * (R.h P).eval t + e * R.q.eval t)
        + ρ * ((1 + e) * R.qGate.eval t + e * R.junk.eval t)
      = ((1 + ρ) * copies * P.vRows.eval t + ρ * (d * d') * gt) / (den * P.vRows.eval t) ∧
    R.top P = P.target stmt γ

end Params

end QuotientSecurity
