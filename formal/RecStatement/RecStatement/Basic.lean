-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/pi2/circuit.rs`
-- (`Coeff`, `Lin`, `Formula`, `Pair`, `Read`, `PublicTerm`, `Circuit`) and `crates/leanvm_rec/src/circuit/spec.rs`
-- (`CallWord`), branch `leanvm-rec` @ 2b22581.
import UniStatement.Opening

/-!
# π2's circuit as its verifier reads it

The verifier of π2 (`pi2::verifier`) is built from `pi2::circuit::Circuit` without its setup columns
`σ`, `κ` (which the setup's commitment and the circuit's digest bind, and which the verifier never reads):

* a **coefficient** (`Coeff`) is an element of `E` (three 64-bit limbs, low first) times a power `γ^gamma` of
  the copy argument's third challenge;
* a **linear form** (`Lin`) is `Σ coefficient · cell` plus an optional constant; a **formula** (`Formula`)
  a linear form plus products `coefficient · lin_a · lin_b` (degree at most two in a row's cells);
* a **pair** (`Pair`): role `role` of the rows `firstRow … firstRow + 2^logRows` (an aligned block), pushing
  formula `formula` of its row (`pulls = false`: a hole, pulling nothing);
* the **reads** (`Read`): how the public data after the public input's four words comes from the stream (an
  integer, a root's two halves, an element of `E`);
* the **public terms** (`PublicTerm`): the verifier adds `1/(α + F + β ω_tag)`, `F` the term's linear form of the
  public scalars;
* π1's `PCS_OPEN` calls are words (`CallWord`): constants, π1's roots as the stream carries them, π1's claims'
  elements (public scalars), and the coordinates of π1-rec3's pair points of them.

A `List` stands for a `Vec`; an index out of range reads a default (`getD`), where the Rust would panic (the
verifier reads in range on the circuits the runner checks).
-/

namespace RecStatement

open LeanVM.Parameters UniStatement

/-- **A coefficient** (`Coeff`): the element `c0 + c1 y + c2 y²` of `E` times `γ^gamma`. -/
structure Coeff where
  c0 : UInt64
  c1 : UInt64
  c2 : UInt64
  gamma : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The coefficient's element of `E`, without its power of `γ` (`Coeff::field`). -/
def Coeff.field (c : Coeff) : E := eNew c.c0 c.c1 c.c2

/-- **A linear form** (`Lin`): `Σ coefficient · cell`, plus a constant. -/
structure Lin where
  terms : List (Coeff × ℕ)
  constant : Option Coeff
  deriving DecidableEq, Repr, Inhabited

/-- **A formula** (`Formula`): a linear form plus products of two linear forms. -/
structure Formula where
  lin : Lin
  products : List (Coeff × Lin × Lin)
  deriving DecidableEq, Repr, Inhabited

/-- **A (block, role) pair** (`Pair`). -/
structure Pair where
  firstRow : ℕ
  logRows : ℕ
  role : ℕ
  formula : ℕ
  pulls : Bool
  deriving DecidableEq, Repr, Inhabited

/-- **A read of the public data** (`Read`). -/
inductive Read where
  /-- A big-endian integer of this many bytes: one scalar. -/
  | integer (bytes : ℕ)
  /-- A root: its two 16-byte halves, two scalars. -/
  | root
  /-- A 24-byte element of `E`: one scalar. -/
  | scalar
  deriving DecidableEq, Repr, Inhabited

/-- The scalars a read gives (`Read::scalars`). -/
def Read.scalars : Read → ℕ
  | .root => 2
  | _ => 1

/-- The bytes a read takes (`Read::bytes`). -/
def Read.bytes : Read → ℕ
  | .integer b => b
  | .root => 32
  | .scalar => 24

/-- **A public term** (`PublicTerm`). -/
structure PublicTerm where
  tag : ℕ
  value : Lin
  deriving DecidableEq, Repr, Inhabited

/-- **π2's circuit** as the verifier reads it (`pi2::circuit::Circuit` without `σ`, `κ`). -/
structure Circuit where
  logN : ℕ
  logRow : ℕ
  formulas : List Formula
  pairs : List Pair
  reads : List Read
  publicTerms : List PublicTerm
  deriving Inhabited

/-- **A word of one of π1's `PCS_OPEN` inputs** (`spec::CallWord`). -/
inductive CallWord where
  /-- A constant word. -/
  | const (word : List UInt8)
  /-- π1's root `i`, its 32 bytes as the stream carries them. -/
  | root (i : ℕ)
  /-- π1's claims' element `i`, as `element_word`. -/
  | element (i : ℕ)
  /-- Coordinate `coordinate` of `pair_point` of element `element` (π1-rec3's paired batch). -/
  | pair (element coordinate : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- The bytes of a lowercase hex string. -/
def hexBytes (s : String) : List UInt8 := bytesOfHex s

/-- `TAG_BITS` (`pi2::circuit`, `quotient::domain::BASIS`): tags are points `ω_j`, `j < 2^28`. -/
def tagBits : ℕ := 28

end RecStatement
