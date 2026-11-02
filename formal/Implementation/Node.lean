-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

/-!
# The recorded graph's nodes

`crates/evm/src/record.rs`'s `Node` and `crates/evm/src/codegen.rs`'s `Word`, as Lean data:
`Graph.lean` (generated from the Rust) is a list of these. Operands are indices of earlier
nodes; a field element is a natural number below `2^192` (limb `i` its bits `64i .. 64i + 64`),
a state a natural number below `2^256` (the 32 bytes of a Keccak-256 digest, big-endian), as
the EVM holds both.
-/

namespace Implementation

/-- A recorded value (`record::Node`). -/
inductive Node where
  /-- A field element, its limbs `c0 + 2^64 c1 + 2^128 c2`. -/
  | const (c : Nat)
  /-- A half of `y` (0, 1) or of `root` (2, 3). -/
  | statement (k : Nat)
  /-- A scalar of a commitment: two a commitment, in the order they are sent. -/
  | root (k : Nat)
  /-- A scalar of the proof. -/
  | input (i : Nat)
  | add (a b : Nat)
  | mul (a b : Nat)
  /-- `x^(2^64)`. -/
  | frob (a : Nat)
  /-- The transcript's seed: the hash of the label. -/
  | seed
  /-- The hash of a state and of these scalars. -/
  | hash (st : Nat) (xs : List Nat)
  /-- The low 192 bits of a state: a challenge. -/
  | low (a : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A word the contract writes for its calls of `PCS_OPEN` (`codegen::Word`). -/
inductive Word where
  /-- A recorded value. -/
  | node (i : Nat)
  /-- A constant word. -/
  | const (w : Nat)
  /-- The word of the arguments (calldata after the selector) at this offset. -/
  | calldata (offset : Nat)
  /-- The circuit's commitment, as `PCS_OPEN` reads a root. -/
  | storedRoot
  deriving DecidableEq, Repr, Inhabited

end Implementation
