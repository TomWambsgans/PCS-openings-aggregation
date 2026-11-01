-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/quotient/src/statement.rs` (itself adapted from leanVM's
-- `crates/flock/src/membership.rs`, branch PCS-openings-aggregation, commit 651453c6). Keccak-256 is
-- leanerVM's (`Statement/Keccak.lean`, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0).
module

public import Statement.Keccak

/-!
# The relation

Read first. The statement `crates/quotient` proves: Ethereum's Keccak-256 `H` of a 64-byte block,
the public values `y` and `root` (32 bytes each), and the secret `x`, a Merkle path of depth `32`
(`siblings`) and its `directions`, such that

```text
y    = H(x ‖ 0x11^32)
leaf = H(x ‖ 0x22^32)
root = the fold of the path from `leaf`: at level `i`, H(sibling_i ‖ node) if direction `i` is set
       (the sibling is on the left), H(node ‖ sibling_i) otherwise.
```

`H` is the **deployed** Keccak-256 (`LeanVM.Protocol.KeccakHash.keccak256`, Keccak-f[1600] itself),
not the random permutation of the model: the circuit computes the deployed Keccak-f[1600], so the
relation is about it, independently of the permutation `π` the protocol's commitments and
transcripts hash with in the model (`Security.lean`). This is mumbai's convention for leanVM's
`KECCAK` instruction (`Statement/README.md` there, "The model").
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- `DEPTH` (`statement.rs:12`): the Merkle path's length. -/
def depth : ℕ := 32

/-- `Y_PAD` (`statement.rs:15`): the constant `x` is hashed with to give `y`. -/
def yPad : UInt8 := 0x11

/-- `LEAF_PAD` (`statement.rs:16`): the constant `x` is hashed with to give the leaf. -/
def leafPad : UInt8 := 0x22

/-- Thirty-two bytes: a hash input half, a digest, a public value. -/
abbrev Bytes32 : Type := Vector UInt8 32

/-- `pair(left, right) = H(left ‖ right)` (`statement.rs:19-21`): the deployed Keccak-256 of the
64-byte block. -/
def pair (left right : Bytes32) : Bytes32 :=
  (keccak256 (left.toList ++ right.toList)).toBytes

/-- **The public values** (`Statement`, `statement.rs:24-29`). -/
structure Statement where
  y : Bytes32
  root : Bytes32
  deriving DecidableEq

/-- **What the prover knows** (`Secret`, `statement.rs:40-46`): `x`, the siblings from the leaf up,
and the directions, `directions[i]` saying that the sibling is on the left at level `i` (bit `i` of
the Rust's `u32`). -/
structure Secret where
  x : Bytes32
  siblings : Vector Bytes32 depth
  directions : Vector Bool depth

/-- The leaf, `H(x ‖ 0x22^32)`. -/
def Secret.leaf (w : Secret) : Bytes32 := pair w.x (Vector.replicate 32 leafPad)

/-- The root the path folds to (`Secret::statement`, `statement.rs:50-57`). -/
def Secret.root (w : Secret) : Bytes32 :=
  (List.finRange depth).foldl
    (fun node i ↦ if w.directions[i] then pair w.siblings[i] node else pair node w.siblings[i])
    w.leaf

/-- **The statement a secret proves**, by hashing natively (`Secret::statement`). -/
def Secret.statement (w : Secret) : Statement :=
  ⟨pair w.x (Vector.replicate 32 yPad), w.root⟩

/-- **The relation**: `w` is a witness for `stmt`. -/
def Relation (stmt : Statement) (w : Secret) : Prop := w.statement = stmt

instance (stmt : Statement) (w : Secret) : Decidable (Relation stmt w) :=
  inferInstanceAs (Decidable (_ = _))

end PcsQuotient

end
