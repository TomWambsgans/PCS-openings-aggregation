-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): Keccak-256 (`Statement/Keccak.lean`, `keccak256`, `Digest.toBytes`).
import QuotientSecurity.Pinning
import Statement.Keccak

/-!
# The circuit's completeness: an honest witness satisfies the relation

`crates/quotient/src/statement.rs`: the statement is `y = H(x ‖ 0x11^32)` and the root of a
Merkle path of depth `32` from `H(x ‖ 0x22^32)`, `H` Keccak-256 of a 64-byte block (`pair`); the
secret is `x`, the siblings and the directions (`Secret`, `Secret.statement`). Here they are
transcribed with leanerVM `mumbai`'s Keccak-256 (`keccak256`, the deployed function, transcribed
from leanVM's verifier and executed against it there).

**The interface F0b discharges** (`MembershipCircuit`): the deployed circuit as a Lean
`ChiCircuit` `C`, the assignment of its rows the Rust builder computes from a secret (`assign`,
the circuit evaluated on the secret's input bits), and, **in the forward direction, Keccak
correctness**: the assignment satisfies every gate (`satisfies`), and its public bits are the
bits of the statement the secret proves (`publicBits`, as `circuit::public_words` reads `y` and
`root`), with words 4 to 7 laid as `Builder::finish` lays them (`1, 0, 0, 0`). These are fields
of a structure, so every theorem below that takes a `MembershipCircuit` holds of whatever F0b
builds; nothing about Keccak is assumed beyond them.

`honest_relation`: on an instance whose wiring is the circuit's (`wiringOf C`) and whose bit
weights are `coordinate_weight`'s, the cells of the assignment (`cellsOfBits`) satisfy the relation
for the statement's eight words (`statementWords`: the halves of `(y, root)`, then `1, 0, 0, 0`).
F0a's `relation_statementWords` is the step from words to the relation; the words are the bits'
weighted sums (`halves_eq_sum`), so no independence of the weights is needed in this direction.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Completeness

open QuotientSecurity

/-- Thirty-two bytes. -/
abbrev Bytes32 := Fin 32 → UInt8

/-- **`statement::pair`**: Keccak-256 of the 64 bytes `left ‖ right`. -/
def pair (left right : Bytes32) : Bytes32 := fun i =>
  (LeanVM.Protocol.Digest.toBytes
    (LeanVM.Protocol.KeccakHash.keccak256 (List.ofFn left ++ List.ofFn right)))[i]

/-- `Y_PAD`, `LEAF_PAD`. -/
def yPad : UInt8 := 0x11
def leafPad : UInt8 := 0x22

/-- **`statement::Secret`**: `x`, the `DEPTH = 32` siblings, and the directions (bit `i`: the
sibling is on the left at level `i`). -/
structure Secret where
  x : Bytes32
  siblings : Fin 32 → Bytes32
  directions : Fin 32 → Bool

/-- **`statement::Statement`**: the public values. -/
structure Statement where
  y : Bytes32
  root : Bytes32

/-- The leaf: `H(x ‖ 0x22^32)`. -/
def Secret.leaf (s : Secret) : Bytes32 := pair s.x fun _ => leafPad

/-- The root: the path folded from the leaf, level `0` first. -/
def Secret.root (s : Secret) : Bytes32 :=
  (List.finRange 32).foldl
    (fun node i => if s.directions i then pair (s.siblings i) node else pair node (s.siblings i))
    s.leaf

/-- **`Secret::statement`**: `y = H(x ‖ 0x11^32)` and the root. -/
def Secret.statement (s : Secret) : Statement :=
  ⟨pair s.x (fun _ => yPad), s.root⟩

/-- **What F0b proves of the deployed circuit** (layer F0 of `formal/README.md`): the circuit as
a Lean `ChiCircuit` on `2^22` rows, the assignment its builder computes from a secret, and Keccak
correctness in the forward direction: that assignment satisfies every gate, and its public bits
are the statement's (`y`'s and `root`'s bits as `circuit::public_words` reads them); words 4 to 7
read `1, 0, 0, 0`. -/
structure MembershipCircuit where
  C : ChiCircuit (Fin (2 ^ 22))
  /-- The rows' outputs the circuit computes from a secret (`Builder`'s evaluation). -/
  assign : Secret → Fin (2 ^ 22) → Bool
  /-- Every gate holds. -/
  satisfies : ∀ s, C.SatisfiesBits (assign s)
  /-- **Keccak correctness, forward**: the public bits are the statement's. -/
  publicBits : ∀ (s : Secret) (J : Fin 4) (j : Fin 128),
    C.pubBit (assign s) (Fin.castLE (by norm_num) J) j =
      statementBit s.statement.y s.statement.root J j
  word4_one : C.pubSrc 4 0 = .one
  word4 : ∀ j, j ≠ 0 → C.pubSrc 4 j = .zero
  word5 : ∀ j, C.pubSrc 5 j = .zero
  word6 : ∀ j, C.pubSrc 6 j = .zero
  word7 : ∀ j, C.pubSrc 7 j = .zero

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

/-- A public word of the assignment is the statement's half, as the bits are. -/
theorem pubWord_eq_halves (M : MembershipCircuit) (x Y : F) (s : Secret) (J : Fin 4) :
    M.C.pubWord x Y (M.assign s) (Fin.castLE (by norm_num) J) =
      halves x Y s.statement.y s.statement.root J := by
  rw [halves_eq_sum, ChiCircuit.pubWord]
  exact sum_congr rfl fun j _ => by rw [M.publicBits s J j]

/-- **The honest cells satisfy the relation.** On an instance whose wiring is the circuit's and
whose bit weights are `coordinate_weight`'s, the cells of the assignment of a secret satisfy the
relation for the eight words of the statement it proves. -/
theorem honest_relation (M : MembershipCircuit) (I : Instance F) {x Y : F}
    (hc : I.c = coordWeight x Y) (hw : I.wiring = wiringOf M.C) (s : Secret) :
    I.Relation (statementWords x Y s.statement.y s.statement.root) (M.C.cellsOfBits (M.assign s)) :=
  I.relation_statementWords M.C hc hw M.word4_one M.word4 M.word5 M.word6 M.word7 (M.assign s)
    (M.satisfies s) _ _ (pubWord_eq_halves M x Y s)

end Completeness
