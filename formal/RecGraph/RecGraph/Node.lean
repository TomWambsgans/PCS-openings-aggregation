-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The node set is `crates/leanvm_flock_gas/src/evm/record.rs`'s
-- (`Node`, `Graph`) and the call words `crates/leanvm_flock_gas/src/evm/codegen.rs`'s (`Word`); the form follows
-- `formal/Implementation/Node.lean` (the Merkle-path verifier's graph).

/-!
# The recorded graph's nodes

`leanvm_flock_gas::evm::record`'s `Node`, `Graph` and `codegen::Word`, as Lean data. The recorder runs π1's verifier
(`crates/leanvm_univariate`'s `reduce`, generic over its scalar) on a symbol: every read of the stream, every
challenge, every addition and product of `E`, every bit field of a row count and every ring-switch weight is a node,
its operands the indices of earlier nodes (hash-consed: one node per distinct operation). `Emitted.lean` (written by
the Rust, `crates/leanvm_rec/src/lean.rs`) is π1-rec's; `Semantics.lean` gives a graph its meaning.

Generalises `formal/Implementation`'s nodes: a stream read is at a byte offset with a length (a scalar's 24 bytes, a
root half's 16, a packed integer's at most 8), a hash absorbs a run of the stream's bytes, and there are bit fields
(`bits`) and the ring switch's weight (`ringWeight`, one node for `ring_tower::weight_at`).
-/

namespace RecGraph

/-- **A recorded value** (`record::Node`). Operands are indices of earlier nodes. -/
inductive Node where
  /-- An element of `E`, its limbs `c0 + c1 y + c2 y²` (`E::new(c0, c1, c2)`). -/
  | const (c0 c1 c2 : UInt64)
  /-- Word `k` of the public input, a 64-bit number (big-endian bytes `8k .. 8k + 8`). -/
  | statement (k : ℕ)
  /-- The scalar at byte `offset` of the stream, `len` bytes big-endian: an element of `E` (`24`), a root's half (`16`),
  or a packed integer (at most `8`). -/
  | input (offset len : ℕ)
  | add (a b : ℕ)
  | mul (a b : ℕ)
  /-- The transcript's seed: the hash of the name, the contract's IV and the public input. -/
  | seed
  /-- The transcript's step: the hash of the state `state` and of the stream's bytes `from .. to`. -/
  | hash (state «from» to : ℕ)
  /-- The low 192 bits of a state: a challenge. -/
  | low (h : ℕ)
  /-- `(v >> shift) mod 2^width` of an integer `v` held in a scalar's low limb (`Scalar::bits`). -/
  | bits (v shift width : ℕ)
  /-- The ring switch's weight at a point (`ring_tower::weight_at`): kernel `kernel` of the graph's `kernels`
  (the point's `n` coordinates, then `1 + r`'s `n`, then the map). -/
  | ringWeight (kernel n : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- **A word a `PCS_OPEN` call takes** (`codegen::Word`, but `Stored`: π1's contract stores nothing). -/
inductive Word where
  /-- A recorded value: an element of `E`, as `element_word` writes it. -/
  | node (id : ℕ)
  /-- A constant word, big-endian. -/
  | const (w : ℕ)
  /-- The 32 bytes of the stream at this offset: a root, as the stream carries it. -/
  | stream (at_ : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- **A recorded verifier** (`record::Graph` with what `contract::calls` reads of the recording): its nodes in
creation order, the values it requires zero and then nonzero (in the order required), each ring-weight node's
operands, the words of its `PCS_OPEN` calls (in call order), and the stream's length. -/
structure Graph where
  nodes : Array Node
  zero : List ℕ
  nonzero : List ℕ
  kernels : Array (List ℕ)
  calls : List (List Word)
  streamLen : ℕ
  deriving Inhabited

/-- Every operand of a node, but a ring-weight node's kernel (its operands are the kernel's entries). -/
def Node.operands : Node → List ℕ
  | .add a b | .mul a b => [a, b]
  | .hash s _ _ => [s]
  | .low h => [h]
  | .bits v _ _ => [v]
  | _ => []

/-- **A well-formed graph**: every node reads only nodes before it (a ring-weight node its kernel's entries), every
check and every call word names a node. The recorder writes only such graphs (`Record.lean`). -/
def Graph.WellFormed (g : Graph) : Prop :=
  (∀ i (h : i < g.nodes.size), (∀ a ∈ (g.nodes[i]).operands, a < i) ∧
    ∀ k n, g.nodes[i] = .ringWeight k n → ∀ a ∈ g.kernels.getD k [], a < i) ∧
  (∀ a ∈ g.zero ++ g.nonzero, a < g.nodes.size) ∧
  (∀ ws ∈ g.calls, ∀ id, Word.node id ∈ ws → id < g.nodes.size)

end RecGraph
