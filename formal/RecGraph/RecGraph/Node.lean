-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The node set is `crates/leanvm_flock_gas/src/evm/record.rs`'s
-- (`Node`, `Graph`) and the call words `crates/leanvm_flock_gas/src/evm/codegen.rs`'s (`Word`); the form follows
-- `formal/Implementation/Node.lean` (the Merkle-path verifier's graph).

/-!
# The recorded graph's nodes

`leanvm_flock_gas::evm::record`'s `Node`, `Graph` and `codegen::Word`, as Lean data. The recorder runs π1's verifier
(`crates/leanvm_univariate`'s `reduce`, generic over its scalar) on a symbol: every read of the stream, every
challenge, every addition and product of `E`, every bit field of a row count and every ring-switch weight is a node,
its operands the indices of earlier nodes (hash-consed: one node per distinct operation). `Emitted.lean` (written by
the Rust, `crates/leanvm_rec/src/lean.rs`) is π1-rec3's; `Semantics.lean` gives a graph its meaning.

Generalises `formal/Implementation`'s nodes: a stream read is at a byte offset with a length (a scalar's 24 bytes, a
root half's 16, a packed integer's at most 8), a hash absorbs a run of the stream's bytes, and there are bit fields
(`bits`), the ring switch's weight (`ringWeight`, one node for `ring_tower::weight_at`) and narrow challenges
(`narrow`). π1-rec3's other novelties are no new kinds: a pair's coordinates (`pair_point`) are additions and products
(one by the constant `β_1`), and the BLAKE2s circuit's walk (`walked_terminal`) is additions and products.
-/

namespace RecGraph

/-- **A recorded value** (`record::Node`). Operands are indices of earlier nodes. -/
inductive Node where
  /-- An element of `E`, its limbs `c0 + c1 y + c2 y²` (`E::new(c0, c1, c2)`). -/
  | const (c0 c1 c2 : UInt64)
  /-- Word `k` of the public input, a 64-bit number (big-endian bytes `8k .. 8k + 8`). -/
  | statement (k : Nat)
  /-- The scalar at byte `offset` of the stream, `len` bytes big-endian: an element of `E` (`24`), a root's half (`16`),
  or a packed integer (at most `8`). -/
  | input (offset len : Nat)
  | add (a b : Nat)
  | mul (a b : Nat)
  /-- The transcript's seed: the hash of the name, the contract's IV and the public input. -/
  | seed
  /-- The transcript's step: the hash of the state `state` and of the stream's bytes `from .. to`. -/
  | hash (state «from» to : Nat)
  /-- The low 192 bits of a state: a challenge. -/
  | low (h : Nat)
  /-- A state's low 160 bits: a narrow challenge (`Channel::sample_narrow`, π1-rec2 and π1-rec3's batch). -/
  | narrow (h : Nat)
  /-- `(v >> shift) mod 2^width` of an integer `v` held in a scalar's low limb (`Scalar::bits`). -/
  | bits (v shift width : Nat)
  /-- The ring switch's weight at a point (`ring_tower::weight_at`): kernel `kernel` of the graph's `kernels`
  (the point's `n` coordinates, then `1 + r`'s `n`, then the map). -/
  | ringWeight (kernel n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- **A word a `PCS_OPEN` call takes** (`codegen::Word`, but `Stored`: π1's contract stores nothing). -/
inductive Word where
  /-- A recorded value: an element of `E`, as `element_word` writes it. -/
  | node (id : Nat)
  /-- A constant word, big-endian. -/
  | const (w : Nat)
  /-- The 32 bytes of the stream at this offset: a root, as the stream carries it. -/
  | stream (at_ : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- **A recorded verifier** (`record::Graph` with what `contract::calls` reads of the recording): its nodes in
creation order, the values it requires zero and then nonzero (in the order required), each ring-weight node's
operands, the words of its `PCS_OPEN` calls (in call order), and the stream's length. -/
structure Graph where
  nodes : Array Node
  zero : List Nat
  nonzero : List Nat
  kernels : Array (List Nat)
  calls : List (List Word)
  streamLen : Nat
  deriving Inhabited

/-- Every operand of a node, but a ring-weight node's kernel (its operands are the kernel's entries). -/
def Node.operands : Node → List Nat
  | .add a b | .mul a b => [a, b]
  | .hash s _ _ => [s]
  | .low h | .narrow h => [h]
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
