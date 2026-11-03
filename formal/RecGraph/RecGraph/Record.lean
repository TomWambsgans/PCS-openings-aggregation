-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from
-- `crates/leanvm_flock_gas/src/evm/record.rs` (`Sym::new`, `Sym`'s `Add`, `Mul`, `Scalar::constant`, `bits`,
-- `ring_weight`; `Recorder`'s `new`, `statement`, `input`, `sample`, `sample_narrow`, `require_zero`,
-- `require_nonzero`).
import RecGraph.Semantics
import Std.Data.HashMap

/-!
# The recorder, and recording commutes with evaluation

`record.rs`'s recorder in Lean (`RecState`): the nodes, hash-consed (`RecState.new`, a node's index if it is there,
else appended), the smart constructors of `Sym` as the Rust has them (`RecState.add`: two constants fold, a zero is
dropped, `x + x` is zero, the operands ordered; `RecState.mul`: two constants fold, a zero absorbs, a one is dropped;
`constant`, `bits`, `ringWeight`), and the channel (`Recorder`: the seed, the stream's reads at the cursor, the
challenges as a hash of the state and the bytes read since the last, low or narrow).

A **program** (`Prog`) is a verifier written against these operations: a free monad whose scalars are node indices.
`Prog.record` records it (its graph); `Prog.run` records it and evaluates each new node as it is made, over `F`, on
a stream (`stepNode`).

`Commute.lean` proves, for every program, pure permutation, IV, public input and stream, that **recording commutes
with evaluation** (`run_vals`, `record_eval`): the values `Prog.run` computes as it records are the recorded graph's
`evalNodes`. So a verifier written as a `Prog` and recorded is a graph whose evaluation is that program's own
computation on `E`, its points compared as symbols (node indices). What is left for "graph = verifier" is the
simulation of `UniStatement`'s verifier by such a program, and the smart constructors' values (see
`formal/RecGraph/README.md`).
-/

namespace RecGraph

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

deriving instance Hashable for Node

/-- **The recorder's state** (`record::Graph` and `Recorder`): the nodes in creation order, their index (`Sym::new`'s
hash-consing), the values required zero and nonzero, the ring-weight kernels, the stream's cursor, the bytes the
state has absorbed, the state's node. -/
structure RecState where
  nodes : Array Node
  index : Std.HashMap Node Nat
  zero : Array Nat
  nonzero : Array Nat
  kernels : Array (List Nat)
  cursor : Nat
  absorbed : Nat
  state : Nat

namespace RecState

/-- **`Sym::new(node)`**: the node's index if it is recorded, else appended. -/
def new (st : RecState) (n : Node) : Nat × RecState :=
  match st.index[n]? with
  | some i => (i, st)
  | none => (st.nodes.size, { st with nodes := st.nodes.push n, index := st.index.insert n st.nodes.size })

/-- `Sym::value`: the constant a node is, if it is one. -/
def constAt (st : RecState) (i : Nat) : Option E :=
  match st.nodes[i]? with
  | some (.const c0 c1 c2) => some (eNew c0 c1 c2)
  | _ => none

/-- **`Scalar::constant(x)`**: the node `Const(x's limbs)`. -/
def constant (st : RecState) (x : E) : Nat × RecState :=
  st.new (.const (x.limb 0).lane (x.limb 1).lane (x.limb 2).lane)

/-- **`Sym + Sym`**: two constants fold, a zero is dropped, `x + x` is zero, else `Add(min, max)`. -/
def add (st : RecState) (a b : Nat) : Nat × RecState :=
  match st.constAt a, st.constAt b with
  | some x, some y => st.constant (x + y)
  | ca, cb =>
    if ca = some 0 then (b, st)
    else if cb = some 0 then (a, st)
    else if a = b then st.constant 0
    else st.new (.add (min a b) (max a b))

/-- **`Sym * Sym`**: two constants fold, a zero absorbs, a one is dropped, else `Mul(min, max)`. -/
def mul (st : RecState) (a b : Nat) : Nat × RecState :=
  match st.constAt a, st.constAt b with
  | some x, some y => st.constant (x * y)
  | ca, cb =>
    if ca = some 0 ∨ cb = some 0 then st.constant 0
    else if ca = some 1 then (b, st)
    else if cb = some 1 then (a, st)
    else st.new (.mul (min a b) (max a b))

/-- **`Scalar::bits(shift, width)`** of `Sym`: a constant's folds, else `Bits(v, shift, min(width, 255))`. -/
def bits (st : RecState) (v shift width : Nat) : Nat × RecState :=
  match st.constAt v with
  | some x => st.constant (bitsValue x shift width)
  | none => st.new (.bits v shift (min width 255))

/-- **`Scalar::ring_weight(point, 1 + r, map)`** of `Sym`: a new kernel of the operands, and its node. -/
def ringWeight (st : RecState) (point onePlusR map : List Nat) : Nat × RecState :=
  let st := { st with kernels := st.kernels.push (point ++ onePlusR ++ map) }
  st.new (.ringWeight (st.kernels.size - 1) point.length)

/-- **`Recorder::new`**: the seed's node, the cursor at the stream's start. -/
def start : RecState :=
  let empty : RecState := ⟨#[], ∅, #[], #[], #[], 0, 0, 0⟩
  let (seed, st) := empty.new .seed
  { st with state := seed }

/-- **`Recorder::input(len)`** (`next_scalar` 24, `next_root` 16 a half, `next_integer`): the bytes at the cursor. -/
def input (st : RecState) (len : Nat) : Nat × RecState :=
  let (i, st') := st.new (.input st.cursor len)
  (i, { st' with cursor := st.cursor + len })

/-- **`Recorder::sample`** (`narrow`: `sample_narrow`): the state's hash with the bytes read since the last, then its
challenge. -/
def sample (st : RecState) (narrow : Bool) : Nat × RecState :=
  let (h, st) := st.new (.hash st.state st.absorbed st.cursor)
  let st := { st with state := h, absorbed := st.cursor }
  st.new (if narrow then .narrow h else .low h)

/-- **`Recorder::statement`**: word `k` of the public input. -/
def statement (st : RecState) (k : Nat) : Nat × RecState := st.new (.statement k)

end RecState

/-- **An operation that gives a scalar** (a node's index). -/
inductive Op where
  | constant (x : E)
  | statement (k : Nat)
  | input (len : Nat)
  | sample (narrow : Bool)
  | add (a b : Nat)
  | mul (a b : Nat)
  | bits (v shift width : Nat)
  | ringWeight (point onePlusR map : List Nat)

/-- The recorder's step for an operation. -/
def RecState.op (st : RecState) : Op → Nat × RecState
  | .constant x => st.constant x
  | .statement k => st.statement k
  | .input len => st.input len
  | .sample narrow => st.sample narrow
  | .add a b => st.add a b
  | .mul a b => st.mul a b
  | .bits v s w => st.bits v s w
  | .ringWeight p o m => st.ringWeight p o m

/-- **A program over the recorder** (a verifier written against `Sym` and `Recorder`): a free monad, its scalars
node indices; `zero`, `nonzero` are `require_zero`, `require_nonzero`. -/
inductive Prog (α : Type) where
  | pure (a : α)
  | op (o : Op) (k : Nat → Prog α)
  | zero (v : Nat) (k : Prog α)
  | nonzero (v : Nat) (k : Prog α)

namespace Prog

/-- Sequencing. -/
def bind {α β : Type} : Prog α → (α → Prog β) → Prog β
  | .pure a, f => f a
  | .op o k, f => .op o fun i ↦ (k i).bind f
  | .zero v k, f => .zero v (k.bind f)
  | .nonzero v k, f => .nonzero v (k.bind f)

instance : Monad Prog where
  pure := .pure
  bind := Prog.bind

/-- **The graph a program records**: run on the recorder's state. -/
def record {α : Type} : Prog α → RecState → α × RecState
  | .pure a, st => (a, st)
  | .op o k, st => (k (st.op o).1).record (st.op o).2
  | .zero v k, st => k.record { st with zero := st.zero.push v }
  | .nonzero v k, st => k.record { st with nonzero := st.nonzero.push v }

/-- The graph of a recorder's state, of a stream of `len` bytes, with the calls `calls`. -/
def _root_.RecGraph.RecState.graph (st : RecState) (calls : List (List Word)) (len : Nat) : Graph :=
  ⟨st.nodes, st.zero.toList, st.nonzero.toList, st.kernels, calls, len⟩

section Run

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- The nodes `st'` appended to `st`'s, evaluated after `vals` (over the final kernels: a kernel, once made, does not
change). -/
def extend (st' : RecState) (n : Nat) (vals : Array Value) : Array Value :=
  Id.run (evalList (m := Id) (fun s ↦ (Pure.pure (π s) : Id KeccakState)) st'.kernels iv publicInput stream vals
    (st'.nodes.toList.drop n))

/-- **The program run on `E`**: recorded, and each node it makes evaluated as it is made (`stepNode`): the values of
the recorded nodes, in creation order. -/
def run {α : Type} : Prog α → RecState × Array Value → α × RecState × Array Value
  | .pure a, (st, vals) => (a, st, vals)
  | .op o k, (st, vals) =>
    let (i, st') := st.op o
    (k i).run (st', extend π iv publicInput stream st' st.nodes.size vals)
  | .zero v k, (st, vals) => k.run ({ st with zero := st.zero.push v }, vals)
  | .nonzero v k, (st, vals) => k.run ({ st with nonzero := st.nonzero.push v }, vals)

end Run

end Prog

end RecGraph
