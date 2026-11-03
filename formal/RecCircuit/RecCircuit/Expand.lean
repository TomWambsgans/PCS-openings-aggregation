-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/circuit/compile.rs`
-- (`expand`) and `crates/leanvm_flock_gas/src/evm/record.rs` (`Sym`: hash-consing, its constant folding).
import RecCircuit.Graph
import Std.Data.HashMap

/-!
# The graph, expanded (`compile::expand`)

The graph replayed on the recorder's symbol with every ring-switch weight computed (`ring_tower::weight_at` on
symbols), so that every node is a read, a hash, a challenge, a bit field, a constant, a sum or a product. The symbol is
`record::Sym`: one node per distinct operation (hash-consed), sums and products of constants folded, `x + 0`, `x · 1`,
`x · 0`, `x + x` simplified, operands ordered.
-/

namespace RecCircuit

open Primitives

/-- The recorder's graph under construction. -/
structure Rec where
  nodes : Array Node := #[]
  index : Std.HashMap Node ℕ := {}

abbrev RM := StateT Rec (Except String)

namespace Sym

/-- `Sym::new`: the node's index, the existing one if it was recorded before. -/
def new (node : Node) : RM ℕ := do
  let s ← get
  match s.index.get? node with
  | some id => return id
  | none =>
    let id := s.nodes.size
    modify fun s => { s with nodes := s.nodes.push node, index := s.index.insert node id }
    return id

def constant (x : F192) : RM ℕ := new (.const x.c0 x.c1 x.c2)

def value (id : ℕ) : RM (Option F192) := do
  match (← get).nodes.getD id default with
  | .const c0 c1 c2 => return some (F192.new c0 c1 c2)
  | _ => return none

def add (a b : ℕ) : RM ℕ := do
  match ← value a, ← value b with
  | some x, some y => constant (x + y)
  | some x, _ => if x = 0 then return b else if a = b then constant 0 else new (.add (min a b) (max a b))
  | _, some y => if y = 0 then return a else if a = b then constant 0 else new (.add (min a b) (max a b))
  | none, none => if a = b then constant 0 else new (.add (min a b) (max a b))

def mul (a b : ℕ) : RM ℕ := do
  match ← value a, ← value b with
  | some x, some y => constant (x * y)
  | va, vb =>
    if va = some 0 || vb = some 0 then constant 0
    else if va = some 1 then return b
    else if vb = some 1 then return a
    else new (.mul (min a b) (max a b))

/-- `E::bits` on a constant (the Rust asserts an integer scalar). -/
def eBits (x : F192) (shift width : ℕ) : Except String F192 :=
  if x.c1 = 0 ∧ x.c2 = 0 ∧ shift < 64 then
    let mask : UInt64 := if width ≥ 64 then 0xFFFFFFFFFFFFFFFF else (1 <<< width.toUInt64) - 1
    pure (F192.new ((x.c0 >>> shift.toUInt64) &&& mask) 0 0)
  else throw "bit field of a non-integer constant"

def bits (v shift width : ℕ) : RM ℕ := do
  match ← value v with
  | some x => constant (← liftM (eBits x shift width))
  | none => new (.bits v shift (min width 255))
where
  liftM {α : Type} (e : Except String α) : RM α := match e with
    | .ok a => pure a
    | .error m => throw m

end Sym

/-- **The graph replayed with every ring-switch kernel expanded, and each original node's image** (`expand`). -/
def expand (g : Graph) : Except String (Array Node × Array ℕ) := do
  let run : RM (Array ℕ) := do
    let mut map : Array ℕ := #[]
    for node in g.nodes do
      let m := fun (id : ℕ) => map.getD id 0
      let s ← match node with
        | .const c0 c1 c2 => Sym.constant (F192.new c0 c1 c2)
        | .statement _ | .input _ _ | .seed => Sym.new node
        | .add a b => Sym.add (m a) (m b)
        | .mul a b => Sym.mul (m a) (m b)
        | .hash s f t => Sym.new (.hash (m s) f t)
        | .low h => Sym.new (.low (m h))
        | .narrow h => Sym.new (.narrow (m h))
        | .bits v shift width => Sym.bits (m v) shift width
        | .ringWeight k n => do
          let ops := (g.kernels.getD k []).map m
          weightAtM Sym.add Sym.mul (Sym.constant 1) 0 (ops.take n) ((ops.drop n).take n) (ops.drop (2 * n))
      map := map.push s
    return map
  let (map, r) ← run.run {}
  return (r.nodes, map)

end RecCircuit
