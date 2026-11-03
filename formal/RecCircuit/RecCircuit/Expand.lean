-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/circuit/compile.rs`
-- (`expand`), on `formal/RecGraph`'s recorder (`RecGraph.RecState`, the transcription of `record.rs`'s `Sym`:
-- hash-consing, constant folding, `x + 0`, `x · 1`, `x · 0`, `x + x` simplified, operands ordered).
import RecCircuit.Graph
import RecGraph.Record

/-!
# The graph, expanded (`compile::expand`)

The graph replayed on the recorder's symbol with every ring-switch weight computed (`ring_tower::weight_at` on
symbols, `weightSym`), so that every node is a read, a hash, a challenge, a bit field, a constant, a sum or a product.
The symbol is `RecGraph`'s `RecState` (`record.rs`'s `Sym`, which `RecGraph` proves sound: `add_val`, `mul_val`,
`bits_val`, `new_val`). The replay starts from `RecState.start`, which holds the seed: π1's recorder makes the seed
first (`Recorder::new`), so node 0 must be the seed, and then the replay is the Rust's from an empty graph.

The Rust panics, and so does this transcription (`Except.error`), on a bit field of a constant that is not an integer
(`E::bits` asserts it). It also refuses a ring weight whose map is not `towerStages = 6` long (`ring_tower::STAGES`;
`RecGraph`'s `Flock.towerWeightAt` reads six stages).
-/

namespace RecCircuit

open Primitives LeanVM.Parameters UniStatement

/-- `RecGraph`'s node as this library's (the same constructors). -/
def ofRGNode : RecGraph.Node → Node
  | .const a b d => .const a b d
  | .statement k => .statement k
  | .input o l => .input o l
  | .add a b => .add a b
  | .mul a b => .mul a b
  | .seed => .seed
  | .hash s f t => .hash s f t
  | .low h => .low h
  | .narrow h => .narrow h
  | .bits v s w => .bits v s w
  | .ringWeight k n => .ringWeight k n

/-- This library's node as `RecGraph`'s. -/
def toRGNode : Node → RecGraph.Node
  | .const a b d => .const a b d
  | .statement k => .statement k
  | .input o l => .input o l
  | .add a b => .add a b
  | .mul a b => .mul a b
  | .seed => .seed
  | .hash s f t => .hash s f t
  | .low h => .low h
  | .narrow h => .narrow h
  | .bits v s w => .bits v s w
  | .ringWeight k n => .ringWeight k n

theorem toRG_ofRG (n : RecGraph.Node) : toRGNode (ofRGNode n) = n := by cases n <;> rfl

theorem ofRG_toRG (n : Node) : ofRGNode (toRGNode n) = n := by cases n <;> rfl

/-! ## `ring_tower::weight_at` on symbols -/

/-- The recorder's state monad. -/
abbrev SM := StateM RecGraph.RecState

def symAdd (a b : ℕ) : SM ℕ := fun st => st.add a b
def symMul (a b : ℕ) : SM ℕ := fun st => st.mul a b
def symOne : SM ℕ := fun st => st.constant 1

/-- **`weight_at` on symbols** (`Scalar for Sym`): the Rust's operations, in its order (`weightAtM`). -/
def weightSym (point onePlusR map : List ℕ) : SM ℕ := weightAtM symAdd symMul symOne 0 point onePlusR map

/-- `weight_at` on symbols, run on the recorder: the weight's symbol and the recorder after it. -/
def weightRun (st : RecGraph.RecState) (point onePlusR map : List ℕ) : ℕ × RecGraph.RecState :=
  (weightSym point onePlusR map).run st

/-! ## The graph's types -/

/-- A state node (the seed, a hash): what a hash, a challenge and a narrow challenge read. -/
def Node.isState : Node → Bool
  | .seed | .hash .. => true
  | _ => false

/-- **Node `i` is well typed**: it reads only earlier nodes; a hash, a challenge and a narrow challenge read a state;
a sum, a product, a bit field and a ring weight read elements; a ring weight's kernel has `2n + 6` operands (the
point's `n` coordinates, `1 + r`'s `n`, the map's `towerStages = 6` stages). -/
def Graph.typedAt (g : Graph) (i : ℕ) : Node → Bool
  | .add a b | .mul a b => a < i && b < i && !(g.nodes.getD a default).isState && !(g.nodes.getD b default).isState
  | .bits v _ _ => v < i && !(g.nodes.getD v default).isState
  | .hash s _ _ | .low s | .narrow s => s < i && (g.nodes.getD s default).isState
  | .ringWeight k n => (g.kernels.getD k []).all (fun a => a < i && !(g.nodes.getD a default).isState) &&
      (g.kernels.getD k []).length == 2 * n + 6
  | _ => true

/-- The checks and the calls name nodes of the graph. -/
def Graph.outputsIn (g : Graph) : Bool :=
  (g.zero ++ g.nonzero).all (· < g.nodes.size) &&
    g.calls.all (·.all fun w => match w with | .node id => decide (id < g.nodes.size) | _ => true)

/-- **The graph is well typed**: node 0 is the seed (π1's recorder makes it first, `Recorder::new`), every node is
well typed, and the checks and the calls name nodes. -/
def Graph.typed (g : Graph) : Bool :=
  g.nodes.getD 0 default == .seed && (List.range g.nodes.size).all (fun i => g.typedAt i (g.nodes.getD i default)) &&
    g.outputsIn

/-! ## The expansion -/

/-- One original node replayed (`expand`'s loop body): its image and the recorder after it. -/
def expandNode (kernels : Array (List ℕ)) (map : Array ℕ) (st : RecGraph.RecState) (node : Node) :
    Except String (ℕ × RecGraph.RecState) :=
  let m := fun id => map.getD id 0
  match node with
  | .const c0 c1 c2 => pure (st.constant (eNew c0 c1 c2))
  | .statement _ | .input _ _ | .seed => pure (st.new (toRGNode node))
  | .add a b => pure (st.add (m a) (m b))
  | .mul a b => pure (st.mul (m a) (m b))
  | .hash s f t => pure (st.new (.hash (m s) f t))
  | .low h => pure (st.new (.low (m h)))
  | .narrow h => pure (st.new (.narrow (m h)))
  | .bits v shift width =>
    match st.constAt (m v) with
    | some x =>
      if F192.c1 x = 0 ∧ F192.c2 x = 0 ∧ shift < 64 then pure (st.bits (m v) shift width)
      else throw "bit field of a non-integer constant"
    | none => pure (st.bits (m v) shift width)
  | .ringWeight k n =>
    let ops := (kernels.getD k []).map m
    if ops.length = 2 * n + 6 then pure (weightRun st (ops.take n) ((ops.drop n).take n) (ops.drop (2 * n)))
    else throw "a ring weight's map has 6 stages"

/-- The replay of a list of nodes. -/
def expandList (kernels : Array (List ℕ)) :
    List Node → RecGraph.RecState × Array ℕ → Except String (RecGraph.RecState × Array ℕ)
  | [], acc => pure acc
  | n :: ns, (st, map) => do
    let (i, st') ← expandNode kernels map st n
    expandList kernels ns (st', map.push i)

/-- **The graph replayed with every ring-switch kernel expanded, and each original node's image** (`expand`). -/
def expand (g : Graph) : Except String (Array Node × Array ℕ) := do
  if g.nodes.getD 0 default != .seed then throw "node 0 is the seed (Recorder::new)"
  let (st, map) ← expandList g.kernels g.nodes.toList (RecGraph.RecState.start, #[])
  return (st.nodes.map ofRGNode, map)

end RecCircuit
