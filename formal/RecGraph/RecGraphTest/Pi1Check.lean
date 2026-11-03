-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Emitted
import RecGraph.Pi1.Verifier

/-!
# π1-rec3's program records the Rust's graph, node for node

`lake env lean ../RecGraph/RecGraphTest/Pi1Check.lean` (from `formal/EndToEnd`): `Pi1.pi1Graph` (the program
`Pi1.pi1Rec3` recorded in Lean) against `Emitted.graph` (the Rust's recording, written by `crates/leanvm_rec`): the
nodes, the zero and nonzero checks, the kernels, the calls' words and the stream's length, each equal. Compiled
evaluation (`#eval`), not the kernel. Throws on the first difference, with the nodes around it.
-/

open RecGraph

def showNode (n : Node) : String := reprStr n

#eval show IO Unit from do
  let g := Pi1.pi1Graph
  let e := Emitted.graph
  IO.println s!"Lean recording: {g.nodes.size} nodes, {g.zero.length} zeros, {g.nonzero.length} nonzeros, \
    {g.kernels.size} kernels, {g.calls.length} calls, stream {g.streamLen}"
  IO.println s!"Rust recording: {e.nodes.size} nodes, {e.zero.length} zeros, {e.nonzero.length} nonzeros, \
    {e.kernels.size} kernels, {e.calls.length} calls, stream {e.streamLen}"
  let n := min g.nodes.size e.nodes.size
  let first := (List.range n).find? fun i ↦ g.nodes[i]! != e.nodes[i]!
  match first with
  | some i =>
    IO.println s!"first different node: {i}"
    for j in [i - min i 12 : min n (i + 6)] do
      IO.println s!"  {j}: Lean {showNode g.nodes[j]!}   Rust {showNode e.nodes[j]!}"
    throw (IO.userError "the nodes differ")
  | none =>
    if g.nodes.size != e.nodes.size then
      IO.println s!"one is a prefix of the other ({g.nodes.size} against {e.nodes.size})"
      throw (IO.userError "the node counts differ")
  IO.println s!"the {n} nodes are equal"
  if g.zero != e.zero then throw (IO.userError s!"zeros: Lean {g.zero}, Rust {e.zero}")
  if g.nonzero != e.nonzero then throw (IO.userError s!"nonzeros: Lean {g.nonzero}, Rust {e.nonzero}")
  if g.kernels != e.kernels then throw (IO.userError "kernels differ")
  if g.calls != e.calls then
    for (a, b) in g.calls.zip e.calls do
      if a != b then
        IO.println s!"call: Lean {reprStr a}"
        IO.println s!"      Rust {reprStr b}"
    throw (IO.userError "calls differ")
  if g.streamLen != e.streamLen then throw (IO.userError "stream lengths differ")
  IO.println "the zeros, nonzeros, kernels, calls and stream length are equal: pi1Graph = Emitted.graph"
