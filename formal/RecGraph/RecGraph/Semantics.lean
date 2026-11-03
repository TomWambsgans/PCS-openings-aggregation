-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The node semantics are `crates/leanvm_rec/src/eval.rs`'s
-- (`evaluate`, `call_inputs`, `checks`), on `formal/UniStatement`'s definitions of the transcript (`KeccakChannel`:
-- `seedWith`, `beWordAt`, `challengeOf`, `narrowE`), the bit fields (`intBits`), the ring switch's weight
-- (`Flock.towerWeightAt`) and `PCS_OPEN`'s words (`elementWord`, `pcsCalls`).
import RecGraph.Node
import UniStatement.Rec

/-!
# The graph's meaning

`evalGraph F g iv publicInput stream`: every node's value, in creation order, for the transcript seeded by the
contract's IV and the public input, over a permutation `F` of the Keccak state in any monad (the random permutation
`π` in the model, Keccak-f[1600] deployed: the random-permutation model's style, `formal/QuotientRpm`,
`Common.RandomPermutationOracles`, as `formal/UniStatement`'s verifier is written); then what the graph outputs: the
bytes of each `PCS_OPEN` call (`Word.node` an element's word, `Word.const` a constant, `Word.stream` 32 bytes of the
stream: a root), the values required zero, the values required nonzero. A stream of another length than the graph's
has no outputs (`none`: the contract checks the calldata's length; the verifier rejects it, `StreamExhausted` or
`StreamNotConsumed`).

A node's value (`stepNode`), as `eval.rs` computes it and as `UniStatement` reads the same bytes:

* `const c0 c1 c2` is `eNew c0 c1 c2`; `statement k` the public input's big-endian word `k` (`publicWordsOf`);
* `input offset len` the stream's bytes `offset .. offset + len`: 24 an element (`nextScalar`), 16 a root's half
  (`nextRoot`), at most 8 a packed integer in limb 0 (`nextInteger`);
* `add`, `mul` are `E`'s; `bits v shift width` is `Scalar::bits` of `v`'s limb 0 (`intBits`);
* `seed` is `keccak(name ‖ IV ‖ public input)` over `F` (`seedWith`); `hash s from to` the Keccak-256 over `F` of the
  state `s`'s 32 bytes and the stream's bytes `from .. to` (`sample`); `low h` the state's challenge (`challengeOf`),
  `narrow h` that cut to 160 bits (`narrowE`, `sampleNarrow`);
* `ringWeight k n` is `ring_tower::weight_at` (`Flock.towerWeightAt`) of kernel `k`'s values: the point's `n`
  coordinates, `1 + r`'s `n`, the map.

`verifierOutputsWith` is the same outputs by `UniStatement`'s verifier (`runWithFs`, `pcsCalls`, the zeros it
collects; it requires nothing nonzero). `GraphIsVerifier` states that a graph is a verifier for every permutation, IV,
public input and stream.
-/

namespace RecGraph

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

/-- **A node's value** (`eval::Value`): an element of `E`, or (a seed or a hash) the transcript's state. -/
inductive Value where
  | elem (x : E)
  | state (d : Digest)
  deriving Inhabited

/-- The element at node `i` (`0` where there is none: never, in a well-formed graph). -/
def valE (vals : Array Value) (i : ℕ) : E :=
  match vals[i]? with
  | some (.elem x) => x
  | _ => 0

/-- The state at node `i` (zero where there is none). -/
def valState (vals : Array Value) (i : ℕ) : Digest :=
  match vals[i]? with
  | some (.state d) => d
  | _ => Vector.replicate 4 0

/-- The scalar a stream read of `len` bytes gives (`eval.rs`'s `Input`): 24 bytes an element, limbs `2, 1, 0`
big-endian; 16 a root's half, limbs `1, 0`; at most 8 a big-endian integer in limb 0. -/
def inputValue (b : Array UInt8) (len : ℕ) : E :=
  if len = 24 then eNew (beWordAt b 16) (beWordAt b 8) (beWordAt b 0)
  else if len = 16 then eNew (beWordAt b 8) (beWordAt b 0) 0
  else eK (UInt64.ofNat (b.foldl (fun acc x ↦ acc * 256 + x.toNat) 0))

/-- `Scalar::bits(x, shift, width)` on `E`: the integer `(c0 >> shift) mod 2^width` of `x`'s limb 0. -/
def bitsValue (x : E) (shift width : ℕ) : E := intBits (x.limb 0).lane.toNat shift width

/-- `ring_tower::weight_at` of a kernel's values: the point's `n` coordinates, `1 + r`'s `n`, the map. -/
def ringWeightValue (ops : List E) (n : ℕ) : E :=
  Flock.towerWeightAt (ops.take n) ((ops.drop n).take n) (ops.drop (2 * n))

/-- The 32 big-endian bytes of `w mod 2^256` (a constant word). -/
def beBytes32 (w : ℕ) : List UInt8 := (List.range 32).map fun k ↦ ((w >>> (8 * (31 - k))) % 256).toUInt8

/-- **What a graph outputs** (`eval::call_inputs`, `eval::checks`): each `PCS_OPEN` call's bytes, in call order, the
values required zero, the values required nonzero. -/
structure Outputs where
  calls : List (List UInt8)
  zeros : List E
  nonzeros : List E

instance : BEq Outputs := ⟨fun a b ↦ a.calls == b.calls && a.zeros == b.zeros && a.nonzeros == b.nonzeros⟩

/-- A call word's bytes. -/
def wordBytes (stream : Array UInt8) (vals : Array Value) : Word → List UInt8
  | .node id => elementWord (valE vals id)
  | .const w => beBytes32 w
  | .stream at_ => (stream.extract at_ (at_ + 32)).toList

/-- The outputs of a graph whose nodes have the values `vals`. -/
def outputsOf (g : Graph) (stream : Array UInt8) (vals : Array Value) : Outputs :=
  ⟨g.calls.map (·.flatMap (wordBytes stream vals)), g.zero.map (valE vals), g.nonzero.map (valE vals)⟩

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **One node's value** from the values of the nodes before it (`eval::evaluate`'s step). -/
def stepNode (kernels : Array (List ℕ)) (iv publicInput : List UInt8) (stream : Array UInt8) (vals : Array Value) :
    Node → m Value
  | .const c0 c1 c2 => pure (.elem (eNew c0 c1 c2))
  | .statement k => pure (.elem (eK (beWordAt publicInput.toArray (8 * k))))
  | .input offset len => pure (.elem (inputValue (stream.extract offset (offset + len)) len))
  | .add a b => pure (.elem (valE vals a + valE vals b))
  | .mul a b => pure (.elem (valE vals a * valE vals b))
  | .seed => Value.state <$> seedWith F iv publicInput
  | .hash s fr upto =>
    Value.state <$> keccak256With F (digestBytes (valState vals s) ++ (stream.extract fr upto).toList)
  | .low h => pure (.elem (PcsQuotient.Transcript.challengeOf (valState vals h)))
  | .narrow h => pure (.elem (narrowE (PcsQuotient.Transcript.challengeOf (valState vals h))))
  | .bits v shift width => pure (.elem (bitsValue (valE vals v) shift width))
  | .ringWeight k n => pure (.elem (ringWeightValue ((kernels.getD k []).map (valE vals)) n))

/-- The values of a list of nodes, appended to `vals` in order. -/
def evalList (kernels : Array (List ℕ)) (iv publicInput : List UInt8) (stream : Array UInt8) :
    Array Value → List Node → m (Array Value)
  | vals, [] => pure vals
  | vals, n :: ns => do
    let v ← stepNode F kernels iv publicInput stream vals n
    evalList kernels iv publicInput stream (vals.push v) ns

/-- **Every node's value** (`eval::evaluate`), in creation order. -/
def evalNodes (g : Graph) (iv publicInput : List UInt8) (stream : Array UInt8) : m (Array Value) :=
  evalList F g.kernels iv publicInput stream #[] g.nodes.toList

/-- **The graph's meaning**: on a stream of its length, its outputs, every node evaluated over `F` for the transcript
seeded by `iv` and `publicInput`; on another, none. -/
def evalGraph (g : Graph) (iv publicInput : List UInt8) (stream : Array UInt8) : m (Option Outputs) :=
  if stream.size = g.streamLen then do
    let vals ← evalNodes F g iv publicInput stream
    return some (outputsOf g stream vals)
  else return none

/-- **The same outputs, by `UniStatement`'s verifier** at a Fiat–Shamir shape (`fs`, `walk`; the main line's Flock and
the point-claim ABI): the run on the stream (`runWithFs`), and on success its `PCS_OPEN` inputs (`pcsCalls`) and the
values it collected as zeros; nothing is required nonzero. A run that ends in an error has none. -/
def verifierOutputsWith (shape : Shape) (roots : SetupRoots) (iv publicInput : List UInt8) (stream : Array UInt8)
    (fs : FsShape) (walk : Bool) : m (Option Outputs) := do
  let o ← runWithFs F shape iv publicInput stream (.flock flockMain) .point fs walk
  return match o.result with
    | .ok r => some ⟨pcsCalls shape roots r, o.chan.zeros.toList, []⟩
    | .error _ => none

end With

/-- **Graph = verifier**: for every permutation `π` of the Keccak state, every IV, public input and stream, the graph's
outputs are `UniStatement`'s verifier's at the shape, the setup roots and the Fiat–Shamir shape. For π1-rec3:
`GraphIsVerifier Emitted.graph reference referenceRoots .rec3 true`. -/
def GraphIsVerifier (g : Graph) (shape : Shape) (roots : SetupRoots) (fs : FsShape) (walk : Bool) : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv : List UInt8) (publicInput : Vector UInt8 32) (stream : Array UInt8),
    evalGraph (m := Id) (fun s ↦ pure (π s)) g iv publicInput.toList stream =
      verifierOutputsWith (m := Id) (fun s ↦ pure (π s)) shape roots iv publicInput.toList stream fs walk

/-- The graph's outputs over Keccak-f[1600] (the deployed contract's). -/
def evalGraphDeployed (g : Graph) (iv publicInput : List UInt8) (stream : Array UInt8) : Option Outputs :=
  Id.run (evalGraph (m := Id) (fun s ↦ pure (keccakF1600 s)) g iv publicInput stream)

/-- `UniStatement`'s outputs over Keccak-f[1600]. -/
def verifierOutputsDeployed (shape : Shape) (roots : SetupRoots) (iv publicInput : List UInt8) (stream : Array UInt8)
    (fs : FsShape) (walk : Bool) : Option Outputs :=
  Id.run (verifierOutputsWith (m := Id) (fun s ↦ pure (keccakF1600 s)) shape roots iv publicInput stream fs walk)

end RecGraph
