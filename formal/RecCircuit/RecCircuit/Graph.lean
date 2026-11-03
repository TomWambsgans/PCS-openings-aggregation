-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The node set is `crates/leanvm_flock_gas/src/evm/record.rs`'s
-- (`Node`, `Graph`), the call words `codegen.rs`'s (`Word`), the semantics `crates/leanvm_rec/src/eval.rs`'s
-- (`evaluate`), `transcript.rs`'s (`challenge_of`, `narrow`, `keccak_seed`), `scalar.rs`'s (`E::bits`) and
-- `ring_tower.rs`'s (`weight_at`). The constructors are branch `lean-rec-graph`'s `RecGraph.Node` (and its `narrow`,
-- π1-rec3's), so that its `evalGraph` can replace this one.
import Field.F192
import Statement.Keccak

/-!
# π1's recorded graph and its semantics

A graph's nodes in creation order, every operand an earlier node; `Graph.eval` gives each node its value on a public
input and a stream, as `eval::evaluate` does: an element of `E = F192` (`Value.e`) or, for the transcript's seed and
hashes, a 32-byte Keccak state (`Value.state`). Keccak-256 is leanerVM's (`LeanVM.Protocol.KeccakHash.keccak256`,
the digest's bytes `digestBytes`), Ethereum's.

*Until branch `lean-rec-graph` lands (`RecGraph.evalGraph`), this is the graph semantics the end theorem is stated
against; it is a transcription of the Rust's `eval::evaluate`.*
-/

namespace RecCircuit

open Primitives LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **A recorded value** (`record::Node`). Operands are indices of earlier nodes. -/
inductive Node where
  | const (c0 c1 c2 : UInt64)
  | statement (k : ℕ)
  | input (offset len : ℕ)
  | add (a b : ℕ)
  | mul (a b : ℕ)
  | seed
  | hash (state frm upto : ℕ)
  | low (h : ℕ)
  | narrow (h : ℕ)
  | bits (v shift width : ℕ)
  | ringWeight (kernel n : ℕ)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- **A word a `PCS_OPEN` call takes** (`codegen::Word`, but `Stored`). -/
inductive Word where
  | node (id : ℕ)
  | const (w : ℕ)
  | stream (at_ : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- **A recorded verifier** (`record::Graph` and what `contract::calls` reads of the recording). -/
structure Graph where
  nodes : Array Node
  zero : List ℕ
  nonzero : List ℕ
  kernels : Array (List ℕ)
  calls : List (List Word)
  streamLen : ℕ
  deriving Inhabited

/-! ## Values -/

/-- A node's value: an element of `E`, or a Keccak state's 32 bytes. -/
inductive Value where
  | e (x : F192)
  | state (s : List UInt8)
  deriving Inhabited

def Value.toE : Value → F192
  | .e x => x
  | .state _ => 0

def Value.toState : Value → List UInt8
  | .state s => s
  | .e _ => []

/-- A big-endian number of bytes (`eval::be`, on `ℕ`: exact for at most 8 bytes). -/
def beNat (bytes : List UInt8) : ℕ := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The element `c0 + c1 y + c2 y²` of three numbers' words (`E::new`, `F192.new`, each limb mod `2^64`). -/
def elemOfNats (c0 c1 c2 : ℕ) : F192 := F192.ofLimbs (F64.ofNat c0) (F64.ofNat c1) (F64.ofNat c2)

/-- Bytes `a .. a + n` of a byte string. -/
def slice (bytes : List UInt8) (a n : ℕ) : List UInt8 := (bytes.drop a).take n

/-- A read of `len` bytes at `offset` (`Node::Input`): a scalar's 24 bytes `c2 ‖ c1 ‖ c0`, a root's half, or an integer. -/
def inputValue (stream : List UInt8) (offset len : ℕ) : F192 :=
  let bytes := slice stream offset len
  if len = 24 then elemOfNats (beNat (slice bytes 16 8)) (beNat (slice bytes 8 8)) (beNat (slice bytes 0 8))
  else if len = 16 then elemOfNats (beNat (slice bytes 8 8)) (beNat (slice bytes 0 8)) 0
  else elemOfNats (beNat bytes) 0 0

/-- `challenge_of`: limb `i` the big-endian word of the state's bytes `24 − 8i .. 32 − 8i`. -/
def challengeOf (state : List UInt8) : F192 :=
  elemOfNats (beNat (slice state 24 8)) (beNat (slice state 16 8)) (beNat (slice state 8 8))

/-- `narrow`: limb 2 cut to its low 32 bits. -/
def narrowOf (state : List UInt8) : F192 :=
  elemOfNats (beNat (slice state 24 8)) (beNat (slice state 16 8)) (beNat (slice state 8 8) % 2 ^ 32)

/-- `E::bits`: `(c0 >> shift) mod 2^width` of an integer scalar (on `ℕ`; the Rust asserts `c1 = c2 = 0`,
`shift < 64`). -/
def bitsOf (x : F192) (shift width : ℕ) : F192 := elemOfNats (x.c0.toNat / 2 ^ shift % 2 ^ width) 0 0

/-- The contract's name, which the seed hashes (`leanvm_univariate::contract::NAME`). -/
def NAME : List UInt8 := "leanVM-univar-v1".toUTF8.toList

/-- `keccak_seed`: the hash of the name, π1's contract IV and the public input. -/
def keccakSeed (iv pub : List UInt8) : List UInt8 := digestBytes (keccak256 (NAME ++ iv ++ pub))

/-! ## The ring switch's weight (`ring_tower::weight_at`), over any scalar in any monad -/

section Weight

variable {S : Type} {m : Type → Type} [Monad m] (add mul : S → S → m S) (one : m S)

/-- `frobenius`: `times` squarings. -/
def frobeniusM (value : S) : ℕ → m S
  | 0 => pure value
  | t + 1 => do let v ← mul value value; frobeniusM v t

/-- The 64 products `g_k = Π_i (a_i + c_i^(2^k))`. -/
def weightGs (point onePlusR : List S) : m (Array S) := do
  let mut chain := point
  let mut g : Array S := #[]
  for k in [0:64] do
    if k > 0 then
      chain ← chain.mapM fun c => mul c c
    let mut acc ← one
    for (c, a) in chain.zip onePlusR do
      let s ← add a c
      acc ← mul acc s
    g := g.push acc
  return g

/-- `weight_at`: the products, then the map's stages folded in. -/
def weightAtM (default : S) (point onePlusR map : List S) : m S := do
  let mut g ← weightGs add mul one point onePlusR
  let mut j := 0
  for f in map do
    let step := 2 ^ j
    let mut power := f
    for t in [0:(64 + 2 * step - 1) / (2 * step)] do
      let k := t * (2 * step)
      if k > 0 then
        power ← frobeniusM mul power (2 * step)
      let t ← mul power (g.getD (k + step) default)
      let s ← add (g.getD k default) t
      g := g.set! k s
    j := j + 1
  return g.getD 0 default

end Weight

/-- `weight_at` on `E`. -/
def weightAt (point onePlusR map : List F192) : F192 :=
  Id.run (weightAtM (fun a b => pure (a + b)) (fun a b => pure (a * b)) (pure 1) 0 point onePlusR map)

/-! ## The graph's evaluation -/

/-- One node's value from the values before it (`evaluate`'s loop body). -/
def Graph.step (g : Graph) (iv pub stream : List UInt8) (values : Array Value) (node : Node) : Value :=
  let e := fun id => (values.getD id default).toE
  match node with
  | .const c0 c1 c2 => .e (F192.new c0 c1 c2)
  | .statement k => .e (elemOfNats (beNat (slice pub (8 * k) 8)) 0 0)
  | .input offset len => .e (inputValue stream offset len)
  | .add a b => .e (e a + e b)
  | .mul a b => .e (e a * e b)
  | .seed => .state (keccakSeed iv pub)
  | .hash s f t => .state (digestBytes (keccak256 ((values.getD s default).toState ++ slice stream f (t - f))))
  | .low h => .e (challengeOf (values.getD h default).toState)
  | .narrow h => .e (narrowOf (values.getD h default).toState)
  | .bits v shift width => .e (bitsOf (e v) shift width)
  | .ringWeight k n =>
    let ops := (g.kernels.getD k []).map e
    .e (weightAt (ops.take n) ((ops.drop n).take n) (ops.drop (2 * n)))

/-- **Every node's value** (`eval::evaluate`), for π1's contract IV `iv`, the public input and the stream. -/
def Graph.eval (g : Graph) (iv pub stream : List UInt8) : Array Value :=
  g.nodes.foldl (fun values node => values.push (g.step iv pub stream values node)) #[]

end RecCircuit
