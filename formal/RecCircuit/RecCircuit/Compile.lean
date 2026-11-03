-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/circuit/compile.rs`
-- (`compile` with `D16::new`, `pair_coordinate`, `be_bits`, `le_bits`), `crates/leanvm_rec/src/count.rs` (`live`) and
-- `crates/leanvm_flock_gas/src/evm/machine.rs` (`root_word`, `element_word`), `transcript.rs` (`cantor_beta1`).
import RecCircuit.Templates
import RecCircuit.Expand

/-!
# The compiler (`compile.rs`)

`compile r`: π1's recorded verifier `r` (its graph, where its roots are in the stream, π1's contract IV) to π2's
circuit in D16v (`pi2(recorded, Layout::D16v, ·)`), and what the checker and the theorems read: the final view, the
builder's traces, each node's limbs, the free bits. Every step is the Rust's, in the Rust's order (regions, rows, values
and `κ` are made in the same order, so the circuit is the same, which `RecCircuitTest` compares); the witness is not
computed (it is the Rust's, for the honest prover), so neither are the free bits' and free limbs' words.

**Deviations, all rejections** (the Rust would build a circuit; the Lean compiler refuses the graph, and π1-rec3's graph
has none of them): a read never hashed must be a 24-byte scalar (`compile.rs` makes the free limbs of a shorter one
free values, so their `c1`, `c2` limbs would be unconstrained, while the graph's are zero); a bit field's integer must
be at most 8 bytes (for a wider read, the circuit's field could take bits past the low limb that `E::bits` ignores).
-/

namespace RecCircuit

open Primitives

/-- π1's recorded verifier, as the compiler takes it (`Recorded`). -/
structure Recorded where
  graph : Graph
  /-- Where each of π1's roots starts in the stream (`roots_at`). -/
  rootsAt : List ℕ
  /-- π1's contract IV, which the seed hashes (`recorded.iv(program_iv)`). -/
  iv : List UInt8
  deriving Inhabited

/-- The bits of a big-endian integer of `nbytes` bytes from byte `first`, as `(exponent, bit)` (`be_bits`). -/
def beBits {α : Type} (bit : ℕ → α) (first nbytes : ℕ) : List (ℕ × α) :=
  (List.range (8 * nbytes)).map fun e => (e, bit (8 * (first + nbytes - 1 - e / 8) + e % 8))

/-- The bits of a little-endian integer (`le_bits`). -/
def leBits {α : Type} (bit : ℕ → α) (first nbytes : ℕ) : List (ℕ × α) :=
  (List.range (8 * nbytes)).map fun e => (e, bit (8 * (first + e / 8) + e % 8))

/-- A number's 32 big-endian bytes. -/
def wordBytes32 (w : ℕ) : List UInt8 := (List.range 32).map fun i => (w / 256 ^ (31 - i) % 256).toUInt8

def bytesWord (bytes : List UInt8) : ℕ := beNat bytes

/-- `root_word`: each 16-byte half reversed. -/
def rootWord (w : ℕ) : ℕ :=
  let b := wordBytes32 w
  bytesWord ((b.take 16).reverse ++ (b.drop 16).reverse)

/-- `element_word`: `c0 + c1·2^64 + c2·2^128`. -/
def elementWord (x : F192) : ℕ := x.c0.toNat + x.c1.toNat * 2 ^ 64 + x.c2.toNat * 2 ^ 128

/-- The nodes `outputs` read, through their operands (`count::live`). -/
def live (nodes : Array Node) (outputs : List ℕ) : Array Bool := Id.run do
  let mut live := Array.replicate nodes.size false
  for o in outputs do live := live.set! o true
  for i' in [0:nodes.size] do
    let i := nodes.size - 1 - i'
    if live.getD i false then
      match nodes.getD i default with
      | .add a b | .mul a b => live := (live.set! a true).set! b true
      | .hash s _ _ => live := live.set! s true
      | .low h | .narrow h | .bits h _ _ => live := live.set! h true
      | _ => pure ()
  return live

/-- A challenge node (`pair_coordinate`'s `is_challenge`). -/
def pairChallenge (nodes : Array Node) (z : ℕ) : Bool :=
  match nodes.getD z default with
  | .narrow _ | .low _ => true
  | _ => false

/-- `pair_coordinate`'s `y1_of`: node `i` is `y_1(z) = z·z + z` of a challenge `z`. -/
def pairY1 (nodes : Array Node) (i : ℕ) : Option ℕ :=
  match nodes.getD i default with
  | .add a b => [(a, b), (b, a)].findSome? fun (sq, z) => match nodes.getD sq default with
    | .mul x y => if x = z ∧ y = z ∧ pairChallenge nodes z = true then some z else none
    | _ => none
  | _ => none

/-- `pair_coordinate`: a call word's node `y_1(z) = z·z + z` or `y_0(z) = z + β_1 · y_1(z)` of a challenge `z`
(`β_1` is `UniStatement.cantorBeta1`, `transcript::cantor_beta1`). -/
def pairCoordinate (nodes : Array Node) (id : ℕ) : Option (ℕ × ℕ) :=
  match pairY1 nodes id with
  | some z => some (z, 1)
  | none => match nodes.getD id default with
    | .add a b => [(a, b), (b, a)].findSome? fun (z, product) => match nodes.getD product default with
      | .mul c y => [(c, y), (y, c)].findSome? fun (c, y) => match nodes.getD c default with
        | .const l0 l1 l2 => if F192.new l0 l1 l2 = UniStatement.cantorBeta1 ∧ pairY1 nodes y = some z then some (z, 0) else none
        | _ => none
      | _ => none
    | _ => none

/-- What the compiler returns: the circuit, the final view, the builder's final state (its traces), and per node of
the expanded graph its limbs and digest. -/
structure Compiled where
  circuit : Circuit
  view : View
  st : St
  nodes : Array Node
  map : Array ℕ
  live : Array Bool
  /-- An element node's three limb values. -/
  limbs : Array (Option (Array Val))
  /-- A seed's or hash's 256 digest values. -/
  digests : Array (Option (Array Val))
  /-- Each stream bit's free bit (`none`: not hashed), and each public-input bit's. -/
  bitSelf : Array (Option Val)
  /-- A first-block stream bit's copy, and each public-input bit's. -/
  bitCopy : Array (Option Val)
  publicSelf : Array Val
  publicCopy : Array Val
  /-- The never-hashed reads: offset and their three free limbs. -/
  freeReads : Array (ℕ × Array Val)
  statementLimb : Array Val
  /-- Each root's four limbs (as its port carries them). -/
  rootLimbs : Array (Array Val)
  /-- The zero checks' nodes (mapped), the calls' element nodes (by element index). -/
  zero : List ℕ
  elementNodes : Array ℕ
  deriving Inhabited

namespace Builder

def constantBits (bytes : List UInt8) : Array Bit :=
  ((List.range (8 * bytes.length)).map fun i =>
    if (bytes.getD (i / 8) 0).toNat.testBit (i % 8) then Bit.one else Bit.zero).toArray

/-- **π2's circuit for `r` in D16v** (`compile(recorded, 4, D16::new, ·)`). -/
def compileM (r : Recorded) (g : Array Node) (map : Array ℕ) : BM Compiled := do
  let streamLen := r.graph.streamLen
  let mapW := fun (w : Word) => match w with
    | .node id => Word.node (map.getD id 0)
    | other => other
  let callWords := r.graph.calls.map (·.map mapW)
  let zero := r.graph.zero.map fun id => map.getD id 0
  need r.graph.nonzero.isEmpty "π1's verifier checks nothing nonzero"
  let outputs := (callWords.flatten.filterMap fun w => match w with | .node id => some id | _ => none) ++ zero
  let live := RecCircuit.live g outputs
  initD16
  initXors
  initBools
  initPacker
  initArith
  initPorts
  -- The stream's hashed bytes, and those in a call's first block.
  let mut hashed := Array.replicate streamLen false
  let mut firstBlock := Array.replicate streamLen false
  for id in [0:g.size] do
    if live.getD id false then
      match g.getD id default with
      | .hash _ f t =>
        for i in [f:t] do hashed := hashed.set! i true
        for i in [f:min t (f + 136 - 32)] do firstBlock := firstBlock.set! i true
      | _ => pure ()
  -- Free bits: the stream's hashed bytes', then the public input's.
  let mut bitSelf : Array (Option Val) := Array.replicate (8 * streamLen) none
  let mut bitCopy : Array (Option Val) := Array.replicate (8 * streamLen) none
  for i in [0:streamLen] do
    if hashed.getD i false then
      for j in [0:8] do
        let (v, c) ← bitAndCopy
        bitSelf := bitSelf.set! (8 * i + j) (some v)
        if firstBlock.getD i false then bitCopy := bitCopy.set! (8 * i + j) (some c)
  let mut publicSelf : Array Val := #[]
  let mut publicCopy : Array Val := #[]
  for _ in [0:256] do
    let (v, c) ← bitAndCopy
    publicSelf := publicSelf.push v
    publicCopy := publicCopy.push c
  let streamBit := fun (i : ℕ) => (bitSelf.getD i none).getD NONE
  -- Keccak-256 calls, in the chain's order.
  let mut digests : Array (Option (Array Val)) := Array.replicate g.size none
  for id in [0:g.size] do
    if live.getD id false then
      match g.getD id default with
      | .seed =>
        let message := constantBits NAME ++ constantBits r.iv ++ publicCopy.map Bit.v
        digests := digests.set! id (some (← keccak256 message))
      | .hash s f t =>
        let state := (digests.getD s none).getD #[]
        let mut message : Array Bit := state.map Bit.v
        for i in [f:t] do
          for j in [0:8] do
            let k := 8 * i + j
            match bitCopy.getD k none with
            | some c => message := message.push (.v c)
            | none =>
              need ((bitSelf.getD k none).isSome) "a hashed bit"
              message := message.push (.v (streamBit k))
        digests := digests.set! id (some (← keccak256 message))
      | _ => pure ()
  -- The statement's limbs, packed once.
  let mut statementLimb : Array Val := #[]
  for k in [0:4] do
    statementLimb := statementLimb.push (← pack (beBits (fun i => publicSelf.getD i 0) (8 * k) 8))
  -- Uses left of each node.
  let mut uses : Array ℕ := Array.replicate g.size 0
  for id in [0:g.size] do
    if live.getD id false then
      match g.getD id default with
      | .add a c | .mul a c =>
        uses := uses.modify a (· + 1)
        if a != c then uses := uses.modify c (· + 1)
      | _ => pure ()
  -- Element nodes' limbs, in node order.
  let mut limbs : Array (Option (Array Val)) := Array.replicate g.size none
  let mut endable : Array Bool := Array.replicate g.size false
  let mut freeReads : Array (ℕ × Array Val) := #[]
  for id in [0:g.size] do
    if live.getD id false then
      let node := g.getD id default
      let res : Option (Array Val × Bool) ← match node with
        | .const c0 c1 c2 => do
          let a ← fresh (F64.ofU64 c0)
          let b ← fresh (F64.ofU64 c1)
          let c ← fresh (F64.ofU64 c2)
          pure (some (#[a, b, c], true))
        | .statement k => do
          let z1 ← fresh 0
          let z2 ← fresh 0
          pure (some (#[statementLimb.getD k 0, z1, z2], true))
        | .input offset len => do
          let allHashed := (List.range len).all fun i => hashed.getD (offset + i) false
          need (allHashed || (List.range len).all fun i => !hashed.getD (offset + i) false) "a read partly hashed"
          if !allHashed then
            need (len == 24) "a read never hashed is a 24-byte scalar (Lean compiler's check)"
            let l0 ← free
            let l1 ← free
            let l2 ← free
            freeReads := freeReads.push (offset, #[l0, l1, l2])
            pure (some (#[l0, l1, l2], false))
          else
            let pk := fun (first n : ℕ) => pack (beBits streamBit first n)
            if len == 24 then do
              let a ← pk (offset + 16) 8
              let b ← pk (offset + 8) 8
              let c ← pk offset 8
              pure (some (#[a, b, c], true))
            else if len == 16 then do
              let c0 ← pk (offset + 8) 8
              let c1 ← pk offset 8
              let z ← fresh 0
              pure (some (#[c0, c1, z], true))
            else do
              let c0 ← pk offset len
              let z1 ← fresh 0
              let z2 ← fresh 0
              pure (some (#[c0, z1, z2], true))
        | .low h => do
          let d := (digests.getD h none).getD #[]
          let db := fun i => d.getD i 0
          let l0 ← pack (beBits db 24 8)
          let l1 ← pack (beBits db 16 8)
          let l2 ← pack (beBits db 8 8)
          pure (some (#[l0, l1, l2], true))
        | .narrow h => do
          let d := (digests.getD h none).getD #[]
          let db := fun i => d.getD i 0
          let l0 ← pack (beBits db 24 8)
          let l1 ← pack (beBits db 16 8)
          let l2 ← pack (beBits db 12 4)
          pure (some (#[l0, l1, l2], true))
        | .bits v shift width => do
          let (offset, len) ← match g.getD v default with
            | .input offset len => pure (offset, len)
            | _ => throw "a bit field of a read integer"
          need (len ≤ 8) "a bit field of an integer of at most 8 bytes (Lean compiler's check)"
          let field := (beBits streamBit offset len).filterMap fun (e, x) =>
            if shift ≤ e && e < shift + width then some (e - shift, x) else none
          let z1 ← fresh 0
          let z2 ← fresh 0
          match field with
          | [] => do
            let z ← fresh 0
            pure (some (#[z, z1, z2], true))
          | [(0, x)] => pure (some (#[x, z1, z2], false))
          | _ => do
            let p ← pack field
            pure (some (#[p, z1, z2], true))
        | .add x y | .mul x y => do
          let op := match node with
            | .add .. => Op.add
            | _ => if x == y then Op.square else Op.mul
          let lx := (limbs.getD x none).getD #[]
          let ly := (limbs.getD y none).getD #[]
          let (ex, ey) := (endable.getD x false, endable.getD y false)
          let endX := ex && (!ey || uses.getD x 0 ≤ uses.getD y 0)
          let (a, c, en, ended) :=
            if op == .square then (lx, lx, ex, x)
            else if endX then (lx, ly, true, x)
            else if ey then (ly, lx, true, y)
            else (lx, ly, false, x)
          if en then endable := endable.set! ended false
          uses := uses.modify x (· - 1)
          if x != y then uses := uses.modify y (· - 1)
          pure (some (← arith op a c en, true))
        | .seed | .hash .. => pure none
        | .ringWeight .. => throw "expanded"
      match res with
      | some (l, canEnd) =>
        limbs := limbs.set! id (some l)
        endable := endable.set! id canEnd
      | none => pure ()
  -- Ports: the zero checks first, padded to a power of two; the statement, the roots, the calls' elements.
  let mut zeroPorts := 0
  for id in zero do
    match g.getD id default with
    | .const c0 c1 c2 => need (c0 == 0 && c1 == 0 && c2 == 0) "a zero check on a nonzero constant"
    | _ =>
      portOf ((limbs.getD id none).getD #[]) .zero
      zeroPorts := zeroPorts + 1
  if zeroPorts > 1 then
    for _ in [zeroPorts:nextPow2 zeroPorts] do
      let a ← fresh 0
      let b ← fresh 0
      let c ← fresh 0
      portOf #[a, b, c] .pad
  portOf statementLimb .statement
  let mut rootOf : List (ℕ × ℕ) := []
  let mut nRoots := 0
  let mut rootLimbs : Array (Array Val) := #[]
  for at_ in r.rootsAt do
    need ((List.range 32).all fun i => hashed.getD (at_ + i) false) "a root is hashed"
    let mut rl : Array Val := #[]
    for first in [16, 24, 0, 8] do
      rl := rl.push (← pack (leBits streamBit (at_ + first) 8))
    rootOf := rootOf ++ [(at_, nRoots)]
    rootLimbs := rootLimbs.push rl
    portOf rl (.root nRoots)
    nRoots := nRoots + 1
  let mut elementNodes : Array ℕ := #[]
  let mut circuitCalls : List (List CallWord) := []
  for call in callWords do
    let mut words : List CallWord := []
    let mut k := 0
    for w in call do
      let cw ← match w with
        | .const bytes => pure (if k == 0 then CallWord.const (rootWord bytes) else CallWord.const bytes)
        | .stream at_ => match rootOf.lookup at_ with
          | some i => pure (CallWord.root i)
          | none => throw "a stream word that is no root"
        | .node id =>
          match g.getD id default, pairCoordinate g id with
          | .const c0 c1 c2, _ => pure (CallWord.const (elementWord (F192.new c0 c1 c2)))
          | _, some (z, coordinate) => do
            let e ← match elementNodes.findIdx? (· == z) with
              | some e => pure e
              | none => do
                elementNodes := elementNodes.push z
                pure (elementNodes.size - 1)
            pure (CallWord.pair e coordinate)
          | _, none => do
            let e ← match elementNodes.findIdx? (· == id) with
              | some e => pure e
              | none => do
                elementNodes := elementNodes.push id
                pure (elementNodes.size - 1)
            pure (CallWord.element e)
      words := words ++ [cw]
      k := k + 1
    circuitCalls := circuitCalls ++ [words]
  for e in [0:elementNodes.size] do
    portOf ((limbs.getD (elementNodes.getD e 0) none).getD #[]) (.element e)
  modify fun s => { s with calls := circuitCalls }
  let (circuit, view) ← finish
  return ⟨circuit, view, ← get, g, map, live, limbs, digests, bitSelf, bitCopy, publicSelf, publicCopy, freeReads,
    statementLimb, rootLimbs, zero, elementNodes⟩

end Builder

/-- **The compiler**: π1's recorded verifier to π2's circuit (D16v), or why the Rust would panic (or the Lean
compiler refuses the graph). -/
def compileRaw (r : Recorded) : Except String Compiled := do
  if !r.graph.typed then throw "the graph is not well typed"
  let (g, map) ← expand r.graph
  let (c, _) ← (Builder.compileM r g map).run { logWidth := 4 }
  return { c with nodes := g, map := map }

end RecCircuit
