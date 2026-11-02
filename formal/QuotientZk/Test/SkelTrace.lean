-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The Lean half of the differential test of `QuotientZk.Deployed.skel` against the Rust prover; the
-- Rust half, which writes this driver's input and compares its output with the prover's own record,
-- is `crates/quotient/tests/skel_trace.rs`. The oracle is leanerVM `mumbai`'s Keccak-256 and
-- Keccak-f[1600] (`Statement.Keccak`, compiled through the proved `@[csimp]` lemmas of
-- `Statement.Fast.Keccak`; https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR
-- Apache-2.0).
import QuotientZk.Deployed.Skeleton
import Statement.Fast.Keccak

/-!
# Running the skeleton on the Rust prover's data

`skel sh` is run as it is compiled (no restatement), every operation answered by a concrete
implementation (`implD`):

* `pub`/`chal` on bytes: Keccak-256 (`LeanVM.Protocol.KeccakHash.keccak256`), the digest's 32 bytes;
* `pub`/`chal` on a state: Keccak-f[1600] (`LeanVM.Semantics.keccakF1600`);
* `leaf k x`: the Rust tree's digest at leaf `x` of table `k` (the rows are the prover's secret, the
  skeleton never sees them);
* `msg`: the next message of the input, which the Rust half cut from the prover's own transcript.

Every operation is written to the trace, one line each (runs of grinding tries and of consecutive
secret leaves as one line); the proof `skel` returns is written to a second file. The Rust half
compares both with what the prover did. The shape `sh` is read from the input (the Rust half derives
it from the WHIR configuration, the same derivation `deployedShape` is checked against at `2^22`);
the IV prefix is built by the skeleton's own `ivPrefix`.

Lines: `H len out [in]` (`pub` Keccak-256; the input when it is no tree's), `C len in out` (`chal`
Keccak-256), `F in out` (`pub` permutation), `X in out` (`chal` permutation), `G first last count in
out` (consecutive grinding tries, the last one's state), `L k from to` (secret leaves), `M i items`
(a message). A state is its 25 lanes, each 16 hexadecimal digits, lane 0 first.
-/

open OracleComp OracleSpec QuotientRpm

namespace QuotientZk.Test.SkelTrace

open QuotientZk.Deployed

/-! ## Hexadecimal -/

def hexChars : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

def pushByte (s : String) (b : UInt8) : String :=
  (s.push (hexChars.getD (b >>> 4).toNat '0')).push (hexChars.getD (b &&& 15).toNat '0')

def hexBytes (l : List UInt8) : String := l.foldl pushByte ""

/-- A word as 16 hexadecimal digits, most significant first. -/
def pushWord (s : String) (w : UInt64) : String :=
  (List.range 8).foldl (fun s k => pushByte s (w >>> (8 * (7 - k)).toUInt64).toUInt8) s

def hexState (x : KSt) : String := x.toList.foldl pushWord ""

def hexLimbs (x : Limbs) : String := s!"{pushWord "" x.1} {pushWord "" x.2.1} {pushWord "" x.2.2}"

/-! ## Reading the input -/

/-- The little-endian word at byte `p`. -/
def u64At (b : ByteArray) (p : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc k => acc ||| ((b.get! (p + k)).toUInt64 <<< (8 * k).toUInt64)) 0

def natAt (b : ByteArray) (p : Nat) : Nat := (u64At b p).toNat

def bytesAt (b : ByteArray) (p n : Nat) : List UInt8 := (b.extract p (p + n)).toList

def b32At (b : ByteArray) (p : Nat) : Bytes32 := Vector.ofFn fun i : Fin 32 => b.get! (p + i)

/-- `n` length-prefixed byte strings from `p`. -/
def rowsAt (b : ByteArray) (p n : Nat) : List (List UInt8) × Nat := Id.run do
  let mut p := p
  let mut acc : Array (List UInt8) := #[]
  for _ in [0:n] do
    let len := natAt b p
    acc := acc.push (bytesAt b (p + 8) len)
    p := p + 8 + len
  return (acc.toList, p)

/-- `n` words from `p`. -/
def wordsAt (b : ByteArray) (p n : Nat) : List UInt64 := Id.run do
  let mut acc : Array UInt64 := #[]
  for i in [0:n] do
    acc := acc.push (u64At b (p + 8 * i))
  return acc.toList

/-- `n` naturals (words) from `p`. -/
def natsAt (b : ByteArray) (p n : Nat) : List Nat := (wordsAt b p n).map (·.toNat)

/-- A message: its items, each a tag (`0` scalars, `1` rows, `2` opened rows, `3` bytes) and its data. -/
def msgAt (b : ByteArray) (p : Nat) : Msg × Nat := Id.run do
  let n := natAt b p
  let mut p := p + 8
  let mut items : Array Item := #[]
  for _ in [0:n] do
    let tag := natAt b p
    let k := natAt b (p + 8)
    p := p + 16
    if tag = 0 then
      let ws := (wordsAt b p (3 * k)).toArray
      items := items.push (.scalars ((List.range k).map fun i =>
        (ws.getD (3 * i) 0, ws.getD (3 * i + 1) 0, ws.getD (3 * i + 2) 0)))
      p := p + 24 * k
    else if tag = 1 then
      let (rows, q) := rowsAt b p k
      items := items.push (.rows rows)
      p := q
    else if tag = 2 then
      let mut rows : Array (List UInt64) := #[]
      for _ in [0:k] do
        let len := natAt b p
        rows := rows.push (wordsAt b (p + 8) len)
        p := p + 8 + 8 * len
      items := items.push (.opened rows.toList)
    else
      items := items.push (.bytes (bytesAt b p k))
      p := p + k
  return (items.toList, p)

/-- One opening's shape as the input gives it. -/
structure InShape where
  layoutId : Bytes32
  logN : Nat
  secret : Nat
  depth₀ : Nat
  depth₁ : Nat
  ood₀ : Nat
  levels : List (Nat × Nat × Nat)
  queries : List Nat
  lastFolds : Nat
  residualVars : Nat
  rows : List (List UInt8)

/-- A shape: the layout's id, then `log_n`, the table (`0`, `1`, `2` for none), `depth₀`, `depth₁`,
`ood₀`, the levels (their number, then three words each), the queries (their number, then each),
`lastFolds`, `residualVars`, the public rows (their number, then each). -/
def shapeAt (b : ByteArray) (p : Nat) : InShape × Nat := Id.run do
  let id := b32At b p
  let w := natsAt b (p + 32) 6
  let nl := w.getD 5 0
  let lv := natsAt b (p + 32 + 48) (3 * nl)
  let p := p + 32 + 48 + 24 * nl
  let nq := natAt b p
  let qs := natsAt b (p + 8) nq
  let p := p + 8 + 8 * nq
  let tail := natsAt b p 3
  let (rows, p) := rowsAt b (p + 24) (tail.getD 2 0)
  return (⟨id, w.getD 0 0, w.getD 1 0, w.getD 2 0, w.getD 3 0, w.getD 4 0,
    (List.range nl).map (fun i => (lv.getD (3 * i) 0, lv.getD (3 * i + 1) 0, lv.getD (3 * i + 2) 0)),
    qs, tail.getD 0 0, tail.getD 1 0, rows⟩, p)

/-- The skeleton's shape of an opening: the IV prefix by the skeleton's own `ivPrefix`. -/
def InShape.toOpen (s : InShape) : OpenShape where
  ivPrefix := ivPrefix s.layoutId s.logN
  secret := if s.secret = 0 then some 0 else if s.secret = 1 then some 1 else none
  pubRows := s.rows
  depth₀ := s.depth₀
  depth₁ := s.depth₁
  ood₀ := s.ood₀
  levels := s.levels
  queries := s.queries
  lastFolds := s.lastFolds
  residualVars := s.residualVars

/-- `n` digests from `p`. -/
def digestsAt (b : ByteArray) (p n : Nat) : Array Bytes32 := Id.run do
  let mut acc : Array Bytes32 := Array.mkEmpty n
  for i in [0:n] do
    acc := acc.push (b32At b (p + 32 * i))
  return acc

/-- The input: the statement, the ids of the `2^22` layouts (for `deployedShape`), the three shapes,
the two secret tables' leaf digests, and where the messages start and how many there are. -/
structure Input where
  st : Statement
  ids22 : List Bytes32
  shapes : List InShape
  leaves : Array (Array Bytes32)
  msgPos : Nat
  msgCount : Nat

def inputAt (b : ByteArray) : Except String Input := do
  if bytesAt b 0 8 ≠ "SKELIN01".toUTF8.toList then throw "not a skeleton input"
  let st : Statement := ⟨b32At b 8, Vector.ofFn fun i : Fin 64 => b.get! (40 + i)⟩
  let ids22 := (List.range 3).map fun i => b32At b (104 + 32 * i)
  let (s0, p) := shapeAt b 200
  let (s1, p) := shapeAt b p
  let (s2, p) := shapeAt b p
  let n0 := natAt b p
  let l0 := digestsAt b (p + 8) n0
  let p := p + 8 + 32 * n0
  let n1 := natAt b p
  let l1 := digestsAt b (p + 8) n1
  let p := p + 8 + 32 * n1
  return ⟨st, ids22, [s0, s1, s2], #[l0, l1], p + 8, natAt b p⟩

/-! ## The implementation -/

/-- Consecutive grinding tries: the state with the nonce's lane zeroed, the nonces, the last try. -/
structure GrindRun where
  base : KSt
  first : UInt64
  last : UInt64
  count : Nat
  lastIn : KSt
  lastOut : KSt

structure DState where
  buf : ByteArray
  pos : Nat
  msgsLeft : Nat
  msgIdx : Nat
  leaves : Array (Array Bytes32)
  grind : Option GrindRun
  leafRun : Option (Nat × Nat × Nat)
  out : IO.FS.Handle
  /-- Operations of each kind: `H C F X tries L M`. -/
  counts : Array Nat
  errors : Array String

abbrev DM := StateT DState IO

def emit (s : String) : DM Unit := do (← get).out.putStrLn s

def bump (i : Nat) : DM Unit := modify fun st => { st with counts := st.counts.modify i (· + 1) }

def flushRuns : DM Unit := do
  let st ← get
  if let some g := st.grind then
    emit s!"G {g.first} {g.last} {g.count} {hexState g.lastIn} {hexState g.lastOut}"
  if let some (k, a, b) := st.leafRun then
    emit s!"L {k} {a} {b}"
  modify fun st => { st with grind := none, leafRun := none }

/-- The waiting scalars of a permutation's input: the scalars whose tag lane is nonzero. -/
def pending (x : KSt) : Nat :=
  let l := fun i => x.toArray.getD i 0
  if l 3 = 0 then 0 else if l 7 = 0 then 1 else if l 11 = 0 then 2 else if l 15 = 0 then 3 else 4

/-- A grinding try: its last waiting scalar is a nonce (tag `4`, `(n, 0, 0)`); the state with its
nonce lane zeroed and the nonce. -/
def grindTry? (x : KSt) : Option (KSt × UInt64) :=
  let p := pending x
  let l := fun i => x.toArray.getD i 0
  if p = 0 then none
  else
    let i := 4 * (p - 1)
    if l (i + 3) = 4 ∧ l (i + 1) = 0 ∧ l (i + 2) = 0 then some (x.setIfInBounds i 0, l i) else none

def keccak (m : List UInt8) : Bytes32 := (LeanVM.Protocol.KeccakHash.keccak256 m).toBytes

/-- Inputs of these lengths are the trees' (leaves of `2^4` extension elements, `64` words, nodes):
their bytes are not written. -/
def treeLen (n : Nat) : Bool := n = 64 || n = 384 || n = 512

def implD : QueryImpl DSpec DM
  | .pub (.inl m) => do
    flushRuns
    bump 0
    let d := keccak m
    let n := m.length
    emit (if treeLen n then s!"H {n} {hexBytes d.toList}"
      else s!"H {n} {hexBytes d.toList} {hexBytes m}")
    return (d, default)
  | .pub (.inr x) => do
    let y := LeanVM.Semantics.keccakF1600 x
    match grindTry? x with
    | some (base, n) =>
      bump 4
      let st ← get
      if st.leafRun.isSome then flushRuns
      match (← get).grind with
      | some g =>
        if g.base = base ∧ n = g.last + 1 then
          let next : GrindRun := ⟨g.base, g.first, n, g.count + 1, x, y⟩
          modify fun st => { st with grind := some next }
        else
          flushRuns
          modify fun st => { st with grind := some ⟨base, n, n, 1, x, y⟩ }
      | none => modify fun st => { st with grind := some ⟨base, n, n, 1, x, y⟩ }
    | none =>
      flushRuns
      bump 2
      emit s!"F {hexState x} {hexState y}"
    return (default, y)
  | .chal (.inl m) => do
    flushRuns
    bump 1
    let d := keccak m
    emit s!"C {m.length} {hexBytes m} {hexBytes d.toList}"
    return (d, default)
  | .chal (.inr x) => do
    flushRuns
    bump 3
    let y := LeanVM.Semantics.keccakF1600 x
    emit s!"X {hexState x} {hexState y}"
    return (default, y)
  | .leaf k x => do
    bump 5
    let st ← get
    if st.grind.isSome then flushRuns
    let (kn, xn) := (k.val, x.val)
    match (← get).leafRun with
    | some (k', a, b) =>
      if k' = kn ∧ xn = b + 1 then modify fun st => { st with leafRun := some (k', a, xn) }
      else
        flushRuns
        modify fun st => { st with leafRun := some (kn, xn, xn) }
    | none => modify fun st => { st with leafRun := some (kn, xn, xn) }
    let st ← get
    match (st.leaves.getD kn #[])[xn]? with
    | some d => return (d, default)
    | none =>
      modify fun st => { st with errors := st.errors.push s!"leaf {kn} {xn}: no digest" }
      return (default, default)
  | .msg => do
    flushRuns
    bump 6
    let st ← get
    if st.msgsLeft = 0 then
      emit "M none"
      modify fun st => { st with errors := st.errors.push s!"message {st.msgIdx}: none left" }
      return []
    let (m, p) := msgAt st.buf st.pos
    set { st with pos := p, msgsLeft := st.msgsLeft - 1, msgIdx := st.msgIdx + 1 }
    emit s!"M {st.msgIdx} {m.length}"
    return m

/-- Run an operation program against `implD`, one operation at a time (a loop, so that millions of
operations take no stack). -/
partial def runLoop {α : Type} (oa : OracleComp DSpec α) (st : DState) : IO (α × DState) :=
  match oa with
  | .pure a => pure (a, st)
  | .liftBind q k => do
    let (u, st) ← implD q st
    runLoop (k u) st

/-! ## Output -/

def writeProof (h : IO.FS.Handle) (p : Proof) : IO Unit := do
  h.putStrLn s!"wRoot {hexBytes p.wRoot.toList}"
  h.putStrLn s!"qRoot {hexBytes p.qRoot.toList}"
  for v in p.values do h.putStrLn s!"value {hexLimbs v}"
  for (i, (stream, merkle)) in (List.range p.openings.length).zip p.openings do
    h.putStrLn s!"opening {i} stream {stream.length}"
    for x in stream do h.putStrLn s!"s {hexLimbs x}"
    for (j, (pos, opened, sib)) in (List.range merkle.length).zip merkle do
      let ps := " ".intercalate (pos.map toString)
      let ss := " ".intercalate (sib.map fun d => hexBytes d.toList)
      h.putStrLn s!"merkle {i} {j} positions {pos.length} {ps}"
      h.putStrLn s!"merkle {i} {j} opened {opened.length}"
      h.putStrLn s!"merkle {i} {j} siblings {sib.length} {ss}"

/-- An opening shape's numbers, in the Rust half's format. -/
def shapeLine (s : OpenShape) : String :=
  let lv := ";".intercalate (s.levels.map fun (a, b, c) => s!"{a},{b},{c}")
  let qs := ",".intercalate (s.queries.map toString)
  let sec := match s.secret with | some k => toString k.val | none => "none"
  s!"secret={sec} depth0={s.depth₀} depth1={s.depth₁} ood0={s.ood₀} levels={lv} queries={qs} " ++
    s!"lastFolds={s.lastFolds} residual={s.residualVars} ivPrefix={hexBytes s.ivPrefix}"

end QuotientZk.Test.SkelTrace
