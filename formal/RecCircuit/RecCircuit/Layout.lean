-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/circuit/layout.rs`.
import RecCircuit.Spec

/-!
# The layout framework (`layout.rs`)

A transcription of `PolyBuilder`, `Builder` and `Units`, and of `Builder::finish` without the witness (the circuit
depends on the graph only: the words, the dead slots' check and the witness are the Rust's, for the honest prover).
The builder's state `St` also holds the state of every unit kind of `units.rs`, `keccak.rs`, `keccak16.rs` (their
`Units`, pools and counters) and the traces the checker reads (`Trace.lean`): the Rust's structs, flattened into one
state, in a state monad `BM` over `Except String` (a Rust panic is an `Except.error`).

`finish` returns the circuit and the **final view** (`View`): where every value is produced and placed, in the final
positions, and each value's chain (its producer, its forwards, its end) as `σ` was built from it. The checker
(`Check.lean`) checks the circuit against the view; the theorems read only the circuit and the view.
-/

namespace RecCircuit

open Primitives

/-- A value of the computation (`layout::Value`). -/
abbrev Val := ℕ

/-- `u32::MAX`: no value (`NONE`), or a free value's producer (`FREE`). -/
def NONE : ℕ := 4294967295

/-- The marker of a linear term in `PolyBuilder`'s keys (`u8::MAX`). -/
def LINEAR : ℕ := 255

/-! ## `PolyBuilder` -/

/-- `Σ coefficient · cell` and `Σ coefficient · cell_a · cell_b`, term by term, keyed by `(a, b)` in increasing order
(the Rust's `BTreeMap`), equal terms cancelling. -/
structure PolyBuilder where
  terms : List ((ℕ × ℕ) × UInt64) := []
  deriving Inhabited

namespace PolyBuilder

def keyLt (a b : ℕ × ℕ) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- `*terms.entry(key).or_insert(0) ^= k`. -/
def insertTerm (key : ℕ × ℕ) (k : UInt64) : List ((ℕ × ℕ) × UInt64) → List ((ℕ × ℕ) × UInt64)
  | [] => [(key, k)]
  | (key', v) :: rest =>
    if key' == key then (key', v ^^^ k) :: rest
    else if keyLt key key' then (key, k) :: (key', v) :: rest
    else (key', v) :: insertTerm key k rest

def addLinear (p : PolyBuilder) (cell : ℕ) (k : UInt64) : PolyBuilder := ⟨insertTerm (cell, LINEAR) k p.terms⟩

def linear (p : PolyBuilder) (cell : ℕ) (k : UInt64) : PolyBuilder := p.addLinear cell k

def addQuadratic (p : PolyBuilder) (a b : ℕ) (k : UInt64) : PolyBuilder := ⟨insertTerm (min a b, max a b) k p.terms⟩

def quadratic (p : PolyBuilder) (a b : ℕ) (k : UInt64) : PolyBuilder := p.addQuadratic a b k

/-- Add another polynomial (coefficient 1). -/
def add (p other : PolyBuilder) : PolyBuilder := ⟨other.terms.foldl (fun acc t => insertTerm t.1 t.2 acc) p.terms⟩

def build (p : PolyBuilder) : Poly where
  linear := p.terms.filterMap fun t => if t.2 == 0 || t.1.2 != LINEAR then none else some (t.1.1, F64.ofU64 t.2)
  quadratic := p.terms.filterMap fun t =>
    if t.2 == 0 || t.1.2 == LINEAR then none else some (t.1.1, t.1.2, F64.ofU64 t.2)

end PolyBuilder

/-- `W` forwards. -/
def forwards (w : ℕ) : Array Formula := Array.replicate w .forward

/-! ## Traces (what the checker reads) -/

/-- One input bit of a Keccak-256 call (`keccak::Bit`). -/
inductive Bit where
  | v (x : Val)
  | zero
  | one
  deriving DecidableEq, Inhabited, Repr

/-- A D16v Keccak-f instance: its values by round. `a j` is round `j`'s input (`a 0` the permutation's input, after
its constant bits are made), `a 24` its output; `c j`, `d j` round `j`'s parities and mixes; `p j y` the partial sums of
round `j`'s output, plane by plane (`p j 4 = c (j + 1)`). Indices `64·lane + z`, `64·x + z`. -/
structure KeccakT where
  a : Array (Array Val)
  c : Array (Array Val)
  d : Array (Array Val)
  p : Array (Array (Array Val))
  deriving Inhabited

/-- A Keccak-256 call: the message bits, then per block the permutation's input (`Bit`s, before its constants) and
instance. -/
structure SpongeT where
  message : Array Bit
  /-- Per block: the instance's index in `St.keccaks`. -/
  perms : Array ℕ
  /-- Per later block: the rate's 1088 bits as made (`Bit.v` the value given to the permutation). -/
  inputs : Array (Array Bit)
  digest : Array Val
  deriving Inhabited

/-- A packing: its `(exponent, bit)` input, its windows from the top, and its result. A window: its cells' values,
its accumulator's (`none` for a top window of `pack-top4`) and its output. -/
structure PackT where
  bits : List (ℕ × Val)
  windows : Array (Array Val × Option Val × Val)
  out : Val
  deriving Inhabited

/-! ## The builder's state -/

/-- `Units`: units of `size` consecutive roles, `perRow` to a row of one region. -/
structure Units where
  region : ℕ
  size : ℕ
  perRow : ℕ
  row : ℕ
  used : ℕ
  deriving Inhabited, Repr

def Units.new (region size perRow : ℕ) : Units := ⟨region, size, perRow, 0, perRow⟩

/-- The `E` operations. -/
inductive Op where
  | mul
  | add
  | square
  deriving DecidableEq, Inhabited, Repr

/-- The builder and every unit kind's state. -/
structure St where
  logWidth : ℕ
  regions : Array Region := #[]
  regionIndex : List (String × ℕ) := []
  readByRow : Array (Array Bool) := #[]
  rowRegion : Array ℕ := #[]
  /-- Per position (creation row · W + role): the value placed there. -/
  cell : Array ℕ := #[]
  /-- Per position: the value its slot produces. -/
  produced : Array ℕ := #[]
  /-- Per position: `κ` (the Rust's map holds the nonzero ones). -/
  kappa : Array K := #[]
  /-- The ports' sources, by position. -/
  portSrc : Array (ℕ × Source) := #[]
  /-- Per value: its producing position, or `NONE` (free). -/
  producer : Array ℕ := #[]
  calls : List (List CallWord) := []
  -- `Constants`
  constUnits : Option Units := none
  spare : Array (ℕ × ℕ) := #[]
  constMade : ℕ := 0
  constOwnRows : ℕ := 0
  -- `Xors`
  xorUnits : Units := default
  -- `D16`
  k0 : ℕ := 0
  k1 : ℕ := 0
  kd : ℕ := 0
  kprep : ℕ := 0
  pool : Array (ℕ × ℕ) := #[]
  poolHead : ℕ := 0
  permutations : ℕ := 0
  -- `Bools`
  bitUnits : Units := default
  -- `Packer`
  packTop : Units := default
  packNext : Units := default
  packZero : Option Val := none
  -- `Arith`
  ended : Array Units := #[]
  forwarded : Array Units := #[]
  arithCounts : Array (Array ℕ) := #[#[0, 0], #[0, 0], #[0, 0]]
  -- `Ports`
  portUnits : Array Units := #[]
  -- Traces
  keccaks : Array KeccakT := #[]
  sponges : Array SpongeT := #[]
  packs : Array PackT := #[]
  deriving Inhabited

/-- The builder's monad. -/
abbrev BM := StateT St (Except String)

def need (b : Bool) (msg : String) : BM Unit := if b then pure () else throw msg

namespace Builder

def width : BM ℕ := return 2 ^ (← get).logWidth

/-- Register a region type (`Builder::region`): once per name, later calls must agree. -/
def region (name : String) (roles : Array Formula) : BM ℕ := do
  let w ← width
  need (roles.size == w) s!"region {name}: one formula a role"
  let s ← get
  match s.regionIndex.lookup name with
  | some r =>
    need ((s.regions.getD r default).roles == roles) s!"region {name} redefined"
    return r
  | none =>
    let read := roles.foldl (fun read f => f.reads.foldl (fun read c => read.set! c true) read)
      (Array.replicate w false)
    let r := s.regions.size
    modify fun s => { s with
      regions := s.regions.push ⟨name, roles⟩
      readByRow := s.readByRow.push read
      regionIndex := (name, r) :: s.regionIndex }
    return r

/-- A new row of `region` (`Builder::row`). -/
def row (region : ℕ) : BM ℕ := do
  let w ← width
  let r := (← get).rowRegion.size
  modify fun s => { s with
    rowRegion := s.rowRegion.push region
    cell := s.cell ++ Array.replicate w NONE
    produced := s.produced ++ Array.replicate w NONE
    kappa := s.kappa ++ Array.replicate w 0 }
  return r

def pos (row role : ℕ) : BM ℕ := do
  let w ← width
  need (role < w) "a role past the row"
  return row * w + role

def formula (row role : ℕ) : BM Formula := do
  let s ← get
  return (s.regions.getD (s.rowRegion.getD row 0) default).roles.getD role .forward

def isExpr : Formula → Bool
  | .expr _ => true
  | _ => false

/-- Place `value` at `(row, role)` (`Builder::place`). -/
def place (row role value : ℕ) : BM Unit := do
  let p ← pos row role
  let s ← get
  need (s.cell.getD p 0 == NONE) s!"cell ({row}, {role}) placed twice"
  need (value < s.producer.size) "an unknown value"
  modify fun s => { s with cell := s.cell.set! p value }

def newValue (producer : ℕ) : BM Val := do
  let v := (← get).producer.size
  modify fun s => { s with producer := s.producer.push producer }
  return v

/-- The value the slot at `(row, role)` pushes (`Builder::produce`; `produce_given`'s word is the witness's). -/
def produce (row role : ℕ) : BM Val := do
  let p ← pos row role
  need (isExpr (← formula row role)) s!"({row}, {role}) is not an expression slot"
  need ((← get).produced.getD p 0 == NONE) s!"slot ({row}, {role}) produced twice"
  let v ← newValue p
  modify fun s => { s with produced := s.produced.set! p v }
  return v

/-- A free value (`Builder::free`; its word is the witness's). -/
def free : BM Val := newValue NONE

def setKappa (row role : ℕ) (k : K) : BM Unit := do
  let p ← pos row role
  need (isExpr (← formula row role)) "κ off an expression slot"
  if k != 0 then modify fun s => { s with kappa := s.kappa.set! p k }

def port (row role : ℕ) (source : Source) : BM Unit := do
  let p ← pos row role
  need ((← formula row role).isPort) "not a port role"
  need (!(← get).portSrc.any (·.1 == p)) "port set twice"
  modify fun s => { s with portSrc := s.portSrc.push (p, source) }

end Builder

/-- The next unit: its row and first role (`Units::next`). -/
def Units.next (u : Units) : BM (Units × ℕ × ℕ) := do
  let u ← if u.used == u.perRow then do
      let r ← Builder.row u.region
      pure { u with row := r, used := 0 }
    else pure u
  return ({ u with used := u.used + 1 }, u.row, u.used * u.size)

/-! ## Placement (`pad`, `pad_counts`) -/

/-- The smallest count `≥ c` with at most `k` binary digits (`pad`). -/
def pad (c k : ℕ) : ℕ := Id.run do
  if (Nat.toDigits 2 c).count '1' ≤ k then return c
  let mut kept := 0
  let mut low := 0
  for i in [0:64] do
    let bit := 63 - i
    if c >>> bit &&& 1 == 1 && (Nat.toDigits 2 kept).count '1' < k then
      kept := kept ||| (1 <<< bit)
      low := 1 <<< bit
  return kept + low

def popcount (c : ℕ) : ℕ := (Nat.toDigits 2 c).count '1'

def nextPow2 (n : ℕ) : ℕ := Id.run do
  let mut p := 1
  while p < n do p := 2 * p
  return p

/-- Each region's rows padded to fewer blocks within the `2^L` rows the unpadded layout needs (`pad_counts`): greedily,
the region whose next binary digit saves the most rows per added pair (`f64`, the last of equal gains). -/
def padCounts (count : Array ℕ) (regions : Array Region) : Except String (Array ℕ) := do
  let total := count.foldl (· + ·) 0
  let budget := nextPow2 (max total 1)
  let roles := regions.map fun r => (r.roles.filter (· != .forward)).size
  let isPort := fun r => (regions.getD r default).roles.any (·.isPort)
  let mut k : Array ℕ := (List.range count.size).toArray.map fun r =>
    let c := count.getD r 0
    if isPort r || roles.getD r 0 == 0 then popcount c else min (popcount c) 1
  let rows := fun (k : Array ℕ) => (List.range count.size).foldl (fun acc r => acc + pad (count.getD r 0) (k.getD r 0)) 0
  let mut fuel := 64 * count.size + 1
  while rows k > budget do
    if fuel == 0 then throw "pad_counts: no progress"
    fuel := fuel - 1
    let gain := fun (r : ℕ) => Float.ofNat (pad (count.getD r 0) (k.getD r 0) - pad (count.getD r 0) (k.getD r 0 + 1)) /
      Float.ofNat (max (roles.getD r 0) 1)
    let cands := (List.range count.size).filter fun r => k.getD r 0 < popcount (count.getD r 0)
    match cands with
    | [] => throw "the unpadded layout fits"
    | c :: cs =>
      let best := cs.foldl (fun best r => if gain best ≤ gain r then r else best) c
      k := k.set! best (k.getD best 0 + 1)
  return (List.range count.size).toArray.map fun r => pad (count.getD r 0) (k.getD r 0)

/-! ## `finish` -/

/-- **The final view**: in the final positions, each value's producer (`NONE`: free), each position's placed value
(`NONE`: none), each value's chain (a produced value: its producer, its forwards, its end; a free value: its forwards,
a cycle) and each placed position's index in its value's chain. -/
structure View where
  rowMap : Array ℕ
  producerF : Array ℕ
  cellF : Array ℕ
  chains : Array (Array ℕ)
  idxF : Array ℕ
  deriving Inhabited

/-- Lay the rows out, derive `σ` and check the invariant (`Builder::finish`, without the words). -/
def finish : BM (Circuit × View) := do
  let w ← width'
  let s ← get
  let rows := s.rowRegion.size
  let formulaOf := fun (s : St) (p : ℕ) =>
    (s.regions.getD (s.rowRegion.getD (p / w) 0) default).roles.getD (p % w) .forward
  -- Every port role has a source.
  for p in [0:rows * w] do
    if (formulaOf s p).isPort then
      need (s.portSrc.any (·.1 == p)) s!"port at {p} has no source"
  -- Junk.
  for p in [0:rows * w] do
    let s ← get
    if Builder.isExpr (formulaOf s p) && s.produced.getD p 0 == NONE && s.cell.getD p 0 != NONE then
      let v ← Builder.newValue p
      modify fun s => { s with produced := s.produced.set! p v }
  let s ← get
  let values := s.producer.size
  -- The invariant: slot placements, live reads, placed cells read.
  let mut slotEnd : Array ℕ := Array.replicate values NONE
  let mut fwds : Array (Array ℕ) := Array.replicate values #[]
  for p in [0:rows * w] do
    let v := s.cell.getD p 0
    if v != NONE then
      match formulaOf s p with
      | .forward => fwds := fwds.modify v (·.push p)
      | .expr _ =>
        need (s.producer.getD v 0 != NONE) s!"free value {v} placed at slot {p}"
        need (slotEnd.getD v 0 == NONE) s!"value {v} placed at two slots"
        slotEnd := slotEnd.set! v p
      | .port _ => throw s!"a value placed at port {p}"
      need ((s.readByRow.getD (s.rowRegion.getD (p / w) 0) #[]).getD (p % w) false)
        s!"value {v} placed at {p}, which no formula of the row reads"
  for p in [0:rows * w] do
    let f := formulaOf s p
    let live := match f with
      | .forward => false
      | .expr _ => s.produced.getD p 0 != NONE
      | .port _ => true
    if live then
      for c in f.reads do
        need (s.cell.getD ((p / w) * w + c) 0 != NONE) s!"position {p} reads cell {c}, which holds nothing"
  -- Placement: blocks by region, largest first.
  let mut count : Array ℕ := Array.replicate s.regions.size 0
  for r in s.rowRegion do count := count.modify r (· + 1)
  let padded ← liftExcept (padCounts count s.regions)
  let mut wanted : Array (ℕ × ℕ) := #[]
  for r in [0:padded.size] do
    let c := padded.getD r 0
    for bit in [0:64] do
      if c >>> bit &&& 1 == 1 then wanted := wanted.push (bit, r)
  wanted := wanted.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)
  let mut blocks : Array Block := #[]
  let mut nextRow := 0
  let mut regionStarts : Array (Array (ℕ × ℕ)) := Array.replicate s.regions.size #[]
  for (bit, r) in wanted do
    blocks := blocks.push ⟨nextRow, bit, r⟩
    regionStarts := regionStarts.modify r (·.push (nextRow, 2 ^ bit))
    nextRow := nextRow + 2 ^ bit
  let totalRows := nextRow
  let logRows := Nat.log2 (nextPow2 (max totalRows 1))
  let logN := logRows + s.logWidth
  let n := 2 ^ logN
  let mut rowMap : Array ℕ := Array.replicate rows 0
  let mut cursor : Array (ℕ × ℕ) := Array.replicate s.regions.size (0, 0)
  for row in [0:rows] do
    let r := s.rowRegion.getD row 0
    let (b, off) := cursor.getD r (0, 0)
    let (start, len) := (regionStarts.getD r #[]).getD b (0, 0)
    rowMap := rowMap.set! row (start + off)
    cursor := cursor.set! r (if off + 1 == len then (b + 1, 0) else (b, off + 1))
  let fpos := fun (p : ℕ) => rowMap.getD (p / w) 0 * w + p % w
  -- Ports, in final position order.
  let ports : Array Port := (s.portSrc.map fun (p, source) => (⟨fpos p, source⟩ : Port)).qsort
    fun a b => a.position < b.position
  -- σ: self-loops by default, then the chains.
  let mut sigma : Array ℕ := (List.range n).toArray
  for j in [0:ports.size] do
    sigma := sigma.set! (ports.getD j default).position (n + j)
  let mut freeEnds : Array ℕ := #[]
  for p in [0:rows * w] do
    if Builder.isExpr (formulaOf s p) && s.cell.getD p 0 == NONE && s.produced.getD p 0 != NONE then
      freeEnds := freeEnds.push p
  let mut endOf := slotEnd
  let mut next := 0
  for v in [0:values] do
    if s.producer.getD v 0 != NONE && endOf.getD v 0 == NONE then
      need (next < freeEnds.size) "as many free ends as values without an end"
      endOf := endOf.set! v (freeEnds.getD next 0)
      next := next + 1
  need (next == freeEnds.size) "as many free ends as values without an end"
  let mut chains : Array (Array ℕ) := Array.replicate values #[]
  for v in [0:values] do
    let chain := fwds.getD v #[]
    if s.producer.getD v 0 == NONE then
      for k in [0:chain.size] do
        sigma := sigma.set! (fpos (chain.getD k 0)) (fpos (chain.getD ((k + 1) % chain.size) 0))
      chains := chains.set! v (chain.map fpos)
    else
      let mut at_ := s.producer.getD v 0
      for f in chain do
        sigma := sigma.set! (fpos at_) (fpos f)
        at_ := f
      sigma := sigma.set! (fpos at_) (fpos (endOf.getD v 0))
      chains := chains.set! v ((#[s.producer.getD v 0] ++ chain ++ #[endOf.getD v 0]).map fpos)
  -- κ, in final position order.
  let mut kappa : Array (ℕ × K) := #[]
  for p in [0:rows * w] do
    let k := s.kappa.getD p 0
    if k != 0 then kappa := kappa.push (fpos p, k)
  kappa := kappa.qsort fun a b => a.1 < b.1
  -- The final view.
  let producerF := s.producer.map fun p => if p == NONE then NONE else fpos p
  let mut cellF : Array ℕ := Array.replicate n NONE
  for p in [0:rows * w] do
    cellF := cellF.set! (fpos p) (s.cell.getD p 0)
  -- A produced value's chain starts at its producer, which is not one of its placements.
  let mut idxF : Array ℕ := Array.replicate n 0
  for v in [0:values] do
    let ch := chains.getD v #[]
    let first := if s.producer.getD v 0 == NONE then 0 else 1
    for k in [first:ch.size] do
      idxF := idxF.set! (ch.getD k 0) k
  let circuit : Circuit := ⟨logN, s.logWidth, s.regions, blocks, sigma, kappa, ports, s.calls⟩
  return (circuit, ⟨rowMap, producerF, cellF, chains, idxF⟩)
where
  width' : BM ℕ := return 2 ^ (← get).logWidth
  liftExcept {α : Type} (e : Except String α) : BM α := match e with
    | .ok a => pure a
    | .error m => throw m

end RecCircuit
