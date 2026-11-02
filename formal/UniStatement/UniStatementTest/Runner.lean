-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniStatement.Run
import UniStatement.Mapping

/-!
# The differential runner

`lake env lean ../UniStatement/UniStatementTest/Runner.lean` (from `formal/EndToEnd`), with the vectors of
`crates/leanvm_univariate/tests/lean_vectors.rs` at `$UNI_VECTORS`: the Lean verifier (`UniStatement.run`,
compiled evaluation, not the kernel) on every vector's calldata, compared with the Rust verifier's on
**every value it states**: the verdict (stream error or not, and which), every challenge drawn, every value
it requires to be zero, the accept bit, the number of relations, each stack's variables, every opening
handed to `PCS_OPEN` (point claims with their points and values, or weighted claims with their points,
terms and values, and the bit-slice claim) and Flock's claims on `A0`, `B0`. It prints one line per vector
and a summary, and fails (`IO.Process.exit 1` is not available under `#eval`, so it throws) on any
disagreement or unreadable vector.
-/

open LeanVM.Parameters UniStatement

namespace UniStatementTest

/-- A parser of a line's tokens. -/
abbrev Parse := StateT (List String) (Except String)

def token : Parse String := do
  match ← get with
  | [] => throw "the line ended early"
  | t :: ts => set ts; pure t

def expect (s : String) : Parse Unit := do
  let t ← token
  if t ≠ s then throw s!"expected {s}, got {t}"

def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexNat (s : String) : Except String ℕ :=
  s.toList.foldlM (fun acc c ↦ match hexDigit c with
    | some d => pure (16 * acc + d)
    | none => throw s!"not hex: {s}") 0

def nat : Parse ℕ := do
  let t ← token
  match t.toNat? with
  | some n => pure n
  | none => throw s!"not a number: {t}"

def eElem : Parse E := do
  match (← token).splitOn ":" with
  | [a, b, c] =>
    let limb (s : String) : Except String UInt64 := UInt64.ofNat <$> hexNat s
    pure (eNew (← limb a) (← limb b) (← limb c))
  | _ => throw "not an element of E"

def many {α : Type} (p : Parse α) : Parse (List α) := do
  let n ← nat
  (List.range n).mapM fun _ ↦ p

/-- Bytes from hex. -/
def hexBytes (s : String) : Except String (Array UInt8) := do
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then throw "odd hex"
  let mut out : Array UInt8 := Array.mkEmpty (cs.size / 2)
  for i in [0:cs.size / 2] do
    match hexDigit (cs.getD (2 * i) '0'), hexDigit (cs.getD (2 * i + 1) '0') with
    | some a, some b => out := out.push (UInt8.ofNat (16 * a + b))
    | _, _ => throw "not hex"
  return out

def eHex (x : E) : String :=
  s!"{String.ofList (Nat.toDigits 16 (x.limb 0).lane.toNat)}:{String.ofList (Nat.toDigits 16 (x.limb 1).lane.toNat)}:{String.ofList (Nat.toDigits 16 (x.limb 2).lane.toNat)}"

/-- A combined claim as the Rust writes it: its points, its terms (column id, point, twist, coefficient),
its value, its relations. -/
structure RustCombined where
  points : List (List E)
  terms : List (ℕ × ℕ × ℕ × E)
  value : E
  relations : ℕ

def combinedP : Parse RustCombined := do
  expect "P"
  let points ← many (many eElem)
  expect "T"
  let terms ← many do
    let id ← hexNat (← token)
    let p ← nat
    let twist ← nat
    let c ← eElem
    pure (id, p, twist, c)
  expect "V"
  let value ← eElem
  expect "R"
  let relations ← nat
  pure ⟨points, terms, value, relations⟩

inductive RustOpening where
  | point (commitment : String) (pt : List E) (value : E) (bitSlice : Option RustCombined)
  | weighted (commitment : String) (claim : RustCombined)

def openingP : Parse RustOpening := do
  expect "OPENING"
  let c ← token
  match ← token with
  | "POINT" =>
    let pt ← many eElem
    expect "VALUE"
    let v ← eElem
    expect "BITSLICE"
    let bs ← match ← token with
      | "0" => pure none
      | "1" => some <$> combinedP
      | t => throw s!"BITSLICE {t}"
    pure (.point c pt v bs)
  | "WEIGHTED" => .weighted c <$> combinedP
  | t => throw s!"opening kind {t}"

/-- A vector: its configuration, its calldata, and the Rust's outcome. -/
structure Vector' where
  id : String
  shape : String
  flock : String
  claims : String
  kind : String
  iv : Array UInt8
  publicInput : Array UInt8
  stream : Array UInt8
  error : Option String
  challenges : List E
  zeros : List E
  nonzeros : List E
  accept : Bool
  relations : Option ℕ
  stackVars : List (String × ℕ)
  openings : List RustOpening
  matrices : Option (List E × E × E)

/-- The tokens of a line. -/
def tokens (line : String) : List String := (line.splitOn " ").filter (· ≠ "")

/-- Parse one vector from its lines (`VECTOR` to `END`). -/
def parseVector (lines : List String) : Except String Vector' := do
  let byKey (k : String) : Option (List String) :=
    (lines.map tokens).find? (fun ts ↦ ts.head? == some k) |>.map (·.drop 1)
  let req (k : String) : Except String (List String) :=
    match byKey k with
    | some ts => pure ts
    | none => throw s!"no {k} line"
  let header ← req "VECTOR"
  let (id, shape, flock, claims, kind) ← match header with
    | [a, b, c, d, e] => pure (a, b, c, d, e)
    | _ => throw "bad VECTOR line"
  let iv ← hexBytes ((← req "IV").headD "")
  let publicInput ← hexBytes ((← req "PUBLIC").headD "")
  let stream ← hexBytes (((← req "STREAM").drop 1).headD "")
  let error := match byKey "RESULT" with
    | some ["ERR", e] => some e
    | _ => none
  let (challenges, _) ← (many eElem).run (← req "CHALLENGES")
  let (zeros, _) ← (many eElem).run (← req "ZEROS")
  let (nonzeros, _) ← (many eElem).run (← req "NONZEROS")
  let accept := byKey "ACCEPT" == some ["1"]
  let relations := (byKey "RELATIONS").bind (·.head?) |>.bind String.toNat?
  let stackVars ← match byKey "STACKVARS" with
    | some ts => (do
        let n ← nat
        (List.range n).mapM fun _ ↦ do
          let c ← token
          let v ← nat
          pure (c, v) : Parse _).run' ts
    | none => pure []
  let openings ← (lines.filter (·.startsWith "OPENING ")).mapM fun l ↦ openingP.run' (tokens l)
  let matrices ← match byKey "MATRICES" with
    | some ("1" :: rest) => (do
        let pt ← many eElem
        expect "A"
        let a ← eElem
        expect "B"
        let b ← eElem
        pure (some (pt, a, b)) : Parse _).run' (("" :: rest).drop 1)
    | _ => pure none
  pure ⟨id, shape, flock, claims, kind, iv, publicInput, stream, error, challenges, zeros, nonzeros,
    accept, relations, stackVars, openings, matrices⟩

/-- The configuration a vector names. -/
def blake2sNamed : String → Option Blake2s
  | "main" => some (.flock flockMain)
  | "bitslice" => some (.flock flockBitSlice)
  | "leanvm" => some (.flock flockLeanvmSkip)
  | "omitted" => some .omitted
  | _ => none

def modeNamed : String → Option ClaimsMode
  | "point" => some .point
  | "weighted" => some .weighted
  | _ => none

/-- Lean's combined claim against the Rust's: the same points, terms (in order), value, relations. -/
def sameCombined (lean : Combined) (rust : RustCombined) : Bool :=
  lean.points == rust.points &&
    lean.terms.map (fun (c, p, k, v) ↦ (c.id, p, k, v)) == rust.terms &&
    lean.value == rust.value && lean.relations == rust.relations

def sameOpening (lean : Commitment × Opening) (rust : RustOpening) : Bool :=
  match lean.2, rust with
  | .point pt v bs, .point c pt' v' bs' =>
    lean.1.name == c && pt == pt' && v == v' &&
      (match bs, bs' with
        | none, none => true
        | some a, some b => sameCombined a b
        | _, _ => false)
  | .weighted claim, .weighted c claim' => lean.1.name == c && sameCombined claim claim'
  | _, _ => false

/-- The first disagreement between the Lean run and the Rust's outcome, if any. -/
def compare (v : Vector') : Except String (Option String) := do
  let some shape := shapeNamed v.shape | throw s!"unknown shape {v.shape}"
  let some blake2s := blake2sNamed v.flock | throw s!"unknown flock {v.flock}"
  let some mode := modeNamed v.claims | throw s!"unknown claims {v.claims}"
  let o := run shape v.iv.toList v.publicInput.toList v.stream blake2s mode
  let leanError := match o.result with
    | .ok _ => none
    | .error e => some e.name
  if leanError != v.error then return some s!"result: Lean {leanError}, Rust {v.error}"
  if o.chan.challenges.toList.length != v.challenges.length then
    return some s!"challenges: Lean {o.chan.challenges.size}, Rust {v.challenges.length}"
  for (i, (a, b)) in (List.range v.challenges.length).zip (o.chan.challenges.toList.zip v.challenges) do
    if a != b then return some s!"challenge {i}: Lean {eHex a}, Rust {eHex b}"
  if o.chan.zeros.toList != v.zeros then
    return some s!"zeros: Lean {o.chan.zeros.toList.map eHex}, Rust {v.zeros.map eHex}"
  if !v.nonzeros.isEmpty then return some "the Rust checked a nonzero value; this verifier has none"
  if o.accepts != v.accept then return some s!"accept: Lean {o.accepts}, Rust {v.accept}"
  match o.result with
  | .error _ => return none
  | .ok r =>
    if some r.relations != v.relations then return some s!"relations: Lean {r.relations}, Rust {v.relations}"
    if r.stackVars.map (fun (c, n) ↦ (c.name, n)) != v.stackVars then
      return some s!"stack vars: Lean {r.stackVars.map fun (c, n) ↦ (c.name, n)}, Rust {v.stackVars}"
    if r.openings.length != v.openings.length then
      return some s!"openings: Lean {r.openings.length}, Rust {v.openings.length}"
    for (i, (a, b)) in (List.range r.openings.length).zip (r.openings.zip v.openings) do
      if !sameOpening a b then return some s!"opening {i} ({a.1.name}) differs"
    let sameMatrices := match r.matrices, v.matrices with
      | none, none => true
      | some m, some (pt, a, b) => m.point == pt && m.a == a && m.b == b
      | _, _ => false
    if !sameMatrices then return some "matrices differ"
    return none

/-- Split the file into vectors. -/
def vectorsOf (text : String) : List (List String) :=
  let lines := (text.splitOn "\n").filter fun l ↦ !l.startsWith "#" && l ≠ ""
  let (done, current) := lines.foldl (fun (acc : List (List String) × List String) l ↦
    if l.startsWith "VECTOR " then (if acc.2.isEmpty then acc.1 else acc.1 ++ [acc.2], [l])
    else if l == "END" then (acc.1 ++ [acc.2], []) else (acc.1, acc.2 ++ [l])) ([], [])
  if current.isEmpty then done else done ++ [current]

/-! ### Self-tests: the defining properties of the constants, and the mapping's transform -/

/-- A xorshift word stream (`domain.rs`'s test generator). -/
def xorshift (seed : UInt64) (count : ℕ) : List UInt64 :=
  ((List.range count).foldl (fun (acc : UInt64 × Array UInt64) _ ↦
    let s := acc.1 ^^^ (acc.1 <<< 13)
    let s := s ^^^ (s >>> 7)
    let s := s ^^^ (s <<< 17)
    (s, acc.2.push s)) (seed ||| 1, #[])).2.toList

/-! ### The bridge to Lv42's instance: the same tables, read two ways -/

/-- A form on a row of `K`. -/
def evalForm (f : Form) (row : ℕ → K) : E :=
  f.foldl (fun acc (mono, c) ↦ acc + mono.foldl (fun p i ↦ p * ofK (row i)) c) 0

/-- **The verifier's tables are Lv42's** on random rows: for each opcode table, the multiset of pull tuples
and of push tuples (`layout.rs`'s forms, padded to 16 slots) equals the instance's flushes of that side
(Clean's components through `toM3`), the counter columns are the instance's count columns, and the
constraints (JUMP's two, none elsewhere) vanish together. The sides are compared as multisets: the
fingerprint is a sum over a tuple's slots and the bus a product over tuples. -/
def lv42Bridge : List (String × Bool) :=
  (List.finRange 6).flatMap fun j ↦
    let t := tables.getD j.val default
    let rows := (List.range 3).map fun s ↦ (xorshift (UInt64.ofNat (1000 * j.val + 7 * s + 1)) 64).toArray
    let pad (tuple : List E) : List E := tuple ++ List.replicate (16 - tuple.length) 0
    let mine (sideOf : Flushes → List (List Form)) (row : Array UInt64) : List (List E) :=
      (sideOf t.flushes).map fun tuple ↦ pad (tuple.map fun f ↦ evalForm f fun i ↦ K.ofLane (row.getD i 0))
    let theirs (side : Lv42.Protocol.Side) (row : Array UInt64) : List (List E) :=
      ((Lv42.Protocol.LeanIsa.flushes (Lv42.Protocol.LeanIsa.opIdx j)).filter (·.1 == side)).map fun f ↦
        f.2.toList.map fun P ↦ ofK (P.eval fun i ↦ K.ofLane (row.getD i.val 0))
    let flushesAgree := rows.all fun row ↦
      (mine (·.pull) row).isPerm (theirs .pull row) && (mine (·.push) row).isPerm (theirs .push row) &&
        -- a control: the sides are told apart
        !(mine (·.pull) row).isPerm (theirs .push row)
    let countsAgree := t.countColumns ==
      (Lv42.Protocol.LeanIsa.counts (Lv42.Protocol.LeanIsa.opIdx j)).map (·.val)
    let widthAgrees := t.width == Lv42.Protocol.LeanIsa.width (Lv42.Protocol.LeanIsa.opIdx j)
    -- JUMP's rows: random (both fail), `v_cond = b = 0` (both hold), `b = 1, w = v_cond⁻¹` (both hold),
    -- `b = 1, w` random (both fail).
    let r0 := rows.getD 0 #[]
    let x := K.ofLane (r0.getD 5 3)
    let at_ (n : String) := colIdx t.columns n
    let set (row : Array UInt64) (n : String) (v : UInt64) : Array UInt64 := row.set! (at_ n) v
    let constraintRows := rows ++ if t.opcode = opJump then
        [set (set r0 "v_cond" 0) "b" 0, set (set (set r0 "v_cond" x.lane) "w" x⁻¹.lane) "b" 1,
          set (set r0 "v_cond" x.lane) "b" 1]
      else []
    let constraintsAgree := constraintRows.all fun row ↦
      let value (n : String) : E := ofK (K.ofLane (row.getD (colIdx t.columns n) 0))
      let mineVanish := if t.opcode = opJump then
          value "b" + value "v_cond" * value "w" == 0 && value "v_cond" * (value "b" + 1) == 0
        else true
      let theirsVanish := (Lv42.Protocol.LeanIsa.constraints (Lv42.Protocol.LeanIsa.opIdx j)).all fun C ↦
        C.eval (fun i ↦ K.ofLane (row.getD i.val 0)) == 0
      mineVanish == theirsVanish &&
        (Lv42.Protocol.LeanIsa.constraints (Lv42.Protocol.LeanIsa.opIdx j)).length ==
          if t.opcode = opJump then 2 else 0
    [(s!"Lv42 bridge, table {j.val}: width", widthAgrees),
      (s!"Lv42 bridge, table {j.val}: pull and push tuples (multisets, 3 random rows)", flushesAgree),
      (s!"Lv42 bridge, table {j.val}: counter columns", countsAgree),
      (s!"Lv42 bridge, table {j.val}: constraints", constraintsAgree)]

/-- The Rust's unit tests of `domain.rs` and `heap.rs`, and the mapping's transform pair, on the Lean
definitions: each `(name, holds)`. -/
def selfTests : List (String × Bool) :=
  let ws := xorshift 3 400
  -- `s(β_{k+1}) = β_k`, `w_l(ω_i) = ω_{i >> l}`, `w_r` vanishes on `V_r` and is `1` at `β_r`.
  let cantor := (List.range (basisSize - 1)).all fun k ↦ sK (beta.getD (k + 1) 0) == beta.getD k 0
  let digitsRead := (ws.take 50).all fun x ↦
    let i := x.toNat % 2 ^ 24
    let w := digits (pointE i) 25
    (List.range 25).all fun l ↦ w.getD l 0 == pointE (i >>> l)
  let vanishes := (ws.take 50).all fun x ↦
    let i := x.toNat % 2 ^ 24
    let r := x.toNat / 2 ^ 24 % 24 + 1
    (digits (pointE (i % 2 ^ r)) (r + 1)).getD r 1 == 0
  let one := (digits (pointE (2 ^ 10)) 11).getD 10 0 == 1
  -- `y_l(ω_i) = i_l` on `V_18`.
  let a := coordinateFunctionals 18
  let functionals := (ws.drop 50 |>.take 20).all fun x ↦
    let i := x.toNat % 2 ^ 18
    (coordinatesAt (pointE i) a |>.zip (List.range 18)).all fun (y, l) ↦ y == bitE i l
  -- The prefix and suffix vanishing polynomials vanish exactly where they should; their product is `w_r`.
  let rows := 2731
  let r := 12
  let activePadding := [0, 1, 2730, 2731, 2732, 4095, 1000].all fun i ↦
    let w := digits (pointE i) (r + 1)
    (prefixVanishing w rows == 0) == decide (i < rows) && (suffixVanishing w rows r == 0) == decide (i ≥ rows)
  let t := eNew 0x123456789abc 0x42 0x77
  let wt := digits t 22
  let product := prefixVanishing wt rows * suffixVanishing wt rows r == wt.getD r 0 &&
    vanishingRatio wt 17 21 * wt.getD 17 0 == wt.getD 21 0
  -- The heap at the reference workload: `2^22` leaves, the memory first, one unused block of `2^17`.
  let heap := HeapLayout.new 21 19 [18, 18, 18, 18, 17, 18]
  let heapOk := heap.h == 23 &&
    (heap.blocks.head?.map fun b ↦ b.leaves == .memory && b.position == 2 ^ 22) == some true &&
    (heap.blocks.getD 1 default).position == 2 ^ 22 + 2 ^ 21 &&
    (heap.blocks.filter (·.leaves == .unused)).map (·.r) == [17] &&
    heap.blocks.all fun b ↦ b.position % 2 ^ b.r == 0
  -- The mapping's transform: the basis-`B` coefficients of a column of values give back its values.
  let transform := [1, 3, 6, 9].all fun r ↦
    let vals : Array K := ((xorshift (UInt64.ofNat (17 * r)) (2 ^ r)).map K.ofLane).toArray
    let c := bCoefficients r vals
    (List.range (2 ^ r)).all fun x ↦ basisValue c r x == vals.getD x 0
  -- …and agree with the verifier's reading of a column at a point (`f(t)` = the coefficients' extension at
  -- the digits of `t`), at `t = ω_x`.
  let reading := [5, 8].all fun r ↦
    let vals : Array K := ((xorshift (UInt64.ofNat (29 * r)) (2 ^ r)).map K.ofLane).toArray
    let c := bCoefficients r vals
    (List.range (2 ^ r)).all fun x ↦
      multilinearEval (c.toList.map ofK) (digits (pointE x) r) == ofK (vals.getD x 0)
  [("cantor basis: s(beta[k+1]) = beta[k]", cantor), ("digits: w_l(omega_i) = omega_{i >> l}", digitsRead),
    ("w_r vanishes on V_r", vanishes), ("w_10(beta_10) = 1", one),
    ("coordinate functionals: y_l(omega_i) = i_l on V_18", functionals),
    ("prefix/suffix vanishing: their zeros", activePadding),
    ("prefix * suffix = w_r; vanishing ratio", product), ("heap layout at the reference workload", heapOk),
    ("mapping: basisValue (bCoefficients v) = v", transform),
    ("mapping: the verifier's reading at omega_x is the value", reading)]

def main : IO Unit := do
  let tests := selfTests ++ lv42Bridge
  for (n, ok) in tests do
    IO.println s!"{if ok then "SELF-TEST OK" else "SELF-TEST FAILED"} {n}"
  if !tests.all (·.2) then throw (IO.userError "a self-test failed")
  let path := (← IO.getEnv "UNI_VECTORS").getD "uni_vectors.txt"
  let text ← IO.FS.readFile path
  let vectors := vectorsOf text
  let mut agree := 0
  let mut failures : List String := []
  let mut accepted := 0
  let mut rejected := 0
  let mut tally : List (String × ℕ × ℕ) := []
  let start ← IO.monoMsNow
  for lines in vectors do
    match parseVector lines with
    | .error e =>
      failures := failures ++ [s!"unreadable vector: {e}"]
      IO.println s!"UNREADABLE {e}"
    | .ok v =>
      match compare v with
      | .ok none =>
        agree := agree + 1
        if v.accept then accepted := accepted + 1 else rejected := rejected + 1
        let key := v.kind
        let (a, r) := ((tally.find? (·.1 == key)).map (·.2)).getD (0, 0)
        tally := (tally.filter (·.1 != key)) ++ [(key, if v.accept then (a + 1, r) else (a, r + 1))]
        IO.println s!"AGREE {v.id} {v.shape} {v.flock} {v.claims} {v.kind}: {if v.accept then "accept" else
          s!"reject{(v.error.map (" " ++ ·)).getD ""}"}, {v.challenges.length} challenges, {v.zeros.length} checks, {v.openings.length} openings"
      | .ok (some d) =>
        failures := failures ++ [s!"{v.id}: {d}"]
        IO.println s!"DISAGREE {v.id} {v.shape} {v.flock} {v.claims} {v.kind}: {d}"
      | .error e =>
        failures := failures ++ [s!"{v.id}: {e}"]
        IO.println s!"ERROR {v.id}: {e}"
  let stop ← IO.monoMsNow
  IO.println s!"SUMMARY {agree}/{vectors.length} vectors agree on every value; accepted by both {accepted}, rejected by both {rejected}; by kind (accept, reject): {tally}; {(stop - start) / 1000} s"
  if !failures.isEmpty then throw (IO.userError s!"{failures.length} disagreements: {failures}")

end UniStatementTest

#eval UniStatementTest.main
