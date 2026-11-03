-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The parsing follows `formal/UniStatement`'s runner
-- (`UniStatementTest/Runner.lean`).
import RecStatement

/-!
# The differential runner

`lake env lean ../RecStatement/RecStatementTest/Runner.lean` (from `formal/EndToEnd`), with the vectors of
`crates/leanvm_rec/tests/lean_statement.rs` at `$REC_STATEMENT_VECTORS`: π2's real circuit for π1-rec3
(`RecStatement.Data`), the Lean verifier (`RecStatement.run`, compiled evaluation, not the kernel) on every vector's
calldata, compared with the Rust verifier's on **every value**: the verdict (the stream's error, or the value
required nonzero), every intermediate value of the arithmetic (the trace: the challenges, the digits, the row's
cells, `Ẑ_s(t)`, the groups' fractions, the public terms' denominators, the public side, the zero coset, the pushes'
sums, the identity's values, the inversion's, the digits' inverses, `u`, the quotient claim's values, `ρ`'s powers,
the fold), the public scalars and their pair points, the roots, the four claims, and **every `PCS_OPEN` input word for
word** (`pcsCalls`). The header's constants are compared with the Lean's own: `Spec.of`'s pairs, recursion
constants, groups, pull-less pairs, public terms, zero coset, walk and highest power of `γ`; π2's IV; the layout
words; `β_1`; the extension; the stream's length. First the self-tests (the Rust's unit tests: the norm's inverse, the
zero coset's closed form, the indicators' cosets, `β_1`, `w_k`'s coefficients; and the data: π1's contract IV and
π1's calls' constants against `formal/UniStatement`'s reference shape and roots). It throws (so `lean` exits with an
error) on any failure, disagreement or unreadable vector.
-/

open LeanVM.Parameters RecStatement

namespace RecStatementTest

/-- A parser of a line's tokens. -/
abbrev Parse := StateT (List String) (Except String)

def token : Parse String := do
  match ← get with
  | [] => throw "the line ended early"
  | t :: ts => set ts; pure t

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
    pure (UniStatement.eNew (← limb a) (← limb b) (← limb c))
  | _ => throw "not an element of E"

def many {α : Type} (p : Parse α) : Parse (List α) := do
  let n ← nat
  (List.range n).mapM fun _ ↦ p

def hexBytes' (s : String) : Except String (List UInt8) := do
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then throw "odd hex"
  let mut out : Array UInt8 := Array.mkEmpty (cs.size / 2)
  for i in [0:cs.size / 2] do
    match hexDigit (cs.getD (2 * i) '0'), hexDigit (cs.getD (2 * i + 1) '0') with
    | some a, some b => out := out.push (UInt8.ofNat (16 * a + b))
    | _, _ => throw "not hex"
  return out.toList

def bytesP : Parse (List UInt8) := do hexBytes' (← token)

def tokens (line : String) : List String := (line.splitOn " ").filter (· ≠ "")

def eHex (x : E) : String :=
  s!"{String.ofList (Nat.toDigits 16 (x.limb 0).lane.toNat)}:{String.ofList (Nat.toDigits 16 (x.limb 1).lane.toNat)}:{String.ofList (Nat.toDigits 16 (x.limb 2).lane.toNat)}"

/-- Run a parser on a line's tokens after its key(s). -/
def onLine {α : Type} (p : Parse α) (ts : List String) : Except String α := do
  let (a, rest) ← p.run ts
  if rest.isEmpty then pure a else throw s!"trailing tokens: {rest.take 3}"

/-- The header's constants. -/
structure Header where
  pairs : List (ℕ × E)
  c : List E
  groups : List (ℕ × Bool × List ℕ)
  pullLess : List ℕ
  publicTags : List ℕ
  coset : Option (ℕ × ℕ × List E)
  walk : List ℕ
  maxGamma : ℕ
  iv : List UInt8
  layoutWords : List (List UInt8)
  beta1 : E
  extension : List E
  streamLen : ℕ

/-- One vector. -/
structure Vec' where
  name : String
  publicInput : List UInt8
  stream : List UInt8
  traces : List (String × List E)
  result : String
  nonzero : List E
  scalars : List E
  pairPoints : List E
  roots : List E
  claims : List (String × List E × E)
  calls : List (List (List UInt8))
  contract : Option ℕ

/-- The lines of each key. -/
def linesOf (lines : List (List String)) (key : String) : List (List String) :=
  (lines.filter fun ts ↦ ts.head? = some key).map (·.drop 1)

def theLine (lines : List (List String)) (key : String) : Except String (List String) :=
  match linesOf lines key with
  | [ts] => pure ts
  | [] => throw s!"no {key} line"
  | _ => throw s!"several {key} lines"

def specLine (lines : List (List String)) (key : String) : Except String (List String) := do
  match (linesOf lines "SPEC").filter (·.head? = some key) with
  | [ts] => pure (ts.drop 1)
  | _ => throw s!"no single SPEC {key} line"

def constLine (lines : List (List String)) (key : String) : Except String (List String) := do
  match (linesOf lines "CONST").filter (·.head? = some key) with
  | [ts] => pure (ts.drop 1)
  | _ => throw s!"no single CONST {key} line"

def parseHeader (lines : List (List String)) : Except String Header := do
  let pairs ← onLine (many do let s ← nat; let z ← eElem; pure (s, z)) (← specLine lines "pairs")
  let c ← onLine (many eElem) (← specLine lines "c")
  let groups ← onLine (many do
    let role ← nat
    let pulls ← nat
    let ps ← many nat
    pure (role, pulls == 1, ps)) (← specLine lines "groups")
  let pullLess ← onLine (many nat) (← specLine lines "pullless")
  let publicTags ← onLine (many nat) (← specLine lines "public")
  let coset ← match ← specLine lines "coset" with
    | ["none"] => pure none
    | ts => some <$> onLine (do let tag ← nat; let k ← nat; let a ← many eElem; pure (tag, k, a)) ts
  let walk ← onLine (many nat) (← specLine lines "walk")
  let maxGamma ← onLine nat (← specLine lines "maxgamma")
  let iv ← onLine bytesP (← constLine lines "iv")
  let layoutWords ← onLine (do let a ← bytesP; let b ← bytesP; let c ← bytesP; pure [a, b, c])
    (← constLine lines "layoutwords")
  let beta1 ← onLine eElem (← constLine lines "beta1")
  let extension ← onLine (do let a ← eElem; let b ← eElem; let c ← eElem; pure [a, b, c])
    (← constLine lines "extension")
  let streamLen ← onLine nat (← constLine lines "streamlen")
  pure ⟨pairs, c, groups, pullLess, publicTags, coset, walk, maxGamma, iv, layoutWords, beta1, extension, streamLen⟩

def parseVector (lines : List (List String)) : Except String Vec' := do
  let name ← match ← theLine lines "VECTOR" with
    | [n] => pure n
    | _ => throw "bad VECTOR line"
  let publicInput ← onLine bytesP (← theLine lines "PUBLIC")
  let stream ← match ← theLine lines "STREAM" with
    | [] => pure []
    | ts => onLine bytesP ts
  let traces ← (linesOf lines "TRACE").mapM fun ts ↦ match ts with
    | step :: rest => do pure (step, ← onLine (many eElem) rest)
    | [] => throw "bad TRACE line"
  let result ← match ← theLine lines "RESULT" with
    | [r] => pure r
    | _ => throw "bad RESULT line"
  let ok := result == "ok"
  let listOr (key : String) : Except String (List E) :=
    if ok then do onLine (many eElem) (← theLine lines key) else pure []
  let nonzero ← listOr "NONZERO"
  let scalars ← listOr "PUBLICS"
  let pairPoints ← listOr "PAIRPOINTS"
  let roots ← listOr "ROOTS"
  let claims ← (linesOf lines "CLAIM").mapM fun ts ↦ match ts with
    | c :: rest => do
      let (pt, v) ← onLine (do let pt ← many eElem; let v ← eElem; pure (pt, v)) rest
      pure (c, pt, v)
    | [] => throw "bad CLAIM line"
  let calls ← (linesOf lines "CALL").mapM fun ts ↦ onLine (many bytesP) ts
  let contract := ((linesOf lines "CONTRACT").head?.bind (·.head?)).bind String.toNat?
  pure ⟨name, publicInput, stream, traces, result, nonzero, scalars, pairPoints, roots, claims, calls, contract⟩

/-- The file's header lines and its vectors' lines (`VECTOR` … `END`). -/
def split (text : String) : List (List String) × List (List (List String)) := Id.run do
  let mut header : List (List String) := []
  let mut vectors : List (List (List String)) := []
  let mut current : Option (List (List String)) := none
  for line in text.splitOn "\n" do
    let ts := tokens line
    match ts.head? with
    | none => pure ()
    | some "#" => pure ()
    | some "VECTOR" => current := some [ts]
    | some "END" =>
      if let some v := current then vectors := vectors ++ [v]
      current := none
    | some _ =>
      match current with
      | some v => current := some (v ++ [ts])
      | none => header := header ++ [ts]
  return (header, vectors)

/-! ## The comparisons -/

/-- The first disagreement, if any, of named comparisons. -/
def firstFailure (checks : List (String × Bool)) : Option String := (checks.find? (!·.2)).map (·.1)

/-- The spec, its arithmetic's constants and the IV (computed once). -/
def spec : Spec := Spec.of Data.circuit
def core : CoreSpec E := spec.core
def theIv : List UInt8 := RecStatement.iv Data.pi1Iv Data.digest Data.setupRoot Data.circuit.logN

def compareHeader (h : Header) : List (String × Bool) :=
  let (lw, lq, ls) := layoutWords Data.circuit.logN
  [("SPEC pairs", spec.pairs.map (fun p ↦ (p.logRows, kE p.z)) == h.pairs),
   ("SPEC c", spec.c.map kE == h.c),
   ("SPEC groups", spec.groups.map (fun g ↦ (g.role, g.pulls, g.pairs)) == h.groups),
   ("SPEC pullless", spec.pullLess == h.pullLess),
   ("SPEC public", spec.publicTerms.map (·.tag) == h.publicTags),
   ("SPEC coset", spec.zeroCoset.map (fun z ↦ (z.1, z.2.1, z.2.2.map kE)) == h.coset),
   ("SPEC walk", core.walk == h.walk),
   ("SPEC maxgamma", spec.maxGamma == h.maxGamma),
   ("CONST iv", theIv == h.iv),
   ("CONST layoutwords", [lw, lq, ls] == h.layoutWords),
   ("CONST beta1", cantorBeta1 == h.beta1),
   ("CONST extension", [extension.1.1, extension.1.2, extension.2] == h.extension),
   ("CONST streamlen", streamLen Data.circuit == h.streamLen)]

/-- The Lean's value of each trace step. -/
def leanTrace (r : Reduced) : List (String × List E) :=
  let o := r.out
  let side := if core.publicTerms.isEmpty then [] else
    let f := fraction o.publicDens
    [f.1, f.2]
  let coset := match core.zeroCoset with
    | some (tag, k, a) => let z := cosetSum core.ω r.inputs.α r.inputs.β tag k a; [z.1, z.2]
    | none => []
  [("challenges", [r.inputs.α, r.inputs.β, r.inputs.γ, r.inputs.t, r.inputs.ρ]),
   ("digits", o.digits), ("cells", o.cells), ("zt", o.zt),
   ("groups", o.groupFracs.flatMap fun nd ↦ [nd.1, nd.2]),
   ("public_terms", o.publicDens), ("public_side", side), ("zero_coset", coset),
   ("push", [o.num, o.den, o.sNum, o.sDen]),
   ("identity", [o.dPull, o.dNum, o.y, o.x, o.publicNum, o.publicDen, o.p1, o.p2, o.all]),
   ("inverse", [o.invAll, o.invP2, o.target, o.invP1, o.invTop]),
   ("digit_inverses", o.wInvs), ("u", o.uList),
   ("quotient", [o.rhoQ, o.combination, o.digitsScale, o.quotientValue]),
   ("rhos", o.rhos), ("fold", [o.fold])]

def permutation : LeanVM.Semantics.KeccakState → Id LeanVM.Semantics.KeccakState :=
  fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)

/-- The reduction before `finish` (an extended stream's trace is complete although the run fails). -/
def reduced (v : Vec') : Except UniStatement.UniError Reduced :=
  let seed := LeanVM.Protocol.KeccakHash.keccak256 (name ++ theIv ++ v.publicInput)
  (Id.run ((reduceWith (m := Id) permutation spec (UniStatement.publicWordsOf v.publicInput)).run.run
    (UniStatement.Chan.start seed v.stream.toArray))).1

/-- Compare one vector: the verdict, the trace, the values, the claims, the calls. `none` if every value agrees. -/
def compare (v : Vec') : Option String := Id.run do
  let o := RecStatement.run spec theIv v.publicInput v.stream.toArray
  let leanResult := match o.result with
    | .ok _ => "ok"
    | .error e => e.name
  if leanResult != v.result then return some s!"result: Lean {leanResult}, Rust {v.result}"
  let traceChecks : List (String × Bool) := match reduced v with
    | .ok r =>
      let lt := leanTrace r
      v.traces.map fun (step, values) ↦
        (s!"trace {step}", (lt.lookup step).any (· == values))
    | .error _ => if v.traces.isEmpty then [] else [("trace: Lean's reduction failed", false)]
  if let some f := firstFailure traceChecks then return some f
  if v.traces.length != (match reduced v with | .ok _ => 16 | .error _ => v.traces.length) then
    return some s!"trace steps: Rust {v.traces.length}"
  match o.result with
  | .error _ => return none
  | .ok r =>
    let claims : List (String × List E × E) :=
      [("witness", r.witness.1, r.witness.2), ("quotient", r.quotient.1, r.quotient.2),
       ("sum", r.sum.1, r.sum.2), ("setup", r.setup.1, r.setup.2)]
    let calls := pcsCalls Data.circuit Data.pi1Calls Data.setupRoot v.stream.toArray r
    let invOk := r.out.all == 0 || (normInverse r.out.all == r.out.all⁻¹ && normInverse r.out.all * r.out.all == 1)
    -- PCS_OPEN's decoding (the Props' verifier): every call decodes under the registry, π1's three by π1's layouts and
    -- π2's three by π2's, re-encodes to its words, and π2's claims are the reduction's.
    let reg := registryOf UniStatement.reference Data.circuit.logN
    let reencodes := v.calls.all fun words ↦
      match decodeWith reg words with
      | none => false
      | some (root, _, cs) =>
        [rootWordOfBytes (LeanVM.Protocol.KeccakHash.digestBytes root), words.getD 1 [], UniStatement.numberWord cs.length] ++
          cs.flatMap (fun c ↦ (c.point ++ [c.value]).map UniStatement.elementWord) == words
    let kinds := v.calls.map fun words ↦ match decodeWith reg words with
      | some (_, .pi1 _, _) => 1
      | some (_, .pi2 _, _) => 2
      | none => 0
    let pi2Claims := (v.calls.drop 3).map fun words ↦ (decodeWith reg words).map (·.2.2)
    let checks : List (String × Bool) :=
      [("nonzero", v.nonzero == [r.out.all]),
       ("verdict", o.accepts == (v.nonzero.all (· != 0))),
       ("publics", r.scalars == v.scalars),
       ("pair points", r.pairPoints.flatMap (fun p ↦ [p.1, p.2]) == v.pairPoints),
       ("roots", [r.roots.1.1, r.roots.1.2, r.roots.2.1, r.roots.2.2] == v.roots),
       ("claims", claims == v.claims),
       ("calls", calls == v.calls),
       ("the norm's inverse is the field's", invOk),
       ("PCS_OPEN: every call decodes and re-encodes", reencodes),
       ("PCS_OPEN: pi1's three by pi1's layouts, pi2's three by pi2's", kinds == [1, 1, 1, 2, 2, 2]),
       ("PCS_OPEN: pi2's decoded claims are the reduction's", pi2Claims ==
         [some [⟨r.witness.1, r.witness.2⟩], some [⟨r.setup.1, r.setup.2⟩],
          some [⟨r.quotient.1, r.quotient.2⟩, ⟨r.sum.1, r.sum.2⟩]]),
       ("the contract's calls", match v.contract with
         | some n => n == (if o.accepts then calls.length else 0)
         | none => true)]
    return firstFailure checks

/-! ## The self-tests (the Rust's unit tests, and the data against `formal/UniStatement`) -/

def sampleE (k : ℕ) : E :=
  UniStatement.eNew (UInt64.ofNat (0x1234_5678_9abc_def1 * (k + 3))) (UInt64.ofNat (0x0fed_cba9_8765_4321 + 7 * k))
    (UInt64.ofNat (0x5555_aaaa_3333_cccc ^^^ k))

/-- `inverse_inverts`. -/
def inverseTest : Bool := (List.range 8).all fun k ↦ normInverse (sampleE k) * sampleE k == 1

/-- `the_zero_coset_sum_is_its_closed_form` (`k ≤ 5`, the coset at `2^24`), and `w_k` vanishes on `V_k`. -/
def cosetTest : Bool :=
  let α := UniStatement.eNew 3 1 4
  let β := UniStatement.eNew 1 5 9
  subspaceCoefficients 4 == [1, 0, 0, 0, 1] && (List.range 5).all fun k' ↦
    let k := k' + 1
    let a := subspaceCoefficients k
    let wk (x : K) : K := (List.range a.length).foldl (fun acc i ↦ acc + a.getD i 0 * UniStatement.frobK x i) 0
    let vanishes := (List.range (2 ^ k)).all fun u ↦ wk (UniStatement.point u) == 0
    let c := 2 ^ 24
    let sum := (List.range (2 ^ k)).foldl (fun acc u ↦ acc + (α + β * UniStatement.pointE (c + u))⁻¹) 0
    let (n, f) := cosetSum UniStatement.pointE α β c k (a.map kE)
    vanishes && sum * f == n

/-- `indicators_select_their_cosets` (`m = 10`, `r = 4`): a pair's denominator `Ẑ_s(ω_i) + Ẑ_s(c_p)` vanishes exactly on
its coset; and `Ẑ_s = Z_{U_s} / Π_{j ≤ s} e_j` by the normalised recursion. -/
def indicatorTest : Bool :=
  let (m, r) := (10, 4)
  let e := cosetConstants r (m - r)
  let c := normalisedConstants e
  let pairs : List (ℕ × ℕ × ℕ) := [(0, 0, 0), (8, 3, 5), (16, 4, 15), (0, 6, 9), (37, 0, 3), (48, 4, 0)]
  (pairs.all fun (firstRow, logRows, role) ↦
    let p : Pair := ⟨firstRow, logRows, role, 0, true⟩
    let (z, norm) := pairConstants p r e
    (List.range (2 ^ m)).all fun i ↦
      let inside := firstRow ≤ i / 2 ^ r ∧ i / 2 ^ r < firstRow + 2 ^ logRows ∧ i % 2 ^ r = role
      ((vanishing (UniStatement.point i) e logRows + z) == 0) == decide inside &&
        zHat c logRows (UniStatement.point i) == vanishing (UniStatement.point i) e logRows * norm⁻¹) &&
  (List.range 7).all fun s ↦ zHat c s (UniStatement.point 77) * (e.take s).foldl (· * ·) 1 ==
    vanishing (UniStatement.point 77) e s

/-- `β_1² + β_1 = 1`, its low bit clear. -/
def beta1Test : Bool := cantorBeta1 * cantorBeta1 + cantorBeta1 == 1 && ((cantorBeta1.limb 0).lane &&& 1) == 0

/-- π1's contract IV is `contract_iv_for` at the reference shape, π1-rec3, the program's IV and the reference roots;
π1's calls' constants are the reference layout words, one claim each, and `F`'s root word. -/
def pi1Test : List (String × Bool) :=
  let words := UniStatement.layoutWords UniStatement.reference
  let calls := Data.pi1Calls
  let constAt (call : List CallWord) (k : ℕ) : Option (List UInt8) := match call.getD k (.root 0) with
    | .const w => some w
    | _ => none
  [("pi1's contract IV", pi1Iv UniStatement.reference UniStatement.programIv UniStatement.referenceRoots == Data.pi1Iv),
   ("pi1's layout words", (List.range 3).all fun k ↦ constAt (calls.getD k []) 1 == some (words.getD k [])),
   ("pi1's claim counts", (List.range 3).all fun k ↦ constAt (calls.getD k []) 2 == some (UniStatement.numberWord 1)),
   ("pi1's roots: C1, C2 from the stream, F's root word", calls.length == 3 &&
     (calls.getD 0 []).head? == some (.root 0) && (calls.getD 1 []).head? == some (.root 1) &&
     constAt (calls.getD 2 []) 0 ==
       some (rootWordOfBytes (LeanVM.Protocol.KeccakHash.digestBytes UniStatement.referenceRoots.bytecode)))]

def selfTests : List (String × Bool) :=
  [("the norm's inverse inverts", inverseTest), ("the zero coset's closed form; w_k vanishes on V_k", cosetTest),
   ("the indicators' cosets; the normalised recursion", indicatorTest), ("beta_1", beta1Test)] ++ pi1Test

def main : IO Unit := do
  for (n, ok) in selfTests do
    IO.println s!"{if ok then "SELF-TEST OK" else "SELF-TEST FAILED"} {n}"
  if !selfTests.all (·.2) then throw (IO.userError "a self-test failed")
  let path := (← IO.getEnv "REC_STATEMENT_VECTORS").getD "rec_statement_vectors.txt"
  let text ← IO.FS.readFile path
  let (headerLines, vectors) := split text
  match parseHeader headerLines with
  | .error e => throw (IO.userError s!"unreadable header: {e}")
  | .ok h =>
    for (n, ok) in compareHeader h do
      IO.println s!"{if ok then "CONSTANT OK" else "CONSTANT DISAGREES"} {n}"
    if !(compareHeader h).all (·.2) then throw (IO.userError "a constant disagrees")
  let mut agree := 0
  let mut accepted := 0
  let mut rejected := 0
  let mut failures : List String := []
  let start ← IO.monoMsNow
  for lines in vectors do
    match parseVector lines with
    | .error e =>
      failures := failures ++ [s!"unreadable vector: {e}"]
      IO.println s!"UNREADABLE {e}"
    | .ok v =>
      match compare v with
      | none =>
        agree := agree + 1
        let acc := v.result == "ok" && v.nonzero.all (· != 0)
        if acc then accepted := accepted + 1 else rejected := rejected + 1
        IO.println s!"AGREE {v.name}: {if acc then "accept" else s!"reject {v.result}"}, {v.traces.length} trace steps, {v.calls.length} calls ({(v.calls.map (·.length)).sum} words)"
      | some d =>
        failures := failures ++ [s!"{v.name}: {d}"]
        IO.println s!"DISAGREE {v.name}: {d}"
  let stop ← IO.monoMsNow
  IO.println s!"SUMMARY {agree}/{vectors.length} vectors agree on every value; accepted by both {accepted}, rejected by both {rejected}; {(stop - start) / 1000} s"
  if !failures.isEmpty then throw (IO.userError s!"{failures.length} disagreements: {failures}")

end RecStatementTest

#eval RecStatementTest.main
