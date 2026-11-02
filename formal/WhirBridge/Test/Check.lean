/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

Runs the Lean `opening::verify` (`WhirBridge.openingVerifyWithHash`, over leanerVM mumbai's Keccak-256
and Keccak-f[1600], `Statement/Keccak.lean`) on openings made by the Rust prover, and recomputes the
prefixes of the protocol's layouts. `crates/quotient/tests/whir_bridge_vector.rs` writes the vectors: a
public layout, the deployed witness and quotient layouts at `2^17` rows, and the 76-byte prefix of each
of the 18 layouts the protocol opens. For each opening: the layout is rebuilt from its constructor's
arguments by the Lean `Layout.new` / `Layout.hidden`, its prefix recomputed and compared with the
Rust's, the honest proof accepted, and a wrong value, a wrong expected root, a changed stream scalar,
a changed leaf word and no claim at all rejected (and, on the public layout, a wrong prefix: the same
layout with one more overflow piece, which only its id reads; on the hidden layouts, the honest proof
against the weight without the gadget's term, so the gadget's transcription is exercised). For each
of the 18 layouts: the Lean `witnessLayout`, `wiringLayout`, `quotientLayout` give the Rust's
prefix, and the 18 prefixes are distinct.

  cargo test -p quotient --release --test whir_bridge_vector -- --ignored   # from the repository root
  lake env lean --run Test/Check.lean ../../target/whir_bridge_vector.txt
-/
import WhirBridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash WhirBridge

instance : Inhabited Claim := ⟨⟨[], 0⟩⟩
instance : Inhabited Opening := ⟨⟨[], []⟩⟩

/-- The numbers after a line's tag. -/
def nums (l : String) : List ℕ := ((l.splitOn " ").drop 1).filterMap String.toNat?

/-- Scalars from their limbs, three at a time. -/
def scalars : List ℕ → List E
  | a :: b :: c :: rest =>
    E.ofLimbs (K.ofLane a.toUInt64) (K.ofLane b.toUInt64) (K.ofLane c.toUInt64) :: scalars rest
  | _ => []

/-- Digests from their words, four at a time. -/
def digests : List ℕ → List Digest
  | a :: b :: c :: d :: rest =>
    (Vector.ofFn fun i : Fin 4 ↦ ([a, b, c, d].getD i 0).toUInt64) :: digests rest
  | _ => []

/-- Pairs, two at a time. -/
def pairs : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: pairs rest
  | _ => []

/-- `opening::verify` in Lean, with the deployed Keccak. -/
def verifyId (L : Layout) (root : Digest) (claims : List Claim) (π : Proof) : Bool :=
  Id.run (openingVerifyWithHash (m := Id) keccak256 keccakF1600 L logInvRate root claims π)

/-- `opening::verify` in Lean with the gadget's term left out of the weight (a hidden layout's
honest proof must fail it: the gadget's term is read). -/
def verifyNoGadget (L : Layout) (root : Digest) (claims : List Claim) (π : Proof) : Bool :=
  let prog : Prog Bool := do
    LeanVM.Protocol.Verifier.commitStack L.logN logInvRate
    Prog.require (∀ c ∈ claims, c.point.length = L.vars)
    let lam ← Prog.sampleChallenge
    let ls := lambdas lam claims.length
    LeanVM.Protocol.Verifier.verifyWhir L.logN logInvRate (target ls claims) fun x ↦
      L.weight ls claims x - gadgetSum (L.gadgetParts (ls.getD claims.length 0))
        (laneEqs L.lanes.length (x.drop L.logLane)) (x.take L.logLane)
    return true
  Id.run do
    let iv ← keccak256 (openingPrefix L logInvRate ++ claimsBytes claims)
    let seed ← keccakF1600 (seedInput iv publicDigest)
    if rootOf π = some root then runProofWithHash (m := Id) keccak256 keccakF1600 prog seed π
    else pure false

def bytesNat (b : Bytes) : List ℕ := b.map (·.toNat)

/-- The vectors: the lines between `vector <name>` and `end`. -/
def vectors : List String → List (String × List String)
  | [] => []
  | l :: rest =>
    if l.startsWith "vector " then
      let body := rest.takeWhile (· != "end")
      ((l.drop 7).toString, body) :: vectors (rest.drop (body.length + 1))
    else vectors rest
termination_by ls => ls.length
decreasing_by all_goals (simp_wf; try omega)

/-- Check one opening; `true` when every check passes. -/
def checkVector (name : String) (lines : List String) : IO Bool := do
  let tagged := fun (t : String) ↦ (lines.filter fun l ↦ l.startsWith (t ++ " ")).map nums
  let L : Layout ←
    match (tagged "new").head?, (tagged "hidden").head? with
    | some h, _ => pure (Layout.new (h.getD 0 0) (h.getD 1 0) (h.getD 2 0) (pairs (h.drop 3)))
    | none, some h => pure (Layout.hidden (h.getD 0 0) (h.getD 1 0) (h.getD 2 0) (pairs (h.drop 5))
        (h.getD 3 0) (h.getD 4 0))
    | none, none => throw (IO.userError s!"{name}: no layout")
  let pre := (tagged "prefix").headD []
  let preOk := bytesNat (openingPrefix L logInvRate) == pre
  let root := (digests ((tagged "root").headD [])).headD default
  let claims := (tagged "claim").map fun c ↦
    let xs := scalars c
    (⟨xs.take L.vars, xs.getD L.vars 0⟩ : Claim)
  let stream := scalars ((tagged "stream").headD [])
  let openings := (tagged "open").map fun o ↦
    let n := o.getD 0 0
    (⟨((o.drop 1).take n).map fun w ↦ K.ofLane w.toUInt64, digests (o.drop (1 + n))⟩ : Opening)
  let π : Proof := ⟨stream, openings⟩
  IO.println s!"{name}: {L.vars} variables, log_n {L.logN}, {L.lanes.length} lanes, piece {L.logPiece}, {L.pieces.length} pieces; {claims.length} claims; {stream.length} scalars, {openings.length} paths"
  IO.println s!"  prefix recomputed: {preOk}"
  let honest := verifyId L root claims π
  IO.println s!"  honest proof accepted: {honest}"
  let wrong := claims.set 0 { claims[0]! with value := claims[0]!.value + 1 }
  let rejectWrong := !verifyId L root wrong π
  IO.println s!"  wrong value rejected: {rejectWrong}"
  let badRoot : Digest := root.set 0 (root[0] ^^^ 1)
  let rejectRoot := !verifyId L badRoot claims π
  IO.println s!"  wrong root rejected: {rejectRoot}"
  let tampered : Proof := ⟨stream.set 5 (stream[5]! + 1), openings⟩
  let rejectTampered := !verifyId L root claims tampered
  IO.println s!"  tampered stream rejected: {rejectTampered}"
  let pathTampered : Proof := ⟨stream, openings.set 0
    { openings[0]! with leaf := openings[0]!.leaf.set 63 (openings[0]!.leaf[63]! + 1) }⟩
  let rejectPath := !verifyId L root claims pathTampered
  IO.println s!"  tampered leaf rejected: {rejectPath}"
  let rejectEmpty := !verifyId L root [] π
  IO.println s!"  no claim rejected: {rejectEmpty}"
  let rejectPrefix ← if L.logPiece.isNone then do
      -- the same public layout with one more overflow piece: only its id (the prefix) reads it
      let L' := { L with pieces := L.pieces ++ [12345] }
      let r := openingPrefix L' logInvRate != openingPrefix L logInvRate &&
        !verifyId L' root claims π
      IO.println s!"  wrong prefix rejected: {r}"
      -- control: a public layout has no gadget, so the verifier without its term accepts
      let c := verifyNoGadget L root claims π
      IO.println s!"  (control) accepted without the gadget's term, which it has none of: {c}"
      pure (r && c)
    else do
      -- the honest proof against the weight without the gadget's term
      let r := !verifyNoGadget L root claims π
      IO.println s!"  without the gadget's term rejected: {r}"
      pure r
  return preOk && honest && rejectWrong && rejectRoot && rejectTampered && rejectPath &&
    rejectEmpty && rejectPrefix

def main (args : List String) : IO UInt32 := do
  let text ← IO.FS.readFile (args.getD 0 "whir_bridge_vector.txt")
  let lines := text.splitOn "\n"
  let mut ok := true
  let vs := vectors lines
  if vs.length != 3 then
    IO.println s!"expected 3 vectors, found {vs.length}"
    ok := false
  for (name, body) in vs do
    ok := (← checkVector name body) && ok
  -- the 18 layouts' prefixes
  let pres := (lines.filter fun l ↦ l.startsWith "layoutprefix ").map nums
  let mut computed : List (List ℕ) := []
  for p in pres do
    let code := p.getD 0 0
    let r := p.getD 1 0
    let L := match code with
      | 0 => witnessLayout r
      | 1 => wiringLayout r
      | _ => quotientLayout r
    let mine := bytesNat (openingPrefix L logInvRate)
    computed := computed ++ [mine]
    if mine != p.drop 2 then
      IO.println s!"layout {code} at 2^{r} rows: prefix differs from the Rust's"
      ok := false
  let distinct := computed.length == 18 && computed.Nodup
  IO.println s!"18 layouts' prefixes recomputed: {pres.length == 18 && ok}, distinct: {distinct}"
  ok := ok && pres.length == 18 && distinct
  IO.println s!"all checks: {ok}"
  return if ok then 0 else 1
