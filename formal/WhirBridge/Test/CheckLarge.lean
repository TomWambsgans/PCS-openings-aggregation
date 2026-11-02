/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Adapted from `Test/Check.lean` (this
repository): the same parsing and the same checks, on public openings only.

Runs the Lean `opening::verify` (`WhirBridge.openingVerifyWithHash`, over leanerVM mumbai's Keccak-256
and Keccak-f[1600]) on public openings of `2^24 ..= 2^28` words made by the Rust prover
(`crates/quotient/tests/whir_large_params.rs`, `large_public_openings`, which writes
`target/whir_large_vector.txt`): for each, the layout is rebuilt by the Lean `Layout.new` from the
constructor's arguments, `NewOK` (the hypothesis of `ours_sound_public`) evaluated on it, its prefix
recomputed and compared with the Rust's, the honest proof accepted, and a wrong value, a wrong expected
root, a changed stream scalar, a changed leaf word, no claim at all and a wrong prefix rejected.

  WHIR_LARGE_MAX=28 cargo test --release -p quotient --test whir_large_params -- --ignored large_public_openings
  lake env lean --run Test/CheckLarge.lean ../../target/whir_large_vector.txt
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

/-- Check one public opening; `true` when every check passes. -/
def checkVector (name : String) (lines : List String) : IO Bool := do
  let tagged := fun (t : String) ↦ (lines.filter fun l ↦ l.startsWith (t ++ " ")).map nums
  let some h := (tagged "new").head? | throw (IO.userError s!"{name}: no public layout")
  let (vars, logChunk, logN, chunks) := (h.getD 0 0, h.getD 1 0, h.getD 2 0, pairs (h.drop 3))
  let L := Layout.new vars logChunk logN chunks
  let ok := decide (NewOK vars logChunk logN chunks) && decide (largeMin ≤ logN ∧ logN ≤ largeMax)
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
  IO.println s!"{name}: {L.vars} variables, log_n {L.logN}, {chunks.length} chunks, {L.lanes.length} lanes; {claims.length} claims; {stream.length} scalars, {openings.length} paths"
  IO.println s!"  NewOK and 24 ≤ log_n ≤ 28 (ours_sound_public's hypotheses): {ok}"
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
  -- the same layout with one more overflow piece: only its id (the prefix) reads it
  let L' := { L with pieces := L.pieces ++ [12345] }
  let rejectPrefix := openingPrefix L' logInvRate != openingPrefix L logInvRate &&
    !verifyId L' root claims π
  IO.println s!"  wrong prefix rejected: {rejectPrefix}"
  return ok && preOk && honest && rejectWrong && rejectRoot && rejectTampered && rejectPath &&
    rejectEmpty && rejectPrefix

def main (args : List String) : IO UInt32 := do
  let text ← IO.FS.readFile (args.getD 0 "whir_large_vector.txt")
  let vs := vectors (text.splitOn "\n")
  let mut ok := !vs.isEmpty
  for (name, body) in vs do
    ok := (← checkVector name body) && ok
  IO.println s!"{vs.length} public openings; all checks: {ok}"
  return if ok then 0 else 1
