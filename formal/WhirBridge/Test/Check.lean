/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

Runs the Lean mirror of `opening::verify` (`WhirBridge.openingVerifyWithHash`, over leanerVM mumbai's
Keccak-256 and Keccak-f[1600], `Statement/Keccak.lean`) on an opening proof made by the Rust prover:
`crates/quotient/tests/whir_bridge_vector.rs` writes it, the pruned Merkle batches expanded into one full
path per query (mumbai's `Proof`).

  cargo test -p quotient --release --test whir_bridge_vector -- --ignored
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

/-- `opening::verify` in Lean, with the deployed Keccak. -/
def verifyId (L : Layout) (root : Digest) (claims : List Claim) (π : Proof) : Bool :=
  Id.run (openingVerifyWithHash (m := Id) keccak256 keccakF1600 L logInvRate root claims π)

def main (args : List String) : IO UInt32 := do
  let text ← IO.FS.readFile (args.getD 0 "whir_bridge_vector.txt")
  let lines := text.splitOn "\n"
  let tagged := fun (t : String) ↦ (lines.filter fun l ↦ l.startsWith (t ++ " ")).map nums
  let lay := (tagged "layout").headD []
  let vars := lay.getD 0 0
  let L : Layout := ⟨vars, lay.getD 1 0, (lay.drop 3).take (lay.getD 2 0)⟩
  let root := ((digests ((tagged "root").headD [])).headD default)
  let claims := (tagged "claim").map fun c ↦
    let xs := scalars c
    (⟨xs.take vars, xs.getD vars 0⟩ : Claim)
  let stream := scalars ((tagged "stream").headD [])
  let openings := (tagged "open").map fun o ↦
    let n := o.getD 0 0
    (⟨((o.drop 1).take n).map fun w ↦ K.ofLane w.toUInt64, digests (o.drop (1 + n))⟩ : Opening)
  let π : Proof := ⟨stream, openings⟩
  IO.println s!"layout: {vars} variables, log_n {L.logN}, {L.lanes} lanes; {claims.length} claims; {stream.length} scalars, {openings.length} paths"
  let honest := verifyId L root claims π
  IO.println s!"honest proof accepted: {honest}"
  let wrong := claims.set 1 { claims[1]! with value := claims[1]!.value + 1 }
  let rejectWrong := !verifyId L root wrong π
  IO.println s!"wrong value rejected: {rejectWrong}"
  let tampered : Proof := ⟨stream.set 5 (stream[5]! + 1), openings⟩
  let rejectTampered := !verifyId L root claims tampered
  IO.println s!"tampered stream rejected: {rejectTampered}"
  let pathTampered : Proof := ⟨stream, openings.set 0
    { openings[0]! with leaf := openings[0]!.leaf.set 63 (openings[0]!.leaf[63]! + 1) }⟩
  let rejectPath := !verifyId L root claims pathTampered
  IO.println s!"tampered leaf rejected: {rejectPath}"
  return if honest && rejectWrong && rejectTampered && rejectPath then 0 else 1
