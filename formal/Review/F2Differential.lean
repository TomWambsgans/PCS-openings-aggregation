/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (F0a/F2/F4 review).

Runs the Lean `opening::verify` (`WhirBridge.openingVerifyWithHash`, mumbai's Keccak) on the vectors of
`crates/quotient/tests/review_f0f2f4.rs`: an opening of the **deployed wiring layout at `2^22` rows**
(which `Test/Check.lean` never runs), and generic tamperings of it, each against the Rust verdict the vector
records. A tampering the Rust accepts and the Lean rejects would be a proof the theorem does not cover.

  cargo test -p quotient --release --test review_f0f2f4 -- --ignored --nocapture
  (cd formal/Compose && lake env lean --run ../Review/F2Differential.lean ../../target/review_f0f2f4_vector.txt)
-/
import WhirBridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash WhirBridge

instance : Inhabited Claim := ⟨⟨[], 0⟩⟩
instance : Inhabited Opening := ⟨⟨[], []⟩⟩

def nums (l : String) : List ℕ := ((l.splitOn " ").drop 1).filterMap String.toNat?

def scalars : List ℕ → List E
  | a :: b :: c :: rest =>
    E.ofLimbs (K.ofLane a.toUInt64) (K.ofLane b.toUInt64) (K.ofLane c.toUInt64) :: scalars rest
  | _ => []

def digests : List ℕ → List Digest
  | a :: b :: c :: d :: rest =>
    (Vector.ofFn fun i : Fin 4 ↦ ([a, b, c, d].getD i 0).toUInt64) :: digests rest
  | _ => []

def pairs : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: pairs rest
  | _ => []

def verifyId (L : Layout) (root : Digest) (claims : List Claim) (π : Proof) : Bool :=
  Id.run (openingVerifyWithHash (m := Id) keccak256 keccakF1600 L logInvRate root claims π)

def bytesNat (b : Bytes) : List ℕ := b.map (·.toNat)

def main (args : List String) : IO UInt32 := do
  let text ← IO.FS.readFile (args.getD 0 "review_f0f2f4_vector.txt")
  let lines := text.splitOn "\n"
  let tagged := fun (t : String) ↦ (lines.filter fun l ↦ l.startsWith (t ++ " ")).map nums
  let h := (tagged "new").headD []
  let L := Layout.new (h.getD 0 0) (h.getD 1 0) (h.getD 2 0) (pairs (h.drop 3))
  let deployed := L == wiringLayout 22
  IO.println s!"layout: {L.vars} vars, log_n {L.logN}, {L.lanes.length} lanes; = wiringLayout 22: {deployed}"
  let preOk := bytesNat (openingPrefix L logInvRate) == (tagged "prefix").headD []
  IO.println s!"prefix recomputed: {preOk}"
  let root := (digests ((tagged "root").headD [])).headD default
  let claims := (tagged "claim").map fun c ↦
    let xs := scalars c
    (⟨xs.take L.vars, xs.getD L.vars 0⟩ : Claim)
  let stream := scalars ((tagged "stream").headD [])
  let openings := (tagged "open").map fun o ↦
    let n := o.getD 0 0
    (⟨((o.drop 1).take n).map fun w ↦ K.ofLane w.toUInt64, digests (o.drop (1 + n))⟩ : Opening)
  let π : Proof := ⟨stream, openings⟩
  let c0 := claims.headD default
  let s0 := stream.headD 0
  let s1 := stream.getD 1 0
  let variant : String → Bool
    | "honest" => verifyId L root claims π
    | "dupclaim" => verifyId L root [c0, c0] π
    | "noclaims" => verifyId L root [] π
    | "longpoint" => verifyId L root [{ c0 with point := c0.point ++ [0] }] π
    | "trailing" => verifyId L root claims ⟨stream ++ [0], openings⟩
    | "rootc2" => verifyId L root claims
        ⟨stream.set 0 (E.ofLimbs (s0.limb 0) (s0.limb 1) 1), openings⟩
    | "swaproot" => verifyId L root claims ⟨(stream.set 0 s1).set 1 s0, openings⟩
    | "truncated" => verifyId L root claims ⟨stream.dropLast, openings⟩
    | _ => false
  let mut ok := deployed && preOk
  for l in lines.filter (·.startsWith "variant ") do
    let ws := l.splitOn " "
    let name := ws.getD 1 ""
    let rust := ws.getD 2 "" == "1"
    let lean := variant name
    IO.println s!"variant {name}: rust {rust}, lean {lean}{if rust == lean then "" else "  MISMATCH"}"
    ok := ok && (rust == lean)
  IO.println s!"all agree: {ok}"
  return if ok then 0 else 1
