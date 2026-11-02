/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

Review of layer F2 (`formal/WhirBridge`), experiment 2: the branch of `opening::verify`'s weight closure
the bridge does not transcribe (a hidden layout, `opening.rs:702-717`), transcribed here, and run with
mumbai's `verifyWhir` and the deployed Keccak on a deployed witness opening (`witness_layout(17)`, the
real prover; `crates/quotient/tests/review_f2f3.rs` writes the vector with `REVIEW_F2_HIDDEN_VECTOR`).
The bridge's own `openingCheck` (its `witnessLayout 17`) rejects that proof (`Test/Check.lean` on the
`REVIEW_F2_VECTOR` file prints `honest proof accepted: false`); the same program with this weight
accepts it. So mumbai's verifier covers the deployed proof; what is missing is the transcription (and
`isMultiaffine`, `holds_iff` for it).

  cd formal/WhirBridge && lake env lean --run ../Review/HiddenWeight.lean <hidden vector>
-/
import WhirBridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash WhirBridge

namespace WhirBridge.Review

/-- What a lane of a hidden layout holds (`opening::Lane`). -/
inductive HLane where
  | block (b : ℕ)
  | overflow
  | random
  deriving Inhabited, BEq

/-- `opening::Layout` with a piece (`Layout::hidden`). -/
structure HLayout where
  vars : ℕ
  logN : ℕ
  lanes : List HLane
  logPiece : ℕ
  pieces : List ℕ
  share : ℕ

namespace HLayout

def logLane (L : HLayout) : ℕ := L.logN - laneFold

def overflow (L : HLayout) : ℕ := (L.lanes.findIdx? (· == .overflow)).getD 0

/-- `Layout::scales` (`opening.rs:243-259`). -/
def scales (L : HLayout) (point : List E) : List E × List E :=
  (L.lanes.map fun
      | .block b => eqBits (point.drop L.logLane) b
      | _ => 0,
    L.pieces.map fun p => eqBits (point.drop L.logPiece) p)

end HLayout

/-- `eq` as `verify` folds it (`opening.rs:681-682`), zipping. -/
def eqZ (a b : List E) : E := (a.zip b).foldl (fun w cp => w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) 1

/-- **The weight closure of `opening::verify` for a hidden layout** (`opening.rs:667-718`, the
`Some(s)` branch), at a stack point `x`. -/
def hiddenWeight (L : HLayout) (ls : List E) (claims : List Claim) (x : List E) : E :=
  let s := L.logPiece
  let low := x.take L.logLane
  let high := x.drop L.logLane
  let laneEq := fun l => eqBits high l
  let parts := (claims.zip ls).map fun cl =>
    let sc := L.scales cl.1.point
    (cl.1.point.take L.logLane, sc.1.map (cl.2 * ·), sc.2.map (cl.2 * ·))
  parts.foldl (fun acc part =>
    let on := fun (odd : ℕ) => (L.lanes.zipIdx.zip part.2.1).foldl (fun sum lw =>
      match lw.1.1 with
      | .block _ => if lw.1.2 % 2 = odd then sum + lw.2 * laneEq lw.1.2 else sum
      | _ => sum) 0
    let pl := part.1
    let below := eqZ (pl.take s) (low.take s)
    let above := eqZ (pl.drop (s + 1)) (low.drop (s + 1))
    let firstAbove := (pl.drop (s + 1)).foldl (fun w p => w * (1 + p)) 1
    let firstPiece := (low.drop s).foldl (fun w p => w * (1 + p)) 1
    let ls := low.getD s 0
    let block := fun (c : E) => above * (c * ls + (1 + c) * (1 + ls)) + firstAbove * (1 + c) * firstPiece
    let even := block (pl.getD s 0)
    let odd := block (1 + pl.getD s 0)
    let pieces := part.2.2.zipIdx.foldl (fun sum wk => sum + wk.1 * eqBits (low.drop s) (wk.2 + 1)) 0
    let onOverflow := laneEq L.overflow + laneEq L.share
    acc + below * (even * on 0 + odd * on 1 + pieces * onOverflow)) 0

/-- `opening::verify` for a hidden layout, as a program of mumbai's language. -/
def hiddenCheck (L : HLayout) (R : ℕ) (claims : List Claim) : Prog Unit := do
  Prog.require (∀ c ∈ claims, c.point.length = L.vars)
  let lam ← Prog.sampleChallenge
  let ls := lambdas lam claims.length
  verifyWhir L.logN R (target ls claims) (hiddenWeight L ls claims)

/-- `openingVerifyWithHash` (`Gaps.lean`) with `hiddenCheck`. -/
def hiddenVerify (L : HLayout) (root : Digest) (claims : List Claim) (π : Proof) : Bool :=
  Id.run do
    let iv ← (keccak256 label : Id Digest)
    let pd ← (keccak256 (statementBytes root claims) : Id Digest)
    let seed ← (keccakF1600 (seedInput iv pd) : Id KeccakState)
    match ← runWithHash (m := Id) keccak256 keccakF1600
        ((hiddenCheck L logInvRate claims).bind fun _ ↦ Prog.ret true)
        ⟨⟨seed, []⟩, π.stream, π.openings, [(root, L.logN - laneFold + logInvRate, 2 ^ laneFold)]⟩ with
    | some (true, s) => pure (s.stream.isEmpty && s.openings.isEmpty)
    | _ => pure false

end WhirBridge.Review

open WhirBridge.Review

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

/-- A lane from its code in the vector: `2b` a block `b`, `1` the overflow lane, `3` random. -/
def lane (n : ℕ) : HLane := if n % 2 = 0 then .block (n / 2) else if n = 1 then .overflow else .random

def main (args : List String) : IO UInt32 := do
  let text ← IO.FS.readFile (args.getD 0 "review_f2_hidden_vector.txt")
  let lines := text.splitOn "\n"
  let tagged := fun (t : String) ↦ (lines.filter fun l ↦ l.startsWith (t ++ " ")).map nums
  let h := (tagged "hidden").headD []
  let n := h.getD 4 0
  let L : HLayout := ⟨h.getD 0 0, h.getD 1 0, ((h.drop 5).take n).map lane, h.getD 2 0,
    (tagged "pieces").headD [], h.getD 3 0⟩
  let root := (digests ((tagged "root").headD [])).headD default
  let claims := (tagged "claim").map fun c ↦
    let xs := scalars c
    (⟨xs.take L.vars, xs.getD L.vars 0⟩ : Claim)
  let stream := scalars ((tagged "stream").headD [])
  let openings := (tagged "open").map fun o ↦
    let k := o.getD 0 0
    (⟨((o.drop 1).take k).map fun w ↦ K.ofLane w.toUInt64, digests (o.drop (1 + k))⟩ : Opening)
  let π : Proof := ⟨stream, openings⟩
  IO.println s!"hidden layout: {L.vars} variables, log_n {L.logN}, {L.lanes.length} lanes, piece 2^{L.logPiece}, {L.pieces.length} pieces, share {L.share}, overflow {L.overflow}; {claims.length} claims"
  let honest := hiddenVerify L root claims π
  IO.println s!"deployed opening accepted with the hidden weight: {honest}"
  let wrong := claims.map fun c ↦ { c with value := c.value + 1 }
  let rejectWrong := !hiddenVerify L root wrong π
  IO.println s!"wrong value rejected: {rejectWrong}"
  return if honest && rejectWrong then 0 else 1
