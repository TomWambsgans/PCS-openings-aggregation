-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/pi2/prover.rs`
-- (`halves`, `public_scalars`, `prove_with`, `quotient_on_extension`, `open`; `PI2.md` §3), branch `leanvm-rec-opt`.
-- The writer and the commitments are `formal/UniComplete`'s (`Wr`, `sendRoot`, `sampleW`, `commitWithH`), the WHIR
-- openings `formal/EndToEnd/Completeness`'s (`proveOpeningWithH`), the transforms `formal/Statement`'s
-- (`PcsQuotient.Domain.values`, `coefficients`).
import RecCompose.Tables
import UniComplete.Prover
import UniComplete.AlgHPoly

/-!
# π2's honest prover

`prover.rs`, phase by phase, over a Keccak-256 `H` (and the permutation `F` for WHIR's proofs of work), for any
circuit as π2's PIOP reads it (`RecPiop.Circuit E`: positions, roles, blocks, `σ`, `κ`, ports; the compiled circuit's
`toPiop` at the deployment):

1. **the public values** (`PublicValue`), each as its read takes it (`sendInteger`, `sendRoot` of `halvesOf`, `sendScalar`);
2. **`W`**: the witness's basis-`B` coefficients (`bCoefficients`), placed under `W`'s layout (`placePublic`),
   committed (`commitWithH`), its root's halves; `α, β, γ`;
3. **`h` on `V_m`** (`hValues`): `[pull]/(α + w_i + β ω_i) + 1/(α + P_i + β ω_{σ_i})`, `P_i` the circuit's push; its
   novel coefficients;
4. **`q` on the extension coset** `D = β_{m+2} + V_{m+2}` (`qValues`, `4N` points, disjoint from `V_m`): `w`, `σ`, `κ`, `h`
   by the transform (`onCoset`), the row's cells `w(x + ω_c)` (index `p ⊕ c`), each pair's indicator (`indAt`, the
   polynomial `RecPiop.Circuit.ind` at the point), the push `P`, `d_pull`, `d_push`, and
   `q = (h d_pull d_push + (1 + 1_S) d_push + d_pull) / Z_V`; `q`'s novel coefficients (`coefficients` at `D`'s offset);
5. **`Q`**: `h`'s and `q`'s novel coefficients, three limbs each (`qEntry`: entry `pd + 2^(m+2)(kind + 2 limb)`), placed
   under `Q`'s layout, committed, its root's halves; `t`;
6. **the values at `t`**: the `2^r` fold values (`foldValues`: `W`'s table's partial evaluation at `w_r(t), …, w_{m−1}(t)`)
   and `ξ = κ(t) + β σ(t)` from the setup's halves `κ`, `κ + σ` (`xiOf`, PI2.md §9); `ρ`.

`pi2ProveWith` adds the seed `keccak(NAME ‖ IV ‖ public input)` and the three WHIR openings (`W`'s claim, the setup's,
`Q`'s two, in the contract's call order), the claims the verifier's arithmetic on the prover's own inputs
(`CoreSpec.run`, which the verifier's run on the stream reproduces); `none` if a proof of work fails.

Decisions: the prover is mathematical, not vectorised: one value per point, the indicators by their products (no
batched inversion); the kinds of read and value that do not match are skipped (the Rust panics). Every function here is
computable (the differential test runs it, `RecComposeTest/Pi2Prover.lean`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash Finset

/-! ## The public values -/

/-- **A public value** as the stream carries it (`PublicValue`): an integer, 32 bytes as they are (π1's roots as
`PCS_OPEN`'s root words), an element of `E`. -/
inductive PublicValue where
  | integer (x : ℕ)
  | root (bytes : List UInt8)
  | scalar (x : E)
  deriving Inhabited

/-- **`halves(bytes)`**: the two scalars `next_root` reads from 32 bytes, each 16-byte half big-endian limbs `1, 0`. -/
def halvesOf (b : List UInt8) : E × E :=
  (UniStatement.eNew (UniStatement.beWordAt b.toArray 8) (UniStatement.beWordAt b.toArray 0) 0,
    UniStatement.eNew (UniStatement.beWordAt b.toArray 24) (UniStatement.beWordAt b.toArray 16) 0)

/-- A public value's scalars (`public_scalars`' arms). -/
def PublicValue.scalars : PublicValue → List E
  | .integer x => [UniStatement.eK (UInt64.ofNat x)]
  | .root b => [(halvesOf b).1, (halvesOf b).2]
  | .scalar x => [x]

/-- **`public_scalars(public_input, values)`**: the public input's four words, then the values'. -/
def publicScalarsOf (input : List UInt8) (values : List PublicValue) : List E :=
  UniStatement.publicWordsOf input ++ values.flatMap PublicValue.scalars

section Send

variable {m : Type → Type} [Monad m]

/-- **The public values written** as their reads take them (`send_integer`, `send_root(halves)`, `send`). -/
def sendPublic : List (Read × PublicValue) → UniComplete.WrM m Unit
  | [] => pure ()
  | (.integer b, .integer x) :: rest => do
    UniComplete.sendInteger x b
    sendPublic rest
  | (.root, .root bytes) :: rest => do
    UniComplete.sendRoot (halvesOf bytes)
    sendPublic rest
  | (.scalar, .scalar x) :: rest => do
    UniComplete.sendScalar x
    sendPublic rest
  | _ :: rest => sendPublic rest

end Send

/-! ## The tables -/

/-- **A public layout's stack** (`Table::new`): lane `l` holds block `b` of the table (`T (b · lane + k)`), whole lanes. -/
def placePublic (L : PcsQuotient.Layout) (T : ℕ → K) : Array K :=
  Array.ofFn (n := L.lanes.length * 2 ^ L.logLane) fun p ↦
    match L.lanes.getD (p.val / 2 ^ L.logLane) .random with
    | .block b => T (b * 2 ^ L.logLane + p.val % 2 ^ L.logLane)
    | _ => 0

section Honest

variable (G : RecPiop.Circuit E) (w : ℕ → K)

/-- The witness's values, in `K` (`2^m` of them). -/
def wValues : Array K := Array.ofFn (n := G.N) fun i ↦ w i.val

/-- **`W`'s table**: the witness's basis-`B` coefficients (`b_coefficients` of its novel ones). -/
def wTableB : Array K := UniStatement.bCoefficients G.logN (wValues G w)

/-- **`h` on `V_m`** (`prove_with`'s step 2): `[pull]/(α + w_i + β ω_i) + 1/(α + P_i + β ω_{σ_i})`, a hole pulling
nothing. -/
def hValues (α β γ : E) : Array E :=
  Array.ofFn (n := G.N) fun i ↦
    (if (G.role i.val).isPort then 0 else (α + ofK (w i.val) + β * UniStatement.pointE i.val)⁻¹) +
      (α + G.push (fun j ↦ ofK (w j)) γ i.val + β * UniStatement.pointE (G.sigma i.val))⁻¹

/-- `σ`'s points on `V_m`. -/
def sigmaValues : Array E := Array.ofFn (n := G.N) fun i ↦ UniStatement.pointE (G.sigma i.val)

/-- `κ` on `V_m`. -/
def kappaValues : Array E := Array.ofFn (n := G.N) fun i ↦ G.kappa i.val

/-- **The extension coset's offset** `β_{m+2}` (`beta()[m + 2]`). -/
def cosetOffset (m : ℕ) : K := UniStatement.beta.getD (m + 2) 0

/-- The coset's point `p`: `β_{m+2} + B(p)`. -/
def cosetPoint (m p : ℕ) : E := ofK (cosetOffset m + PcsQuotient.Domain.point p)

/-- **Novel coefficients' polynomial on the coset** (`on_d`): `4N` values, the coefficients padded with zeros. -/
def onCoset (m : ℕ) (c : Array E) : Array E :=
  PcsQuotient.Domain.values (m + 2) (cosetOffset m) (Array.ofFn (n := 2 ^ (m + 2)) fun i ↦ c.getD i.val 0)

/-- `Z_V(x) = w_m(x)`. -/
def zvAt (m : ℕ) (x : E) : E := (fun y ↦ y * y + y)^[m] x

/-- **A pair's indicator at a point off `V_m`**: `Z_V(x) / (Π_{j ∉ p} (ω_{c_p} + ω_j) · Π_{j ∈ p} (x + ω_j))`, the
polynomial `RecPiop.Circuit.ind` there. -/
def indAt (p : RecPiop.Block × ℕ) (x : E) : E :=
  zvAt G.logN x * ((∏ j ∈ G.compl p, (UniStatement.pointE (G.pairBase p) + UniStatement.pointE j)) *
    ∏ j ∈ (range G.N).filter (G.InPair p), (x + UniStatement.pointE j))⁻¹

/-- **The push polynomial at coset point `p`** (`P = w + Σ_p I_p (E_p + w) + κ`), from `w` and `κ` on the coset, the
cells `w(x + ω_c)` at `p ⊕ c`. -/
def pushAtCoset (m : ℕ) (wD κD : Array E) (γ : E) (p : ℕ) : E :=
  wD.getD p 0 + ∑ q ∈ G.pairs, indAt G q (cosetPoint m p) *
    ((G.regionRole q.1 q.2).value γ (wD.getD p 0) (fun c ↦ wD.getD (p ^^^ (q.2 ^^^ c)) 0) + wD.getD p 0) +
      κD.getD p 0

/-- **The holes' indicator at coset point `p`** (`1_S`): the port pairs' indicators. -/
def holeAtCoset (m p : ℕ) : E :=
  ∑ q ∈ G.pairs.filter (fun q ↦ (G.regionRole q.1 q.2).isPort = true), indAt G q (cosetPoint m p)

/-- **`h`'s novel coefficients** (`2^m`). -/
def hNovel (α β γ : E) : Array E := UniComplete.novelOfValuesE G.logN (hValues G w α β γ)

/-- **`q` on the extension coset** (`quotient_on_extension`): `(h d_pull d_push + (1 + 1_S) d_push + d_pull) / Z_V`. -/
def qValues (α β γ : E) : Array E :=
  let m := G.logN
  let wD := onCoset m (UniComplete.novelOfValuesK m (wValues G w))
  let σD := onCoset m (UniComplete.novelOfValuesE m (sigmaValues G))
  let κD := onCoset m (UniComplete.novelOfValuesE m (kappaValues G))
  let hD := onCoset m (hNovel G w α β γ)
  Array.ofFn (n := 2 ^ (m + 2)) fun p ↦
    let x := cosetPoint m p.val
    let dPull := α + wD.getD p.val 0 + β * x
    let dPush := α + pushAtCoset G m wD κD γ p.val + β * σD.getD p.val 0
    (hD.getD p.val 0 * dPull * dPush + (1 + holeAtCoset G m p.val) * dPush + dPull) * (zvAt m x)⁻¹

/-- **`q`'s novel coefficients** (`4N`): the transform at the coset's offset. -/
def qNovel (α β γ : E) : Array E :=
  PcsQuotient.Domain.coefficients (G.logN + 2) (cosetOffset G.logN) (qValues G w α β γ)

/-- **`Q`'s table**: entry `pd + 2^(m+2)(kind + 2 limb)` is limb `limb` of `h`'s (kind `0`, `pd < N`) or `q`'s (kind `1`)
novel coefficient `pd` (`chunk = 8 limb + 4 kind + digit`). -/
def qEntry (m : ℕ) (hN qN : Array E) (i : ℕ) : K :=
  let pd := i % 2 ^ (m + 2)
  let kl := i / 2 ^ (m + 2)
  if h : kl / 2 < 3 then
    if kl % 2 = 0 then (if pd < 2 ^ m then (hN.getD pd 0).limb ⟨kl / 2, h⟩ else 0)
    else (qN.getD pd 0).limb ⟨kl / 2, h⟩
  else 0

/-- **The fold values at `t`** (`folds`): `a_k = Σ_j eq(j; w_r(t), …, w_{m−1}(t)) T_{k + 2^r j}`, `k < 2^r`. -/
def foldValues (m r : ℕ) (T : Array K) (t : E) : List E :=
  (List.range (2 ^ r)).map fun k ↦
    ∑ j ∈ range (2 ^ (m - r)), ofK (T.getD (k + 2 ^ r * j) 0) *
      ∏ l ∈ range (m - r), if j.testBit l then (digitsList t (m + 3)).getD (r + l) 0
        else 1 + (digitsList t (m + 3)).getD (r + l) 0

/-- **`ξ = κ(t) + β σ(t)`** from the setup's halves `κ` and `κ + σ` (`mle_eval` at `w_0(t), …, w_{m−1}(t)`). -/
def xiOf (m : ℕ) (setupStack : Array K) (β t : E) : E :=
  let pt := (digitsList t (m + 3)).take m
  let kappaT := UniStatement.multilinearEval ((setupStack.extract 0 (2 ^ m)).toList.map ofK) pt
  let sumT := UniStatement.multilinearEval ((setupStack.extract (2 ^ m) (2 * 2 ^ m)).toList.map ofK) pt
  kappaT + β * (kappaT + sumT)

end Honest

/-! ## The prover -/

/-- **What the prover leaves**: the stream, `W`'s and `Q`'s stacks and trees, and the inputs of the verifier's
arithmetic (its public scalars, challenges and values). -/
structure Pi2Out where
  stream : Array UInt8
  wStack : Array K
  wTree : LeanVM.Prover.Tree
  qStack : Array K
  qTree : LeanVM.Prover.Tree
  inputs : Inputs E

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **The prover's stream** (`prove_with`), from the seed: the public values, `W` and `α, β, γ`, `Q` and `t`, the
values at `t` and `ρ`. -/
def pi2ProveStreamWith (G : RecPiop.Circuit E) (reads : List Read) (setupStack : Array K) (input : List UInt8)
    (values : List PublicValue) (w : ℕ → K) : UniComplete.WrM m Pi2Out := do
  let n := G.logN
  let (lw, lq, _) := layoutsOf n
  sendPublic (reads.zip values)
  -- W
  let tb := wTableB G w
  let wStack := placePublic lw fun i ↦ tb.getD i 0
  let wTree ← (StateT.lift (E2ECompleteness.commitWithH H lw.logN wStack) : UniComplete.WrM m LeanVM.Prover.Tree)
  UniComplete.sendRoot (digestScalars wTree.root)
  let α ← UniComplete.sampleW H
  let β ← UniComplete.sampleW H
  let γ ← UniComplete.sampleW H
  -- Q
  let hN := hNovel G w α β γ
  let qN := qNovel G w α β γ
  let qStack := placePublic lq (qEntry n hN qN)
  let qTree ← (StateT.lift (E2ECompleteness.commitWithH H lq.logN qStack) : UniComplete.WrM m LeanVM.Prover.Tree)
  UniComplete.sendRoot (digestScalars qTree.root)
  let t ← UniComplete.sampleW H
  -- the values at t
  let a := foldValues n G.logW tb t
  let ξ := xiOf n setupStack β t
  UniComplete.sendScalars (a ++ [ξ])
  let ρ ← UniComplete.sampleW H
  let c ← get
  return ⟨c.stream, wStack, wTree, qStack, qTree, ⟨publicScalarsOf input values, α, β, γ, t, a, ξ, ρ⟩⟩

/-- **π2's honest prover** over `H`, `F` (`prove_with`, then `open`): the seed `keccak(NAME ‖ IV ‖ public input)`, the
stream, then the three WHIR openings in the contract's order (`W`'s one claim, the setup's one, `Q`'s two), at the
claims of the verifier's arithmetic (`CoreSpec.run` of the circuit's view) on the prover's inputs; the stream and the
three proofs, or `none` if a proof of work fails. -/
def pi2ProveWith (fuel : ℕ) (G : RecPiop.Circuit E) (view : Circuit) (setupStack : Array K)
    (setupTree : LeanVM.Prover.Tree) (iv input : List UInt8) (values : List PublicValue) (w : ℕ → K) :
    m (Option (Array UInt8 × Compile.Proof × Compile.Proof × Compile.Proof)) := do
  let seed ← H (RecStatement.name ++ iv ++ input)
  let (out, _) ← (pi2ProveStreamWith H G view.reads setupStack input values w).run (UniComplete.Wr.start seed)
  let o := (Spec.of view).core.run out.inputs
  let (lw, lq, ls) := layoutsOf G.logN
  let pW ← E2ECompleteness.proveOpeningWithH H F fuel lw out.wTree out.wStack [⟨o.witnessPoint, o.fold⟩]
  let pS ← E2ECompleteness.proveOpeningWithH H F fuel ls setupTree setupStack [⟨o.setupPoint, out.inputs.ξ⟩]
  let pQ ← E2ECompleteness.proveOpeningWithH H F fuel lq out.qTree out.qStack
    [⟨o.quotientPoint, o.quotientValue⟩, ⟨o.sumPoint, o.sumValue⟩]
  return do
    let a ← pW
    let b ← pS
    let c ← pQ
    pure (out.stream, a, b, c)

end With

end RecCompose
