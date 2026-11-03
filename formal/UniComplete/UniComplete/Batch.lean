-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `crates/leanvm_univariate/src/prover/batch.rs`
-- (branch `leanvm-univariate-prover2`): the batching sumcheck's prover (SPEC.md §8, §13 lever 4a).
import UniComplete.Trace

/-!
# The batching sumcheck, prover side (`batch.rs`)

`Σ_k λ^k Σ_u W_k(u) C_k(u) = Σ_k λ^k v_k` over the longest stack (the others zero-extended), with Flock's pending
matrices' product sum `Σ G L̂ ŝ` at the next power of `λ` over the first `k + 6` variables (zero-extended by
`eq(·, 0)` after them): each round sends `q(0)` and `q`'s `X²` coefficient (the verifier derives `q`'s `X`
coefficient from the claim), then draws the round's challenge and folds every table low variable first. Then every
stack's value at its part of the point, and the matrices' `a`, `b`.

**A claim's weight on its stack** (`denseWeight`, `dense_weight`): what the verifier's `weightAt` evaluates at the
point, written out over the stack's words: each term's `eq(point, ·)` on its column's blocks (a limb scaled by
`(1, y, y²)`), Frobenius-twisted terms as `eq^(2^k)` (on the cube `eq(φ^k(p), u) = eq(p, u)^(2^k)`), the ring-switch
term (`ringTwist`) as the map of `eq` (`Φ(eq(p, u))`, `towerRingMap`), `q_flock`'s slot `j` at words `j + 256 u`.
-/

namespace UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- A limb's scale `(1, y, y²)` times the coefficient (`weightAt`'s `scale`). -/
def limbScale (coefficient : E) (limb : ℕ) : E :=
  if limb = 0 then coefficient else coefficient * limbBasis.getD limb 0

/-- Add `x` to entry `i`. -/
def addAt (a : Array E) (i : ℕ) (x : E) : Array E := a.modify i (· + x)

/-- **A combined claim's weight on its stack** (`dense_weight`), `2^layout.vars` words. -/
def denseWeight (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) : Array E :=
  let points := claim.points.toArray
  claim.terms.foldl (fun (W : Array E) (column, p, twist, coefficient) ↦
    let point := points.getD p []
    match column with
    | .qflockSlot j =>
      (layout.limbs .qflock).foldl (fun W (limb, _, offset) ↦
        let scale := limbScale coefficient limb
        let eq := eqKernel point
        (List.range eq.size).foldl (fun W u ↦ addAt W (offset + j + 256 * u) (scale * eq.getD u 0)) W) W
    | _ =>
      (layout.limbs column).foldl (fun W (limb, vars, offset) ↦
        let scale := limbScale coefficient limb
        let eq := eqKernel ((point ++ List.replicate vars 0).take vars)
        (List.range (2 ^ vars)).foldl (fun W u ↦
          let e := eq.getD u 0
          let v := if twist = ringTwist then
              (match ringMap with
                | some map => Flock.towerRingMap e map
                | none => 0)
            else sqn e twist
          addAt W (offset + u) (scale * v)) W) W)
    (Array.replicate (2 ^ layout.vars) 0)

/-- **A round's sums** over a weight table and a stack table (`round_sums`): `Σ w₀ c₀` and
`Σ (w₀ + w₁)(c₀ + c₁)`, an odd tail's partner zero. -/
def roundSums (w c : Array E) : E × E :=
  (List.range ((w.size + 1) / 2)).foldl (fun (acc : E × E) i ↦
    let w0 := w.getD (2 * i) 0
    let w1 := w.getD (2 * i + 1) 0
    let c0 := c.getD (2 * i) 0
    let c1 := c.getD (2 * i + 1) 0
    (acc.1 + w0 * c0, acc.2 + (w0 + w1) * (c0 + c1))) (0, 0)

/-- **A fold** at `r` (`fold`): `v[2i] + r (v[2i] + v[2i+1])`. -/
def foldE (v : Array E) (r : E) : Array E :=
  Array.ofFn (n := (v.size + 1) / 2) fun i ↦
    let a := v.getD (2 * i.val) 0
    let b := v.getD (2 * i.val + 1) 0
    a + r * (a + b)

/-- **The matrices' product sum's round** (`product_round`): `q(0)` and the `X²` coefficient of
`Σ_i g(X, i) l(X, i) s(X, i)` (its `X³` coefficient vanishes: degree 2 in every variable). -/
def productRound (g l s : Array E) : E × E :=
  (List.range (g.size / 2)).foldl (fun (acc : E × E) i ↦
    let g0 := g.getD (2 * i) 0
    let l0 := l.getD (2 * i) 0
    let s0 := s.getD (2 * i) 0
    let dg := g0 + g.getD (2 * i + 1) 0
    let dl := l0 + l.getD (2 * i + 1) 0
    let ds := s0 + s.getD (2 * i + 1) 0
    (acc.1 + g0 * l0 * s0, acc.2 + (g0 * dl * ds + dg * l0 * ds + dg * dl * s0))) (0, 0)

/-- The matrices' pending product sum: its tables `G`, `L̂`, `ŝ` over its variables (index `x + 2^k y`), and its
number of variables. -/
structure PendingTables where
  g : Array E
  l : Array E
  s : Array E
  rounds : ℕ
  deriving Inhabited

/-- The batch's state through the rounds: the weights, the stacks' folded tables, the matrices' tables, their value
past their variables, the point so far. -/
structure BatchState where
  weights : List (Array E)
  tabs : List (Array E)
  matrices : Option PendingTables
  matrixValue : E
  point : List E

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **One round** (round `j`): the message `(q(0), X²)`, sent, the challenge drawn, every table folded. -/
def batchRound (lambda : E) (j : ℕ) (st : BatchState) : WrM m BatchState := do
  let n := st.tabs.length
  let (q0, q2, _) := (st.weights.zip st.tabs).foldl (fun (acc : E × E × E) (w, c) ↦
    let (a, b) := roundSums w c
    (acc.1 + acc.2.2 * a, acc.2.1 + acc.2.2 * b, acc.2.2 * lambda)) (0, 0, 1)
  let scale := epow lambda n
  let (q0, q2) := match st.matrices with
    | some p => if j < p.rounds then
        let (a, b) := productRound p.g p.l p.s
        (q0 + scale * a, q2 + scale * b)
      else (q0 + scale * st.matrixValue, q2)
    | none => (q0, q2)
  sendScalar q0
  sendScalar q2
  let r ← sampleW H
  let matrices := st.matrices.map fun p ↦
    if j < p.rounds then { p with g := foldE p.g r, l := foldE p.l r, s := foldE p.s r } else p
  let matrixValue := match st.matrices, matrices with
    | some p, some p' =>
      if j < p.rounds then (if j + 1 = p.rounds then p'.g.getD 0 0 * p'.l.getD 0 0 * p'.s.getD 0 0 else 0)
      else st.matrixValue * (1 + r)
    | _, _ => 0
  return ⟨st.weights.map (foldE · r), st.tabs.map (foldE · r), matrices, matrixValue, st.point ++ [r]⟩

/-- **The batching sumcheck's rounds**, `vars` of them: returns the point. -/
def batchRounds (lambda : E) (vars : ℕ) (st : BatchState) : WrM m (List E) := do
  let mut st := st
  for j in List.range vars do
    st ← batchRound H lambda j st
  return st.point

end With

end UniComplete
