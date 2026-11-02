-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The simulation of the four values is the one of leanVM's `formal/quotient` (branch
-- PCS-openings-aggregation, commit 651453c6, `QuotientSecurity/ZeroKnowledge.lean`'s `simValues`, ported in
-- `formal/QuotientSecurity`). The permutation's state, its lookups and the WHIR prover's pieces are
-- leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`,
-- `Statement/Prover/Run.lean`, `Statement/Prover/Ntt.lean`).
module

public import PcsQuotient.Prover
public import Statement.RandomPermutation

/-!
# The zero-knowledge simulator

The simulator of `ZeroKnowledge` (`Security.lean`), explicit and computable: given the statement and
no witness, it **answers the random permutation** for the whole experiment (it keeps the permutation's
edges, `SimState`, and answers the distinguisher's queries from them, `simOracle`) and produces a
proof (`simulate`). It is the **honest prover on fake tables, with oracle programming** of the two
tables' Merkle roots, and the four values simulated as `formal/`'s reduction simulator draws them:

1. The circuit's commitment, honestly: it is public (`commitWith`, over the simulator's own `π`).
2. The two roots, **uniform digests**, fixed before anything they commit to: they are absorbed into
   the Keccak-256 chain, which the simulator then runs honestly over its own `π`, drawing
   `α, β, γ` and `t` as the verifier will.
3. **The four values, uniform** (`simValues` of `formal/QuotientSecurity/ZeroKnowledge.lean`): in `K`
   when the row of `t` (`w₂(t)`) is in `K` (then so are the real ones), in `E` otherwise; `next`, the
   wiring polynomial at `t`, honestly (it is public). Then `ρ`, and the verifier's four claims
   (`claimsAt`).
4. **The fake tables** (`fakeStack`): each hidden stack uniform on its layout's lanes, **conditioned on
   its claims**: `3·#claims` of its entries solved for (the claims are linear over `K` limb by limb); that
   is a uniform table with those claims, uniformly padded.
5. **The programmed trees** (`programmedTree`): each fake table's WHIR tree built honestly over the
   simulator's `π` up to the root's two children, and `π` **programmed** at the root node's input so
   that its Keccak-256 is the root drawn in step 2 (the answer's other `21` lanes uniform).
6. **The openings**: the honest WHIR prover (`proveOpeningWith`) on the fake tables against their
   programmed trees, and on the public wiring table against its honest tree.

Its answers to fresh queries are uniform states (`uniformState`), not uniform among the states not yet
answered: a random function rather than a permutation, which differs on a collision only. A
programmed point replaces its forward edge; the inverse of the answer it replaces stays recorded (a
uniform state, which a distinguisher finds with negligible probability). The tables are hash maps, so
each query costs one lookup.

**Why step 4 is the right distribution** (`crates/quotient/HIDING.md`): the secret tables are committed in
hidden layouts, and for fixed challenges a translation of the padding maps the opening's view of a table onto
that of any other table with the same claims (under conditions (Q), (S), (R) there, on the challenges); so the
honest opening of the real table is distributed as that of a uniform table with the same claims, uniformly
padded, which is `fakeStack`'s stack. Conditions (S) and (R) are checked at random challenges, not proved for
every claim point (`HIDING.md`, "What remains open"), and the deployed prover draws its padding from ChaCha12
where `prover` (`Security.lean`) takes it uniform.
-/

@[expose] public section

namespace PcsQuotient.Simulator

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover PcsQuotient.Domain PcsQuotient.Transcript
open Common OracleComp OracleSpec

/-- Keccak states hashed by their lanes, for the simulator's tables. -/
instance : Hashable KeccakState := ⟨fun s ↦ hash s.toArray⟩

/-- **The simulator's state**: the permutation's edges it has fixed, both ways: `forward[x] = π x`,
`inverse[y] = π⁻¹ y`. -/
structure SimState where
  forward : Std.HashMap KeccakState KeccakState := {}
  inverse : Std.HashMap KeccakState KeccakState := {}

/-- Record the edge `π x = y`, both ways; a programmed point's new edge replaces the old forward. -/
def SimState.record (s : SimState) (x y : KeccakState) : SimState :=
  ⟨s.forward.insert x y, s.inverse.insert y x⟩

/-- The simulator's computations: coins, and its state. -/
abbrev SimM : Type → Type := StateT SimState ProbComp

/-! ### Coins -/

/-- A uniform 64-bit word. -/
def uniformWord : ProbComp UInt64 := do
  let n ← $[0..(2 ^ 64 - 1)]
  return UInt64.ofNat n.val

/-- A uniform Keccak state: `25` uniform lanes. -/
def uniformState : ProbComp KeccakState := do
  let lanes ← (List.range 25).mapM fun _ ↦ uniformWord
  return Vector.ofFn fun i ↦ lanes.getD i.val 0

/-- A uniform element of `K`. -/
def uniformK : ProbComp K := K.ofLane <$> uniformWord

/-- A uniform element of `E`. -/
def uniformE : ProbComp E := do return E.ofLimbs (← uniformK) (← uniformK) (← uniformK)

/-- A uniform digest. -/
def uniformDigest : ProbComp Digest := do
  let w ← (List.range 4).mapM fun _ ↦ uniformWord
  return Vector.ofFn fun i ↦ w.getD i.val 0

/-! ### The simulator's permutation -/

/-- **The simulator's oracle**, which answers the distinguisher: coins forwarded; `π x` and `π⁻¹ y`
from the edges fixed so far, a fresh query answered by a uniform state, recorded. -/
def simOracle : QueryImpl RandomPermutationOracles SimM
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.forward x) => do
    match (← get).forward[x]? with
    | some y => return y
    | none =>
      let y ← liftM uniformState
      modify (·.record x y)
      return y
  | .inr (.inverse y) => do
    match (← get).inverse[y]? with
    | some x => return x
    | none =>
      let x ← liftM uniformState
      modify (·.record x y)
      return x

/-- The simulator's own forward call of `π`. -/
def simPermutation (x : KeccakState) : SimM KeccakState := simOracle (.inr (.forward x))

/-- **Programming** `π x := y`: the edge replaces whatever `π x` was. -/
def program (x y : KeccakState) : SimM Unit := modify (·.record x y)

/-! ### Programmed Merkle trees -/

/-- The permutation's input when Keccak-256 hashes the 64 bytes `left ‖ right`: one padded block over
the zero state (`absorbBlockWith`). -/
def nodeInput (left right : Digest) : KeccakState :=
  Vector.ofFn fun i ↦
    if i.val < 17 then leLane (padBlock (digestBytes left ++ digestBytes right)) i.val else 0

/-- The levels of a tree from a level of `2^k` nodes up to `root`, the last parent **programmed**: `π`
at its input answers `root`'s four lanes, then `21` uniform ones. -/
def programmedLevels : ℕ → Array Digest → Digest → SimM (List (Array Digest))
  | 0, level, _ => return [level]
  | 1, level, root => do
    let rest ← liftM uniformState
    program (nodeInput (level.getD 0 default) (level.getD 1 default))
      (Vector.ofFn fun i ↦ if h : i.val < 4 then root[i.val] else rest[i])
    return [level, #[root]]
  | k + 2, level, root => do
    let up ← parentsM simPermutation level (2 ^ (k + 1))
    let rest ← programmedLevels (k + 1) up root
    return level :: rest

/-- **A tree under a given root**: the rows' leaves and the levels over the simulator's `π`, the root
node programmed. -/
def programmedTree (height : ℕ) (word : Word) (root : Digest) : SimM Tree := do
  let leaves ← leafDigestsM simPermutation height word
  let levels ← programmedLevels height leaves root
  return ⟨height, word, levels.toArray⟩

/-! ### Fake tables -/

/-- Reduce `v` by an echelon basis (each vector `1` at its pivot and `0` at the pivots before it). -/
def reduceBy (basis : List (ℕ × Array K)) (v : Array K) : Array K :=
  basis.foldl (fun v (i, b) ↦
    let c := v.getD i 0
    if c = 0 then v else Array.zipWith (fun x y ↦ x + c * y) v b) v

/-- **The free positions** of a system of `k` linear equations over `K` whose column at stack position `p` is
`column p`: the first `k` positions (in stack order) whose columns are independent, chosen greedily by
incremental elimination; fewer if the system has rank below `k`. They depend on the claims only. -/
def freePositions (k size : ℕ) (column : ℕ → Array K) : List ℕ :=
  ((List.range size).foldl
    (fun (acc : List (ℕ × Array K) × List ℕ) p ↦
      if acc.2.length = k then acc
      else
        let v := reduceBy acc.1 (column p)
        match (List.range k).find? (fun i ↦ v.getD i 0 ≠ 0) with
        | none => acc
        | some i => (acc.1 ++ [(i, v.map (· * (v.getD i 0)⁻¹))], acc.2 ++ [p]))
    ([], [])).2

/-- **A uniform stack conditioned on claims**: uniform words on the layout's lanes, then `k = 3·#claims` of
them solved for, so that each claim's value is the stack's (the claims are linear over `K`, one equation per
claim and limb, their weight on the stack `Layout.weightAt`): the free positions are the first whose columns
are independent (`freePositions`; a claim's weight may vanish on whole lanes, as the sum claim's on lane `0`),
the system solved by Gauss–Jordan elimination (`Domain.eliminate`). In a hidden layout this is a uniform table
conditioned on its claims, padded uniformly: the stack is an affine bijection of the table and the padding,
and the claims weigh the table only; the gadget's entries are then cancelled as the prover cancels them
(`Layout.cancelGadget`: first-piece entries, which no claim weighs). A system of rank below `k` (claims that
contradict each other) leaves
the words uniform. -/
def fakeStack (L : Layout) (claims : List Claim) : ProbComp (Array K) := do
  let lane := 2 ^ L.logLane
  let size := L.lanes.length * lane
  let r ← (Array.range size).mapM fun _ ↦ uniformK
  let k := 3 * claims.length
  let weights := claims.map L.claimWeights
  let table := weights.toArray
  let empty := L.claimWeights ⟨[], 0⟩
  let weightAt (w : ClaimWeights) (p : ℕ) : E := L.weightAt w (p / lane) (p % lane)
  let free : List ℕ := freePositions k size fun p ↦ Array.ofFn (n := k) fun e ↦
    LeanVM.Prover.limbAt (weightAt (table.getD (e.val / 3) empty) p) (e.val % 3)
  -- Each claim's value less what the words outside the free positions give it.
  let rest : List E := (claims.zip weights).map fun (c, w) ↦
    c.value + (List.range size).foldl
      (fun acc p ↦ if free.contains p then acc else acc + weightAt w p * ofK (r.getD p 0)) 0
  let rows : Array (Array K) := Array.ofFn (n := k) fun e ↦
    let w := table.getD (e.val / 3) empty
    let limb := e.val % 3
    Array.ofFn (n := k + 1) fun q ↦
      if q.val < k then LeanVM.Prover.limbAt (weightAt w (free.getD q.val 0)) limb
      else LeanVM.Prover.limbAt (rest.getD (e.val / 3) 0) limb
  let reduced := (List.range k).foldl (eliminate k) rows
  return L.cancelGadget <| (List.range k).foldl
    (fun s q ↦ s.setIfInBounds (free.getD q 0) ((reduced.getD q #[]).getD k 0)) r

/-! ### The simulator -/

/-- **The simulated proof** of `stmt` on `circuit`, trying `fuel` nonces per proof of work: steps 1 to 6 of the module
note, over the simulator's own permutation; `none` where the honest prover would make none (a proof of
work without a nonce below `fuel`, a vanishing denominator). -/
def simulateFor (circuit : Circuit) (fuel : ℕ) (stmt : Statement) : SimM (Option Proof) := do
  let logRows := circuit.logRows
  let mv := cellVars logRows
  -- 1. The circuit's commitment.
  let sigmaHat := circuit.wiringTable
  let indexTree ← commitWith simPermutation mv sigmaHat
  -- 2. The two roots, uniform; the chain run honestly.
  let witnessRoot ← liftM uniformDigest
  let quotientRoot ← liftM uniformDigest
  let c ← Chain.startWith simPermutation (label indexTree.root stmt)
  let wScalars := digestScalars witnessRoot
  let c := (c.absorb wScalars.1).absorb wScalars.2
  let (α, c) ← c.squeezeWith simPermutation
  let (β, c) ← c.squeezeWith simPermutation
  let (γ, c) ← c.squeezeWith simPermutation
  let qScalars := digestScalars quotientRoot
  let c := (c.absorb qScalars.1).absorb qScalars.2
  let (t, c) ← c.squeezeWith simPermutation
  -- 3. The four values, uniform in the row's field; `next` honestly.
  let digits := digitsOf t mv
  let values : List E ← liftM <| (List.range 4).mapM fun _ ↦
    if IsInK (digits.getD 2 0) then ofK <$> uniformK else uniformE
  let a : Vector E 4 := Vector.ofFn fun j ↦ values.getD j.val 0
  let next := novelEval sigmaHat 0 1 (digits.take mv)
  let c := (a.toList.foldl Chain.absorb c).absorb next
  let (ρ, _) ← c.squeezeWith simPermutation
  match claimsAt logRows stmt α β γ t ρ a next with
  | none => return none
  | some claims =>
    -- 4. The fake tables; 5. their trees under the drawn roots.
    let wL := witnessLayout logRows
    let qL := quotientLayout logRows
    let wStack ← liftM (fakeStack wL [claims.witness])
    let qStack ← liftM (fakeStack qL [claims.quotient, claims.sum])
    let wTree ← programmedTree (wL.logN - laneFold + logInvRate)
      (stackWordFast wL.logN logInvRate wStack) witnessRoot
    let qTree ← programmedTree (qL.logN - laneFold + logInvRate)
      (stackWordFast qL.logN logInvRate qStack) quotientRoot
    -- 6. The openings.
    let some witness ← proveOpeningWith simPermutation fuel wL wTree wStack [claims.witness]
      | return none
    let some wiring ← proveOpeningWith simPermutation fuel (wiringLayout logRows) indexTree sigmaHat
      [claims.wiring] | return none
    let some quotient ← proveOpeningWith simPermutation fuel qL qTree qStack
      [claims.quotient, claims.sum] | return none
    return some ⟨⟨wScalars, qScalars, a, next⟩, witness, wiring, quotient⟩

/-- **The simulator** of the membership statement: `simulateFor` on the membership circuit. -/
def simulate (fuel : ℕ) (stmt : Statement) : SimM (Option Proof) :=
  simulateFor (membership PcsQuotient.logRows) fuel stmt

end PcsQuotient.Simulator

end
