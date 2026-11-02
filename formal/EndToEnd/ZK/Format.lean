-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The opening's proof format and the verifier's program are leanerVM's (branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0: `Statement/LeanVmVerifier.lean`'s `Compile.Proof`, `Compile.Prog`,
-- `Compile.run`); `fillRun` is `Compile.run` producing the Merkle openings instead of checking them.
import ZK.Coins
import QuotientZk.Deployed.Skeleton

/-!
# The statement's proof from the skeleton's (`fmt`)

`QuotientZk`'s skeleton (`Deployed.skel`) outputs the deployed prover's proof: the two roots and the
five values, and per opening its scalar stream and, per query phase, a **pruned multiproof** (the
sorted distinct positions, their rows, the siblings not on another path: `PrunedMerklePaths`). The
statement's proof (`PcsQuotient.Proof`) carries the reduction's nine scalars and, per opening, mumbai's
format (`Compile.Proof`): the stream and **one full Merkle path per queried position**, in the order
the verifier queries them (positions repeated as drawn).

**`fmt stmt pf`** is that public translation, a computation of `π` (the distinguisher's post-processing):

* the reduction's proof (`reductionOf`): the roots as their halves, the values as elements of `E`;
* per opening (`fillOpening`): the stream's scalars as elements of `E`; the claims recomputed as the
  verifier computes them (the circuit's commitment `setupWith`, the chain `reduceWith`), the opening's
  sponge (`openingSpongeWith`); then the verifier's own program (`verifyStackedOpening`) run as mumbai's
  `Compile.run` runs it (the challenges squeezed, the stream absorbed), except that at each query the
  openings are **produced** from the next multiproof (`expandMulti`: the leaves hashed, the levels
  climbed, the pruned siblings consumed as `PrunedMerklePaths::prune` emits them) rather than read and
  checked (`fillRun`);
* within a budget of `fmtBudget = 2^23` calls of `π` (`budgeted`: past it, no proof), so that
  **`fmt_queryBound`**: `fmt` makes at most `2^23` calls, on every path (the circuit's commitment, the
  largest part, is about `2^21.3`).

`fmt` is the post-processing of `QuotientZk`'s games in the end theorem; that it maps the skeleton's
proof to the statement's prover's is part of `ProverBridge` (`ZK/Real.lean`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

namespace PcsQuotient.EndToEnd

set_option linter.unusedSectionVars false

/-- `π`, as the distinguisher asks it. -/
def permF (x : KeccakState) : OracleComp PermSpec KeccakState :=
  liftM (PermSpec.query (.forward x))

/-! ## Encodings -/

/-- A Keccak-256 digest's 32 bytes as its four little-endian lanes. -/
def digestOfBytes (b : QuotientRpm.Bytes32) : Digest :=
  Vector.ofFn fun i : Fin 4 ↦ LeanVM.Rpm.bytesLane ((b.toList.drop (8 * i.val)).take 8)

/-- A scalar's three 64-bit limbs as an element of `E`. -/
def eOfLimbs (x : QuotientRpm.Limbs) : E := E.ofLimbs (K.ofLane x.1) (K.ofLane x.2.1) (K.ofLane x.2.2)

/-- **The reduction's proof** of the skeleton's: the roots as their halves, the four values and `next`. -/
def reductionOf (pf : QuotientZk.Deployed.Proof) : ReductionProof :=
  ⟨digestScalars (digestOfBytes pf.wRoot), digestScalars (digestOfBytes pf.qRoot),
    Vector.ofFn fun j : Fin 4 ↦ eOfLimbs (pf.values.getD j.val (0, 0, 0)),
    eOfLimbs (pf.values.getD 4 (0, 0, 0))⟩

/-! ## Full paths from a pruned multiproof -/

/-- A pruned multiproof: the sorted distinct positions, their rows (as words), the siblings sent. -/
abbrev Multi := List ℕ × List (List UInt64) × List QuotientRpm.Bytes32

/-- A node and its sibling, left first. -/
def withSibling (p : ℕ) (d s : Digest) : List (ℕ × Digest) :=
  if p % 2 = 0 then [(p, d), (p ^^^ 1, s)] else [(p ^^^ 1, s), (p, d)]

/-- **One level of the expansion** (the inverse of `Deployed.pruneLevel`): the level's known nodes
(sorted) completed into sibling pairs, a node whose sibling is not known taking the next sibling sent;
the siblings left. -/
def expandLevel : List (ℕ × Digest) → List Digest → List (ℕ × Digest) × List Digest
  | (p, d) :: (q, e) :: rest, sibs =>
    if q = p ^^^ 1 then
      let r := expandLevel rest sibs
      ((p, d) :: (q, e) :: r.1, r.2)
    else
      match sibs with
      | s :: ss =>
        let r := expandLevel ((q, e) :: rest) ss
        (withSibling p d s ++ r.1, r.2)
      | [] => ([], [])
  | [(p, d)], s :: ss => (withSibling p d s, ss)
  | _, sibs => ([], sibs)

/-- The parents of sibling pairs: `H(left ‖ right)` at half the left's position. -/
def pairUp : List (ℕ × Digest) → OracleComp PermSpec (List (ℕ × Digest))
  | (a, x) :: (_, y) :: rest => do
    let h ← keccak256With permF (digestBytes x ++ digestBytes y)
    let r ← pairUp rest
    pure ((a / 2, h) :: r)
  | _ => pure []

/-- The levels' completed nodes, from the leaves' up, `height` levels. -/
def expandLevels : ℕ → List (ℕ × Digest) → List Digest →
    OracleComp PermSpec (List (List (ℕ × Digest)))
  | 0, _, _ => pure []
  | h + 1, known, sibs => do
    let (level, rest) := expandLevel known sibs
    let up ← pairUp level
    let more ← expandLevels h up rest
    pure (level :: more)

/-- A node's digest at a level, or the zero digest. -/
def nodeAt (level : List (ℕ × Digest)) (p : ℕ) : Digest :=
  ((level.find? fun e ↦ e.1 = p).map Prod.snd).getD (Vector.replicate 4 0)

/-- **The openings of the queried positions `ps`** (in the verifier's order) from a pruned multiproof
of a tree of `height` levels: each position's row (its words as `K`) and its siblings from the leaf
up. -/
def expandMulti (mp : Multi) (height : ℕ) (ps : List ℕ) : OracleComp PermSpec (List Opening) := do
  let rowAt (p : ℕ) : List K :=
    ((mp.1.zip mp.2.1).find? fun e ↦ e.1 = p).elim [] fun e ↦ e.2.map K.ofLane
  let leaves ← mp.1.mapM fun p ↦ do
    let d ← keccak256With permF ((rowAt p).flatMap kBytes)
    pure (p, d)
  let levels ← expandLevels height leaves (mp.2.2.map digestOfBytes)
  pure (ps.map fun q ↦
    ⟨rowAt q, (List.range height).map fun k ↦ nodeAt (levels.getD k []) ((q >>> k) ^^^ 1)⟩)

/-! ## The verifier's program, the openings produced -/

/-- The state of the production: the sponge, the scalars not yet read, the multiproofs not yet
used, the roots read so far (with height and width), the openings produced. -/
structure FillState where
  sponge : Sponge
  stream : List E
  multis : List Multi
  roots : List (Digest × ℕ × ℕ)
  out : List Opening

/-- **`Compile.run`, the openings produced**: every challenge squeezed and every scalar absorbed as
the verifier does, a query's openings produced from the next multiproof (no check). -/
def fillRun {α : Type} : Prog α → FillState → OracleComp PermSpec (Option (α × FillState))
  | .ret a, s => pure (some (a, s))
  | .fail, _ => pure none
  | .read k, s => match s.stream with
    | [] => pure none
    | x :: xs => do
      let sp ← absorb permF s.sponge x dsObserve
      fillRun (k x) { s with sponge := sp, stream := xs }
  | .sample k, s => do
    let (c, sp) ← squeeze permF s.sponge
    fillRun (k c) { s with sponge := sp }
  | .grind _ k, s => match s.stream with
    | [] => pure none
    | n :: xs => do
      let sp ← absorb permF s.sponge n dsPowNonce
      let (_, sp) ← squeeze permF sp
      fillRun k { s with sponge := sp, stream := xs }
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs => do
      let sp ← absorb permF s.sponge x0 dsObserve
      let sp ← absorb permF sp x1 dsObserve
      match digestOfScalars (x0, x1) with
      | some root =>
        fillRun k { s with sponge := sp, stream := xs, roots := s.roots ++ [(root, height, width)] }
      | none => pure none
    | _ => pure none
  | .query i ps k, s => match s.roots[i]?, s.multis with
    | some (_, height, _), mp :: rest => do
      let opens ← expandMulti mp height ps
      fillRun (k (opens.map (·.leaf))) { s with multis := rest, out := s.out ++ opens }
    | _, _ => pure none

/-- **An opening's proof in mumbai's format** from the skeleton's (its stream and multiproofs), for the
layout `L`, the root and the claims the verifier has: the opening's sponge, the root's halves absorbed,
then the verifier's program run with the openings produced (`openingWith`'s steps). -/
def fillOpening (L : Layout) (root : Digest) (claims : List Claim)
    (o : List QuotientRpm.Limbs × List Multi) : OracleComp PermSpec (Option Compile.Proof) :=
  match o.1.map eOfLimbs with
  | x0 :: x1 :: rest => do
    let sp ← openingSpongeWith permF L claims
    let sp ← absorb permF sp x0 dsObserve
    let sp ← absorb permF sp x1 dsObserve
    let program := verifyStackedOpening L.logN logInvRate (stackClaims L claims)
    let height := L.logN - laneFold + logInvRate
    let r ← fillRun program ⟨sp, rest, o.2, [(root, height, 2 ^ laneFold)], []⟩
    pure (r.map fun z ↦ ⟨x0 :: x1 :: rest, z.2.out⟩)
  | _ => pure none

/-- **The statement's proof of the skeleton's**, unbudgeted: the reduction's proof; the claims as the
verifier computes them (the circuit's commitment, the chain); the three openings in mumbai's format. -/
def fmtCore (stmt : Statement) (pf : QuotientZk.Deployed.Proof) :
    OracleComp PermSpec (Option Proof) := do
  let red := reductionOf pf
  let indexRoot ← setupWith permF
  match ← reduceWith permF logRows indexRoot stmt red with
  | none => pure none
  | some r =>
    match pf.openings with
    | [oW, oσ, oQ] => do
      let w ← fillOpening (witnessLayout logRows) r.witnessRoot [r.claims.witness] oW
      let σ ← fillOpening (wiringLayout logRows) indexRoot [r.claims.wiring] oσ
      let q ← fillOpening (quotientLayout logRows) r.quotientRoot [r.claims.quotient, r.claims.sum] oQ
      pure (match w, σ, q with
        | some w, some σ, some q => some ⟨red, w, σ, q⟩
        | _, _, _ => none)
    | _ => pure none

/-! ## The budget -/

/-- `π` within a budget: past it, no call and the run marked failed. -/
def budgetImpl : QueryImpl PermSpec (StateT (ℕ × Bool) (OracleComp PermSpec)) :=
  fun q ↦ StateT.mk fun s ↦ match s with
    | (0, _) => pure (default, (0, false))
    | (b + 1, ok) => (fun a ↦ (a, (b, ok))) <$> liftM (PermSpec.query q)

/-- **A computation within `n` calls of `π`**: its output if it made at most `n`, else none. -/
def budgeted {α : Type} (n : ℕ) (X : OracleComp PermSpec (Option α)) :
    OracleComp PermSpec (Option α) := do
  let z ← (simulateQ budgetImpl X).run (n, true)
  pure (if z.2.2 then z.1 else none)

theorem budget_queryBound {α : Type} (X : OracleComp PermSpec α) :
    ∀ (b : ℕ) (ok : Bool), IsTotalQueryBound ((simulateQ budgetImpl X).run (b, ok)) b := by
  induction X using OracleComp.inductionOn with
  | pure a => intro b ok; simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind q k ih =>
    intro b ok
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rcases b with _ | b
    · change IsTotalQueryBound ((pure (default, (0, false)) : OracleComp PermSpec _) >>= _) 0
      rw [pure_bind]
      exact ih _ 0 false
    · change IsTotalQueryBound (((fun a ↦ (a, (b, ok))) <$>
        (liftM (PermSpec.query q) : OracleComp PermSpec _)) >>= _) (b + 1)
      rw [bind_map_left, isTotalQueryBound_query_bind_iff]
      exact ⟨Nat.succ_pos b, fun a ↦ ih a b ok⟩

/-- A budgeted computation makes at most its budget of calls. -/
theorem budgeted_queryBound {α : Type} (n : ℕ) (X : OracleComp PermSpec (Option α)) :
    IsTotalQueryBound (budgeted n X) n := by
  unfold budgeted
  have h : IsTotalQueryBound ((simulateQ budgetImpl X).run (n, true) >>= fun z ↦
      (pure (if z.2.2 then z.1 else none) : OracleComp PermSpec (Option α))) (n + 0) :=
    isTotalQueryBound_bind (budget_queryBound X n true) fun _ ↦ trivial
  simpa using h

/-- The formatting's budget of `π` calls: `2^23` (the circuit's commitment about `2^21.3`, the chain,
the three openings' sponges and paths far less). -/
def fmtBudget : ℕ := 2 ^ 23

/-- **The statement's proof of the skeleton's** (`fmtCore` within `fmtBudget` calls of `π`). -/
def fmt (stmt : Statement) (pf : QuotientZk.Deployed.Proof) : OracleComp PermSpec (Option Proof) :=
  budgeted fmtBudget (fmtCore stmt pf)

/-- **`fmt` makes at most `2^23` calls of `π`.** -/
theorem fmt_queryBound (stmt : Statement) (pf : QuotientZk.Deployed.Proof) :
    IsTotalQueryBound (fmt stmt pf) fmtBudget :=
  budgeted_queryBound _ _

end PcsQuotient.EndToEnd
