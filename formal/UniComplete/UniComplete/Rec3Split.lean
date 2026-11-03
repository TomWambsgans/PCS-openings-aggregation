-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's prover (`Rec3Prover.lean`) cut at the bus
-- challenges and at `t`, as `ProbSplit.lean` cuts the main line's: the tails are its text, copied.
import UniComplete.Rec3Prover
import UniComplete.ProbSplit

/-!
# π1-rec3's honest prover, cut at the bus challenges and at `t`

π1-rec3's prover (`uniProverRec3With`, any lawful monad) is, as a program, the main line's prefix up to `C1`'s root
(`proverA3`: the setup's trees, **π1-rec3's IV** `contractIvRec3Of`, the seed, `C1`'s commitment), **two** chained
bus answers (`s₁ = H(firstInput rows a)`, `α = squares (chal s₁) 4`; `s₂ = H(digestBytes s₁)`, `β = chal s₂`), and a
tail (`proverC3`: the stream from `γ` on, `streamTail3`, then the three openings `openingsTail3`):
**`uniProverRec3With_split`**. The tail is cut at `t` (**`proverC3_split`**): `γ`, Flock's prover and `C2`'s root
(`Prob.midB`, the main line's, generic in Flock's prover), `t = chal (H (tInput w))`, then the rest (`proverD3`:
`tailT3`, the values at `t`, `ρ`, the paired batch, the openings).

The **prover's challenges** at a pure `H` (`proverChallenges3`: `(squares (chal s₁) 4, chal s₂)`; `proverTChallenge3`:
Flock's point and `t`) are what the bad events (`BadFp`, `BadT`) of the end theorem are about.

Decisions: as `ProbSplit.lean`, the tails are the prover's text copied (`proveStreamRec3With_split` checks the copy
by `rfl`); the main line's `ProverA`, `firstInput`, `prefixStream`, `midB`, `tInput`, `afterT` are reused as they are.
-/

namespace UniComplete.Rec3

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open UniComplete.Prob (chal ProverA firstInput prefixStream midB tInput afterT run_forIn_send run_sendRoot
  run_sampleW extract_size_toList)

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **The stream from `t` on** (`proveStreamRec3With`'s text from `let a := atTOf …`). -/
def tailT3 (tr : Trace) (committed1 : Committed) (alphas : List E) (beta gamma : E) (flockOut : Option FlockOut)
    (committed2 : Committed) (t : E) : WrM m CoreOut := do
  let shape := tr.shape
  let stack1 := c1Stack tr
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let a := atTOf tr c2 alphas beta gamma t flockOut
  sendScalars a.values
  let rho ← sampleW H
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layouts shape a.c2Columns
  let stack3 := setupStackOf tr
  let stackOf : Commitment → Array K
    | .c1 => stack1
    | .c2 => c2.stack
    | .setup => stack3
  let lambda ← sampleW H
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) a.ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), none, 0, []⟩
  let r ← batchRounds3 H lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  let c ← get
  return ⟨c.stream, (stack1, committed1), (c2.stack, committed2), stack3, claims, none, combined, c2.heapVals⟩

/-- **The stream's tail** from `γ` on (`proveStreamRec3With`'s text from `let gamma ← sampleW H`). -/
def streamTail3 (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m) (tr : Trace)
    (committed1 : Committed) (alphas : List E) (beta : E) : WrM m CoreOut := do
  let shape := tr.shape
  let stack1 := c1Stack tr
  let gamma ← sampleW H
  let logN := blake2sR1csLogSize + shape.heights.getD opBlake2s 0
  let flockOut : Option FlockOut ← some <$> flock logN flockMain tr.qflock
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 ← (StateT.lift (commit .c2 (((layoutsOf shape).lookup .c2).getD default).vars c2.stack) :
    WrM m Committed)
  sendRoot committed2.halves
  let t ← sampleW H
  let a := atTOf tr c2 alphas beta gamma t flockOut
  sendScalars a.values
  let rho ← sampleW H
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layouts shape a.c2Columns
  let stack3 := setupStackOf tr
  let stackOf : Commitment → Array K
    | .c1 => stack1
    | .c2 => c2.stack
    | .setup => stack3
  let lambda ← sampleW H
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) a.ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), none, 0, []⟩
  let r ← batchRounds3 H lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  let c ← get
  return ⟨c.stream, (stack1, committed1), (c2.stack, committed2), stack3, claims, none, combined, c2.heapVals⟩

/-- **The stream, cut at the bus challenges.** -/
theorem proveStreamRec3With_split (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m)
    (tr : Trace) :
    proveStreamRec3With H commit flock tr = (do
      for rows in tr.rows do
        sendInteger rows 4
      let committed1 ← (StateT.lift (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)) : WrM m Committed)
      sendRoot committed1.halves
      let alphas ← drawRunW H 4
      let beta ← sampleW H
      streamTail3 H commit flock tr committed1 alphas beta) := rfl

/-- **The stream's tail, cut at `t`.** -/
theorem streamTail3_cut [LawfulMonad m] (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m)
    (tr : Trace) (committed1 : Committed) (alphas : List E) (beta : E) :
    streamTail3 H commit flock tr committed1 alphas beta = (do
      let x ← midB H commit flock tr alphas beta
      let t ← sampleW H
      tailT3 H tr committed1 alphas beta x.1 (some x.2.1) x.2.2 t) := by
  simp only [streamTail3, midB, tailT3, bind_assoc, pure_bind, bind_map_left]

end With

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **The three openings** after the stream (`proveRec3With`'s text after `let (out, _) ← …`). -/
def openingsTail3 (fuel : ℕ) (tr : Trace) (trees : SetupTrees) (out : CoreOut) : m (Option UniProof) := do
  let words := layoutWords tr.shape
  let openOne (c : Commitment) (pt : List E) (value : E) : m (Option Compile.Proof) :=
    let (stack, tree, word) : Array K × LeanVM.Prover.Tree × List UInt8 := match c with
      | .c1 => (out.c1.1, out.c1.2.tree, words.getD 0 [])
      | .c2 => (out.c2.1, out.c2.2.tree, words.getD 1 [])
      | .setup => (out.setup, trees.bytecode, words.getD 2 [])
    E2ECompleteness.proveOpeningWithH H F fuel (plainLayout (layoutWordVars word)) tree stack [⟨pt, value⟩]
  let p1 ← match out.claims.find? (·.1 == .c1) with
    | some (_, pt, v) => openOne .c1 pt v
    | none => pure none
  let p2 ← match out.claims.find? (·.1 == .c2) with
    | some (_, pt, v) => openOne .c2 pt v
    | none => pure none
  let p3 ← match out.claims.find? (·.1 == .setup) with
    | some (_, pt, v) => openOne .setup pt v
    | none => pure none
  return do
    let c1 ← p1
    let c2 ← p2
    let s ← p3
    pure ⟨out.stream, c1, c2, s, noProof, noProof⟩

/-- **The prover, cut after the stream.** -/
theorem proveRec3With_split (fuel : ℕ) (flock : FlockProver m) (programIv : List UInt8) (tr : Trace) :
    proveRec3With H F fuel flock programIv tr = (do
      let trees ← setupTreesOf H tr
      let iv ← contractIvRec3Of H tr.shape programIv trees.roots
      let seed ← seedOf H iv tr.publicInput
      let (out, _) ← (proveStreamRec3With H (commitReal H) flock tr).run (Wr.start seed)
      openingsTail3 H F fuel tr trees out) := rfl

end With

/-- **The writer after π1-rec3's two bus challenges**: the prefix absorbed, the state `s₂`, the challenges drawn
(`chal s₁`, the squares' root, and `β = chal s₂`). -/
def writerAfter3 (rows : List ℕ) (c1 : LeanVM.Prover.Tree) (s₁ s₂ : Digest) : Wr :=
  ⟨prefixStream rows c1, (prefixStream rows c1).size, s₂, #[chal s₁, chal s₂]⟩

section Run

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest)

omit [LawfulMonad m] in
theorem drawRunW_four : drawRunW H 4 = (do
    let c ← sampleW H
    pure (squares c 4)) := rfl

/-- **The stream's prefix, run from the seed**: `C1`'s commitment, the two bus answers, the tail. -/
theorem run_proveStreamRec3With (flock : FlockProver m) (tr : Trace) (seed : Digest) :
    (proveStreamRec3With H (commitReal H) flock tr).run (Wr.start seed) = (do
      let c1 ← E2ECompleteness.commitWithH H (c1Layout tr.shape).vars (c1Stack tr)
      let s₁ ← H (digestBytes seed ++
        ((prefixStream tr.rows c1).extract 0 (prefixStream tr.rows c1).size).toList)
      let s₂ ← H (digestBytes s₁)
      (streamTail3 H (commitReal H) flock tr ⟨c1, digestScalars c1.root⟩
        (squares (chal s₁) 4) (chal s₂)).run (writerAfter3 tr.rows c1 s₁ s₂)) := by
  rw [proveStreamRec3With_split, StateT.run_bind, run_forIn_send]
  · simp only [pure_bind, StateT.run_bind, StateT.run_lift, commitReal, bind_assoc, run_sendRoot,
      drawRunW_four, run_sampleW, extract_size_toList, List.append_nil, Wr.start]
    rfl
  · intro r u w
    simp [sendInteger, sendBytes]

end Run

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **π1-rec3's prover before the bus challenges**: the setup's trees, π1-rec3's IV, the seed, `C1`'s tree. -/
def proverA3 (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : m ProverA := do
  let tr := honestTrace D input rows q
  let trees ← setupTreesOf H tr
  let iv ← contractIvRec3Of H tr.shape D.programIv trees.roots
  let seed ← seedOf H iv tr.publicInput
  let c1 ← E2ECompleteness.commitWithH H (c1Layout tr.shape).vars (c1Stack tr)
  return ⟨trees, iv, seed, c1⟩

/-- **π1-rec3's prover after the two bus challenges**: the stream's tail on the writer after them, the openings. -/
def proverC3 (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (a : ProverA) (s₁ s₂ : Digest) : m (Option UniProof) := do
  let tr := honestTrace D input rows q
  let (out, _) ← (streamTail3 H (commitReal H) flock tr ⟨a.c1, digestScalars a.c1.root⟩
    (squares (chal s₁) 4) (chal s₂)).run (writerAfter3 rows a.c1 s₁ s₂)
  openingsTail3 H F PcsQuotient.nonceFuel tr a.trees out

/-- **π1-rec3's honest prover, cut at the bus challenges**, in any lawful monad. -/
theorem uniProverRec3With_split [LawfulMonad m] (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) :
    uniProverRec3With H F flock D input rows q = (do
      let a ← proverA3 H D input rows q
      let s₁ ← H (firstInput rows a)
      let s₂ ← H (digestBytes s₁)
      proverC3 H F flock D input rows q a s₁ s₂) := by
  simp only [uniProverRec3With, proveRec3With_split, run_proveStreamRec3With, proverA3, proverC3, bind_assoc,
    pure_bind]
  rfl

/-- **The prover after `t`**: the stream's tail from `t` on the writer after it, the openings. -/
def proverD3 (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (a : ProverA)
    (s₁ s₂ : Digest) (x : (E × FlockOut × Committed) × Wr) (st : Digest) : m (Option UniProof) := do
  let tr := honestTrace D input rows q
  let (out, _) ← (tailT3 H tr ⟨a.c1, digestScalars a.c1.root⟩ (squares (chal s₁) 4) (chal s₂) x.1.1
    (some x.1.2.1) x.1.2.2 (chal st)).run (afterT x.2 st)
  openingsTail3 H F PcsQuotient.nonceFuel tr a.trees out

/-- **The prover after the bus challenges, cut at `t`.** -/
theorem proverC3_split [LawfulMonad m] (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (a : ProverA) (s₁ s₂ : Digest) :
    proverC3 H F flock D input rows q a s₁ s₂ = (do
      let x ← (midB H (commitReal H) flock (honestTrace D input rows q) (squares (chal s₁) 4) (chal s₂)).run
        (writerAfter3 rows a.c1 s₁ s₂)
      let st ← H (tInput x.2)
      proverD3 H F D input rows q a s₁ s₂ x st) := by
  simp only [proverC3, streamTail3_cut, StateT.run_bind, bind_assoc]
  refine bind_congr fun x ↦ ?_
  simp only [run_sampleW, bind_assoc, pure_bind, proverD3]
  rfl

end With

/-- **π1-rec3's bus challenges** at a hash function `H` (at `Id`): `α = squares (chal s₁) 4` and `β = chal s₂`,
`s₁ = H(firstInput rows a)`, `s₂ = H(s₁)`, `a` the prover's computations before them. -/
def proverChallenges3 (H : List UInt8 → Digest) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) : List E × E :=
  let a := proverA3 (m := Id) H D input rows q
  let s₁ := H (firstInput rows a)
  let s₂ := H (digestBytes s₁)
  (squares (chal s₁) 4, chal s₂)

/-- **π1-rec3's `t`-stage challenge** at a hash function `H` and Flock's prover `flock` (at `Id`): Flock's point on
`q_flock` (fixed before `t`) and `t`. -/
def proverTChallenge3 (H : List UInt8 → Digest) (flock : FlockProver Id) (D : Deployment) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) : List E × E :=
  let a := proverA3 (m := Id) H D input rows q
  let s₁ := H (firstInput rows a)
  let s₂ := H (digestBytes s₁)
  let x := (midB (m := Id) H (commitReal (m := Id) H) flock (honestTrace D input rows q) (squares (chal s₁) 4)
    (chal s₂)).run (writerAfter3 rows a.c1 s₁ s₂)
  (x.1.2.1.point, chal (H (tInput x.2)))

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.uniProverRec3With_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.uniProverRec3With_split

/-- info: 'UniComplete.Rec3.proverC3_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.proverC3_split
