-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The prover's code (`Prover.lean`, `Witness.lean`) cut at the
-- bus challenges: the tails `streamTail`, `openingsTail` are its text, copied.
import UniComplete.Witness
import UniComplete.ProbChain

/-!
# The honest prover, cut at the bus challenges

The honest prover (`uniProverWith`, any monad `m`, Keccak-256 `H`, permutation `F`) is, **as a program**, a prefix
up to `C1`'s root, the five bus challenges `α₁ … α₄, β` (`samplesW H 4`, `sampleW H`), and a tail
(**`uniProverWith_split`**):

* **`proverA`**: the setup's trees (`setupTreesOf`), the contract's IV (`contractIvOf`), the seed (`seedOf`) and
  `C1`'s commitment (`commitWithH`); the row counts (`countBytes`) and `C1`'s root word are written, not hashed;
* the five answers `s₁ = H(firstInput rows a)` (the seed's bytes, the `24` count bytes, the `32` root bytes:
  `firstInput_length`, `88` bytes when there are six counts) and `s_{k+1} = H(digestBytes s_k)`;
* **`proverC`**: the stream's tail from `γ` (`streamTail`, `proveStreamWith`'s text from `let gamma`) on the writer
  after the five challenges (`writerAfter`), then the openings (`openingsTail`, `proveWith`'s text after the
  stream).

`proveStreamWith_split`, `proveWith_split` cut the code (by `rfl`); `run_proveStreamWith` runs the prefix of the
stream from the seed (the counts' loop `run_forIn_send`, the root, the five `sampleW`s, `run_sampleW`). The
**prover's bus challenges** at a hash function `H` (`proverChallenges`) are then the challenges of these five
answers, at `Id`.

Decisions: the cut is generic in the monad (`LawfulMonad m`), so the same lemma gives the staged run over the two
calls and the prover's challenges at a pure `H`; the copied tails are the prover's text (a change to `Prover.lean`'s
code after `γ` must be copied here, `proveStreamWith_split` checks it by `rfl`).
-/

namespace UniComplete.Prob

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- `challengeOf`, the transcript's (the low 192 bits of a digest). -/
abbrev chal (d : Digest) : E := PcsQuotient.Transcript.challengeOf d

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **The stream's tail** from `γ` on (`proveStreamWith`'s text from `let gamma ← sampleW H`), given `C1`'s commitment
and the bus challenges. -/
def streamTail (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m) (blake2s : Blake2s)
    (tr : Trace) (committed1 : Committed) (alphas : List E) (beta : E) : WrM m CoreOut := do
  let shape := tr.shape
  let stack1 := c1Stack tr
  let gamma ← sampleW H
  -- 2. Flock.
  let logN := blake2sR1csLogSize + shape.heights.getD opBlake2s 0
  let flockOut : Option FlockOut ← match blake2s with
    | .flock variant => some <$> flock logN variant tr.qflock
    | .omitted => pure none
  -- 3. The heap, the quotients, C2.
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 ← (StateT.lift (commit .c2 (((layoutsOf shape).lookup .c2).getD default).vars c2.stack) :
    WrM m Committed)
  sendRoot committed2.halves
  -- 4.–7. The values at t.
  let t ← sampleW H
  let a := atTOf tr c2 alphas beta gamma t flockOut
  sendScalars a.values
  -- 8. ρ, the combined claims.
  let rho ← sampleW H
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layouts shape a.c2Columns
  let stack3 := setupStackOf tr
  let stackOf : Commitment → Array K
    | .c1 => stack1
    | .c2 => c2.stack
    | .setup => stack3
  -- 9. The batching sumcheck.
  let lambda ← sampleW H
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) a.ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), flockOut.map (·.tables), 0, []⟩
  let r ← batchRounds H lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  let matrices ← match a.pending with
    | some (p, _) => do
      let mc := p.matrixClaim r 0 0
      let ma := multilinearEval ((flockMatrixStack true).toList.map ofK) mc.point
      let mb := multilinearEval ((flockMatrixStack false).toList.map ofK) mc.point
      sendScalars [ma, mb]
      pure (some (p.matrixClaim r ma mb))
    | none => pure none
  let c ← get
  return ⟨c.stream, (stack1, committed1), (c2.stack, committed2), stack3, claims, matrices, combined,
    c2.heapVals⟩

/-- **The stream, cut at the bus challenges.** -/
theorem proveStreamWith_split (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m)
    (blake2s : Blake2s) (tr : Trace) :
    proveStreamWith H commit flock blake2s tr = (do
      for rows in tr.rows do
        sendInteger rows 4
      let committed1 ← (StateT.lift (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)) : WrM m Committed)
      sendRoot committed1.halves
      let alphas ← samplesW H 4
      let beta ← sampleW H
      streamTail H commit flock blake2s tr committed1 alphas beta) := rfl

end With

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **The openings** after the stream (`proveWith`'s text after `let (out, _) ← …`). -/
def openingsTail (fuel : ℕ) (tr : Trace) (trees : SetupTrees) (out : CoreOut) : m (Option UniProof) := do
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
  let (pa, pb) ← match out.matrices with
    | some mc => do
      let pa ← E2ECompleteness.proveOpeningWithH H F fuel (plainLayout (layoutWordVars (words.getD 3 [])))
        trees.a0 (flockMatrixStack true) [⟨mc.point, mc.a⟩]
      let pb ← E2ECompleteness.proveOpeningWithH H F fuel (plainLayout (layoutWordVars (words.getD 4 [])))
        trees.b0 (flockMatrixStack false) [⟨mc.point, mc.b⟩]
      pure (pa, pb)
    | none => pure (some noProof, some noProof)
  return do
    let c1 ← p1
    let c2 ← p2
    let s ← p3
    let a ← pa
    let b ← pb
    pure ⟨out.stream, c1, c2, s, a, b⟩

/-- **The prover, cut after the stream.** -/
theorem proveWith_split (fuel : ℕ) (flock : FlockProver m) (blake2s : Blake2s) (programIv : List UInt8)
    (tr : Trace) :
    proveWith H F fuel flock blake2s programIv tr = (do
      let trees ← setupTreesOf H tr
      let iv ← contractIvOf H tr.shape programIv trees.roots
      let seed ← seedOf H iv tr.publicInput
      let (out, _) ← (proveStreamWith H (commitReal H) flock blake2s tr).run (Wr.start seed)
      openingsTail H F fuel tr trees out) := rfl

end With

/-! ## The prefix of the stream, run -/

/-- The row counts' bytes (`sendInteger rows 4`, each four bytes big-endian). -/
def countBytes (rows : List ℕ) : List UInt8 := rows.flatMap fun r ↦ integerWire r 4

/-- **The stream before the bus challenges**: the row counts and `C1`'s root word, as the writer appends them. -/
def prefixStream (rows : List ℕ) (c1 : LeanVM.Prover.Tree) : Array UInt8 :=
  #[] ++ (countBytes rows).toArray ++ (rootWord (digestScalars c1.root)).toArray

/-- **The writer after the five bus challenges**: the prefix absorbed, the state `s₅`, the challenges drawn. -/
def writerAfter (rows : List ℕ) (c1 : LeanVM.Prover.Tree) (s₁ s₂ s₃ s₄ s₅ : Digest) : Wr :=
  ⟨prefixStream rows c1, (prefixStream rows c1).size, s₅, #[chal s₁, chal s₂, chal s₃, chal s₄, chal s₅]⟩

section Run

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest)

/-- The counts' loop appends the counts' bytes. -/
theorem run_forIn_send (l : List ℕ) (f : ℕ → PUnit → WrM m (ForInStep PUnit))
    (hf : ∀ r u w, (f r u).run w =
      pure (ForInStep.yield PUnit.unit, { w with stream := w.stream ++ (integerWire r 4).toArray }))
    (u : PUnit) (w : Wr) :
    (forIn l u f).run w = pure (PUnit.unit, { w with stream := w.stream ++ (countBytes l).toArray }) := by
  induction l generalizing u w with
  | nil =>
    obtain ⟨s, a, st, ch⟩ := w
    simp [countBytes]
  | cons r l ih =>
    rw [List.forIn_cons, StateT.run_bind, hf, pure_bind]
    dsimp only
    rw [ih]
    obtain ⟨s, a, st, ch⟩ := w
    simp [countBytes, Array.append_assoc]

omit [LawfulMonad m] in
theorem run_sendRoot (halves : E × E) (w : Wr) :
    (sendRoot (m := m) halves).run w = pure (PUnit.unit, { w with stream := w.stream ++ (rootWord halves).toArray }) := by
  simp [sendRoot, sendBytes]

/-- **`sample`, run**: the hash of the state and of the bytes since the last challenge. -/
theorem run_sampleW (w : Wr) :
    (sampleW H).run w = H (digestBytes w.state ++ (w.stream.extract w.absorbed w.stream.size).toList) >>= fun s ↦
      pure (chal s, { w with absorbed := w.stream.size, state := s, challenges := w.challenges.push (chal s) }) := by
  simp [sampleW, chal]

theorem samplesW_four : samplesW H 4 = (do
    let a₁ ← sampleW H
    let a₂ ← sampleW H
    let a₃ ← sampleW H
    let a₄ ← sampleW H
    pure [a₁, a₂, a₃, a₄]) := by
  show samplesW H (0 + 1 + 1 + 1 + 1) = _
  simp only [samplesW, bind_assoc, pure_bind]

theorem extract_size_toList (a : Array UInt8) : (a.extract a.size a.size).toList = [] := by
  simp

/-- **The stream's prefix, run from the seed**: `C1`'s commitment, the five bus challenges, the tail. -/
theorem run_proveStreamWith (flock : FlockProver m) (blake2s : Blake2s) (tr : Trace) (seed : Digest) :
    (proveStreamWith H (commitReal H) flock blake2s tr).run (Wr.start seed) = (do
      let c1 ← E2ECompleteness.commitWithH H (c1Layout tr.shape).vars (c1Stack tr)
      let s₁ ← H (digestBytes seed ++
        ((prefixStream tr.rows c1).extract 0 (prefixStream tr.rows c1).size).toList)
      let s₂ ← H (digestBytes s₁)
      let s₃ ← H (digestBytes s₂)
      let s₄ ← H (digestBytes s₃)
      let s₅ ← H (digestBytes s₄)
      (streamTail H (commitReal H) flock blake2s tr ⟨c1, digestScalars c1.root⟩
        [chal s₁, chal s₂, chal s₃, chal s₄] (chal s₅)).run (writerAfter tr.rows c1 s₁ s₂ s₃ s₄ s₅)) := by
  rw [proveStreamWith_split, StateT.run_bind, run_forIn_send]
  · simp only [pure_bind, StateT.run_bind, StateT.run_lift, commitReal, bind_assoc, run_sendRoot,
      samplesW_four, run_sampleW, extract_size_toList, List.append_nil, Wr.start]
    rfl
  · intro r u w
    simp [sendInteger, sendBytes]

end Run

/-! ## The prover, cut at the bus challenges -/

/-- **What the prover computes before the bus challenges**: the setup's trees, the contract's IV, the seed, `C1`'s
tree. -/
structure ProverA where
  trees : SetupTrees
  iv : List UInt8
  seed : Digest
  c1 : LeanVM.Prover.Tree

/-- **The first bus-challenge input**: the seed's bytes, then the stream's prefix (`88` bytes at six counts). -/
def firstInput (rows : List ℕ) (a : ProverA) : List UInt8 :=
  digestBytes a.seed ++ ((prefixStream rows a.c1).extract 0 (prefixStream rows a.c1).size).toList

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **The prover before the bus challenges.** -/
def proverA (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : m ProverA := do
  let tr := honestTrace D input rows q
  let trees ← setupTreesOf H tr
  let iv ← contractIvOf H tr.shape D.programIv trees.roots
  let seed ← seedOf H iv tr.publicInput
  let c1 ← E2ECompleteness.commitWithH H (c1Layout tr.shape).vars (c1Stack tr)
  return ⟨trees, iv, seed, c1⟩

/-- **The prover after the bus challenges**: the stream's tail on the writer after them, the openings. -/
def proverC (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (a : ProverA) (s₁ s₂ s₃ s₄ s₅ : Digest) : m (Option UniProof) := do
  let tr := honestTrace D input rows q
  let (out, _) ← (streamTail H (commitReal H) flock (.flock flockMain) tr ⟨a.c1, digestScalars a.c1.root⟩
    [chal s₁, chal s₂, chal s₃, chal s₄] (chal s₅)).run (writerAfter rows a.c1 s₁ s₂ s₃ s₄ s₅)
  openingsTail H F PcsQuotient.nonceFuel tr a.trees out

/-- **The honest prover, cut at the bus challenges**, in any lawful monad. -/
theorem uniProverWith_split [LawfulMonad m] (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) :
    uniProverWith H F flock D input rows q = (do
      let a ← proverA H D input rows q
      let s₁ ← H (firstInput rows a)
      let s₂ ← H (digestBytes s₁)
      let s₃ ← H (digestBytes s₂)
      let s₄ ← H (digestBytes s₃)
      let s₅ ← H (digestBytes s₄)
      proverC H F flock D input rows q a s₁ s₂ s₃ s₄ s₅) := by
  simp only [uniProverWith, proveWith_split, run_proveStreamWith, proverA, proverC, bind_assoc, pure_bind]
  rfl

end With

/-- **The prover's bus challenges** at a hash function `H` (its writer's first five challenges, at `Id`): the
challenges of `s₁ = H(firstInput rows a)` and `s_{k+1} = H(s_k)`, `a` the prover's computations before them. -/
def proverChallenges (H : List UInt8 → Digest) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) : List E × E :=
  let a := proverA (m := Id) H D input rows q
  let s₁ := H (firstInput rows a)
  let s₂ := H (digestBytes s₁)
  let s₃ := H (digestBytes s₂)
  let s₄ := H (digestBytes s₃)
  let s₅ := H (digestBytes s₄)
  ([chal s₁, chal s₂, chal s₃, chal s₄], chal s₅)

/-! ## Lengths -/

theorem length_digestBytes' (d : Digest) : (digestBytes d).length = 32 := E2ECompleteness.length_digestBytes d

theorem integerWire_length (n bytes : ℕ) : (integerWire n bytes).length = bytes := by
  simp [integerWire]

theorem countBytes_length (rows : List ℕ) : (countBytes rows).length = 4 * rows.length := by
  induction rows with
  | nil => rfl
  | cons r l ih =>
    simp only [countBytes, List.flatMap_cons, List.length_append, integerWire_length, List.length_cons] at ih ⊢
    rw [ih]
    ring

theorem rootWord_length (halves : E × E) : (rootWord halves).length = 32 := by
  simp [rootWord, be64]

/-- **The first bus-challenge input has `88` bytes** at six row counts. -/
theorem firstInput_length {rows : List ℕ} (h : rows.length = 6) (a : ProverA) : (firstInput rows a).length = 88 := by
  simp only [firstInput, prefixStream, Array.toList_extract, List.length_append, length_digestBytes']
  simp [countBytes_length, rootWord_length, h]

/-! ## The prover, cut at `t` -/

section T

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **The stream from `γ` to `C2`'s root** (Flock at the main line): `γ`, Flock's prover, `C2`'s commitment, its
root's halves; it returns `γ`, Flock's output and `C2`'s commitment. -/
def midB (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m) (tr : Trace) (alphas : List E)
    (beta : E) : WrM m (E × FlockOut × Committed) := do
  let gamma ← sampleW H
  let out ← flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 ← (StateT.lift (commit .c2 (((layoutsOf tr.shape).lookup .c2).getD default).vars c2.stack) :
    WrM m Committed)
  sendRoot committed2.halves
  return (gamma, out, committed2)

/-- **The stream from `t` on** (`proveStreamWith`'s text from `let a := atTOf …`). -/
def tailT (tr : Trace) (committed1 : Committed)
    (alphas : List E) (beta gamma : E) (flockOut : Option FlockOut) (committed2 : Committed) (t : E) :
    WrM m CoreOut := do
  let shape := tr.shape
  let stack1 := c1Stack tr
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let a := atTOf tr c2 alphas beta gamma t flockOut
  sendScalars a.values
  -- 8. ρ, the combined claims.
  let rho ← sampleW H
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layouts shape a.c2Columns
  let stack3 := setupStackOf tr
  let stackOf : Commitment → Array K
    | .c1 => stack1
    | .c2 => c2.stack
    | .setup => stack3
  -- 9. The batching sumcheck.
  let lambda ← sampleW H
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) a.ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), flockOut.map (·.tables), 0, []⟩
  let r ← batchRounds H lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  let matrices ← match a.pending with
    | some (p, _) => do
      let mc := p.matrixClaim r 0 0
      let ma := multilinearEval ((flockMatrixStack true).toList.map ofK) mc.point
      let mb := multilinearEval ((flockMatrixStack false).toList.map ofK) mc.point
      sendScalars [ma, mb]
      pure (some (p.matrixClaim r ma mb))
    | none => pure none
  let c ← get
  return ⟨c.stream, (stack1, committed1), (c2.stack, committed2), stack3, claims, matrices, combined,
    c2.heapVals⟩

/-- **`t`'s input**: the writer's state, then the bytes since the last challenge (`sampleW`'s). -/
def tInput (w : Wr) : List UInt8 := digestBytes w.state ++ (w.stream.extract w.absorbed w.stream.size).toList

/-- The writer after `t`. -/
def afterT (w : Wr) (s : Digest) : Wr :=
  { w with absorbed := w.stream.size, state := s, challenges := w.challenges.push (chal s) }

/-- **The stream's tail, cut at `t`.** -/
theorem streamTail_cut [LawfulMonad m] (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m)
    (tr : Trace) (committed1 : Committed) (alphas : List E) (beta : E) :
    streamTail H commit flock (.flock flockMain) tr committed1 alphas beta = (do
      let x ← midB H commit flock tr alphas beta
      let t ← sampleW H
      tailT H tr committed1 alphas beta x.1 (some x.2.1) x.2.2 t) := by
  simp only [streamTail, midB, tailT, bind_assoc, pure_bind, bind_map_left]

/-- **The stream's tail, run, cut at `t`.** -/
theorem run_streamTail [LawfulMonad m] (flock : FlockProver m) (tr : Trace) (committed1 : Committed)
    (alphas : List E) (beta : E) (w : Wr) :
    (streamTail H (commitReal H) flock (.flock flockMain) tr committed1 alphas beta).run w = (do
      let x ← (midB H (commitReal H) flock tr alphas beta).run w
      let st ← H (tInput x.2)
      (tailT H tr committed1 alphas beta x.1.1 (some x.1.2.1) x.1.2.2 (chal st)).run
        (afterT x.2 st)) := by
  rw [streamTail_cut, StateT.run_bind]
  refine bind_congr fun x ↦ ?_
  rw [StateT.run_bind, run_sampleW, bind_assoc]
  simp only [pure_bind]
  rfl

end T

section T

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **The prover after `t`**: the stream's tail from `t` on the writer after it, the openings. -/
def proverD (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (a : ProverA) (s₁ s₂ s₃ s₄ s₅ : Digest) (x : (E × FlockOut × Committed) × Wr) (st : Digest) :
    m (Option UniProof) := do
  let tr := honestTrace D input rows q
  let (out, _) ← (tailT H tr ⟨a.c1, digestScalars a.c1.root⟩ [chal s₁, chal s₂, chal s₃, chal s₄]
    (chal s₅) x.1.1 (some x.1.2.1) x.1.2.2 (chal st)).run (afterT x.2 st)
  openingsTail H F PcsQuotient.nonceFuel tr a.trees out

/-- **The prover after the bus challenges, cut at `t`.** -/
theorem proverC_split [LawfulMonad m] (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (a : ProverA) (s₁ s₂ s₃ s₄ s₅ : Digest) :
    proverC H F flock D input rows q a s₁ s₂ s₃ s₄ s₅ = (do
      let x ← (midB H (commitReal H) flock (honestTrace D input rows q) [chal s₁, chal s₂, chal s₃, chal s₄]
        (chal s₅)).run (writerAfter rows a.c1 s₁ s₂ s₃ s₄ s₅)
      let st ← H (tInput x.2)
      proverD H F D input rows q a s₁ s₂ s₃ s₄ s₅ x st) := by
  simp only [proverC, run_streamTail, bind_assoc]
  rfl

end T

/-- **The prover's `t`-stage challenge** at a hash function `H` and Flock's prover `flock` (at `Id`): Flock's point on
`q_flock` (fixed before `t`) and `t`. -/
def proverTChallenge (H : List UInt8 → Digest) (flock : FlockProver Id) (D : Deployment) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) : List E × E :=
  let a := proverA (m := Id) H D input rows q
  let s₁ := H (firstInput rows a)
  let s₂ := H (digestBytes s₁)
  let s₃ := H (digestBytes s₂)
  let s₄ := H (digestBytes s₃)
  let s₅ := H (digestBytes s₄)
  let x := (midB (m := Id) H (commitReal (m := Id) H) flock (honestTrace D input rows q)
    [chal s₁, chal s₂, chal s₃, chal s₄] (chal s₅)).run (writerAfter rows a.c1 s₁ s₂ s₃ s₄ s₅)
  (x.1.2.1.point, chal (H (tInput x.2)))

end UniComplete.Prob
