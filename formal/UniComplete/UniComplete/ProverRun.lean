-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Prover
import UniComplete.Whir
import UniComplete.Reference

/-!
# The honest prover's run at a pure hash (`proveWith` in `Id`)

`proveWith` (Prover.lean) at `m = Id`, a pure Keccak-256 `H : List UInt8 → Digest` and permutation `F` (as
`E2ECompleteness.ProverOpening` and `Whir.lean` state their lemmas), cut into named pieces:

* **the pieces**: the setup's trees `setupTreesOf`, the IV `contractIvOf`, the seed `proverSeed`, the stream's run
  `streamRun` (`(proveStreamWith …).run (Wr.start seed)`: output and writer), then the five openings: `claimProof`
  (one commitment's: its claim found by `find?`, `openingFor` its stack, tree and layout word) and `matrixProofs`
  (`A0`, `B0` at Flock's claim, or the empty proofs without);
* **`proveWith_eq`**: `proveWith` is those five, bound in `Option`; **`proveWith_eq_some`**: it returns `some π`
  exactly when each returns `some`, `π` the stream and those proofs; **`proveWith_eq_none`**: if it returns `none`,
  a commitment has no claim or one of the five `proveOpeningWithH` calls (named with its layout, tree, stack and
  claim) returned `none`;
* **the stream's run** (`streamRun_facts`, a `StreamFacts`): every commitment has a claim (`claims_complete`:
  `combine` is `some` on each, as `atTOf` states a relation on each, `atTOf_cover`), `C1`'s and the setup's stacks
  and `C2`'s tree are the committed ones, every claim's point has its stack's variables (at most the batch's
  rounds, `batchRounds_point`), the matrices' claim is Flock's pending reduction at the batch's point, there exactly
  with Flock (`matrices_isSome_iff`). Proved by peeling the `StateT` program's binds one at a time (`peel`, …), each
  bound value a variable: no term grows (a `simp` of the whole program takes minutes and overflows the kernel);
* **`prover_none_pow`**: at the reference shape with Flock, if `proveWith` returns `none`, one of the five openings
  reached WHIR's `17`-bit proof of work at a sponge where every nonce below `fuel` fails (`pcsOpen_fails_only_at_pow`,
  each opening at `27, 27, 24, 28, 28` variables, `reference_wordVars`). Under two hypotheses, stated as definitions:
  `C2ColumnsHonest tr` (the prover's `atTOf` lists `C2`'s columns as `Shape.c2Columns` does, so that `C2`'s claim
  has `27` coordinates: the batch cuts it to `layouts shape a.c2Columns`, the commitment uses `layoutsOf shape`), and
  `FlockMatrixPoint flock 27 28` (Flock's prover, a parameter of `proveWith`, leaves a matrices' claim of `28`
  coordinates at the batch's `27`-coordinate point).
-/

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniComplete.ProverRun

theorem idBind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
theorem idPure {α : Type} (a : α) : (pure a : Id α) = a := rfl
theorem idMap {α β : Type} (f : α → β) (x : Id α) : f <$> x = f x := rfl

variable (H : List UInt8 → Digest) (F : KeccakState → KeccakState)

def proverSeed (programIv : List UInt8) (tr : Trace) : Digest :=
  seedOf (m := Id) H (contractIvOf (m := Id) H tr.shape programIv (setupTreesOf (m := Id) H tr).roots)
    tr.publicInput

def streamRun (flock : FlockProver Id) (blake2s : Blake2s) (programIv : List UInt8) (tr : Trace) : CoreOut × Wr :=
  (proveStreamWith (m := Id) H (commitReal (m := Id) H) flock blake2s tr).run
    (Wr.start (proverSeed H programIv tr))

def openingFor (fuel : ℕ) (trees : SetupTrees) (out : CoreOut) (words : List (List UInt8)) :
    Commitment → List E → E → Option Compile.Proof
  | .c1, pt, v => E2ECompleteness.proveOpeningWithH (m := Id) H F fuel
      (plainLayout (layoutWordVars (words.getD 0 []))) out.c1.2.tree out.c1.1 [⟨pt, v⟩]
  | .c2, pt, v => E2ECompleteness.proveOpeningWithH (m := Id) H F fuel
      (plainLayout (layoutWordVars (words.getD 1 []))) out.c2.2.tree out.c2.1 [⟨pt, v⟩]
  | .setup, pt, v => E2ECompleteness.proveOpeningWithH (m := Id) H F fuel
      (plainLayout (layoutWordVars (words.getD 2 []))) trees.bytecode out.setup [⟨pt, v⟩]

def claimProof (fuel : ℕ) (trees : SetupTrees) (out : CoreOut) (words : List (List UInt8)) (c : Commitment) :
    Option Compile.Proof :=
  match out.claims.find? (·.1 == c) with
  | some (_, pt, v) => openingFor H F fuel trees out words c pt v
  | none => none

def matrixProofs (fuel : ℕ) (trees : SetupTrees) (words : List (List UInt8)) :
    Option Flock.MatrixClaim → Option Compile.Proof × Option Compile.Proof
  | some mc =>
    (E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout (layoutWordVars (words.getD 3 [])))
      trees.a0 (flockMatrixStack true) [⟨mc.point, mc.a⟩],
     E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout (layoutWordVars (words.getD 4 [])))
      trees.b0 (flockMatrixStack false) [⟨mc.point, mc.b⟩])
  | none => (some noProof, some noProof)

/-- **`proveWith` at `Id`**: the three claims' openings, then the matrices', bound in `Option`. -/
theorem proveWith_eq (fuel : ℕ) (flock : FlockProver Id) (blake2s : Blake2s) (programIv : List UInt8)
    (tr : Trace) :
    proveWith (m := Id) H F fuel flock blake2s programIv tr =
      (claimProof H F fuel (setupTreesOf (m := Id) H tr) (streamRun H flock blake2s programIv tr).1
          (layoutWords tr.shape) .c1).bind fun p1 ↦
      (claimProof H F fuel (setupTreesOf (m := Id) H tr) (streamRun H flock blake2s programIv tr).1
          (layoutWords tr.shape) .c2).bind fun p2 ↦
      (claimProof H F fuel (setupTreesOf (m := Id) H tr) (streamRun H flock blake2s programIv tr).1
          (layoutWords tr.shape) .setup).bind fun p3 ↦
      (matrixProofs H F fuel (setupTreesOf (m := Id) H tr) (layoutWords tr.shape)
          (streamRun H flock blake2s programIv tr).1.matrices).1.bind fun pa ↦
      (matrixProofs H F fuel (setupTreesOf (m := Id) H tr) (layoutWords tr.shape)
          (streamRun H flock blake2s programIv tr).1.matrices).2.bind fun pb ↦
      some ⟨(streamRun H flock blake2s programIv tr).1.stream, p1, p2, p3, pa, pb⟩ := by
  simp only [proveWith, idBind, idPure, streamRun, proverSeed]
  generalize (StateT.run (proveStreamWith (m := Id) H (commitReal (m := Id) H) flock blake2s tr)
    (Wr.start (seedOf (m := Id) H (contractIvOf (m := Id) H tr.shape programIv (setupTreesOf (m := Id) H tr).roots)
      tr.publicInput))).1 = out
  generalize setupTreesOf (m := Id) H tr = trees
  unfold claimProof matrixProofs
  split <;> split <;> split <;> split <;> (try simp only [openingFor, *]) <;> rfl


/-! ### `combine` and the relations at `t` -/

theorem combine_isSome (relations : List Relation) (c : Commitment) (rho : E)
    (h : ∃ r ∈ relations, r.commitment = c) : (combine relations c rho).isSome := by
  obtain ⟨r, hr, hc⟩ := h
  unfold combine
  have : (relations.filter (·.commitment == c)).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff_exists_mem]
    exact ⟨r, List.mem_filter.mpr ⟨hr, by simp [hc]⟩⟩
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A `for` loop in `Id` whose every step yields keeps an invariant. -/
theorem forIn_invariant {α β : Type} (L : List α) (init : β) (F : α → β → Id (ForInStep β)) (P : β → Prop)
    (hinit : P init) (hF : ∀ a b, P b → ∃ b', F a b = pure (.yield b') ∧ P b') : P (forIn L init F) := by
  induction L generalizing init with
  | nil => exact hinit
  | cons a L ih =>
    obtain ⟨b', hb', hP⟩ := hF a init hinit
    rw [List.forIn_cons, hb']
    exact ih b' hP

theorem heapRelations_heap (shape : UniStatement.Shape) (active : List E) (parts : List TablePart)
    (weights : Array E) (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : E)
    (w : List E) (constraintChunks : List ℕ) :
    Relation.equal .heap (w.take shape.heap.h) heapValue ∈ (heapRelations shape active parts weights beta heapValue
      constraintValue memoryPull memoryPush bytecodePull bytecodePush w constraintChunks).1 := by
  unfold heapRelations
  simp only [Id.run, idBind, idPure]
  rw [Array.toList_push]
  apply List.mem_append_left
  refine forIn_invariant _ _ _
    (fun s : Array Relation × Array (Column × ℕ × Bool) ↦
      Relation.equal .heap (w.take shape.heap.h) heapValue ∈ s.1.toList) ?_ fun a b hb ↦ ?_
  · simp only [Array.toList_push]
    simp
  rcases a with ⟨⟨l, r, pos⟩, idx⟩
  cases l <;> exact ⟨_, rfl, by simp [hb]⟩

/-- The digits `atTOf` reads at `t`. -/
abbrev wAt (tr : Trace) (t : E) : List E := digits t (max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2)

set_option maxHeartbeats 1000000 in
/-- **`C1` has a relation at `t`**: the memory's final counts'. -/
theorem atTOf_mem_c1 (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut) :
    Relation.equal (.memory 3) ((wAt tr t).take tr.shape.logMemory)
      (evalB ((bCoefficients tr.shape.logMemory (tr.memory.getD 3 #[])).map ofK) tr.shape.logMemory (wAt tr t)) ∈
        (atTOf tr c2 alphas beta gamma t fo).relations := by
  unfold atTOf
  simp only [Id.run, idBind, idPure]
  rcases fo with _ | ⟨point, end_, pending, tabs⟩
  · simp
  · cases end_ <;> simp

set_option maxHeartbeats 1000000 in
/-- **The setup has a relation at `t`**: the addresses'. -/
theorem atTOf_mem_setup (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut) :
    Relation.equal .address ((wAt tr t).take tr.shape.logMemory)
      (evalB ((bCoefficients tr.shape.logMemory (addressColumn tr.shape.logMemory)).map ofK) tr.shape.logMemory
        (wAt tr t)) ∈ (atTOf tr c2 alphas beta gamma t fo).relations := by
  unfold atTOf
  simp only [Id.run, idBind, idPure]
  rcases fo with _ | ⟨point, end_, pending, tabs⟩
  · simp
  · cases end_ <;> simp

set_option maxHeartbeats 1000000 in
/-- **`C2` has a relation at `t`**: the heap's value. -/
theorem atTOf_mem_c2 (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut) :
    Relation.equal .heap ((wAt tr t).take tr.shape.heap.h) (evalB c2.heapB tr.shape.heap.h (wAt tr t)) ∈
      (atTOf tr c2 alphas beta gamma t fo).relations := by
  unfold atTOf
  simp only [Id.run, idBind, idPure]
  rcases fo with _ | ⟨point, end_, pending, tabs⟩
  · simp [heapRelations_heap]
  · cases end_ <;> simp [heapRelations_heap]

/-- **Every commitment has a relation at `t`.** -/
theorem atTOf_cover (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut)
    (c : Commitment) : ∃ r ∈ (atTOf tr c2 alphas beta gamma t fo).relations, r.commitment = c := by
  cases c
  · exact ⟨_, atTOf_mem_c1 tr c2 alphas beta gamma t fo, rfl⟩
  · exact ⟨_, atTOf_mem_c2 tr c2 alphas beta gamma t fo, rfl⟩
  · exact ⟨_, atTOf_mem_setup tr c2 alphas beta gamma t fo, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **`atTOf`'s pending matrices are Flock's**, with its point. -/
theorem atTOf_pending (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (fo : Option FlockOut) :
    (atTOf tr c2 alphas beta gamma t fo).pending = fo.map fun o ↦ (o.pending, o.point) := by
  unfold atTOf
  simp only [Id.run, idBind, idPure]
  rcases fo with _ | ⟨point, end_, pending, tabs⟩
  · rfl
  · cases end_ <;> rfl


/-! ### The batching sumcheck's point -/

theorem batchRound_point (H : List UInt8 → Digest) (lambda : E) (j : ℕ) (st : BatchState) (w : Wr) :
    ((batchRound (m := Id) H lambda j st).run w).1.point.length = st.point.length + 1 := by
  unfold batchRound
  simp only [StateT.run_bind, StateT.run_pure, idBind, idPure]
  simp

theorem forIn_batchRound_point (H : List UInt8 → Digest) (lambda : E) :
    ∀ (L : List ℕ) (st : BatchState) (w : Wr),
      (StateT.run (forIn L st fun j st ↦ do
        let st ← batchRound (m := Id) H lambda j st
        pure (ForInStep.yield st)) w).1.point.length = st.point.length + L.length
  | [], st, w => rfl
  | j :: L, st, w => by
    rw [List.forIn_cons]
    simp only [StateT.run_bind, StateT.run_pure, idBind, idPure]
    rw [forIn_batchRound_point H lambda L, batchRound_point, List.length_cons]
    omega

/-- **The batching sumcheck's point has one coordinate a round.** -/
theorem batchRounds_point (H : List UInt8 → Digest) (lambda : E) (vars : ℕ) (st : BatchState) (w : Wr) :
    ((batchRounds (m := Id) H lambda vars st).run w).1.length = st.point.length + vars := by
  unfold batchRounds
  simp only [StateT.run_bind, StateT.run_pure, idBind, idPure]
  rw [forIn_batchRound_point, List.length_range]


/-! ### The stream's run -/

theorem combined_fst (rels : List Relation) (rho : E) (h : ∀ c, ∃ r ∈ rels, r.commitment = c) :
    (commitments.filterMap fun c ↦ (combine rels c rho).map (c, ·)).map (·.1) = [.c1, .c2, .setup] := by
  obtain ⟨x1, h1⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c1 rho (h .c1))
  obtain ⟨x2, h2⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .c2 rho (h .c2))
  obtain ⟨x3, h3⟩ := Option.isSome_iff_exists.mp (combine_isSome rels .setup rho (h .setup))
  simp [commitments, h1, h2, h3]

/-- **`C2`'s columns are the shape's**: the prover's `atTOf` lists `C2`'s columns as `Shape.c2Columns` does, for
every challenge. -/
def C2ColumnsHonest (tr : Trace) : Prop :=
  ∀ c2 alphas beta gamma t fo, (atTOf tr c2 alphas beta gamma t fo).c2Columns = tr.shape.c2Columns

/-- **What the openings read off the stream's output** `out`. -/
structure StreamFacts (commit : Commitment → ℕ → Array K → Id Committed) (flock : FlockProver Id)
    (blake2s : Blake2s) (tr : Trace) (out : CoreOut) : Prop where
  claims_fst : out.claims.map (·.1) = [.c1, .c2, .setup]
  c1 : out.c1 = (c1Stack tr, commit .c1 (c1Layout tr.shape).vars (c1Stack tr))
  c2 : out.c2.2 = commit .c2 (((layoutsOf tr.shape).lookup .c2).getD default).vars out.c2.1
  setup : out.setup = setupStackOf tr
  points : C2ColumnsHonest tr → ∀ x ∈ out.claims, x.2.1.length =
    min (layoutIn (layouts tr.shape tr.shape.c2Columns) x.1).vars
      (((layouts tr.shape tr.shape.c2Columns).map (·.2.vars)).foldl max 0)
  matrices : C2ColumnsHonest tr → ∀ mc, out.matrices = some mc → ∃ logN v q w ma mb r,
    mc = (((flock logN v q).run w).1.pending.matrixClaim r ma mb) ∧
      r.length = ((layouts tr.shape tr.shape.c2Columns).map (·.2.vars)).foldl max 0
  omitted : blake2s = .omitted → out.matrices = none
  flock_some : ∀ v, blake2s = .flock v → out.matrices.isSome

/-! #### Peeling a `StateT` program's binds -/

theorem peel {σ α β : Type} {x : StateT σ Id α} {f : α → StateT σ Id β} {P : β → Prop} {s : σ}
    (h : ∀ a s', x.run s = (a, s') → P ((f a).run s').1) : P ((x >>= f).run s).1 := h _ _ rfl

theorem peel_lift {σ α β : Type} {x : Id α} {f : α → StateT σ Id β} {P : β → Prop} {s : σ}
    (h : P ((f x).run s).1) : P ((StateT.lift x >>= f).run s).1 := h

theorem peel_map {σ α β γ : Type} {g : γ → α} {x : StateT σ Id γ} {f : α → StateT σ Id β} {P : β → Prop}
    {s : σ} (h : ∀ a s', x.run s = (a, s') → P ((f (g a)).run s').1) : P (((g <$> x) >>= f).run s).1 :=
  h _ _ rfl

theorem peel_get {σ β : Type} {f : σ → StateT σ Id β} {P : β → Prop} {s : σ}
    (h : P ((f s).run s).1) : P ((get >>= f).run s).1 := h

theorem peel_pure_bind {σ α β : Type} {a : α} {f : α → StateT σ Id β} {P : β → Prop} {s : σ}
    (h : P ((f a).run s).1) : P ((pure a >>= f).run s).1 := h

theorem peel_pure {σ β : Type} {a : β} {P : β → Prop} {s : σ} (h : P a) : P ((pure a : StateT σ Id β).run s).1 := h

set_option maxHeartbeats 1000000 in
theorem streamRun_facts (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (blake2s : Blake2s) (tr : Trace) (w0 : Wr) :
    StreamFacts commit flock blake2s tr ((proveStreamWith (m := Id) H commit flock blake2s tr).run w0).1 := by
  unfold proveStreamWith
  refine peel fun _ s0 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s1 _ ↦ ?_
  refine peel fun alphas s2 _ ↦ ?_
  refine peel fun beta s3 _ ↦ ?_
  refine peel fun gamma s4 _ ↦ ?_
  cases blake2s with
  | flock v =>
    refine peel_map fun fo s5 hfo ↦ ?_
    dsimp only
    refine peel_lift ?_
    refine peel fun _ s6 _ ↦ ?_
    refine peel fun t s7 _ ↦ ?_
    refine peel fun _ s8 _ ↦ ?_
    refine peel fun rho s9 _ ↦ ?_
    refine peel fun lambda s10 _ ↦ ?_
    refine peel fun r s11 hr ↦ ?_
    refine peel fun _ s12 _ ↦ ?_
    have hpend := atTOf_pending tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some fo)
    split
    · rename_i p snd hp
      refine peel fun _ s13 _ ↦ ?_
      refine peel_pure_bind ?_
      refine peel_get ?_
      refine peel_pure ?_
      have hl := congrArg (fun p ↦ p.1.length) hr
      simp only [batchRounds_point, List.length_nil, Nat.zero_add] at hl
      refine ⟨?_, rfl, rfl, rfl, ?_, ?_, (fun h ↦ nomatch h), fun _ _ ↦ rfl⟩
      · simp only [List.map_map, Function.comp_def]
        exact combined_fst _ _ (atTOf_cover _ _ _ _ _ _ _)
      · intro hC2 x hx
        unfold C2ColumnsHonest at hC2
        simp only [List.mem_map] at hx
        obtain ⟨⟨c, snd⟩, -, rfl⟩ := hx
        rw [List.length_take, ← hl, hC2]
      · intro hC2 mc hmc
        unfold C2ColumnsHonest at hC2
        rw [hp] at hpend
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpend hmc
        have hfo' : fo = ((flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) v tr.qflock).run s4).1 := by
          rw [hfo]
        rw [hpend.1, hfo'] at hmc
        exact ⟨_, v, tr.qflock, s4, _, _, r, hmc.symm, by rw [← hl, hC2]⟩
    · rename_i hp
      rw [hp] at hpend
      exact absurd hpend (by simp)
  | omitted =>
    refine peel_pure_bind ?_
    dsimp only
    refine peel_lift ?_
    refine peel fun _ s6 _ ↦ ?_
    refine peel fun t s7 _ ↦ ?_
    refine peel fun _ s8 _ ↦ ?_
    refine peel fun rho s9 _ ↦ ?_
    refine peel fun lambda s10 _ ↦ ?_
    refine peel fun r s11 hr ↦ ?_
    refine peel fun _ s12 _ ↦ ?_
    have hpend := atTOf_pending tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none
    split
    · rename_i p snd hp
      rw [hp] at hpend
      exact absurd hpend (by simp)
    · rename_i hp
      refine peel_pure_bind ?_
      refine peel_get ?_
      refine peel_pure ?_
      have hl := congrArg (fun p ↦ p.1.length) hr
      simp only [batchRounds_point, List.length_nil, Nat.zero_add] at hl
      refine ⟨?_, rfl, rfl, rfl, ?_, ?_, fun _ ↦ rfl, fun _ h ↦ nomatch h⟩
      · simp only [List.map_map, Function.comp_def]
        exact combined_fst _ _ (atTOf_cover _ _ _ _ _ _ _)
      · intro hC2 x hx
        unfold C2ColumnsHonest at hC2
        simp only [List.mem_map] at hx
        obtain ⟨⟨c, snd⟩, -, rfl⟩ := hx
        rw [List.length_take, ← hl, hC2]
      · intro _ mc hmc
        exact absurd hmc (by simp)


/-! ### The prover's result -/

/-- **Every commitment has a claim** in the stream's output, for every trace and challenge. -/
theorem claims_complete (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (blake2s : Blake2s) (tr : Trace) (w0 : Wr) :
    ((proveStreamWith (m := Id) H commit flock blake2s tr).run w0).1.claims.map (·.1) = [.c1, .c2, .setup] :=
  (streamRun_facts H commit flock blake2s tr w0).claims_fst

/-- **The matrices' claim is there exactly with Flock.** -/
theorem matrices_isSome_iff (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (blake2s : Blake2s) (tr : Trace) (w0 : Wr) :
    ((proveStreamWith (m := Id) H commit flock blake2s tr).run w0).1.matrices.isSome ↔ ∃ v, blake2s = .flock v := by
  have hf := streamRun_facts H commit flock blake2s tr w0
  constructor
  · intro h
    cases blake2s with
    | flock v => exact ⟨v, rfl⟩
    | omitted => rw [hf.omitted rfl] at h; exact absurd h (by simp)
  · rintro ⟨v, rfl⟩
    exact hf.flock_some v rfl

theorem claimProof_eq_some (fuel : ℕ) (trees : SetupTrees) (out : CoreOut) (words : List (List UInt8))
    (c : Commitment) (p : Compile.Proof) :
    claimProof H F fuel trees out words c = some p ↔
      ∃ c' pt v, out.claims.find? (·.1 == c) = some (c', pt, v) ∧ openingFor H F fuel trees out words c pt v = some p := by
  unfold claimProof
  split
  · rename_i c' pt v heq
    simp [heq]
  · rename_i heq
    simp [heq]

theorem claimProof_eq_none (fuel : ℕ) (trees : SetupTrees) (out : CoreOut) (words : List (List UInt8))
    (c : Commitment) :
    claimProof H F fuel trees out words c = none ↔
      out.claims.find? (·.1 == c) = none ∨
        ∃ c' pt v, out.claims.find? (·.1 == c) = some (c', pt, v) ∧ openingFor H F fuel trees out words c pt v = none := by
  unfold claimProof
  split
  · rename_i c' pt v heq
    simp [heq]
  · rename_i heq
    simp [heq]

/-- **`proveWith` returns a proof** exactly when each of `C1`, `C2`, the setup has a claim and the five openings
(`claimProof`: the stack, tree and layout of the commitment, the point claim; `matrixProofs`: `A0`, `B0` at Flock's
claim, or the empty proofs without) all return one; the proof is the stream and those openings. -/
theorem proveWith_eq_some (fuel : ℕ) (flock : FlockProver Id) (blake2s : Blake2s) (programIv : List UInt8)
    (tr : Trace) (π : UniProof) :
    proveWith (m := Id) H F fuel flock blake2s programIv tr = some π ↔
      ∃ p1 p2 p3 pa pb,
        claimProof H F fuel (setupTreesOf (m := Id) H tr) (streamRun H flock blake2s programIv tr).1
          (layoutWords tr.shape) .c1 = some p1 ∧
        claimProof H F fuel (setupTreesOf (m := Id) H tr) (streamRun H flock blake2s programIv tr).1
          (layoutWords tr.shape) .c2 = some p2 ∧
        claimProof H F fuel (setupTreesOf (m := Id) H tr) (streamRun H flock blake2s programIv tr).1
          (layoutWords tr.shape) .setup = some p3 ∧
        (matrixProofs H F fuel (setupTreesOf (m := Id) H tr) (layoutWords tr.shape)
          (streamRun H flock blake2s programIv tr).1.matrices).1 = some pa ∧
        (matrixProofs H F fuel (setupTreesOf (m := Id) H tr) (layoutWords tr.shape)
          (streamRun H flock blake2s programIv tr).1.matrices).2 = some pb ∧
        π = ⟨(streamRun H flock blake2s programIv tr).1.stream, p1, p2, p3, pa, pb⟩ := by
  rw [proveWith_eq, Option.bind_eq_some_iff]
  simp only [Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨p1, h1, p2, h2, p3, h3, pa, ha, pb, hb, rfl⟩
    exact ⟨p1, p2, p3, pa, pb, h1, h2, h3, ha, hb, rfl⟩
  · rintro ⟨p1, p2, p3, pa, pb, h1, h2, h3, ha, hb, rfl⟩
    exact ⟨p1, h1, p2, h2, p3, h3, pa, ha, pb, hb, rfl⟩

/-- **When `proveWith` fails**: a commitment has no claim, or one of the five openings returned `none` (each named
with its layout, tree, stack and point claim). -/
theorem proveWith_eq_none (fuel : ℕ) (flock : FlockProver Id) (blake2s : Blake2s) (programIv : List UInt8)
    (tr : Trace) (h : proveWith (m := Id) H F fuel flock blake2s programIv tr = none) :
    let trees := setupTreesOf (m := Id) H tr
    let out := (streamRun H flock blake2s programIv tr).1
    let words := layoutWords tr.shape
    (∃ c ∈ [Commitment.c1, .c2, .setup], out.claims.find? (·.1 == c) = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .c1) = some (c', pt, v) ∧
      E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout (layoutWordVars (words.getD 0 [])))
        out.c1.2.tree out.c1.1 [⟨pt, v⟩] = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .c2) = some (c', pt, v) ∧
      E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout (layoutWordVars (words.getD 1 [])))
        out.c2.2.tree out.c2.1 [⟨pt, v⟩] = none) ∨
    (∃ c' pt v, out.claims.find? (·.1 == .setup) = some (c', pt, v) ∧
      E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout (layoutWordVars (words.getD 2 [])))
        trees.bytecode out.setup [⟨pt, v⟩] = none) ∨
    (∃ mc, out.matrices = some mc ∧
      E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout (layoutWordVars (words.getD 3 [])))
        trees.a0 (flockMatrixStack true) [⟨mc.point, mc.a⟩] = none) ∨
    (∃ mc, out.matrices = some mc ∧
      E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout (layoutWordVars (words.getD 4 [])))
        trees.b0 (flockMatrixStack false) [⟨mc.point, mc.b⟩] = none) := by
  intro trees out words
  rw [proveWith_eq] at h
  change ((claimProof H F fuel trees out words .c1).bind fun p1 ↦ (claimProof H F fuel trees out words .c2).bind
    fun p2 ↦ (claimProof H F fuel trees out words .setup).bind fun p3 ↦
    (matrixProofs H F fuel trees words out.matrices).1.bind fun pa ↦
    (matrixProofs H F fuel trees words out.matrices).2.bind fun pb ↦
    some (⟨out.stream, p1, p2, p3, pa, pb⟩ : UniProof)) = none at h
  rcases h1 : claimProof H F fuel trees out words .c1 with _ | p1
  · rcases (claimProof_eq_none H F fuel trees out words .c1).mp h1 with h | ⟨c', pt, v, hf, ho⟩
    · exact Or.inl ⟨.c1, by simp, h⟩
    · exact Or.inr (Or.inl ⟨c', pt, v, hf, ho⟩)
  rcases h2 : claimProof H F fuel trees out words .c2 with _ | p2
  · rcases (claimProof_eq_none H F fuel trees out words .c2).mp h2 with h | ⟨c', pt, v, hf, ho⟩
    · exact Or.inl ⟨.c2, by simp, h⟩
    · exact Or.inr (Or.inr (Or.inl ⟨c', pt, v, hf, ho⟩))
  rcases h3 : claimProof H F fuel trees out words .setup with _ | p3
  · rcases (claimProof_eq_none H F fuel trees out words .setup).mp h3 with h | ⟨c', pt, v, hf, ho⟩
    · exact Or.inl ⟨.setup, by simp, h⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c', pt, v, hf, ho⟩)))
  rw [h1, h2, h3] at h
  simp only [Option.bind_some] at h
  rcases hm : out.matrices with _ | mc
  · rw [hm] at h
    exact absurd h (by simp [matrixProofs])
  · rw [hm] at h
    simp only [matrixProofs] at h
    rcases ha : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel
      (plainLayout (layoutWordVars (words.getD 3 []))) trees.a0 (flockMatrixStack true) [⟨mc.point, mc.a⟩] with _ | pa
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨mc, rfl, ha⟩))))
    · rw [ha] at h
      simp only [Option.bind_some] at h
      rcases hb : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel
        (plainLayout (layoutWordVars (words.getD 4 []))) trees.b0 (flockMatrixStack false) [⟨mc.point, mc.b⟩] with _ | pb
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨mc, rfl, hb⟩))))
      · rw [hb] at h
        exact absurd h (by simp)


/-! ### At the reference shape -/

theorem ref_c1Layout : (c1Layout reference).vars = 27 := reference_c1Vars

theorem ref_setupLayout : (setupLayout reference).vars = 24 := reference_setupVars

theorem ref_c2Layout : (((layoutsOf reference).lookup .c2).getD default).vars = 27 := by
  rw [layoutsOf_eq]
  exact reference_c2Vars

theorem ref_layoutIn_c1 : (layoutIn (layouts reference reference.c2Columns) .c1).vars = 27 := reference_c1Vars

theorem ref_layoutIn_c2 : (layoutIn (layouts reference reference.c2Columns) .c2).vars = 27 := reference_c2Vars

theorem ref_layoutIn_setup : (layoutIn (layouts reference reference.c2Columns) .setup).vars = 24 :=
  reference_setupVars

theorem ref_rounds : ((layouts reference reference.c2Columns).map (·.2.vars)).foldl max 0 = 27 := by
  show ((layoutsOf reference).map (·.2.vars)).foldl max 0 = 27
  rw [reference_vars]
  rfl

theorem ref_word (i : ℕ) :
    layoutWordVars ((layoutWords reference).getD i []) = [27, 27, 24, 28, 28].getD i 0 := by
  rw [← reference_wordVars,
    show (0 : ℕ) = layoutWordVars [] from rfl, List.getD_map]

theorem setupTrees_bytecode (tr : Trace) :
    (setupTreesOf (m := Id) H tr).bytecode =
      E2ECompleteness.commitWithH (m := Id) H (setupLayout tr.shape).vars (setupStackOf tr) := rfl

theorem setupTrees_a0 (tr : Trace) :
    (setupTreesOf (m := Id) H tr).a0 = E2ECompleteness.commitWithH (m := Id) H 28 (flockMatrixStack true) := rfl

theorem setupTrees_b0 (tr : Trace) :
    (setupTreesOf (m := Id) H tr).b0 = E2ECompleteness.commitWithH (m := Id) H 28 (flockMatrixStack false) := rfl

/-- **Flock's matrices' claim has `vars` coordinates** at a batch point of `rounds` (what the `A0`, `B0` openings
need of the Flock prover, a parameter of `proveWith`). -/
def FlockMatrixPoint (flock : FlockProver Id) (rounds vars : ℕ) : Prop :=
  ∀ logN v q w (r : List E) ma mb, r.length = rounds →
    (((flock logN v q).run w).1.pending.matrixClaim r ma mb).point.length = vars

/-- **The honest prover fails only at a proof of work**, at the reference shape with Flock: if `proveWith` returns
`none`, one of the five openings (at `24 ≤ vars ≤ 28` variables) reached WHIR's `17`-bit proof of work at a sponge
where every nonce below `fuel` fails. Given that `C2`'s columns are the shape's (`C2ColumnsHonest`) and that Flock's
prover leaves a matrices' claim of `28` coordinates at the batch's `27`-coordinate point (`FlockMatrixPoint`). -/
theorem prover_none_pow (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace)
    (hshape : tr.shape = reference) (hC2 : C2ColumnsHonest tr) (hflock : FlockMatrixPoint flock 27 28)
    (h : proveWith (m := Id) H F fuel flock (.flock flockMain) programIv tr = none) :
    ∃ vars claims hist k sp, 24 ≤ vars ∧ vars ≤ 28 ∧
      (Whir.Complete.openingProgram vars PcsQuotient.logInvRate
        (PcsQuotient.stackClaims (plainLayout vars) claims)).after hist = some (.grind Whir.queryGrindingBits k) ∧
      ∀ n < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf n) (Compile.powStep F sp (Compile.nonceOf n)).1 =
        false := by
  have hf : StreamFacts (commitReal (m := Id) H) flock (.flock flockMain) tr
      (streamRun H flock (.flock flockMain) programIv tr).1 :=
    streamRun_facts H (commitReal (m := Id) H) flock (.flock flockMain) tr _
  have hpts := hf.points hC2
  rw [hshape] at hpts
  -- A claim found for `c` is `c`'s, with a point of its stack's variables.
  have hpt : ∀ c c' pt v, (streamRun H flock (.flock flockMain) programIv tr).1.claims.find? (·.1 == c) =
      some (c', pt, v) → c' = c ∧ pt.length = min (layoutIn (layouts reference reference.c2Columns) c).vars 27 := by
    intro c c' pt v hfind
    have hc : c' = c := by simpa using List.find?_some hfind
    subst hc
    have := hpts _ (List.mem_of_find?_eq_some hfind)
    rw [ref_rounds] at this
    exact ⟨rfl, this⟩
  rcases proveWith_eq_none H F fuel flock (.flock flockMain) programIv tr h with
    hmiss | ⟨c', pt, v, hfind, hopen⟩ | ⟨c', pt, v, hfind, hopen⟩ | ⟨c', pt, v, hfind, hopen⟩ | ⟨mc, hmc, hopen⟩ |
      ⟨mc, hmc, hopen⟩
  · -- Every commitment has a claim.
    obtain ⟨c, hc, hnone⟩ := hmiss
    have hc' : c ∈ (streamRun H flock (.flock flockMain) programIv tr).1.claims.map (·.1) := by
      rw [hf.claims_fst]
      exact hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
    exact absurd (by simp : (x.1 == x.1) = true) (List.find?_eq_none.mp hnone x hx)
  · -- `C1`.
    obtain ⟨-, hlen⟩ := hpt .c1 c' pt v hfind
    rw [ref_layoutIn_c1, Nat.min_self] at hlen
    rw [hf.c1, hshape, ref_word 0, ref_c1Layout] at hopen
    obtain ⟨hist, k, sp, h1, h2⟩ := pcsOpen_fails_only_at_pow H F fuel (vars := 27) (by norm_num) (by norm_num)
      _ _ (fun c hc ↦ by rw [List.mem_singleton] at hc; subst hc; exact hlen) hopen
    exact ⟨27, _, hist, k, sp, by norm_num, by norm_num, h1, h2⟩
  · -- `C2`.
    obtain ⟨-, hlen⟩ := hpt .c2 c' pt v hfind
    rw [ref_layoutIn_c2, Nat.min_self] at hlen
    rw [hf.c2, hshape, ref_word 1, ref_c2Layout] at hopen
    obtain ⟨hist, k, sp, h1, h2⟩ := pcsOpen_fails_only_at_pow H F fuel (vars := 27) (by norm_num) (by norm_num)
      _ _ (fun c hc ↦ by rw [List.mem_singleton] at hc; subst hc; exact hlen) hopen
    exact ⟨27, _, hist, k, sp, by norm_num, by norm_num, h1, h2⟩
  · -- The setup.
    obtain ⟨-, hlen⟩ := hpt .setup c' pt v hfind
    rw [ref_layoutIn_setup, show min 24 27 = 24 from rfl] at hlen
    rw [hf.setup, setupTrees_bytecode, hshape, ref_word 2, ref_setupLayout] at hopen
    obtain ⟨hist, k, sp, h1, h2⟩ := pcsOpen_fails_only_at_pow H F fuel (vars := 24) (by norm_num) (by norm_num)
      (setupStackOf tr) _ (fun c hc ↦ by rw [List.mem_singleton] at hc; subst hc; exact hlen) hopen
    exact ⟨24, _, hist, k, sp, by norm_num, by norm_num, h1, h2⟩
  · -- `A0`.
    obtain ⟨logN, v, q, w, ma, mb, r, rfl, hr⟩ := hf.matrices hC2 mc hmc
    rw [hshape, ref_rounds] at hr
    have hlen := hflock logN v q w r ma mb hr
    rw [setupTrees_a0, hshape, ref_word 3] at hopen
    obtain ⟨hist, k, sp, h1, h2⟩ := pcsOpen_fails_only_at_pow H F fuel (vars := 28) (by norm_num) (by norm_num)
      (flockMatrixStack true) _ (fun c hc ↦ by rw [List.mem_singleton] at hc; subst hc; exact hlen) hopen
    exact ⟨28, _, hist, k, sp, by norm_num, by norm_num, h1, h2⟩
  · -- `B0`.
    obtain ⟨logN, v, q, w, ma, mb, r, rfl, hr⟩ := hf.matrices hC2 mc hmc
    rw [hshape, ref_rounds] at hr
    have hlen := hflock logN v q w r ma mb hr
    rw [setupTrees_b0, hshape, ref_word 4] at hopen
    obtain ⟨hist, k, sp, h1, h2⟩ := pcsOpen_fails_only_at_pow H F fuel (vars := 28) (by norm_num) (by norm_num)
      (flockMatrixStack false) _ (fun c hc ↦ by rw [List.mem_singleton] at hc; subst hc; exact hlen) hopen
    exact ⟨28, _, hist, k, sp, by norm_num, by norm_num, h1, h2⟩

end UniComplete.ProverRun

/-- info: 'UniComplete.ProverRun.proveWith_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.ProverRun.proveWith_eq_some

/-- info: 'UniComplete.ProverRun.proveWith_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.ProverRun.proveWith_eq_none

/-- info: 'UniComplete.ProverRun.claims_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.ProverRun.claims_complete

/-- info: 'UniComplete.ProverRun.matrices_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.ProverRun.matrices_isSome_iff

/-- info: 'UniComplete.ProverRun.streamRun_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.ProverRun.streamRun_facts

/-- info: 'UniComplete.ProverRun.prover_none_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.ProverRun.prover_none_pow
