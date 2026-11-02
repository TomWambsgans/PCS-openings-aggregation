-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.Final

/-!
# Review: `Soundness.knowledgeSoundness` (adversarial review of the end statement)

Not part of any library: checked with `lake env lean Review/E2ESoundness.lean` from
`formal/EndToEnd` (h1, `review-ks`). What it checks:

1. **Axioms** of the end theorem and of every definition its statement names (`#print axioms`).
2. **A sweep of the statement's definitional closure** (`#review_sweep`): every constant reachable
   from the extractor, the verifier, the experiment and the bound through definitions' types and
   bodies (proofs not entered), reporting axioms, `opaque` constants (a `partial def` is one), and
   `@[implemented_by]` / `@[extern]` constants outside Lean's core, and whether the extractor and the
   verifier are `noncomputable`.
3. **The experiments' verifiers are one verifier**: the setup's root is the root of the setup's tree
   (`setupWith_eq`); the deployed verifier is the experiment's at `π := Keccak-f[1600]`
   (`deployedIndexRoot_eq`).
4. **Non-vacuity, as far as it goes**: the honest prover, run as an adversary, is accepted in the
   knowledge-soundness experiment at least as often as in the completeness experiment
   (`honest_accepted_ge`); so `Completeness δ` with `δ < 1` makes the experiment accept with positive
   probability (`nonvacuous_of_completeness`). `Completeness` is not proved (`E2ECompleteness`
   leaves `RejectGood` and the block count), so non-vacuity is not proved either.
5. **The extractor ignores the adversary's coins** (`extractor_coins`).
6. **The extractor's fast path fails on one error** (`#eval`, at the smallest stack, `μ = 15`): a
   word one symbol away from a codeword gets no fast candidate. Before the unique-decoding stage, the
   extractor then fell to the Guruswami–Sudan decoder (at the deployed witness table, `n = 2^20`,
   multiplicity `1149`, `Y`-degree `1625`, `2^39.3` interpolation conditions per lane;
   `E2ESoundnessNumbers.py`); now Gao's unique decoder (`UniqueDecoding.uniqueStacks`) recovers the
   stack (`#eval` at `μ = 9`, the interpreter being slow), and the list decoder runs only for words
   beyond the unique-decoding radius (`PcsQuotient/Extractor.lean`'s cost table).

**Run, not proved (non-vacuity at the deployed size).** The Statement's differential test ships
whole proofs at `2^17` rows only. At `2^22` (from the repository root):

```sh
cargo run --release -p quotient --example statement_vectors -- vectors-full.txt --full
grep '^P 22' vectors-full.txt > vectors-p22.txt          # 1 honest (ACCEPT), 14 tampered (REJECT)
grep '^I membership' vectors-full.txt > vectors-i22.txt
.lake/build/bin/differential vectors-p22.txt               # formal/Statement
.lake/build/bin/differential vectors-i22.txt               # about 3 minutes
```

On h1 (`/root/pcs-quotient-fv/statement`'s `differential`, built from the Statement before
`Layout.id` and `membership` by projections, the same functions at `π := Keccak-f[1600]`): `P: 15
vectors, Lean and Rust agree` (the honest `2^22` membership proof accepted by `PcsQuotient.verify`,
the 14 tamperings rejected) and `I: 1 vectors, Lean and Rust agree` (the Lean commitment of
`membership 22` is `8fd9a050…3ca9`).

**Numbers** (`E2ESoundnessNumbers.py`, exact rationals): `ksBound Q` is `2^-104.98` at `Q = 0`,
`2^-86.0` at `2^40`, `2^-62.0` at `2^64` (just above `2^-62`, by a factor `1 + 2^-43`), and reaches
`1` at `Q ≈ 2^125.2`.
-/

set_option linter.unusedSectionVars false
set_option simprocs false

-- Never evaluate the membership circuit (a closed term of `2^22` rows).
attribute [local irreducible] PcsQuotient.membershipBuilder PcsQuotient.secretOfStack

open OracleSpec OracleComp
open scoped ENNReal

/-! ## 1. Axioms -/

/-- info: 'Soundness.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.knowledgeSoundness

#print axioms PcsQuotient.extractor
#print axioms PcsQuotient.verifier
#print axioms PcsQuotient.deployedVerifier
#print axioms PcsQuotient.Relation
#print axioms PcsQuotient.soundnessExperiment
#print axioms PcsQuotient.BreaksKnowledgeSoundness
#print axioms PcsQuotient.KnowledgeSoundness
#print axioms Soundness.ksBound

/-! ## 2. The definitional closure -/

namespace Review.E2ESoundness

open Lean Elab Command

/-- The module a constant comes from (`current` for this file's). -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `current

/-- Lean's own modules (`Init`, `Std`, `Lean`, `Lake`). -/
def isCore (m : Name) : Bool :=
  m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean || m.getRoot == `Lake

/-- The constants a constant's type and (for a definition, an opaque, an inductive) body use; a
theorem's proof is not entered. -/
def depsOf (ci : ConstantInfo) : Array Name :=
  match ci with
  | .thmInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  | .ctorInfo v => v.type.getUsedConstants.push v.induct
  | .recInfo v => v.type.getUsedConstants
  | .axiomInfo v => v.type.getUsedConstants
  | .quotInfo v => v.type.getUsedConstants

/-- **The sweep**: the closure of the given constants through types and definitions' bodies,
with its axioms, opaques, `implemented_by` and `extern` constants (outside Lean's core listed by
name, inside counted), and whether each root is `noncomputable`. -/
elab "#review_sweep " ids:ident* : command => do
  let env ← getEnv
  let roots := ids.map (·.getId)
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots
  let mut axs : Array Name := #[]
  let mut opq : Array Name := #[]
  let mut impl : Array (Name × Name) := #[]
  let mut ext : Array Name := #[]
  let mut nThm : Nat := 0
  let mut nAll : Nat := 0
  let mut fuel : Nat := 2000000
  while fuel > 0 do
    fuel := fuel - 1
    match todo.back? with
    | none => fuel := 0
    | some n =>
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      nAll := nAll + 1
      let some ci := env.find? n | continue
      if let some i := Lean.Compiler.getImplementedBy? env n then impl := impl.push (n, i)
      if Lean.isExtern env n then ext := ext.push n
      match ci with
      | .axiomInfo _ => axs := axs.push n
      | .opaqueInfo _ => opq := opq.push n
      | .thmInfo _ => nThm := nThm + 1
      | _ => pure ()
      -- a theorem's statement is followed only to its constants' definitions, not its proof
      for d in depsOf ci do
        unless seen.contains d do todo := todo.push d
  let nonCore (n : Name) : Bool := !isCore (moduleOf env n)
  -- a chain from a root to each axiom: breadth first, parents recorded
  let mut parent : NameMap Name := {}
  let mut queue : Array Name := roots
  let mut seen2 : NameSet := NameSet.empty.insertMany roots
  let mut qi : Nat := 0
  while qi < queue.size do
    let n := queue[qi]!
    qi := qi + 1
    let some ci := env.find? n | continue
    for d in depsOf ci do
      unless seen2.contains d do
        seen2 := seen2.insert d
        parent := parent.insert d n
        queue := queue.push d
  let mut chains : Array (List Name) := #[]
  for a in axs do
    let mut chain : List Name := [a]
    let mut cur := a
    let mut k : Nat := 0
    while k < 200 do
      k := k + 1
      match parent.find? cur with
      | some p => chain := p :: chain; cur := p
      | none => k := 200
    chains := chains.push chain
  logInfo m!"axiom chains (root first): {chains}\nopaque in core: {opq.filter (!nonCore ·)}\nimplemented_by in core: {(impl.filter (!nonCore ·.1))}"
  logInfo m!"roots: {roots}\nconstants reached: {nAll} ({nThm} theorems, proofs not entered)\naxioms: {axs}\nopaque outside core: {(opq.filter nonCore).map fun n => (n, moduleOf env n)}\nopaque in core: {(opq.filter (!nonCore ·)).size}\nimplemented_by outside core: {(impl.filter (nonCore ·.1)).map fun p => (p.1, p.2, moduleOf env p.1)}\nimplemented_by in core: {(impl.filter (!nonCore ·.1)).size}\nextern outside core: {(ext.filter nonCore).map fun n => (n, moduleOf env n)}\nextern in core: {(ext.filter (!nonCore ·)).size}\nnoncomputable roots: {roots.filter (Lean.isNoncomputable env ·)}"

end Review.E2ESoundness

#review_sweep PcsQuotient.extractor
#review_sweep PcsQuotient.verifier PcsQuotient.deployedVerifier PcsQuotient.Relation
#review_sweep PcsQuotient.KnowledgeSoundness Soundness.ksBound

namespace Review.E2ESoundness

open PcsQuotient Common

/-! ## 3. The experiments' verifiers are one verifier -/

/-- **The setup's root is its tree's root**, in any lawful monad: the completeness experiment's
`setupWith` and the knowledge-soundness experiment's `setupTreeWith` then `.root` commit to the
same circuit. -/
theorem setupWith_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) :
    setupWith F = (fun t => t.root) <$> setupTreeWith F := by
  unfold setupWith setupTreeWith Circuit.indexRootWith Circuit.indexTreeWith
  rw [map_eq_bind_pure_comp]
  rfl

/-- **The deployed verifier's constant is the experiment's root at `π := Keccak-f[1600]`.** -/
theorem deployedIndexRoot_eq :
    deployedIndexRoot () =
      (Id.run (setupTreeWith (m := Id)
        fun s => pure (LeanVM.Semantics.keccakF1600 s))).root := by
  unfold deployedIndexRoot
  rw [setupWith_eq]
  rfl

/-- **The deployed verifier is the experiment's verifier at `π := Keccak-f[1600]`**, on the
experiment's root. -/
theorem deployedVerifier_eq (stmt : Statement) (proof : Proof) :
    deployedVerifier stmt proof =
      Id.run (verifier (m := Id) (fun s => pure (LeanVM.Semantics.keccakF1600 s))
        (Id.run (setupTreeWith (m := Id)
          fun s => pure (LeanVM.Semantics.keccakF1600 s))).root stmt proof) := by
  unfold deployedVerifier
  rw [deployedIndexRoot_eq]

/-! ## 4. Non-vacuity: the honest prover as an adversary -/

/-- Logging a computation's queries does not change its output. -/
theorem fst_run_logged {α : Type} (A : OracleComp RandomPermutationOracles α) :
    ∀ log : OracleQueryLog, Prod.fst <$> (simulateQ loggedOracles A).run log = A := by
  induction A using OracleComp.inductionOn with
  | pure x => intro log; simp
  | query_bind t k ih =>
    intro log
    simp [loggedOracles, ih]

/-- **The honest adversary** for `(stmt, w)`: the Statement's honest prover with uniform coins,
its proof output (`dflt` when it makes none); it ignores the commitment it is given. -/
noncomputable def honestAdversary (stmt : Statement) (w : Secret) (dflt : Proof) : Adversary :=
  fun _ => do
    let coins ← sampleCoins
    let r ← prover queryPermutation stmt w coins
    return (stmt, r.getD dflt)

/-- The common prefix: the setup's tree, then the honest prover's proof. -/
noncomputable def prefixH (stmt : Statement) (w : Secret) :
    OracleComp RandomPermutationOracles (LeanVM.Prover.Tree × Option Proof) :=
  setupTreeWith queryPermutation >>= fun t =>
    sampleCoins >>= fun c => prover queryPermutation stmt w c >>= fun r => pure (t, r)

/-- The completeness experiment's continuation: no proof is a rejection. -/
noncomputable def contC (stmt : Statement) (a : LeanVM.Prover.Tree × Option Proof) :
    OracleComp RandomPermutationOracles Bool :=
  match a.2 with
  | none => pure false
  | some proof => verifier queryPermutation a.1.root stmt proof

/-- A simulated map. -/
theorem run'_map {β γ : Type} (V : OracleComp RandomPermutationOracles β) (g : β → γ)
    (s : PermutationEdges LeanVM.Semantics.KeccakState) :
    (simulateQ lazyRandomPermutationOracles (g <$> V)).run' s =
      g <$> (simulateQ lazyRandomPermutationOracles V).run' s := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Functor.map_map]

/-- **The knowledge-soundness experiment's acceptance** is the setup, the adversary (its log
dropped) and the verifier. -/
theorem accepted_eq (A : Adversary) :
    Pr{let z ← soundnessExperiment A}[z.accepted] =
      Pr{let b ← runWithRandomPermutation (setupTreeWith queryPermutation >>= fun t =>
          A t.root >>= fun z => verifier queryPermutation t.root z.1 z.2)}[b = true] := by
  have h1 : soundnessExperiment A = runWithRandomPermutation
      (setupTreeWith queryPermutation >>= fun t =>
        (simulateQ loggedOracles (A t.root)).run [] >>= fun p =>
          verifier queryPermutation t.root p.1.1 p.1.2 >>= fun acc =>
            pure (((p.1, acc), Tree.evaluations t, p.2) : Outcome)) := rfl
  have h2 : (setupTreeWith queryPermutation >>= fun t =>
        A t.root >>= fun z => verifier queryPermutation t.root z.1 z.2) =
      (fun z : Outcome => z.1.2) <$> (setupTreeWith queryPermutation >>= fun t =>
        (simulateQ loggedOracles (A t.root)).run [] >>= fun p =>
          verifier queryPermutation t.root p.1.1 p.1.2 >>= fun acc =>
            pure (((p.1, acc), Tree.evaluations t, p.2) : Outcome)) := by
    simp only [map_bind, map_pure]
    congr 1
    funext t
    conv_lhs => rw [← fst_run_logged (A t.root) []]
    rw [bind_map_left]
    simp only [bind_pure]
  rw [h1, h2]
  unfold runWithRandomPermutation
  rw [run'_map, prEvent_map]

/-- The completeness experiment over the common prefix. -/
theorem completeness_eq (stmt : Statement) (w : Secret) :
    completenessExperiment stmt w = runWithRandomPermutation (prefixH stmt w >>= fun a =>
      contC stmt a >>= fun v => pure v) := by
  unfold completenessExperiment prefixH contC
  rw [setupWith_eq]
  simp only [bind_map_left, bind_assoc, pure_bind, bind_pure]
  rfl

/-- The knowledge-soundness experiment of the honest adversary over the common prefix. -/
theorem honest_eq (stmt : Statement) (w : Secret) (dflt : Proof) :
    (setupTreeWith queryPermutation >>= fun t =>
        honestAdversary stmt w dflt t.root >>= fun z => verifier queryPermutation t.root z.1 z.2) =
      prefixH stmt w >>= fun a =>
        verifier queryPermutation a.1.root stmt (a.2.getD dflt) >>= fun v => pure v := by
  unfold honestAdversary prefixH
  simp only [bind_assoc, pure_bind, bind_pure]

/-- **The honest prover, as an adversary, is accepted in the knowledge-soundness experiment at
least as often as in the completeness experiment** (equally often when it makes a proof). The two
experiments run one setup and one verifier. -/
theorem honest_accepted_ge (stmt : Statement) (w : Secret) (dflt : Proof) :
    Pr{let v ← completenessExperiment stmt w}[v = true] ≤
      Pr{let z ← soundnessExperiment (honestAdversary stmt w dflt)}[z.accepted] := by
  rw [accepted_eq, honest_eq, completeness_eq]
  refine Soundness.prEvent_le_of_continuations (prefixH stmt w) (contC stmt)
    (fun a => verifier queryPermutation a.1.root stmt (a.2.getD dflt))
    (fun _ v => v) (fun _ v => v) (· = true) (· = true) fun a s => ?_
  rcases a with ⟨t, _ | p⟩
  · exact le_of_eq_of_le (Soundness.zero_pure lazyRandomPermutationOracles false (· = true)
      Bool.false_ne_true s) bot_le
  · exact le_rfl

/-- **Non-vacuity from completeness**: if the honest proof of a true statement is rejected with
probability at most `δ`, the knowledge-soundness experiment accepts the honest adversary with
probability at least `1 − δ`. -/
theorem nonvacuous_of_completeness {δ : ℝ≥0∞} (hc : Completeness δ) (stmt : Statement)
    (w : Secret) (hrel : Relation stmt w) (dflt : Proof) :
    1 - δ ≤ Pr{let z ← soundnessExperiment (honestAdversary stmt w dflt)}[z.accepted] := by
  refine le_trans ?_ (honest_accepted_ge stmt w dflt)
  have hδ := hc stmt w hrel
  have hf : Pr{let v ← completenessExperiment stmt w}[v = false] =
      1 - Pr{let v ← completenessExperiment stmt w}[v = true] := by
    have := prEvent_not_eq_one_sub (completenessExperiment stmt w) (fun v => v = true)
    simpa using this
  rw [hf] at hδ
  exact tsub_le_iff_tsub_le.mp hδ

/-! ## 5. The extractor reads the adversary's permutation queries, not its coins -/

/-- **The extractor ignores the coins**: two transcripts with the same permutation queries give
the same extraction. -/
theorem extractor_coins (stmt : Statement) (setupEvals : List (List UInt8 × LeanVM.Protocol.Digest))
    (T T' : OracleQueryLog) (h : LeanVM.permutationQueries T = LeanVM.permutationQueries T')
    (proof : Proof) : extractor stmt setupEvals T proof = extractor stmt setupEvals T' proof := by
  unfold extractor transcriptExtractorFor
  rw [h]

end Review.E2ESoundness

/-! ## 6. The fast path on a word with one error -/

namespace Review.E2ESoundness.Demo

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Extraction

/-- A word of the code at `2^15` words (`κ = 9`, rate `1/2`, `2^10` columns): lane 0 a polynomial of
pseudorandom novel-basis coefficients, the other lanes zero; with `corrupt`, lane 0's symbol at
column `0` changed. -/
def word (corrupt : Bool) : ℕ → List K :=
  let c : Array K := Array.ofFn (n := 2 ^ 9) fun i =>
    K.ofLane (UInt64.ofNat (i.val * 2654435761 + 12345))
  let e := novelFwd 9 1 c
  fun v => (List.range 64).reverse.map fun u =>
    if u = 0 then (if corrupt && v == 0 then e.getD v 0 + 1 else e.getD v 0) else 0

end Review.E2ESoundness.Demo

/-- info: (1, 0, 724, 1024) -/
#guard_msgs in
#eval ((LeanVM.Extraction.fastStacks 15 1 (Review.E2ESoundness.Demo.word false)).length,
  (LeanVM.Extraction.fastStacks 15 1 (Review.E2ESoundness.Demo.word true)).length,
  LeanVM.Extraction.johnsonThreshold 15 1, 2 ^ 10)

namespace Review.E2ESoundness.Demo

open LeanVM.Parameters LeanVM.Extraction

/-- The same at `2^9` words (`κ = 3`, `16` columns, unique-decoding radius `4`; the interpreter's
products in `K` are slow, so a small stack): lane `0` a pseudorandom polynomial, its symbol at column
`0` changed with `corrupt`. -/
def smallWord (corrupt : Bool) : ℕ → List K :=
  let c : Array K := Array.ofFn (n := 2 ^ 3) fun i =>
    K.ofLane (UInt64.ofNat (i.val * 2654435761 + 12345))
  let e := novelFwd 3 1 c
  fun v => (List.range 64).reverse.map fun u =>
    if u = 0 then (if corrupt && v == 0 then e.getD v 0 + 1 else e.getD v 0) else 0

end Review.E2ESoundness.Demo

/-- info: (1, 0, 1, true) -/
#guard_msgs in
-- one wrong symbol: no fast candidate, and the unique-decoding stage recovers the stack, the fast
-- path's of the word without the error
#eval
  let ud := PcsQuotient.UniqueDecoding.uniqueStacks 9 1 (Review.E2ESoundness.Demo.smallWord true)
  ((LeanVM.Extraction.fastStacks 9 1 (Review.E2ESoundness.Demo.smallWord false)).length,
    (LeanVM.Extraction.fastStacks 9 1 (Review.E2ESoundness.Demo.smallWord true)).length, ud.length,
    ud == LeanVM.Extraction.fastStacks 9 1 (Review.E2ESoundness.Demo.smallWord false))

/-! ## The review's own lemmas: no `sorry` -/

/-- info: 'Review.E2ESoundness.honest_accepted_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Review.E2ESoundness.honest_accepted_ge

/-- info: 'Review.E2ESoundness.nonvacuous_of_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Review.E2ESoundness.nonvacuous_of_completeness

/-- info: 'Review.E2ESoundness.deployedVerifier_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Review.E2ESoundness.deployedVerifier_eq

/-- info: 'Review.E2ESoundness.extractor_coins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Review.E2ESoundness.extractor_coins
