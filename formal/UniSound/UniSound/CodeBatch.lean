-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The program is `formal/UniStatement`'s
-- `batch` (`Batch.lean`); the sumcheck's reads are `formal/FlockSound/FlockSoundUni/Decode.lean`'s.
import UniSound.CodeTables

/-!
# The batching sumcheck as reads, draws and a result

**`batch_eq`**: with Flock's matrices pending (the main line), `batch` is `λ`, the sumcheck's
`varsOf layouts` rounds of two scalars and a challenge (`readRounds`), the stacks' values and `a`,
`b` (`combined.length + 2` scalars), the terminal zero, and the result: each a function of what was
read and drawn (`batchPure`).
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-- The batch's variables: the longest stack's. -/
def varsOf (layouts : List (Commitment × StackLayout)) : ℕ := (layouts.map fun x => x.2.vars).foldl max 0

/-- The batch's claimed sum: `Σ_k λ^k v_k`, and `λ^n`. -/
def batchTarget (combined : List (Commitment × Combined)) (lambda : E) : E × E :=
  combined.foldl (fun acc x => (acc.1 + acc.2 * x.2.value, acc.2 * lambda)) (0, 1)

/-- A stack's layout by its commitment. -/
def layoutOf (layouts : List (Commitment × StackLayout)) (c : Commitment) : StackLayout :=
  ((layouts.find? fun x => x.1 == c).map fun x => x.2).getD default

/-- The batch's terminal fold over the stacks: `Σ_k λ^k W_k(r) ext_k(r) v_k`, `λ^n`, the point
claims, the bit-slice claim left. -/
def batchFold (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (lambda : E) (r : List E) (values : List E) :
    E × E × Array (Commitment × Opening) × Option Combined :=
  (combined.zip values).foldl
    (fun acc x =>
      (acc.1 + acc.2.1 * weightAt x.1.2 (layoutOf layouts x.1.1) r ringMap *
          (List.range' (layoutOf layouts x.1.1).vars (varsOf layouts - (layoutOf layouts x.1.1).vars)).foldl
            (fun e j => e * (1 + r.getD j 0)) 1 * x.2,
        acc.2.1 * lambda,
        acc.2.2.1.push (x.1.1, .point (r.take (layoutOf layouts x.1.1).vars) x.2
          (if (x.1.1 == .c1) = true then (acc.2.2.2, none) else (none, acc.2.2.2)).1),
        (if (x.1.1 == .c1) = true then (acc.2.2.2, none) else (none, acc.2.2.2)).2))
    (0, 1, #[], bitSlice)

/-- **What the batch computes** from `λ`, its rounds `brs` and the values `tl` (the stacks', then `a`,
`b`): the zeros it collects (the terminal, with the slices) and its result. -/
def batchPure (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (p : Flock.Pending) (flockPoint : List E)
    (lambda : E) (brs : Done) (tl : List E) :
    List E × (List (Commitment × Opening) × Option Flock.MatrixClaim) :=
  let ts := batchTarget combined lambda
  let sc := decodeSC (ts.1 + ts.2 * p.claim) (List.replicate (varsOf layouts) none) brs
  let a := tl.getD combined.length 0
  let b := tl.getD (combined.length + 1) 0
  let fo := batchFold combined layouts bitSlice ringMap lambda sc.1 (tl.take combined.length)
  let extension := (List.range' p.rounds (varsOf layouts - p.rounds)).foldl
    (fun e j => e * (1 + sc.1.getD j 0)) 1
  if p.hasSlices = true then
    ([fo.1 + fo.2.1 * (p.terminal sc.1 a b).1 * extension + sc.2],
      (fo.2.2.1.toList, some (p.terminal sc.1 a b).2))
  else
    ([], ((fo.2.2.1.map fun x => match x.1, x.2 with
        | .c1, .point pt v _ => (x.1, .point pt v (combine [⟨((p.combination sc.1 a b extension fo.2.1).1.zip
            (List.range (p.combination sc.1 a b extension fo.2.1).1.length)).map
              (fun y => ⟨.qflockBits, flockPoint, y.2, y.1⟩), fo.1 + sc.2⟩] .c1 1))
        | _, _ => x).toList,
      some (p.combination sc.1 a b extension fo.2.1).2))

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The batch with Flock's matrices pending**: `λ`, the rounds, the values, the terminal zero,
the result. -/
theorem batch_eq (F : KeccakState → m KeccakState) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (bitSlice : Option Combined)
    (ringMap : Option (List E)) (p : Flock.Pending) (flockPoint : List E) :
    batch F combined layouts bitSlice ringMap (some (p, flockPoint)) = (do
      let lambda ← sample F
      let brs ← readRounds F (List.replicate (varsOf layouts) ⟨false, 2, 0⟩)
      let tl ← nextScalars (m := m) (combined.length + 2)
      ChainProg.requireZeros (batchPure combined layouts bitSlice ringMap p flockPoint lambda brs tl).1
      pure (batchPure combined layouts bitSlice ringMap p flockPoint lambda brs tl).2) := by
  unfold batch
  simp only [sumcheck_eq, sumcheckR_eq, List.length_replicate]
  congr 1
  funext lambda
  rw [bind_map_left]
  congr 1
  funext brs
  rw [nextScalars_add, nextScalars_two, nextScalars_fix combined.length]
  simp only [bind_assoc, pure_bind, bind_map_left]
  congr 1
  funext values
  congr 1
  funext a
  congr 1
  funext b
  have hl : (fixLen combined.length values).length = combined.length := length_fixLen _ _
  cases h : p.hasSlices
  · simp [batchPure, batchFold, batchTarget, layoutOf, varsOf, h, ChainProg.requireZeros, hl]
    rfl
  · simp [batchPure, batchFold, batchTarget, layoutOf, varsOf, h, ChainProg.requireZeros, hl]

end Monad

end UniSound
