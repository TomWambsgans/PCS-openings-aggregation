-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's batch in step: the verifier's
-- `batchFsH … .rec3` (`Rec3VerifierH.lean`, `Rec.lean`'s `batchFs`) reads the prover's (`Rec3Prover.lean`).
import UniComplete.Rec3BatchAlg
import UniComplete.Rec3VerifierH

/-!
# π1-rec3's batching sumcheck in step: `batchFsH … .rec3` reads `batchProver3`

At a pure Keccak-256 `H` (`Id`, `pure ∘ H`), on a channel synchronised with the prover's writer:

* **the narrow challenge** (`syncs_sampleNarrow`): `sampleNarrowH` draws the prover's `sampleNarrowW` (`sampledN`);
* **a pair round** (`syncs_pairRound`): `pairRoundPoly 2 claim` reads the eight scalars `msg8 cs`
  (`reads_pairRoundPoly`: it returns `pairCoeffs claim (msg8 cs)`), the narrow challenge `z` is the prover's, the
  point grows by `pairPoint z`; the prover's state goes from `stOf Z r` to `stOf Z (r ++ pairPoint z)`
  (`ppair_run`);
* **the pair rounds** (`syncs_pairs`, `pairs_run`) and **the last plain round** (`syncs_plain`), so the whole
  `sumcheckPairsDrawnH` reads `batchRounds3` (`syncs_sumcheckPairs`): the verifier returns the prover's point and the
  claim it reaches on the prover's messages (`batch3Run`, from any claim);
* **the batch** (`batchSyncs3`, `BatchSyncs3`): `batchFsH (pure ∘ H) .rec3 combined layouts none ringMap none`
  against `batchProver3` (`λ`, the rounds, the stacks' values): the verifier returns the prover's point claims
  (`pointOpening`), no matrices' claim, and collects one value, `batchTerminal3 w` (that it vanishes on the honest
  batch is `Rec3BatchZero.lean`).

As `BatchProofSync.lean`, the verifier's loops are restated as `forIn` over a list (`sumcheckPairsDrawnH_eq`,
`batchRounds3_eq`, by `rfl` after the range's size is normalised), the loop bodies named (`vpair`, `ppair`), and the
challenges are the prover's, functions of the writer (`pairStep`, `pairsRun`, `batch3Run`).
-/

namespace UniComplete.Rec3

open UniStatement LeanVM.Parameters LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniSound (pairCoeffs)

variable (H : List UInt8 → Digest)

/-! ## The narrow challenge -/

/-- **The prover's narrow challenge** at the writer `w` (`sampleNarrowW` at `pure ∘ H`). -/
def sampledN (w : Wr) : E × Wr :=
  let state := H (digestBytes w.state ++ (w.stream.extract w.absorbed w.stream.size).toList)
  let x := narrowE (PcsQuotient.Transcript.challengeOf state)
  (x, { w with absorbed := w.stream.size, state := state, challenges := w.challenges.push x })

theorem sampleNarrowW_run (w : Wr) : (sampleNarrowW (m := Id) (pure ∘ H)).run w = sampledN H w := rfl

@[simp] theorem sampledN_stream (w : Wr) : (sampledN H w).2.stream = w.stream := rfl

/-- **The narrow challenge in step**: both at the end of the stream, the same input bytes, the same challenge. -/
theorem steps_sampleNarrow (w : Wr) :
    Steps (sampleNarrowH (m := Id) (Pure.pure ∘ H)) (sampleNarrowW (m := Id) (Pure.pure ∘ H)) w.stream.size w
      (sampledN H w).1 (sampledN H w).1 w.stream.size (sampledN H w).2 [] := by
  refine ⟨sampleNarrowW_run H w, List.prefix_refl _, fun D Z hD ↦ ?_⟩
  have hex : D.extract w.absorbed w.stream.size = w.stream.extract w.absorbed w.stream.size := by
    apply Array.toList_inj.mp
    obtain ⟨t, ht⟩ := hD
    simp only [sampledN_stream] at ht
    rw [Array.toList_extract, Array.toList_extract, ← ht, List.extract_eq_take_drop, List.extract_eq_take_drop]
    by_cases hab : w.absorbed ≤ w.stream.toList.length
    · have hl : (List.drop w.absorbed w.stream.toList).length = w.stream.size - w.absorbed := by simp
      rw [List.drop_append_of_le_length hab, List.take_left' hl, List.take_of_length_le (le_of_eq hl)]
    · have h0 : w.stream.size - w.absorbed = 0 := by simp at hab; omega
      rw [h0, List.take_zero, List.take_zero]
  have e : (sampleNarrowH (m := Id) (Pure.pure ∘ H)).run.run (chanAt D w.stream.size w Z) =
      (.ok (narrowE (PcsQuotient.Transcript.challengeOf
          (H (digestBytes w.state ++ (D.extract w.absorbed w.stream.size).toList)))),
        ⟨D, w.stream.size, w.stream.size, H (digestBytes w.state ++ (D.extract w.absorbed w.stream.size).toList),
          w.challenges.push (narrowE (PcsQuotient.Transcript.challengeOf
            (H (digestBytes w.state ++ (D.extract w.absorbed w.stream.size).toList)))), Z⟩) := rfl
  rw [e, hex, show ([] : List E).toArray = #[] from rfl, Array.append_empty]
  rfl

theorem syncs_sampleNarrow (w : Wr) :
    Syncs (sampleNarrowH (m := Id) (Pure.pure ∘ H)) (sampleNarrowW (m := Id) (Pure.pure ∘ H)) w (sampledN H w).1 [] :=
  (steps_sampleNarrow H w).syncs

/-- **The bind lemma, the prover's first step run**: its result and writer named. -/
theorem syncs_bind_of_run {α β γ δ : Type} {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β}
    {g : β → WrM Id δ} {w w' : Wr} {a : α} {b : β} {c : γ} {zs1 zs2 : List E} (h1 : Syncs v p w a zs1)
    (hp : p.run w = (b, w')) (h2 : Syncs (f a) (g b) w' c zs2) : Syncs (v >>= f) (p >>= g) w c (zs1 ++ zs2) := by
  have h2' : Syncs (f a) (g (p.run w).1) (p.run w).2 c zs2 := by rw [hp]; exact h2
  exact Syncs.bind h1 h2'

/-! ## A pair round -/

/-- **`pairRoundPoly 2 claim` reads the eight scalars of `msg8 cs`** and returns `pairCoeffs claim (msg8 cs)`. -/
theorem reads_pairRoundPoly (claim : E) (cs : List E) :
    Reads (pairRoundPoly (m := Id) 2 claim) ((msg8 cs).flatMap scalarWire) (pairCoeffs claim (msg8 cs)) [] := by
  have h1 := nextScalars_reads ((msg8 cs).take 3)
  have h2 := nextScalars_reads ((msg8 cs).drop 3)
  unfold pairRoundPoly
  refine Reads.congr (Reads.bind h1 (Reads.bind_pure h2)) ?_ (pairRoundPoly_fold claim cs) rfl
  rw [← List.flatMap_append, List.take_append_drop]

/-- `sumcheckPairsDrawnH`'s loop body. -/
def vpair (_ : ℕ) (s : Array E × Array E × E) : ChanM Id (ForInStep (Array E × Array E × E)) := do
  let message ← pairRoundPoly (m := Id) 2 s.2.2
  let z ← sampleDrawnH (m := Id) (Pure.pure ∘ H) true
  Pure.pure (ForInStep.yield (s.1 ++ (pairPoint z).toArray, s.2.1.push z, polyEval message z))

/-- `batchRounds3`'s loop body. -/
def ppair (lambda : E) (V : ℕ) (j : ℕ) (st : BatchState) : WrM Id (ForInStep BatchState) := do
  let st ← pairRound3 (m := Id) (Pure.pure ∘ H) lambda (2 ^ (V - 2 * j - 2)) st
  Pure.pure (ForInStep.yield st)

/-- **The prover's pair round `j`** at the state after `r`, from the writer `w`: its nine coefficients, its narrow
challenge (at the writer after the message), the writer after the challenge. -/
def pairStep (lambda : E) (V j : ℕ) (Z : List (Array E × Array E)) (r : List E) (w : Wr) : List E × E × Wr :=
  let cs := pairMsgOf cantorBeta1 lambda (2 ^ (V - 2 * j - 2)) (stOf Z r).weights (stOf Z r).tabs
  let w1 := w.append ((msg8 cs).flatMap scalarWire)
  (cs, (sampledN H w1).1, (sampledN H w1).2)

/-- **A pair round in step**: the verifier reads the eight scalars, draws the prover's narrow challenge. -/
theorem syncs_pairRound (lambda : E) (V j : ℕ) (Z : List (Array E × Array E)) (r : List E) (pa ch : Array E)
    (c : E) (w : Wr) :
    Syncs (vpair H j (pa, ch, c)) (ppair H lambda V j (stOf Z r)) w
      (ForInStep.yield (pa ++ (pairPoint (pairStep H lambda V j Z r w).2.1).toArray,
        ch.push (pairStep H lambda V j Z r w).2.1,
        polyEval (pairCoeffs c (msg8 (pairStep H lambda V j Z r w).1)) (pairStep H lambda V j Z r w).2.1)) [] := by
  set cs := pairMsgOf cantorBeta1 lambda (2 ^ (V - 2 * j - 2)) (stOf Z r).weights (stOf Z r).tabs with hcs
  have hv : vpair H j (pa, ch, c) = (pairRoundPoly (m := Id) 2 c >>= fun msg ↦
      sampleNarrowH (m := Id) (Pure.pure ∘ H) >>= fun z ↦
        Pure.pure (ForInStep.yield (pa ++ (pairPoint z).toArray, ch.push z, polyEval msg z))) := rfl
  have hp : ppair H lambda V j (stOf Z r) = (sendScalars (m := Id) (msg8 cs) >>= fun _ ↦
      sampleNarrowW (m := Id) (Pure.pure ∘ H) >>= fun z ↦
        Pure.pure (ForInStep.yield (foldAt (foldAt (stOf Z r) ((pairPoint z).getD 0 0)) ((pairPoint z).getD 1 0)))) := by
    simp only [ppair, pairRound3, bind_assoc, pure_bind, hcs]
  refine Syncs.congr_p (Syncs.congr_v ?_ hv.symm) hp.symm
  exact Syncs.congr (Syncs.bind (Steps.readWrite (reads_pairRoundPoly c cs) (sendScalars_writes _ w)).syncs
    (Syncs.bind (syncs_sampleNarrow H _) (syncs_pure _ _ _))) rfl (by simp)

/-- The prover's pair round from the writer `w`: the state after `r ++ pairPoint z`, the writer after `z`. -/
theorem ppair_run (lambda : E) (V j : ℕ) (Z : List (Array E × Array E)) (r : List E) (w : Wr) :
    (ppair H lambda V j (stOf Z r)).run w =
      (ForInStep.yield (stOf Z (r ++ pairPoint (pairStep H lambda V j Z r w).2.1)), (pairStep H lambda V j Z r w).2.2) := by
  show (ForInStep.yield (foldAt (foldAt (stOf Z r) _) _), _) = _
  rw [foldAt_stOf, foldAt_stOf, List.append_assoc]
  rfl

/-! ## The pair rounds -/

/-- **Through `n` pair rounds** from round `j`, at the point `r` and the verifier's claim `c`, from the writer `w`:
the challenges, the claim the verifier reaches, the writer after. -/
def pairsRun (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) : ℕ → ℕ → List E → E → Wr → List E × E × Wr
  | 0, _, _, c, w => ([], c, w)
  | n + 1, j, r, c, w =>
    let s := pairStep H lambda V j Z r w
    let rest := pairsRun lambda V Z n (j + 1) (r ++ pairPoint s.2.1) (polyEval (pairCoeffs c (msg8 s.1)) s.2.1)
      s.2.2
    (s.2.1 :: rest.1, rest.2.1, rest.2.2)

/-- The points of a list of pair challenges. -/
def zsPoint (zs : List E) : List E := zs.flatMap pairPoint

theorem zsPoint_cons (z : E) (zs : List E) : zsPoint (z :: zs) = pairPoint z ++ zsPoint zs := by
  simp [zsPoint]

theorem length_zsPoint (zs : List E) : (zsPoint zs).length = 2 * zs.length := by
  induction zs with
  | nil => rfl
  | cons z zs ih => rw [zsPoint_cons, List.length_append, ih, List.length_cons]; simp [pairPoint]; ring

theorem length_pairsRun (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) :
    ∀ (n j : ℕ) (r : List E) (c : E) (w : Wr), (pairsRun H lambda V Z n j r c w).1.length = n
  | 0, _, _, _, _ => rfl
  | n + 1, j, r, c, w => by simp [pairsRun, length_pairsRun lambda V Z n]

/-- **The pair rounds in step.** -/
theorem syncs_pairs (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) : ∀ (n j : ℕ) (r : List E)
    (pa ch : Array E) (c : E) (w : Wr),
    Syncs (forIn (List.range' j n) (pa, ch, c) (vpair H)) (forIn (List.range' j n) (stOf Z r) (ppair H lambda V)) w
      (pa ++ (zsPoint (pairsRun H lambda V Z n j r c w).1).toArray, ch ++ (pairsRun H lambda V Z n j r c w).1.toArray,
        (pairsRun H lambda V Z n j r c w).2.1) []
  | 0, j, r, pa, ch, c, w => by
    simp only [List.range'_zero, List.forIn_nil, pairsRun]
    exact Syncs.congr (syncs_pure _ _ _) (by simp [zsPoint]) rfl
  | n + 1, j, r, pa, ch, c, w => by
    rw [List.range'_succ, List.forIn_cons, List.forIn_cons]
    have h1 := syncs_pairRound H lambda V j Z r pa ch c w
    have h2 := syncs_pairs lambda V Z n (j + 1) (r ++ pairPoint (pairStep H lambda V j Z r w).2.1)
      (pa ++ (pairPoint (pairStep H lambda V j Z r w).2.1).toArray) (ch.push (pairStep H lambda V j Z r w).2.1)
      (polyEval (pairCoeffs c (msg8 (pairStep H lambda V j Z r w).1)) (pairStep H lambda V j Z r w).2.1)
      (pairStep H lambda V j Z r w).2.2
    refine Syncs.congr (syncs_bind_of_run h1 (ppair_run H lambda V j Z r w) h2) ?_ (by simp)
    simp [pairsRun, zsPoint_cons, Array.append_assoc]

/-- The prover's pair rounds: the state after the challenges' points, the writer after. -/
theorem pairs_run (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) : ∀ (n j : ℕ) (r : List E) (c : E) (w : Wr),
    (forIn (List.range' j n) (stOf Z r) (ppair H lambda V)).run w =
      (stOf Z (r ++ zsPoint (pairsRun H lambda V Z n j r c w).1), (pairsRun H lambda V Z n j r c w).2.2)
  | 0, _, r, _, w => by
    simp only [List.range'_zero, List.forIn_nil, pairsRun, zsPoint, List.flatMap_nil, List.append_nil]
    rfl
  | n + 1, j, r, c, w => by
    rw [List.range'_succ, List.forIn_cons, wr_run_bind, ppair_run]
    dsimp only
    rw [pairs_run lambda V Z n (j + 1) _
      (polyEval (pairCoeffs c (msg8 (pairStep H lambda V j Z r w).1)) (pairStep H lambda V j Z r w).2.1)]
    simp [pairsRun, zsPoint_cons, List.append_assoc]

/-! ## The last plain round -/

/-- The prover's plain round at the state after `r`, from the writer `w`: its message, its challenge, the writer after. -/
def plainStep (lambda : E) (Z : List (Array E × Array E)) (r : List E) (w : Wr) : (E × E) × E × Wr :=
  let msg := plainMsgOf lambda 1 (stOf Z r).weights (stOf Z r).tabs
  let w1 := (w.append (scalarWire msg.1)).append (scalarWire msg.2)
  (msg, (sampledN H w1).1, (sampledN H w1).2)

/-- **The last plain round in step.** -/
theorem syncs_plain (lambda : E) (Z : List (Array E × Array E)) (r : List E) (c : E) (w : Wr) :
    Syncs (sumcheckDrawnH (m := Id) (Pure.pure ∘ H) c 3 [none] true) (plainRound3 (m := Id) (Pure.pure ∘ H) lambda 1 (stOf Z r)) w
      ([(plainStep H lambda Z r w).2.1],
        polyEval ([(plainStep H lambda Z r w).1.1, c + esum [(plainStep H lambda Z r w).1.2]] ++
          [(plainStep H lambda Z r w).1.2]) (plainStep H lambda Z r w).2.1) [] := by
  set q0 := (plainMsgOf lambda 1 (stOf Z r).weights (stOf Z r).tabs).1
  set q2 := (plainMsgOf lambda 1 (stOf Z r).weights (stOf Z r).tabs).2
  have hp : plainRound3 (m := Id) (Pure.pure ∘ H) lambda 1 (stOf Z r) = (sendScalar (m := Id) q0 >>= fun _ ↦
      sendScalar (m := Id) q2 >>= fun _ ↦ sampleNarrowW (m := Id) (Pure.pure ∘ H) >>= fun x ↦
        (Pure.pure (foldAt (stOf Z r) x) : WrM Id BatchState)) := rfl
  rw [hp]
  unfold sumcheckDrawnH
  simp only [List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind, roundPoly, sampleDrawnH]
  have h2 : Syncs (nextScalars (m := Id) 1) (sendScalar (m := Id) q2) (w.append (scalarWire q0)) [q2] [] :=
    Syncs.congr_p (syncs_scalars [q2] _) (by simp [sendScalars, sendScalar])
  exact Syncs.congr (Syncs.bind (syncs_scalar q0 w) (Syncs.bind h2 (Syncs.bind (syncs_sampleNarrow H _)
    (syncs_pure _ _ _)))) rfl (by simp)

theorem plainRound3_run (lambda : E) (Z : List (Array E × Array E)) (r : List E) (w : Wr) :
    (plainRound3 (m := Id) (Pure.pure ∘ H) lambda 1 (stOf Z r)).run w =
      (stOf Z (r ++ [(plainStep H lambda Z r w).2.1]), (plainStep H lambda Z r w).2.2) := by
  show (foldAt (stOf Z r) _, _) = _
  rw [foldAt_stOf]
  rfl

/-! ## The whole paired sumcheck -/

theorem sumcheckPairsDrawnH_eq (target : E) (V : ℕ) :
    sumcheckPairsDrawnH (m := Id) (Pure.pure ∘ H) target 2 V true =
      (forIn (List.range' 0 (V / 2)) ((#[] : Array E), (#[] : Array E), target) (vpair H) >>= fun s ↦
        if V % 2 = 1 then
          (sumcheckDrawnH (m := Id) (Pure.pure ∘ H) s.2.2 3 [none] true >>= fun le ↦
            match le with
            | (last, end_) => Pure.pure ((s.1 ++ last.toArray).toList, (s.2.1 ++ last.toArray).toList, end_))
        else Pure.pure (s.1.toList, s.2.1.toList, s.2.2)) := by
  unfold sumcheckPairsDrawnH
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  rfl

theorem batchRounds3_eq (lambda : E) (V : ℕ) (st : BatchState) :
    batchRounds3 (m := Id) (Pure.pure ∘ H) lambda V st =
      (forIn (List.range' 0 (V / 2)) st (ppair H lambda V) >>= fun st ↦
        if V % 2 = 1 then (plainRound3 (m := Id) (Pure.pure ∘ H) lambda 1 st >>= fun st ↦ Pure.pure st.point)
        else Pure.pure st.point) := by
  unfold batchRounds3
  rw [List.range_eq_range']
  rfl

/-- **π1-rec3's batch rounds, run** from the claim `c` at the writer `w`: the point, the claim the verifier reaches,
the writer after (the pairs, then with `V` odd the plain round). -/
def batch3Run (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) (c : E) (w : Wr) : List E × E × Wr :=
  let p := pairsRun H lambda V Z (V / 2) 0 [] c w
  if V % 2 = 1 then
    let s := plainStep H lambda Z (zsPoint p.1) p.2.2
    (zsPoint p.1 ++ [s.2.1], polyEval ([s.1.1, p.2.1 + esum [s.1.2]] ++ [s.1.2]) s.2.1, s.2.2)
  else (zsPoint p.1, p.2.1, p.2.2)

/-- **`sumcheckPairsDrawnH` reads `batchRounds3`**: the prover's point, and the claim the verifier reaches. -/
theorem syncs_sumcheckPairs (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) (c : E) (w : Wr) :
    Syncs (sumcheckPairsDrawnH (m := Id) (Pure.pure ∘ H) c 2 V true)
      (batchRounds3 (m := Id) (Pure.pure ∘ H) lambda V (stOf Z [])) w
      ((batch3Run H lambda V Z c w).1,
        (pairsRun H lambda V Z (V / 2) 0 [] c w).1 ++
          (if V % 2 = 1 then [(plainStep H lambda Z (zsPoint (pairsRun H lambda V Z (V / 2) 0 [] c w).1)
            (pairsRun H lambda V Z (V / 2) 0 [] c w).2.2).2.1] else []),
        (batch3Run H lambda V Z c w).2.1) [] := by
  rw [sumcheckPairsDrawnH_eq, batchRounds3_eq]
  have h1 := syncs_pairs H lambda V Z (V / 2) 0 [] #[] #[] c w
  have hrun := pairs_run H lambda V Z (V / 2) 0 [] c w
  rw [List.nil_append] at hrun
  by_cases hV : V % 2 = 1
  · simp only [hV, ↓reduceIte]
    refine Syncs.congr (syncs_bind_of_run h1 hrun (Syncs.bind (syncs_plain H lambda Z _ _ _) (syncs_pure _ _ _)))
      ?_ (by simp)
    simp [batch3Run, hV]
  · simp only [hV, ↓reduceIte]
    refine Syncs.congr (syncs_bind_of_run h1 hrun (syncs_pure _ _ _)) ?_ (by simp)
    simp [batch3Run, hV]

/-- The prover's rounds: the point and the writer after. -/
theorem batchRounds3_run (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) (c : E) (w : Wr) :
    (batchRounds3 (m := Id) (Pure.pure ∘ H) lambda V (stOf Z [])).run w =
      ((batch3Run H lambda V Z c w).1, (batch3Run H lambda V Z c w).2.2) := by
  rw [batchRounds3_eq, wr_run_bind, pairs_run H lambda V Z (V / 2) 0 [] c w]
  simp only [List.nil_append]
  by_cases hV : V % 2 = 1
  · simp only [hV, ↓reduceIte, wr_run_bind, plainRound3_run]
    simp only [batch3Run, hV, ↓reduceIte, stOf]
    rfl
  · simp only [hV, ↓reduceIte]
    simp only [batch3Run, hV, ↓reduceIte, stOf]
    rfl

/-! ## The batch -/

section BatchProver

variable {m : Type → Type} [Monad m] (H' : List UInt8 → m Digest)

/-- **π1-rec3's batching sumcheck's prover** (`proveStreamRec3With`'s step 9, as a function): `λ`, the paired rounds on
the combined claims' dense weights and the stacks, each stack's value at its part of the point; the point claims. -/
def batchProver3 (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) : WrM m (List (Commitment × List E × E)) := do
  let lambda ← sampleW H'
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), none, 0, []⟩
  let r ← batchRounds3 H' lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  return claims

end BatchProver

/-- The batch's tables: each combined claim's dense weight and its stack. -/
def batchZ (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) : List (Array E × Array E) :=
  combined.map fun x ↦ (denseWeight x.2 (layoutIn stackLayouts x.1) ringMap, (stackOf x.1).map ofK)

theorem batchInit_stOf (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) :
    (⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) ringMap),
      combined.map (fun (c, _) ↦ (stackOf c).map ofK), none, 0, []⟩ : BatchState) =
      stOf (batchZ combined stackLayouts stackOf ringMap) [] := by
  simp [stOf, batchZ, List.map_map, Function.comp_def]

/-- **What the verifier collects** at the writer `w`: `sum + last`, `last` the claim it reaches on the prover's
messages from the target, `sum` its weighted values at the point. -/
def batchTerminal3 (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (w : Wr) : E :=
  let lam := (Wr.sampled H w).1
  let R := batch3Run H lam (batchVars stackLayouts) (batchZ combined stackLayouts stackOf ringMap)
    (targetFold lam combined).1 (Wr.sampled H w).2
  (sumFold combined stackLayouts ringMap lam (batchVars stackLayouts) R.1
    ((claimsOf combined stackLayouts stackOf R.1).map (·.2.2))).1 + R.2.1

/-- **The batching sumcheck's prover synchronises with `batchFsH … .rec3`** (no bit-slice claim, no matrices): from
any writer, the verifier returns the prover's point claims (`pointOpening`) and no matrices' claim, and collects one
value, `terminal w`. -/
def BatchSyncs3 (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (terminal : Wr → E) : Prop :=
  ∀ w : Wr, Syncs (batchFsH (m := Id) (Pure.pure ∘ H) .rec3 combined stackLayouts none ringMap none)
    (batchProver3 (m := Id) (Pure.pure ∘ H) combined stackLayouts stackOf ringMap) w
    (((batchProver3 (m := Id) (Pure.pure ∘ H) combined stackLayouts stackOf ringMap).run w).1.map pointOpening, none)
    [terminal w]

/-- The prover's point claims at its point. -/
theorem batchProver3_run (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (w : Wr) :
    ((batchProver3 (m := Id) (Pure.pure ∘ H) combined stackLayouts stackOf ringMap).run w).1 =
      claimsOf combined stackLayouts stackOf (batch3Run H (Wr.sampled H w).1 (batchVars stackLayouts)
        (batchZ combined stackLayouts stackOf ringMap) (targetFold (Wr.sampled H w).1 combined).1
        (Wr.sampled H w).2).1 := by
  unfold batchProver3
  rw [wr_run_bind, sampleW_run]
  dsimp only
  rw [batchInit_stOf, wr_run_bind, batchRounds3_run H _ _ _ (targetFold (Wr.sampled H w).1 combined).1]
  rfl

/-- **`batchFsH … .rec3` reads the honest paired batch** (`BatchSyncs3` at `batchTerminal3`). -/
theorem batchSyncs3 (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) :
    BatchSyncs3 H combined stackLayouts stackOf ringMap (batchTerminal3 H combined stackLayouts stackOf ringMap) := by
  intro w
  rw [batchProver3_run]
  unfold batchFsH batchProver3
  refine Syncs.bind (syncs_sample H w) ?_
  rw [sampleW_run]
  generalize hlam : (Wr.sampled H w).1 = lam
  generalize hw1 : (Wr.sampled H w).2 = w1
  dsimp only
  rw [batchInit_stOf]
  refine Syncs.bind (syncs_sumcheckPairs H lam _ (batchZ combined stackLayouts stackOf ringMap)
    (List.foldl (fun (acc : E × E) (x : Commitment × Combined) ↦ (acc.1 + acc.2 * x.2.value, acc.2 * lam)) (0, 1)
      combined).1 w1) ?_
  rw [batchRounds3_run H _ _ _ (List.foldl (fun (acc : E × E) (x : Commitment × Combined) ↦
    (acc.1 + acc.2 * x.2.value, acc.2 * lam)) (0, 1) combined).1]
  generalize hR : batch3Run H lam (List.foldl max 0 (List.map (fun x ↦ x.2.vars) stackLayouts))
    (batchZ combined stackLayouts stackOf ringMap) (List.foldl (fun (acc : E × E) (x : Commitment × Combined) ↦
      (acc.1 + acc.2 * x.2.value, acc.2 * lam)) (0, 1) combined).1 w1 = R
  simp only [pure_bind]
  refine Syncs.bind (Syncs.congr_v (syncs_scalars _ _) (by simp)) ?_
  refine Syncs.congr (syncs_requireZero_last _ _ _ _) ?_ ?_
  · refine Prod.ext ?_ rfl
    rw [← hR]
    exact sumFold_openings combined stackLayouts stackOf ringMap lam (batchVars stackLayouts) _
  · unfold batchTerminal3
    rw [hlam, hw1]
    dsimp only
    rw [← hR]
    rfl

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.batchSyncs3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.batchSyncs3
