-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`; VCVio's `support` of an
-- `OracleComp`; and `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean`'s cost of the prover's opening
-- (`cost_proveOpeningWithH`, `blockFactor`) and of a commitment (`qc_commitWithH`, `treeCost`).
import UniComplete.Rec3FlockCost

/-!
# The block count of π1-rec3's honest prover, and the size of its stream

The port of `ProverCost.lean` to π1-rec3's prover (`Rec3Prover.lean`), in its writer calculus (`Cost.WC`):

* **The paired batch** (`wc_batchRounds3`): a pair round sends eight scalars and draws one narrow challenge, its point
  growing by two (`wc_pairRound3`); the last plain round two scalars and one challenge (`wc_plainRound3`); over `vars`
  variables at most `vars` challenges and `96 · vars` bytes (`192` a pair, `48` the plain round), the point growing
  by `vars`.
* **The stream** (`wc_proveStreamRec3With`): `streamBlocks3` (`C1`'s and `C2`'s trees, the challenges: **one** for
  `α = squares c 4`, `β`, `γ`, `t`, `ρ`, `λ`, at most `batchVarsBound` in the batch, Flock's) beyond `streamBytes3`
  bytes (the row counts, the roots, Flock's, at most `valuesBound` values at `t`, `96` a batch variable, the claims'
  three values; **no matrices' two**); its point claims have at most `batchVarsBound` coordinates (`StreamOK3`).
* **The prover** (`costP_proveRec3With`, `uniProverCost3`): the setup's three trees, π1-rec3's IV (`289` bytes and the
  program IV: the main line's `280` and `variantBytes`' `9`, `variantBytes_rec3_length`), the seed, the stream,
  **three** openings (`Cost.openP`).
* **At the reference shape** (`proverBlocks3_reference`): at most **`2^47`** block calls, for Flock's prover within
  `2^32` blocks and `2^32` bytes and a program IV of at most `2^16` bytes (nearly all the three WHIR provers',
  `3 · 40481 · (14 · 2^26 + 2) ≈ 2^46.70`); the stream at most `5776` bytes beyond Flock's
  (`proverStream3_reference`).
* **The named hypotheses** (`Rec3Hyp.lean`) for π1-rec3's honest Flock prover (`flockProve3H`, `Rec3FlockCost.lean`:
  `46` blocks, `3552` bytes) at every deployment of the reference shape with a program IV of at most `2^16` bytes:
  **`proverCost3_flockProve3H : ProverCost3 flockProve3H D (2 ^ 47)`** and
  **`proverStreamSize3_flockProve3H : ProverStreamSize3 flockProve3H D (2 ^ 40)`** (at most `5776 + 3552` bytes).

Decisions (recorded): the stream's lemma takes Flock's prover's cost with no postcondition (π1-rec3's stream does not
use the pending claim), and the deployed prover's takes the main line's `Cost.FlockCost`, weakened; the main line's
calculus, `qc_setupTreesOf`, `openP`, `qc_proveOpening1`, `reference_vars`, `valuesBound_eq` are reused as they are.
Unlike the main line (`3 · 2^46`, its five openings' bound about `2^47.43`), the bound `2^47` that π1-rec3's
probability layer asks for is met.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

set_option autoImplicit false

namespace UniComplete.Rec3

open UniComplete.Cost
open E2ECompleteness.Cost (QC qc_pure qc_H_le treeCost)
open Bounds (batchVarsBound valuesBound)

/-! ## The paired batch -/

/-- **A pair round**: eight scalars, one narrow challenge; the point grows by two. -/
theorem wc_pairRound3 (lambda : E) (nq : ℕ) (st : BatchState) :
    WC (pairRound3 callKeccak256 lambda nq st) 1 (24 * 8) fun st' _ ↦ st'.point.length = st.point.length + 2 := by
  unfold pairRound3
  refine wc_seq (wc_sendScalars _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (le_of_eq (by rw [length_msg8]))
  refine wc_seq wc_sampleNarrowW (fun z _ _ ↦ ?_) le_rfl (Nat.zero_le _)
  refine wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
  subst hb
  simp only [foldAt, List.length_append, List.length_singleton]

/-- **The last plain round**: two scalars, one narrow challenge; the point grows by one. -/
theorem wc_plainRound3 (lambda : E) (nh : ℕ) (st : BatchState) :
    WC (plainRound3 callKeccak256 lambda nh st) 1 48 fun st' _ ↦ st'.point.length = st.point.length + 1 := by
  unfold plainRound3
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq wc_sampleNarrowW (fun r _ _ ↦ ?_) le_rfl (Nat.zero_le _)
  refine wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
  subst hb
  simp only [foldAt, List.length_append, List.length_singleton]

/-- **π1-rec3's batching sumcheck's rounds**: at most `vars` challenges and `96 · vars` bytes; the point grows by
`vars`. -/
theorem wc_batchRounds3 (lambda : E) (vars : ℕ) (st : BatchState) :
    WC (batchRounds3 callKeccak256 lambda vars st) vars (96 * vars)
      fun r _ ↦ r.length = st.point.length + vars := by
  unfold batchRounds3
  have h := wc_forIn_yield (List.range (vars / 2))
    (fun j s ↦ pairRound3 callKeccak256 lambda (2 ^ (vars - 2 * j - 2)) s)
    (fun i s ↦ s.point.length = st.point.length + 2 * i)
    (fun i a s hs ↦ wc_mono (wc_pairRound3 lambda _ s) le_rfl le_rfl fun s' _ h ↦ by omega) st 0 (by simp)
  rw [List.length_range] at h
  refine wc_seq h (fun s _ hs ↦ ?_) (by omega) (by omega)
  dsimp only
  split
  · refine wc_seq (wc_plainRound3 _ _ _) (fun s' _ hs' ↦ ?_) (by omega) (by omega)
    exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by subst hb; omega
  · exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by subst hb; omega

/-! ## The stream -/

/-- **What the openings need of π1-rec3's stream**: its bytes are the writer's; its point claims have at most `V`
coordinates. -/
def StreamOK3 (V : ℕ) (out : CoreOut) (s : Wr) : Prop :=
  out.stream = s.stream ∧ ∀ x ∈ out.claims, x.2.1.length ≤ V

/-- **π1-rec3's stream's blocks beyond its bytes**: `C1`'s and `C2`'s trees, the challenges (one for `α`, `β`, `γ`,
`t`, `ρ`, `λ`, at most one per batch variable), Flock's. -/
def streamBlocks3 (shape : Shape) (kF : ℕ) : ℕ :=
  treeCost (c1Layout shape).vars + 3 + kF + treeCost (((layoutsOf shape).lookup .c2).getD default).vars + 3 +
    batchVarsBound shape

/-- **π1-rec3's stream's bytes**: the row counts, the two roots, Flock's, the values at `t`, `96` a batch variable,
the three claims' values. -/
def streamBytes3 (shape : Shape) (rows wF : ℕ) : ℕ :=
  4 * rows + 64 + wF + 24 * valuesBound + 96 * batchVarsBound shape + 72

/-- **π1-rec3's stream's cost**, given Flock's prover's at its `log_n`. -/
theorem wc_proveStreamRec3With (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ) (tr : Trace)
    (hF : WC (flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock) kF wF
      fun _ _ ↦ True) :
    WC (proveStreamRec3With callKeccak256 (commitReal callKeccak256) flock tr)
      (streamBlocks3 tr.shape kF) (streamBytes3 tr.shape tr.rows.length wF) (StreamOK3 (batchVarsBound tr.shape)) := by
  unfold proveStreamRec3With streamBlocks3 streamBytes3
  refine wc_seq (wc_forIn_list (k := 0) (w := 4) _ _ _ fun _ _ ↦ wc_seq (wc_sendInteger _ 4)
    (fun _ _ _ ↦ wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial) le_rfl le_rfl)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun committed1 _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_drawRunW 4) (fun alphas _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun beta _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun gamma _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_map some hF) (fun flockOut _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun committed2 _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun t _ _ ↦ ?_) (by omega) (by omega)
  have ha := Bounds.atT_facts tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  have hvars := Bounds.batchVars_atT tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (Nat.mul_le_mul_left 24 ha.values) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun rho _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun lambda _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_mono (wc_batchRounds3 _ _ _) hvars (Nat.mul_le_mul_left 96 hvars) fun r _ h ↦ h)
    (fun r _ hr ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (length_claims _ _ _) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  simp only [List.length_nil, Nat.zero_add] at hr
  refine wc_mono (wc_get_pure _ _ fun s ↦ ⟨rfl, ?_⟩) (Nat.zero_le _) (Nat.zero_le _) fun _ _ h ↦ h
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨⟨c, cl⟩, _, rfl⟩ := hx
  dsimp only
  rw [List.length_take]
  omega

/-! ## The prover -/

section Prover

/-- `variant_bytes` at π1-rec3's deployment: `fs-rec3`, the skip, the slices' code. -/
theorem variantBytes_rec3_length : (variantBytes (.flock flockMain) .rec3 true).length = 9 := by decide +kernel

/-- The proof's stream, if a proof is returned (π1-rec3: three openings, `A0`, `B0` empty). -/
theorem stream_of_some3 {s : Array UInt8} {p1 p2 p3 : Option LeanVM.Protocol.Compile.Proof} {p : UniProof}
    (h : (do
      let c1 ← p1
      let c2 ← p2
      let c3 ← p3
      pure ⟨s, c1, c2, c3, noProof, noProof⟩ : Option UniProof) = some p) : p.stream = s := by
  revert h
  cases p1 <;> cases p2 <;> cases p3 <;> simp
  rintro rfl
  rfl

/-- **π1-rec3's honest prover's blocks**: the setup's three trees, π1-rec3's IV, the seed, the stream (its blocks and
its bytes), three openings of claims of at most `batchVarsBound` coordinates. -/
def uniProverCost3 (shape : Shape) (programIvLen rows kF wF : ℕ) : ℕ :=
  treeCost (setupLayout shape).vars + 2 * treeCost matrixVars + ((289 + programIvLen) / 136 + 1) + 1 +
    (streamBlocks3 shape kF + streamBytes3 shape rows wF) + 3 * openP PcsQuotient.nonceFuel (batchVarsBound shape)

set_option hygiene false in
/-- One step of the three openings' walk (`hc`, `h1` … `h3` the local facts on the claims, `hS` on the stream). -/
macro "open3_step" : tactic => `(tactic| first
  | exact fun p hp ↦ by rw [stream_of_some3 hp]; exact hS
  | refine costP_seq_qc (qc_proveOpening1 _ _ _ _ _ _ (v := batchVarsBound tr.shape) (by first
      | exact hc _ _ _ (List.mem_of_find?_eq_some h1)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h2)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h3))) (fun _ ↦ ?_) (by omega))

/-- **π1-rec3's honest prover's block count**, given Flock's prover's at its `log_n`: and every proof it returns has a
stream of at most `streamBytes3` bytes. -/
theorem costP_proveRec3With (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ) (programIv : List UInt8)
    (tr : Trace) (hpub : tr.publicInput.length = 32)
    (hF : WC (flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock) kF wF
      fun _ _ ↦ True) :
    CostP (proveRec3With callKeccak256 callKeccakF1600 PcsQuotient.nonceFuel flock programIv tr)
      (uniProverCost3 tr.shape programIv.length tr.rows.length kF wF)
      fun o _ ↦ ∀ p, o = some p → p.stream.size ≤ streamBytes3 tr.shape tr.rows.length wF := by
  unfold proveRec3With contractIvRec3Of seedOf
  simp only [bind_assoc, pure_bind]
  refine costP_seq_qc (qc_setupTreesOf tr) (fun trees ↦ ?_) (by unfold uniProverCost3; omega)
  refine costP_seq_qc (qc_H_le (k := (289 + programIv.length) / 136 + 1)
    (by rw [List.length_append, ivInput_length', variantBytes_rec3_length]; omega))
    (fun d ↦ ?_) (by unfold uniProverCost3; omega)
  refine costP_seq_qc (qc_H_le (k := 1) (by
    simp only [List.length_append, name_length, len_digestBytes, hpub]; omega)) (fun seed ↦ ?_)
    (by unfold uniProverCost3; omega)
  have hW := wc_proveStreamRec3With flock kF wF tr hF (Wr.start seed) (by simp [WInv, Wr.start])
    (uniProverCost3 tr.shape programIv.length tr.rows.length kF wF -
      (treeCost (setupLayout tr.shape).vars + 2 * treeCost matrixVars) - ((289 + programIv.length) / 136 + 1) - 1 -
      (streamBlocks3 tr.shape kF + streamBytes3 tr.shape tr.rows.length wF))
  rw [show streamBlocks3 tr.shape kF + streamBytes3 tr.shape tr.rows.length wF + wpot (Wr.start seed) +
      (uniProverCost3 tr.shape programIv.length tr.rows.length kF wF -
        (treeCost (setupLayout tr.shape).vars + 2 * treeCost matrixVars) - ((289 + programIv.length) / 136 + 1) - 1 -
        (streamBlocks3 tr.shape kF + streamBytes3 tr.shape tr.rows.length wF)) =
      uniProverCost3 tr.shape programIv.length tr.rows.length kF wF -
        (treeCost (setupLayout tr.shape).vars + 2 * treeCost matrixVars) - ((289 + programIv.length) / 136 + 1) - 1
      by simp only [wpot, Wr.start, Array.size_empty]; unfold uniProverCost3; omega] at hW
  refine CostP.bind hW fun z rem hz ↦ ?_
  obtain ⟨⟨hstream, hc0⟩, -, -, hsize, hrem⟩ := hz
  have hS : z.1.stream.size ≤ streamBytes3 tr.shape tr.rows.length wF := by
    rw [hstream]
    simpa [Wr.start] using hsize
  have hc : ∀ c pt v, (c, pt, v) ∈ z.1.claims → pt.length ≤ batchVarsBound tr.shape :=
    fun c pt v h ↦ hc0 _ h
  refine CostP.mono_budget (n := 3 * openP PcsQuotient.nonceFuel (batchVarsBound tr.shape)) ?_
    (by unfold uniProverCost3 at hrem; omega)
  obtain ⟨out, _⟩ := z
  dsimp only at hS hc ⊢
  generalize h1 : List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize h2 : List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize h3 : List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    repeat open3_step

end Prover

/-! ## The deployed honest prover -/

section Deployed

/-- **π1-rec3's deployed honest prover's block count**, at `rows` row counts, Flock's prover's costs `k`, `w`. -/
def proverBlocks3 (D : Deployment) (rows : ℕ) (k w : ℕ → Flock.Variant → ℕ) : ℕ :=
  uniProverCost3 D.shape D.programIv.length rows (k (flockLogN D.shape) flockMain) (w (flockLogN D.shape) flockMain)

/-- **π1-rec3's honest stream's bytes**, at most. -/
def proverStream3 (D : Deployment) (rows : ℕ) (w : ℕ → Flock.Variant → ℕ) : ℕ :=
  streamBytes3 D.shape rows (w (flockLogN D.shape) flockMain)

/-- **π1-rec3's deployed honest prover over the two calls makes at most `proverBlocks3` block calls, and every proof
it returns has a stream of at most `proverStream3` bytes**, given Flock's prover's cost. -/
theorem costP_uniProverRec3With (flock : FlockProverH) (k w p : ℕ → Flock.Variant → ℕ)
    (hF : FlockCost flock k w p) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    CostP (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      (proverBlocks3 D rows.length k w)
      fun o _ ↦ ∀ proof, o = some proof → proof.stream.size ≤ proverStream3 D rows.length w :=
  costP_proveRec3With (flock callKeccak256) _ _ D.programIv (honestTrace D input rows q)
    (by simp [honestTrace]) (wc_mono (hF _ _ _) le_rfl le_rfl fun _ _ _ ↦ trivial)

/-- **π1-rec3's deployed honest prover over the two calls makes at most `proverBlocks3` block calls.** -/
theorem cost_uniProverRec3With (flock : FlockProverH) (k w p : ℕ → Flock.Variant → ℕ)
    (hF : FlockCost flock k w p) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    Common.QueryCostAtMost (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      hashBlocks (proverBlocks3 D rows.length k w) :=
  (costP_uniProverRec3With flock k w p hF D input rows q).toQC

end Deployed

/-! ## At the reference shape -/

section Reference

open LeanVM.Protocol.Verifier (whirBound costHeight)
open E2ECompleteness.Cost (blockFactor)

/-- **π1-rec3's prover's blocks from bounds on the stacks' variables.** -/
theorem uniProverCost3_le (shape : Shape) (L rows kF wF : ℕ) {a b c d : ℕ} (ha : (setupLayout shape).vars ≤ a)
    (hb : (c1Layout shape).vars ≤ b) (hc : (((layoutsOf shape).lookup .c2).getD default).vars ≤ c)
    (hd : batchVarsBound shape ≤ d) :
    uniProverCost3 shape L rows kF wF ≤ treeCost a + 2 * treeCost matrixVars + ((289 + L) / 136 + 1) + 1 +
      (treeCost b + 3 + kF + treeCost c + 3 + d + (4 * rows + 64 + wF + 24 * valuesBound + 96 * d + 72)) +
      3 * openP PcsQuotient.nonceFuel d := by
  unfold uniProverCost3 streamBlocks3 streamBytes3
  have := treeCost_mono ha
  have := treeCost_mono hb
  have := treeCost_mono hc
  have := openP_mono PcsQuotient.nonceFuel hd
  omega

/-- **π1-rec3's honest prover's blocks at the reference shape: at most `2^47`**, for six row counts, a program IV of
at most `2^16` bytes, Flock's prover at `log_n = 32` of at most `2^32` blocks beyond its bytes and `2^32` bytes.
(Nearly all of it the three WHIR provers': `3 · 40481 · (14 · 2^26 + 2) ≈ 2^46.70`.) -/
theorem proverBlocks3_reference (D : Deployment) (hD : D.shape = reference) (hIv : D.programIv.length ≤ 2 ^ 16)
    (k w : ℕ → Flock.Variant → ℕ) (hk : k 32 flockMain ≤ 2 ^ 32) (hw : w 32 flockMain ≤ 2 ^ 32) :
    proverBlocks3 D 6 k w ≤ 2 ^ 47 := by
  obtain ⟨h1, h2, h3, h4⟩ := reference_vars
  unfold proverBlocks3
  rw [hD, reference_flockLogN]
  refine (uniProverCost3_le reference _ 6 _ _ h3 h1 h2 h4).trans ?_
  rw [valuesBound_eq]
  unfold openP
  norm_num [treeCost, blockFactor, whirBound, costHeight, PcsQuotient.nonceFuel, matrixVars, blake2sR1csLogSize]
  omega

/-- **π1-rec3's honest stream at the reference shape has at most `5776` bytes beyond Flock's**: the six row counts
(`24`), the two roots (`64`), the values at `t` (`122` scalars), at most `28` batch variables (`96` bytes each), the
claims' three values. -/
theorem proverStream3_reference (D : Deployment) (hD : D.shape = reference) (w : ℕ → Flock.Variant → ℕ) :
    proverStream3 D 6 w ≤ 5776 + w 32 flockMain := by
  obtain ⟨-, -, -, h4⟩ := reference_vars
  unfold proverStream3 streamBytes3
  rw [hD, reference_flockLogN, valuesBound_eq]
  omega

end Reference

/-! ## The named hypotheses for π1-rec3's honest Flock prover -/

/-- **π1-rec3's honest prover with its honest Flock prover makes at most `2^47` block calls** at the reference shape
(a program IV of at most `2^16` bytes). -/
theorem proverCost3_flockProve3H (D : Deployment) (hD : D.shape = reference) (hIv : D.programIv.length ≤ 2 ^ 16) :
    ProverCost3 flockProve3H D (2 ^ 47) := by
  intro input rows q hfit _
  have h := cost_uniProverRec3With flockProve3H flockBlocks3 flockBytes flockCoords flockCost_flockProve3H D input
    rows q
  rw [hfit.1] at h
  obtain ⟨hk, hw, -⟩ := flockCost3_reference
  exact h.mono (proverBlocks3_reference D hD hIv flockBlocks3 flockBytes hk hw)

/-- **Every proof π1-rec3's honest prover can output has a stream of at most `2^40` bytes** at the reference shape
(at most `5776 + 3552`). -/
theorem proverStreamSize3_flockProve3H (D : Deployment) (hD : D.shape = reference) :
    ProverStreamSize3 flockProve3H D (2 ^ 40) := by
  intro input rows q hfit _ π hπ
  have h := Prob.CostP.mem_support (costP_uniProverRec3With flockProve3H flockBlocks3 flockBytes flockCoords
    flockCost_flockProve3H D input rows q) _ hπ π rfl
  rw [hfit.1] at h
  have hs := proverStream3_reference D hD flockBytes
  rw [flockBytes_reference] at hs
  exact h.trans (hs.trans (by norm_num))

end UniComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniComplete.Rec3.cost_uniProverRec3With' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.cost_uniProverRec3With

/-- info: 'UniComplete.Rec3.costP_uniProverRec3With' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.costP_uniProverRec3With

/-- info: 'UniComplete.Rec3.proverBlocks3_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.proverBlocks3_reference

/-- info: 'UniComplete.Rec3.proverStream3_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.proverStream3_reference

/-- info: 'UniComplete.Rec3.proverCost3_flockProve3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.proverCost3_flockProve3H

/-- info: 'UniComplete.Rec3.proverStreamSize3_flockProve3H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.proverStreamSize3_flockProve3H
