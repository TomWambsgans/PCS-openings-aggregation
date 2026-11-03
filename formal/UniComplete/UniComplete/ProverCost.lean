-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`; and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean`'s cost of the prover's opening
-- (`cost_proveOpeningWithH`, `blockFactor`) and of a commitment (`qc_commitWithH`, `treeCost`).
import UniComplete.ProverDuplex
import UniComplete.ProverBounds
import UniComplete.VerifierHCost

/-!
# The block count of the honest prover, and the size of its stream
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

namespace UniComplete.Cost

open E2ECompleteness.Cost (QC qc_pure qc_H_le qc_commitWithH treeCost)
open Bounds (batchVarsBound valuesBound)

/-! ## Wire lengths -/

theorem length_be64 (w : UInt64) : (be64 w).length = 8 := by simp [be64]

theorem length_scalarWire (x : E) : (scalarWire x).length = 24 := by simp [scalarWire, length_be64]

theorem length_flatMap_scalarWire : ∀ xs : List E, (xs.flatMap scalarWire).length = 24 * xs.length
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, length_scalarWire, length_flatMap_scalarWire xs, List.length_cons]
    ring

theorem length_integerWire (n bytes : ℕ) : (integerWire n bytes).length = bytes := by simp [integerWire]

theorem length_rootWord (h : E × E) : (rootWord h).length = 32 := by simp [rootWord, length_be64]

/-! ## Costs with a postcondition, on the result alone -/

section CostP

variable {α β : Type}

theorem CostP.mono_budget {X : OracleComp KeccakCalls α} {n n' : ℕ} {P : α → Prop}
    (h : CostP X n fun a _ ↦ P a) (hn : n ≤ n') : CostP X n' fun a _ ↦ P a := by
  induction X using OracleComp.inductionOn generalizing n n' with
  | pure a => exact h
  | query_bind t k ih =>
    rw [costP_query_bind] at h ⊢
    exact ⟨h.1.trans hn, fun u ↦ ih u (h.2 u) (by omega)⟩

theorem costP_bind_qc {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {a b : ℕ}
    {P : β → Prop} (hX : QC X a) (hf : ∀ x, CostP (f x) b fun y _ ↦ P y) :
    CostP (X >>= f) (a + b) fun y _ ↦ P y :=
  CostP.bind (costP_of_qc hX b) fun x _ hr ↦ (hf x).mono_budget hr

end CostP

/-! ## The writer's calculus -/

/-- **The potential**: the bytes written and not yet hashed. -/
def wpot (c : Wr) : ℕ := c.stream.size - c.absorbed

/-- The writer's invariant. -/
def WInv (c : Wr) : Prop := c.absorbed ≤ c.stream.size

/-- **`x` makes at most `k` block calls beyond one per byte it writes, writing at most `w` bytes**: from any state
satisfying the invariant, with any extra budget `e`, at most `k + w` blocks beyond the potential; each outcome
satisfies `P` with its final state, which has grown by at most `w` bytes, its potential and `e` left. -/
def WC {α : Type} (x : PM α) (k w : ℕ) (P : α → Wr → Prop) : Prop :=
  ∀ c, WInv c → ∀ e, CostP (x.run c) (k + w + wpot c + e) fun z rem ↦
    P z.1 z.2 ∧ WInv z.2 ∧ c.stream.size ≤ z.2.stream.size ∧ z.2.stream.size ≤ c.stream.size + w ∧
      wpot z.2 + e ≤ rem

section Calculus

variable {α β : Type}

theorem wc_bind {x : PM α} {f : α → PM β} {k₁ w₁ k₂ w₂ : ℕ} {P : α → Wr → Prop} {Q : β → Wr → Prop}
    (hx : WC x k₁ w₁ P) (hf : ∀ a s, P a s → WC (f a) k₂ w₂ Q) : WC (x >>= f) (k₁ + k₂) (w₁ + w₂) Q := by
  intro c hc e
  rw [StateT.run_bind]
  have h1 := hx c hc (k₂ + w₂ + e)
  rw [show k₁ + w₁ + wpot c + (k₂ + w₂ + e) = k₁ + k₂ + (w₁ + w₂) + wpot c + e by omega] at h1
  refine CostP.bind h1 fun z rem hz ↦ ?_
  obtain ⟨hP, hI, hs1, hs2, hrem⟩ := hz
  have h2 := hf z.1 z.2 hP z.2 hI (rem - k₂ - w₂ - wpot z.2)
  rw [show k₂ + w₂ + wpot z.2 + (rem - k₂ - w₂ - wpot z.2) = rem by omega] at h2
  exact h2.mono fun z' rem' h ↦ ⟨h.1, h.2.1, by omega, by omega, by omega⟩

theorem wc_mono {x : PM α} {k w k' w' : ℕ} {P P' : α → Wr → Prop} (h : WC x k w P) (hk : k ≤ k') (hw : w ≤ w')
    (hP : ∀ a s, P a s → P' a s) : WC x k' w' P' := by
  intro c hc e
  have h1 := h c hc (e + (k' - k) + (w' - w))
  rw [show k + w + wpot c + (e + (k' - k) + (w' - w)) = k' + w' + wpot c + e by omega] at h1
  exact h1.mono fun z rem h ↦ ⟨hP _ _ h.1, h.2.1, h.2.2.1, by omega, by omega⟩

/-- A step paid from the budget, then the rest from what is left. -/
theorem wc_seq {x : PM α} {f : α → PM β} {k₁ w₁ k w : ℕ} {P : α → Wr → Prop} {Q : β → Wr → Prop}
    (hx : WC x k₁ w₁ P) (hf : ∀ a s, P a s → WC (f a) (k - k₁) (w - w₁) Q) (hk : k₁ ≤ k) (hw : w₁ ≤ w) :
    WC (x >>= f) k w Q :=
  wc_mono (wc_bind hx hf) (by omega) (by omega) fun _ _ h ↦ h

theorem wc_pure (a : α) : WC (pure a : PM α) 0 0 fun b _ ↦ b = a :=
  fun c hc e ↦ ⟨rfl, hc, le_rfl, by dsimp only; omega, by dsimp only; omega⟩

/-- A result read off the state. -/
theorem wc_get_pure (F : Wr → α) (P : α → Wr → Prop) (h : ∀ s, P (F s) s) :
    WC ((get : PM Wr) >>= fun s ↦ pure (F s)) 0 0 P :=
  fun c hc e ↦ ⟨h c, hc, le_rfl, by dsimp only; omega, by dsimp only; omega⟩

theorem wc_map {x : PM α} {k w : ℕ} {P : α → Wr → Prop} (f : α → β) (hx : WC x k w P) :
    WC (f <$> x) k w fun b s ↦ ∃ a, b = f a ∧ P a s := by
  intro c hc e
  rw [StateT.run_map, map_eq_bind_pure_comp]
  exact CostP.bind (hx c hc e) fun z rem h ↦ ⟨⟨z.1, rfl, h.1⟩, h.2⟩

theorem wc_sendBytes (b : List UInt8) :
    WC (sendBytes (m := OracleComp KeccakCalls) b) 0 b.length fun _ _ ↦ True := by
  intro c hc e
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;>
    simp only [WInv, wpot, Array.size_append, List.size_toArray] at hc ⊢ <;> omega

theorem wc_sendScalar (x : E) : WC (sendScalar (m := OracleComp KeccakCalls) x) 0 24 fun _ _ ↦ True :=
  wc_mono (wc_sendBytes _) le_rfl (by rw [length_scalarWire]) fun _ _ h ↦ h

theorem wc_sendScalars (xs : List E) :
    WC (sendScalars (m := OracleComp KeccakCalls) xs) 0 (24 * xs.length) fun _ _ ↦ True :=
  wc_mono (wc_sendBytes _) le_rfl (by rw [length_flatMap_scalarWire]) fun _ _ h ↦ h

theorem wc_sendInteger (n bytes : ℕ) :
    WC (sendInteger (m := OracleComp KeccakCalls) n bytes) 0 bytes fun _ _ ↦ True :=
  wc_mono (wc_sendBytes _) le_rfl (by rw [length_integerWire]) fun _ _ h ↦ h

theorem wc_sendRoot (halves : E × E) : WC (sendRoot (m := OracleComp KeccakCalls) halves) 0 32 fun _ _ ↦ True :=
  wc_mono (wc_sendBytes _) le_rfl (by rw [length_rootWord]) fun _ _ h ↦ h

/-- **A challenge** costs at most one block beyond the bytes it hashes, which the potential holds. -/
theorem wc_sampleW : WC (sampleW callKeccak256) 1 0 fun _ _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u ↦ ⟨trivial, ?_, ?_, ?_, ?_⟩⟩
  · show (digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1 ≤
      1 + 0 + wpot c + e
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega
  · show c.stream.size ≤ c.stream.size
    exact le_rfl
  · exact le_rfl
  · show c.stream.size ≤ c.stream.size + 0
    omega
  · show c.stream.size - c.stream.size + e ≤ 1 + 0 + wpot c + e -
      ((digestBytes c.state ++ (c.stream.extract c.absorbed c.stream.size).toList).length / 136 + 1)
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, wpot]
    omega

/-- A lifted computation of the two calls: its blocks, no write. -/
theorem wc_lift {X : OracleComp KeccakCalls α} {n : ℕ} (hX : QC X n) :
    WC (StateT.lift X : PM α) n 0 fun _ _ ↦ True := by
  intro c hc e
  rw [StateT.run_lift]
  have h := costP_of_qc hX (wpot c + e)
  rw [show n + (wpot c + e) = n + 0 + wpot c + e by omega] at h
  exact CostP.bind h fun a rem hr ↦ ⟨trivial, hc, le_rfl, by dsimp only; omega, by dsimp only; omega⟩

/-- **A loop** of steps of cost `(k, w)`. -/
theorem wc_forIn_list {γ : Type} (l : List γ) (b : β) (f : γ → β → PM (ForInStep β)) {k w : ℕ}
    (hf : ∀ a s, WC (f a s) k w fun _ _ ↦ True) :
    WC (forIn l b f) (l.length * k) (l.length * w) fun _ _ ↦ True := by
  induction l generalizing b with
  | nil => exact wc_mono (wc_pure b) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial
  | cons a l ih =>
    rw [List.forIn_cons]
    refine wc_mono (wc_bind (k₂ := l.length * k) (w₂ := l.length * w) (Q := fun _ _ ↦ True) (hf a b)
      fun s _ _ ↦ ?_) (by rw [List.length_cons, Nat.succ_mul]; omega)
      (by rw [List.length_cons, Nat.succ_mul]; omega) fun _ _ h ↦ h
    cases s with
    | done b => exact wc_mono (wc_pure b) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial
    | yield b => exact ih b

/-- **A loop whose steps yield**, with an invariant counting them. -/
theorem wc_forIn_yield {γ : Type} (l : List γ) (g : γ → β → PM β) {k w : ℕ} (I : ℕ → β → Prop)
    (hg : ∀ i a s, I i s → WC (g a s) k w fun s' _ ↦ I (i + 1) s') :
    ∀ (b : β) (i : ℕ), I i b →
      WC (forIn l b fun a s ↦ g a s >>= fun s' ↦ pure (ForInStep.yield s')) (l.length * k) (l.length * w)
        fun r _ ↦ I (i + l.length) r := by
  induction l with
  | nil => intro b i h; exact wc_mono (wc_pure b) (Nat.zero_le _) (Nat.zero_le _) fun _ _ hb ↦ by rw [hb]; exact h
  | cons a l ih =>
    intro b i h
    rw [List.forIn_cons, bind_assoc]
    simp only [pure_bind]
    refine wc_mono (wc_bind (hg i a b h) fun s' _ hs' ↦ ih s' (i + 1) hs')
      (by rw [List.length_cons, Nat.succ_mul]; omega) (by rw [List.length_cons, Nat.succ_mul]; omega)
      fun r _ hr ↦ ?_
    rw [List.length_cons, show i + (l.length + 1) = i + 1 + l.length by omega]
    exact hr

theorem wc_samplesW : ∀ count : ℕ, WC (samplesW callKeccak256 count) count 0 fun _ _ ↦ True
  | 0 => wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial
  | count + 1 => by
    unfold samplesW
    exact wc_seq wc_sampleW (fun _ _ _ ↦ wc_seq (wc_samplesW count) (fun _ _ _ ↦
      wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial) (by omega) le_rfl)
      (by omega) (Nat.zero_le _)

/-- **A round of the batching sumcheck**: two scalars, a challenge; the point grows by one. -/
theorem wc_batchRound (lambda : E) (j : ℕ) (st : BatchState) :
    WC (batchRound callKeccak256 lambda j st) 1 48 fun st' _ ↦ st'.point.length = st.point.length + 1 := by
  unfold batchRound
  exact wc_seq (wc_sendScalar _) (fun _ _ _ ↦ wc_seq (wc_sendScalar _) (fun _ _ _ ↦ wc_seq wc_sampleW
    (fun r _ _ ↦ wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by rw [hb]; simp)
    (by omega) (Nat.zero_le _)) (Nat.zero_le _) (by omega)) (Nat.zero_le _) (by omega)

/-- **The batching sumcheck's rounds**: `vars` rounds; the point grows by `vars`. -/
theorem wc_batchRounds (lambda : E) (vars : ℕ) (st : BatchState) :
    WC (batchRounds callKeccak256 lambda vars st) vars (48 * vars) fun r _ ↦ r.length = st.point.length + vars := by
  unfold batchRounds
  have h := wc_forIn_yield (List.range vars) (fun j s ↦ batchRound callKeccak256 lambda j s)
    (fun i s ↦ s.point.length = st.point.length + i)
    (fun i a s hs ↦ wc_mono (wc_batchRound lambda a s) le_rfl le_rfl fun s' _ h ↦ by rw [h, hs]; omega) st 0
    (by simp)
  rw [List.length_range] at h
  exact wc_seq h (fun r _ hr ↦ wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by
    rw [hb, hr]; omega) (by omega) (by omega)

end Calculus

/-! ## The stream -/

theorem qc_commitReal (c : Commitment) (vars : ℕ) (stack : Array K) :
    QC (commitReal callKeccak256 c vars stack) (treeCost vars) :=
  (qc_commitWithH vars stack).bind_le (fun _ ↦ qc_pure _ 0) le_rfl

/-- **What the openings and the verifier need of the stream**: its bytes are the writer's; its point claims have
at most `V` coordinates, the matrices' claim at most `V + pF`. -/
def StreamOK (V pF : ℕ) (out : CoreOut) (s : Wr) : Prop :=
  out.stream = s.stream ∧ (∀ x ∈ out.claims, x.2.1.length ≤ V) ∧
    ∀ mc, out.matrices = some mc → mc.point.length ≤ V + pF

/-- **The stream's blocks beyond its bytes**: `C1`'s and `C2`'s trees, the challenges (`α ∈ E^4`, `β`, `γ`, `t`,
`ρ`, `λ`, one per batching round), Flock's. -/
def streamBlocks (shape : Shape) (kF : ℕ) : ℕ :=
  treeCost (c1Layout shape).vars + 6 + kF + treeCost (((layoutsOf shape).lookup .c2).getD default).vars + 3 +
    batchVarsBound shape

/-- **The stream's bytes**: the row counts, the two roots, Flock's, the values at `t`, the batching rounds' two
scalars each, the three claims' values, the matrices' two. -/
def streamBytes (shape : Shape) (rows wF : ℕ) : ℕ :=
  4 * rows + 64 + wF + 24 * valuesBound + 72 + 48 * batchVarsBound shape + 48

theorem length_combined (f : Commitment → Option (Commitment × Combined)) :
    (commitments.filterMap f).length ≤ 3 :=
  (List.length_filterMap_le _ _).trans (by decide)

theorem length_claims {α : Type} (f : Commitment → Option (Commitment × Combined)) (g : Commitment × Combined → α)
    (h : α → E) : 24 * (((commitments.filterMap f).map g).map h).length ≤ 72 := by
  simp only [List.length_map]
  have := length_combined f
  omega

theorem length_matrixClaim (p : Flock.Pending) (r : List E) (a b : E) :
    (p.matrixClaim r a b).point.length ≤ r.length + (p.rowLow.length + p.chiIn.length + p.chiInPrime.length) := by
  simp only [Flock.Pending.matrixClaim, List.length_append, List.length_take, List.length_drop]
  omega

/-- **The stream's cost** (Flock's main line), given Flock's prover's at its `log_n`. -/
theorem wc_proveStreamWith (flock : FlockProver (OracleComp KeccakCalls)) (kF wF pF : ℕ) (variant : Flock.Variant)
    (tr : Trace)
    (hF : WC (flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) variant tr.qflock) kF wF
      fun out _ ↦ out.pending.rowLow.length + out.pending.chiIn.length + out.pending.chiInPrime.length ≤ pF) :
    WC (proveStreamWith callKeccak256 (commitReal callKeccak256) flock (.flock variant) tr)
      (streamBlocks tr.shape kF) (streamBytes tr.shape tr.rows.length wF) (StreamOK (batchVarsBound tr.shape) pF) := by
  unfold proveStreamWith streamBlocks streamBytes
  refine wc_seq (wc_forIn_list (k := 0) (w := 4) _ _ _ fun _ _ ↦ wc_seq (wc_sendInteger _ 4)
    (fun _ _ _ ↦ wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial) le_rfl le_rfl)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun committed1 _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_samplesW 4) (fun alphas _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun beta _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun gamma _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_map some hF) (fun flockOut _ hfo ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_lift (qc_commitReal _ _ _)) (fun committed2 _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendRoot _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun t _ _ ↦ ?_) (by omega) (by omega)
  have ha := Bounds.atT_facts tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  have hvars := Bounds.batchVars_atT tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (Nat.mul_le_mul_left 24 ha.values) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun rho _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun lambda _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_mono (wc_batchRounds _ _ _) hvars (Nat.mul_le_mul_left 48 hvars) fun r _ h ↦ h)
    (fun r _ hr ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_mono (wc_sendScalars _) le_rfl (length_claims _ _ _) fun _ _ h ↦ h)
    (fun _ _ _ ↦ ?_) (by omega) (by omega)
  simp only [List.length_nil, Nat.zero_add] at hr
  dsimp only
  split
  next p snd heq =>
    refine wc_seq (wc_mono (k' := 0) (w' := 48) (wc_sendScalars _) le_rfl (by simp) fun _ _ h ↦ h)
      (fun _ _ _ ↦ ?_) (by omega) (by omega)
    refine wc_seq (wc_pure _) (fun m _ hm ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    subst hm
    refine wc_mono (wc_get_pure _ _ fun s ↦ ⟨rfl, ?_, ?_⟩) (Nat.zero_le _) (Nat.zero_le _) fun _ _ h ↦ h
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨⟨c, cl⟩, _, rfl⟩ := hx
      dsimp only
      rw [List.length_take]
      omega
    · intro mc hmc
      cases hmc
      obtain ⟨out, rfl, hout⟩ := hfo
      rw [ha.pending] at heq
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have := length_matrixClaim out.pending r
        (multilinearEval (List.map ofK (flockMatrixStack true).toList) (out.pending.matrixClaim r 0 0).point)
        (multilinearEval (List.map ofK (flockMatrixStack false).toList) (out.pending.matrixClaim r 0 0).point)
      omega
  next heq =>
    refine wc_seq (wc_pure _) (fun m _ hm ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    subst hm
    refine wc_mono (wc_get_pure _ _ fun s ↦ ⟨rfl, ?_, fun mc hmc ↦ by cases hmc⟩) (Nat.zero_le _) (Nat.zero_le _)
      fun _ _ h ↦ h
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨⟨c, cl⟩, _, rfl⟩ := hx
    dsimp only
    rw [List.length_take]
    omega


/-! ## The prover -/

section Prover

open LeanVM.Protocol.Verifier (whirBound costHeight)
open E2ECompleteness.Cost (blockFactor)

/-- **The prover's opening's blocks**, a claim of at most `v` coordinates: its IV, its seed's permutation, the
root's two absorptions, WHIR's prover at height `26` (E2ECompleteness's `cost_proveOpeningWithH`). -/
def openP (fuel v : ℕ) : ℕ := (76 + 24 * (v + 1)) / 136 + 1 + 3 + (4 + (2 + whirBound)) * blockFactor costHeight fuel

theorem qc_proveOpening1 (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
    (pt : List E) (value : E) {v : ℕ} (hv : pt.length ≤ v) :
    QC (E2ECompleteness.proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack [⟨pt, value⟩])
      (openP fuel v) :=
  E2ECompleteness.Cost.cost_proveOpeningWithH fuel L tree stack _ v _
    (fun c hc ↦ by
      simp only [List.mem_singleton] at hc
      subst hc
      exact hv)
    (by simp only [List.length_singleton, Nat.one_mul]; omega)

/-- A step of cost `a`, then the rest from what is left. -/
theorem costP_seq_qc {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {a n : ℕ}
    {P : β → Prop} (hX : QC X a) (hf : ∀ x, CostP (f x) (n - a) fun y _ ↦ P y) (h : a ≤ n) :
    CostP (X >>= f) n fun y _ ↦ P y := by
  have := costP_bind_qc hX hf
  rw [show a + (n - a) = n by omega] at this
  exact this

theorem qc_setupTreesOf (tr : Trace) :
    QC (setupTreesOf callKeccak256 tr) (treeCost (setupLayout tr.shape).vars + 2 * treeCost matrixVars) := by
  unfold setupTreesOf
  exact (qc_commitWithH _ _).bind_le (fun _ ↦ (qc_commitWithH _ _).bind_le (fun _ ↦ (qc_commitWithH _ _).bind_le
    (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl) (by unfold treeCost; omega)

theorem ivInput_length' (shape : Shape) (programIv : List UInt8) (roots : SetupRoots) :
    (ivTag ++ programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++ digestBytes roots.b0 ++
      shapeBytes shape ++ (layoutWords shape).flatten).length = 280 + programIv.length := by
  simp only [List.length_append, ivTag_length, len_digestBytes, shapeBytes_length, layoutWords_length]
  omega

/-- The proof's stream, if a proof is returned. -/
theorem stream_of_some {s : Array UInt8} {p1 p2 p3 pa pb : Option LeanVM.Protocol.Compile.Proof} {p : UniProof}
    (h : (do
      let c1 ← p1
      let c2 ← p2
      let c3 ← p3
      let a ← pa
      let b ← pb
      pure ⟨s, c1, c2, c3, a, b⟩ : Option UniProof) = some p) : p.stream = s := by
  revert h
  cases p1 <;> cases p2 <;> cases p3 <;> cases pa <;> cases pb <;> simp
  rintro rfl
  rfl

/-- **The honest prover's blocks**: the setup's three trees, the IV, the seed, the stream (its blocks and its
bytes), five openings of claims of at most `batchVarsBound + pF` coordinates. -/
def uniProverCost (shape : Shape) (programIvLen rows kF wF pF : ℕ) : ℕ :=
  treeCost (setupLayout shape).vars + 2 * treeCost matrixVars + ((280 + programIvLen) / 136 + 1) + 1 +
    (streamBlocks shape kF + streamBytes shape rows wF) + 5 * openP PcsQuotient.nonceFuel (batchVarsBound shape + pF)

set_option hygiene false in
/-- One step of the openings' walk (`hc`, `hm`, `h1` … `h4` the local facts on the claims). -/
macro "open_step" : tactic => `(tactic| first
  | exact fun p hp ↦ by rw [stream_of_some hp]; exact hS
  | refine costP_seq_qc (qc_proveOpening1 _ _ _ _ _ _ (v := batchVarsBound tr.shape + pF) (by first
      | exact hc _ _ _ (List.mem_of_find?_eq_some h1)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h2)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h3)
      | exact hm _ h4)) (fun _ ↦ ?_) (by omega))

/-- **The honest prover's block count** (Flock's main line), given Flock's prover's at its `log_n`: and every proof
it returns has a stream of at most `streamBytes` bytes. -/
theorem costP_proveWith (flock : FlockProver (OracleComp KeccakCalls)) (kF wF pF : ℕ) (variant : Flock.Variant)
    (programIv : List UInt8) (tr : Trace) (hpub : tr.publicInput.length = 32)
    (hF : WC (flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) variant tr.qflock) kF wF
      fun out _ ↦ out.pending.rowLow.length + out.pending.chiIn.length + out.pending.chiInPrime.length ≤ pF) :
    CostP (proveWith callKeccak256 callKeccakF1600 PcsQuotient.nonceFuel flock (.flock variant) programIv tr)
      (uniProverCost tr.shape programIv.length tr.rows.length kF wF pF)
      fun o _ ↦ ∀ p, o = some p → p.stream.size ≤ streamBytes tr.shape tr.rows.length wF := by
  unfold proveWith contractIvOf seedOf
  simp only [bind_assoc, pure_bind]
  refine costP_seq_qc (qc_setupTreesOf tr) (fun trees ↦ ?_) (by unfold uniProverCost; omega)
  refine costP_seq_qc (qc_H_le (k := (280 + programIv.length) / 136 + 1) (by rw [ivInput_length']; omega))
    (fun d ↦ ?_) (by unfold uniProverCost; omega)
  refine costP_seq_qc (qc_H_le (k := 1) (by
    simp only [List.length_append, name_length, len_digestBytes, hpub]; omega)) (fun seed ↦ ?_)
    (by unfold uniProverCost; omega)
  have hW := wc_proveStreamWith flock kF wF pF variant tr hF (Wr.start seed) (by simp [WInv, Wr.start])
    (uniProverCost tr.shape programIv.length tr.rows.length kF wF pF -
      (treeCost (setupLayout tr.shape).vars + 2 * treeCost matrixVars) - ((280 + programIv.length) / 136 + 1) - 1 -
      (streamBlocks tr.shape kF + streamBytes tr.shape tr.rows.length wF))
  rw [show streamBlocks tr.shape kF + streamBytes tr.shape tr.rows.length wF + wpot (Wr.start seed) +
      (uniProverCost tr.shape programIv.length tr.rows.length kF wF pF -
        (treeCost (setupLayout tr.shape).vars + 2 * treeCost matrixVars) - ((280 + programIv.length) / 136 + 1) - 1 -
        (streamBlocks tr.shape kF + streamBytes tr.shape tr.rows.length wF)) =
      uniProverCost tr.shape programIv.length tr.rows.length kF wF pF -
        (treeCost (setupLayout tr.shape).vars + 2 * treeCost matrixVars) - ((280 + programIv.length) / 136 + 1) - 1
      by simp only [wpot, Wr.start, Array.size_empty]; unfold uniProverCost; omega] at hW
  refine CostP.bind hW fun z rem hz ↦ ?_
  obtain ⟨⟨hstream, hc0, hm0⟩, -, -, hsize, hrem⟩ := hz
  have hS : z.1.stream.size ≤ streamBytes tr.shape tr.rows.length wF := by
    rw [hstream]
    simpa [Wr.start] using hsize
  have hc : ∀ c pt v, (c, pt, v) ∈ z.1.claims → pt.length ≤ batchVarsBound tr.shape + pF :=
    fun c pt v h ↦ (hc0 _ h).trans (Nat.le_add_right _ _)
  have hm : ∀ mc, z.1.matrices = some mc → mc.point.length ≤ batchVarsBound tr.shape + pF := hm0
  refine CostP.mono_budget (n := 5 * openP PcsQuotient.nonceFuel (batchVarsBound tr.shape + pF)) ?_
    (by unfold uniProverCost at hrem; omega)
  obtain ⟨out, _⟩ := z
  dsimp only at hS hc hm ⊢
  generalize h1 : List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize h2 : List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize h3 : List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  generalize h4 : out.matrices = om
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    rcases om with _ | mc <;> repeat open_step

end Prover

/-! ## The deployed honest prover, and the completeness run -/

section Deployed

/-- **Flock's prover's cost** (`FlockCost flock k w p`): over the two calls, at `log_n` and a variant, from any
writer's state, it makes at most `k logN variant` block calls beyond one per byte it writes (each challenge one,
the bytes it hashes paid by the writes, `wc_sampleW`), writes at most `w logN variant` bytes, and its pending
claim on `A0`, `B0` has at most `p logN variant` coordinates of its own (`rowLow`, `chiIn`, `chiInPrime`; the
others are the batching sumcheck's). The facts the block count uses of it: a prover built from `sampleW`,
`sendBytes` and pure code proves it with this file's calculus (`wc_seq`, `wc_sampleW`, `wc_sendScalar`, …). -/
def FlockCost (flock : FlockProverH) (k w p : ℕ → Flock.Variant → ℕ) : Prop :=
  ∀ logN variant words, WC (flock callKeccak256 logN variant words) (k logN variant) (w logN variant)
    fun out _ ↦ out.pending.rowLow.length + out.pending.chiIn.length + out.pending.chiInPrime.length ≤ p logN variant

/-- Flock's `log_n` at a shape: the R1CS's rows' `14` and BLAKE2S's height. -/
abbrev flockLogN (shape : Shape) : ℕ := blake2sR1csLogSize + shape.heights.getD opBlake2s 0

/-- **The deployed honest prover's block count**, at `rows` row counts, Flock's prover's costs `k`, `w`, `p`. -/
def proverBlocks (D : Deployment) (rows : ℕ) (k w p : ℕ → Flock.Variant → ℕ) : ℕ :=
  uniProverCost D.shape D.programIv.length rows (k (flockLogN D.shape) flockMain) (w (flockLogN D.shape) flockMain)
    (p (flockLogN D.shape) flockMain)

/-- **The honest stream's bytes**, at most. -/
def proverStream (D : Deployment) (rows : ℕ) (w : ℕ → Flock.Variant → ℕ) : ℕ :=
  streamBytes D.shape rows (w (flockLogN D.shape) flockMain)

/-- **The deployed honest prover over the two calls makes at most `proverBlocks` block calls, and every proof it
returns has a stream of at most `proverStream` bytes**, given Flock's prover's cost. -/
theorem costP_uniProverWith (flock : FlockProverH) (k w p : ℕ → Flock.Variant → ℕ) (hF : FlockCost flock k w p)
    (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    CostP (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      (proverBlocks D rows.length k w p)
      fun o _ ↦ ∀ proof, o = some proof → proof.stream.size ≤ proverStream D rows.length w :=
  costP_proveWith (flock callKeccak256) _ _ _ flockMain D.programIv (honestTrace D input rows q)
    (by simp [honestTrace]) (hF _ _ _)

/-- **The deployed honest prover over the two calls makes at most `proverBlocks` block calls.** -/
theorem cost_uniProverWith (flock : FlockProverH) (k w p : ℕ → Flock.Variant → ℕ) (hF : FlockCost flock k w p)
    (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    Common.QueryCostAtMost (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      hashBlocks (proverBlocks D rows.length k w p) :=
  (costP_uniProverWith flock k w p hF D input rows q).toQC

theorem CostP.add_budget {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} {P : α → Prop}
    (h : CostP X n fun a _ ↦ P a) (m : ℕ) : CostP X (n + m) fun a r ↦ P a ∧ m ≤ r := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => exact ⟨h, Nat.le_add_left m n⟩
  | query_bind t k ih =>
    rw [costP_query_bind] at h ⊢
    refine ⟨by omega, fun u ↦ ?_⟩
    rw [show n + m - hashBlocks t = (n - hashBlocks t) + m by omega]
    exact ih u (h.2 u)

/-- **The completeness run over the two calls**: the setup, the honest prover's proof, the deployed verifier's
verdict (`uniCompletenessExperiment`'s computation, Keccak-256 and Keccak-f[1600] two calls). -/
def completenessRunH (flock : FlockProverH) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) : OracleComp KeccakCalls Bool := do
  let trees ← setupTreesWithH callKeccak256 callKeccakF1600 D
  match ← uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q with
  | none => return false
  | some proof => Deployment.verifierWithH callKeccak256 callKeccakF1600 D trees.roots input proof

/-- **The completeness run's block count**: the setup's, the prover's, the verifier's on a stream of at most
`proverStream` bytes. -/
theorem cost_completenessRunH (flock : FlockProverH) (k w p : ℕ → Flock.Variant → ℕ) (hF : FlockCost flock k w p)
    (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    Common.QueryCostAtMost (completenessRunH flock D input rows q) hashBlocks
      (setupCost D + (proverBlocks D rows.length k w p + verifierCost D (proverStream D rows.length w))) := by
  refine CostP.toQC (Q := fun _ _ ↦ True) ?_
  unfold completenessRunH
  refine costP_bind_qc (cost_setupTreesWithH D) fun trees ↦ ?_
  refine CostP.bind ((costP_uniProverWith flock k w p hF D input rows q).add_budget _) fun o rem ho ↦ ?_
  rcases o with _ | proof
  · trivial
  · have := ho.2
    exact ((costP_of_qc (cost_verifierWithH D trees.roots input proof _ (ho.1 proof rfl)) 0).mono
      fun _ _ _ ↦ trivial).mono_budget (by omega)

end Deployed

end UniComplete.Cost
