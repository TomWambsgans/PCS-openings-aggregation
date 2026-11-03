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

end UniComplete.Cost
