-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`; and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean`'s cost of the opening (`cost_openingWithH`, `vOpen`)
-- and of a commitment (`qc_commitWithH`).
import UniComplete.VerifierHDuplex
import E2ECompleteness.Cost

/-!
# The block count of the univariate verifier

**`cost_verifierWithH`**: the deployed verifier over the two calls, on any proof whose stream has at most `S` bytes,
makes at most `verifierCost D S` block calls (`hashBlocks`: a Keccak-256 of `n` bytes costs `⌊n / 136⌋ + 1`, a
Keccak-f[1600] one), whatever its opening proofs; **`cost_setupTreesWithH`** bounds the setup.

`verifierCost D S = 3 S + walkCost D.shape flockMain + ivCost D + 2 + 5 (46 + vOpen)`:

* **The walk** (`cc_reduceWithH_flockPoint`): every challenge hashes the state and the bytes read since the last
  one. The count is amortized by a potential on the channel (`pot`: three per unread byte, one per byte read but
  not yet hashed): a read of `n` bytes releases `2 n`; a challenge costs at most `2` plus the bytes it hashes
  (`cc_sampleH`). A sumcheck round reads two scalars (`48` bytes) before its challenge, so the rounds are paid by
  their reads (`cc_sumcheckH`): the bound does not depend on the stacks' layouts (the batch's rounds). The other
  challenges (`α ∈ E^4`, `β`, `γ`, Flock's sampled coordinates, `z`, its `α`, the ring map's six, `t`, `ρ`, `λ`)
  cost `2` each: `walkCost`. From the start, the potential is `3 S`.
* **The seed** (`80` bytes, one block), **the IV** (`ivCost`, `280` bytes and the program's IV).
* **The openings**: at most three point claims (the walk's result has at most three openings, the commitments'),
  then `A0` and `B0`; each `46 + vOpen` blocks (E2ECompleteness's `cost_openingWithH`: a claim of at most `255`
  coordinates, a layout word's byte, whatever the opening proof).

The calculus (`CostP`): a computation over the two calls with at most `n` block calls on every path, each outcome
satisfying a postcondition with the blocks left (as mumbai's `DuplexP` carries the answers); `CC x k g P` for the
channel: from any state with `absorbed ≤ cursor ≤ size` (`Inv`), at most `k` blocks beyond the potential, releasing
`g` more, each successful result satisfying `P`. Only the main line's walk (Flock deferred, point claims: what
`verifyWithH` runs) is counted.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

namespace UniComplete.Cost

/-! ## Costs with a postcondition -/

/-- **At most `n` block calls on every path**, each outcome satisfying `Q` with the blocks left. -/
def CostP {α : Type} : OracleComp KeccakCalls α → ℕ → (α → ℕ → Prop) → Prop
  | .pure a, n, Q => Q a n
  | .liftBind t k, n, Q => hashBlocks t ≤ n ∧ ∀ u, CostP (k u) (n - hashBlocks t) Q

theorem costP_query_bind {α : Type} (t : List UInt8 ⊕ KeccakState)
    (k : KeccakCalls.Range t → OracleComp KeccakCalls α) (n : ℕ) (Q : α → ℕ → Prop) :
    CostP (liftM (KeccakCalls.query t) >>= k) n Q ↔ hashBlocks t ≤ n ∧ ∀ u, CostP (k u) (n - hashBlocks t) Q :=
  Iff.rfl

theorem CostP.bind {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {n : ℕ}
    {Q : α → ℕ → Prop} {R : β → ℕ → Prop} (hX : CostP X n Q) (hf : ∀ a r, Q a r → CostP (f a) r R) :
    CostP (X >>= f) n R := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => simpa using hf a n hX
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [costP_query_bind] at hX ⊢
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem CostP.mono {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} {Q R : α → ℕ → Prop}
    (hX : CostP X n Q) (h : ∀ a r, Q a r → R a r) : CostP X n R := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => exact h a n hX
  | query_bind t k ih =>
    rw [costP_query_bind] at hX ⊢
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

/-- A cost with a postcondition is a cost. -/
theorem CostP.toQC {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} {Q : α → ℕ → Prop}
    (hX : CostP X n Q) : Common.QueryCostAtMost X hashBlocks n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [costP_query_bind] at hX
    exact (Common.isWeightBound_query_bind_iff hashBlocks t k n).mpr ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

/-- A cost, with `m` more blocks, leaves at least `m`. -/
theorem costP_of_qc {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ}
    (hX : Common.QueryCostAtMost X hashBlocks n) (m : ℕ) : CostP X (n + m) fun _ r ↦ m ≤ r := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => exact Nat.le_add_left m n
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at hX
    rw [costP_query_bind]
    refine ⟨by omega, fun u ↦ ?_⟩
    rw [show n + m - hashBlocks t = (n - hashBlocks t) + m by omega]
    exact ih u (hX.2 u)

/-! ## The channel -/

/-- The channel's monad over the two calls. -/
abbrev CM := ChanM (OracleComp KeccakCalls)

/-- **The potential**: three per unread byte, one per byte read and not yet hashed. -/
def pot (c : Chan) : ℕ := 3 * (c.data.size - c.cursor) + (c.cursor - c.absorbed)

/-- The channel's invariant. -/
def Inv (c : Chan) : Prop := c.absorbed ≤ c.cursor ∧ c.cursor ≤ c.data.size

/-- **`x` from `c`**: at most `k` blocks beyond the potential (and any extra `e`), releasing `g`; each successful
result satisfies `P`, from a state satisfying the invariant. -/
def CCAt {α : Type} (c : Chan) (x : CM α) (k g : ℕ) (P : α → Prop) : Prop :=
  ∀ e, CostP (x.run.run c) (k + pot c + e) fun z rem ↦
    ∀ a, z.1 = .ok a → P a ∧ Inv z.2 ∧ pot z.2 + g + e ≤ rem

/-- **`x` costs at most `k` blocks beyond the potential and releases `g`**, from any state satisfying the
invariant, each successful result satisfying `P`. -/
def CC {α : Type} (x : CM α) (k g : ℕ) (P : α → Prop) : Prop := ∀ c, Inv c → CCAt c x k g P

section Calculus

variable {α β : Type}

theorem cc_bind {x : CM α} {f : α → CM β} {k₁ g₁ k₂ g₂ : ℕ} {P : α → Prop} {Q : β → Prop}
    (hx : CC x k₁ g₁ P) (hf : ∀ a, P a → CC (f a) k₂ g₂ Q) :
    CC (x >>= f) (k₁ + (k₂ - g₁)) (g₂ + (g₁ - k₂)) Q := by
  intro c hc e
  rw [show k₁ + (k₂ - g₁) + pot c + e = k₁ + pot c + ((k₂ - g₁) + e) by omega]
  simp only [ExceptT.run_bind, StateT.run_bind]
  refine CostP.bind (hx c hc _) fun z rem hz ↦ ?_
  obtain ⟨r, s⟩ := z
  cases r with
  | error err => exact fun a h ↦ by cases h
  | ok a =>
    obtain ⟨hP, hI, hrem⟩ := hz a rfl
    dsimp only at hI hrem
    have h2 := hf a hP s hI (rem - k₂ - pot s)
    rw [show k₂ + pot s + (rem - k₂ - pot s) = rem by omega] at h2
    exact h2.mono fun z' rem' h a' ha' ↦
      let ⟨h1, h2, h3⟩ := h a' ha'
      ⟨h1, h2, by omega⟩

theorem cc_mono {x : CM α} {k g k' g' : ℕ} {P P' : α → Prop} (h : CC x k g P) (hk : k ≤ k') (hg : g' ≤ g)
    (hP : ∀ a, P a → P' a) : CC x k' g' P' := by
  intro c hc e
  have h1 := h c hc (e + (k' - k))
  rw [show k + pot c + (e + (k' - k)) = k' + pot c + e by omega] at h1
  exact h1.mono fun z rem hz a ha ↦
    let ⟨h1, h2, h3⟩ := hz a ha
    ⟨hP a h1, h2, by omega⟩

/-- A paid step, then the rest from what is left. -/
theorem cc_seq {x : CM α} {f : α → CM β} {k₁ k g : ℕ} {P : α → Prop} {Q : β → Prop}
    (hx : CC x k₁ 0 P) (hf : ∀ a, P a → CC (f a) (k - k₁) g Q) (hk : k₁ ≤ k) : CC (x >>= f) k g Q :=
  cc_mono (cc_bind hx hf) (by omega) (by omega) fun _ h ↦ h

/-- A free step. -/
theorem cc_free {x : CM α} {f : α → CM β} {k g : ℕ} {P : α → Prop} {Q : β → Prop}
    (hx : CC x 0 0 P) (hf : ∀ a, P a → CC (f a) k g Q) : CC (x >>= f) k g Q :=
  cc_seq hx (fun a h ↦ by simpa using hf a h) (Nat.zero_le _)

theorem cc_pure {a : α} {P : α → Prop} (h : P a) (k : ℕ) : CC (pure a : CM α) k 0 P := by
  intro c hc e a' ha'
  cases ha'
  exact ⟨h, hc, by dsimp only; omega⟩

theorem cc_throw (err : UniError) (k g : ℕ) (P : α → Prop) : CC (throw err : CM α) k g P := by
  intro c hc e a ha
  cases ha

theorem cc_throw_bind (err : UniError) (f : α → CM β) (k g : ℕ) (P : β → Prop) :
    CC (throw err >>= f) k g P := by
  intro c hc e a ha
  cases ha

theorem cc_ite {x y : CM α} {k g : ℕ} {P : α → Prop} (cnd : Prop) [Decidable cnd] (hx : CC x k g P)
    (hy : CC y k g P) : CC (if cnd then x else y) k g P := by
  split
  · exact hx
  · exact hy

theorem cc_map {x : CM α} {k g : ℕ} {P : α → Prop} (f : α → β) (hx : CC x k g P) :
    CC (f <$> x) k g fun _ ↦ True := by
  rw [map_eq_bind_pure_comp]
  exact cc_mono (cc_bind hx fun a _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega)
    fun _ _ ↦ trivial

/-- **A loop** of steps of cost `k`. -/
theorem cc_forIn_list {γ : Type} (l : List γ) (b : β) (f : γ → β → CM (ForInStep β)) {k : ℕ}
    (hf : ∀ a s, CC (f a s) k 0 fun _ ↦ True) : CC (forIn l b f) (l.length * k) 0 fun _ ↦ True := by
  induction l generalizing b with
  | nil => exact cc_pure trivial _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine cc_seq (hf a b) (fun s _ ↦ ?_) (by simp [Nat.succ_mul])
    cases s with
    | done b => exact cc_pure trivial _
    | yield b => exact cc_mono (ih b) (by simp [Nat.succ_mul]) le_rfl fun _ h ↦ h

/-- A loop over `[0:n]`. -/
theorem cc_forIn_range (n : ℕ) (b : β) (f : ℕ → β → CM (ForInStep β)) {k : ℕ}
    (hf : ∀ a s, CC (f a s) k 0 fun _ ↦ True) : CC (forIn [0:n] b f) (n * k) 0 fun _ ↦ True := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact cc_mono (cc_forIn_list _ b f hf) (by simp [Std.Legacy.Range.size]) le_rfl fun _ h ↦ h

/-- A loop releases at least its first step's gain. -/
theorem cc_forIn_list_first {γ : Type} (l : List γ) (hl : l ≠ []) (b : β) (f : γ → β → CM (ForInStep β))
    {g : ℕ} (hf : ∀ a s, CC (f a s) 0 g fun _ ↦ True) : CC (forIn l b f) 0 g fun _ ↦ True := by
  obtain ⟨a, l, rfl⟩ : ∃ a l', l = a :: l' := by
    cases l with
    | nil => exact absurd rfl hl
    | cons a l' => exact ⟨a, l', rfl⟩
  rw [List.forIn_cons]
  refine cc_mono (cc_bind (k₂ := 0) (g₂ := 0) (hf a b) fun s _ ↦ ?_) (by omega) (by omega) fun _ h ↦ h
  cases s with
  | done b => exact cc_pure trivial 0
  | yield b =>
    exact cc_mono (cc_forIn_list (k := 0) l b f fun _ _ ↦ cc_mono (hf _ _) le_rfl (Nat.zero_le _) fun _ h ↦ h)
      (by simp) le_rfl fun _ h ↦ h

theorem cc_forIn_range_first (n : ℕ) (hn : 1 ≤ n) (b : β) (f : ℕ → β → CM (ForInStep β)) {g : ℕ}
    (hf : ∀ a s, CC (f a s) 0 g fun _ ↦ True) : CC (forIn [0:n] b f) 0 g fun _ ↦ True := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine cc_forIn_list_first _ ?_ b f hf
  simp [Std.Legacy.Range.size]
  omega

end Calculus

/-! ## The channel's steps -/

section Steps

theorem run_get (c : Chan) : (ExceptT.run (get : CM Chan)).run c = pure (.ok c, c) := by
  show (Except.ok <$> (get : StateT Chan (OracleComp KeccakCalls) Chan)).run c = _
  simp [StateT.run_map, StateT.run_get]

theorem run_set (c c' : Chan) : (ExceptT.run (set c' : CM PUnit)).run c = pure (.ok PUnit.unit, c') := by
  show (Except.ok <$> (set c' : StateT Chan (OracleComp KeccakCalls) PUnit)).run c = _
  simp [StateT.run_map, StateT.run_set]

theorem run_modify (f : Chan → Chan) (c : Chan) :
    (ExceptT.run (modify f : CM PUnit)).run c = pure (.ok PUnit.unit, f c) := by
  show (Except.ok <$> (modifyGet (fun s ↦ (PUnit.unit, f s)) : StateT Chan (OracleComp KeccakCalls) PUnit)).run c = _
  simp [StateT.run_map, StateT.run_modifyGet]

theorem len_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  have : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  rw [this, LeanVM.Rpm.length_lanesBytes]
  simp

/-- **A challenge** costs at most `2` blocks beyond the bytes it hashes, which the potential holds. -/
theorem cc_sampleH : CC (sampleH callKeccak256) 2 0 fun _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u a _ ↦ ⟨trivial, ?_, ?_⟩⟩
  · show (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1 ≤ 2 + pot c + e
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega
  · exact ⟨le_rfl, hc.2⟩
  · show 3 * (c.data.size - c.cursor) + (c.cursor - c.cursor) + 0 + e ≤
      2 + pot c + e - ((digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1)
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega

/-- **A read of `n` bytes** releases `2 n`. -/
theorem cc_takeBytes (n : ℕ) : CC (takeBytes (m := OracleComp KeccakCalls) n) 0 (2 * n) fun _ ↦ True := by
  intro c hc e
  unfold takeBytes
  simp only [ExceptT.run_bind, StateT.run_bind, run_get, pure_bind]
  split
  · rename_i h
    simp only [ExceptT.run_bind, StateT.run_bind, run_set, pure_bind]
    refine fun a _ ↦ ⟨trivial, ⟨hc.1.trans (Nat.le_add_right _ _), h⟩, ?_⟩
    simp only [pot]
    have := hc.1
    omega
  · exact fun a ha ↦ by cases ha

theorem cc_nextScalar : CC (nextScalar (m := OracleComp KeccakCalls)) 0 48 fun _ ↦ True := by
  unfold nextScalar
  exact cc_mono (cc_bind (cc_takeBytes 24) fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega)
    (by omega) fun _ _ ↦ trivial

theorem cc_nextInteger (bytes : ℕ) : CC (nextInteger (m := OracleComp KeccakCalls) bytes) 0 0 fun _ ↦ True := by
  unfold nextInteger
  exact cc_mono (cc_bind (cc_takeBytes bytes) fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega)
    (Nat.zero_le _) fun _ _ ↦ trivial

theorem cc_nextScalars (count : ℕ) : CC (nextScalars (m := OracleComp KeccakCalls) count) 0 0 fun _ ↦ True := by
  unfold nextScalars
  refine cc_free (cc_mono (cc_forIn_range (k := 0) count _ _ fun _ _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h)
    fun _ _ ↦ cc_pure trivial 0
  exact cc_mono (cc_bind cc_nextScalar fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega)
    (Nat.zero_le _) fun _ _ ↦ trivial

/-- At least one scalar read releases `2`. -/
theorem cc_nextScalars_pos (count : ℕ) (h : 1 ≤ count) :
    CC (nextScalars (m := OracleComp KeccakCalls) count) 0 2 fun _ ↦ True := by
  unfold nextScalars
  refine cc_mono (cc_bind (cc_forIn_range_first (g := 48) count h _ _ fun _ _ ↦ ?_) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h
  exact cc_mono (cc_bind cc_nextScalar fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega)
    (by omega) fun _ _ ↦ trivial

theorem cc_nextRoot : CC (nextRoot (m := OracleComp KeccakCalls)) 0 0 fun _ ↦ True := by
  unfold nextRoot
  exact cc_free (cc_mono (cc_takeBytes 16) le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦
    cc_free (cc_mono (cc_takeBytes 16) le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ cc_pure trivial 0

theorem cc_requireZero (value : E) : CC (requireZero (m := OracleComp KeccakCalls) value) 0 0 fun _ ↦ True := by
  intro c hc e
  unfold requireZero
  rw [run_modify]
  exact fun a _ ↦ ⟨trivial, hc, by simp [pot]⟩

theorem cc_finish : CC (finish (m := OracleComp KeccakCalls)) 0 0 fun _ ↦ True := by
  intro c hc e
  unfold finish
  simp only [ExceptT.run_bind, StateT.run_bind, run_get, pure_bind]
  split
  · exact fun a _ ↦ ⟨trivial, hc, by dsimp only; omega⟩
  · exact fun a ha ↦ by cases ha

/-- **A sumcheck round's message** (of at least two coefficients) releases `2`: it reads two scalars. -/
theorem cc_roundPoly (count : ℕ) (h : 2 ≤ count) (claim : E) (eqFactor : Option E) :
    CC (roundPoly (m := OracleComp KeccakCalls) count claim eqFactor) 0 2 fun _ ↦ True := by
  unfold roundPoly
  cases eqFactor with
  | none =>
    exact cc_mono (cc_bind cc_nextScalar fun _ _ ↦ cc_bind (cc_nextScalars _) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ _ ↦ trivial
  | some r =>
    exact cc_mono (cc_bind (cc_nextScalars_pos (count - 1) (by omega)) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ _ ↦ trivial

end Steps

/-! ## The verifier's parts -/

section Parts

theorem cc_samplesH (count : ℕ) : CC (samplesH callKeccak256 count) (2 * count) 0 fun _ ↦ True := by
  unfold samplesH
  refine cc_mono (cc_bind (cc_forIn_range (k := 2) count _ _ fun _ _ ↦ ?_) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h
  exact cc_mono (cc_bind cc_sampleH fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0) (by omega) le_rfl
    fun _ h ↦ h

/-- **A sumcheck is paid by its reads**: each round reads its message before its challenge. -/
theorem cc_sumcheckH (claim : E) (count : ℕ) (h : 2 ≤ count) (equalities : List (Option E)) :
    CC (sumcheckH callKeccak256 claim count equalities) 0 0 fun _ ↦ True := by
  unfold sumcheckH
  refine cc_mono (cc_bind (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ ?_) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h
  exact cc_mono (cc_bind (cc_roundPoly count h _ _) fun _ _ ↦ cc_bind cc_sampleH fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h

theorem cc_countBits (heights : List ℕ) : CC (countBits (m := OracleComp KeccakCalls) heights) 0 0 fun _ ↦ True := by
  unfold countBits
  refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h)
    fun _ _ ↦ cc_pure trivial 0
  exact cc_free (cc_nextInteger _) fun _ _ ↦ cc_free (cc_requireZero _) fun _ _ ↦
    cc_free (cc_requireZero _) fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial 0

theorem cc_tablePart (t : Table) (logHeight : ℕ) (weights : Array E) (beta : E) (w : List E) :
    CC (tablePart (m := OracleComp KeccakCalls) t logHeight weights beta w) 0 0 fun _ ↦ True := by
  unfold tablePart
  refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h)
    fun _ _ ↦ ?_
  · exact cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0
  refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun x _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦
    cc_pure trivial 0
  obtain ⟨pulled, pushed⟩ := x
  repeat (first
    | exact cc_pure (P := fun _ ↦ True) trivial _
    | refine cc_ite _ ?_ ?_
    | refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_)

/-- One step of the walk: a read, a challenge, a part, or a branch (the do-notation's `if` and `match` carry
the rest of the block in each branch). -/
macro "cc_step" : tactic => `(tactic| first
  | with_reducible_and_instances exact cc_pure (P := fun _ ↦ True) trivial _
  | with_reducible_and_instances exact cc_throw_bind _ _ _ _ _
  | with_reducible_and_instances refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_nextScalars _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free cc_nextRoot fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_countBits _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_requireZero _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_map _ (cc_nextScalars _)) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ cc_free (cc_tablePart _ _ _ _ _) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
  | with_reducible_and_instances refine cc_seq (cc_samplesH _) (fun _ _ ↦ ?_) (by omega)
  | with_reducible_and_instances refine cc_seq (cc_map _ (cc_ringEndH _ _)) (fun _ _ ↦ ?_) (by omega)
  | dsimp only
  | split)

theorem cc_zerocheckH (logN k : ℕ) :
    CC (Flock.zerocheckH callKeccak256 logN k) (2 * (logN - k - Flock.nFixed) + 2) 0 fun _ ↦ True := by
  unfold Flock.zerocheckH
  refine cc_seq (cc_samplesH _) (fun _ _ ↦ ?_) (by omega)
  split
  · refine cc_free (cc_nextScalars _) fun _ _ ↦ ?_
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun p _ ↦ ?_
    obtain ⟨zSkip, claim⟩ := p
    refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun q _ ↦ ?_
    obtain ⟨chi, running⟩ := q
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    exact cc_pure trivial _
  · dsimp only
    refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun p _ ↦ ?_
    obtain ⟨zSkip, claim⟩ := p
    refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun q _ ↦ ?_
    obtain ⟨chi, running⟩ := q
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    exact cc_pure trivial _

theorem cc_frontH (logN : ℕ) (variant : Flock.Variant) :
    CC (Flock.frontH callKeccak256 logN variant) (2 * (logN - variant.skip - Flock.nFixed) + 4) 0
      fun _ ↦ True := by
  unfold Flock.frontH
  refine cc_seq (cc_zerocheckH _ _) (fun _ _ ↦ ?_) (by omega)
  repeat cc_step

theorem cc_ringEndH (variant : Flock.Variant) (s : List E) :
    CC (Flock.ringEndH callKeccak256 variant s) 12 0 fun _ ↦ True :=
  cc_seq (cc_samplesH _) (fun _ _ ↦ cc_pure (P := fun _ ↦ True) trivial _) (by simp [Flock.ringMapShifts])

theorem cc_verifyDeferredH (logN : ℕ) (variant : Flock.Variant) :
    CC (Flock.verifyDeferredH callKeccak256 logN variant) (2 * (logN - variant.skip - Flock.nFixed) + 16) 0
      fun _ ↦ True := by
  unfold Flock.verifyDeferredH
  refine cc_seq (cc_frontH _ _) (fun _ _ ↦ ?_) (by omega)
  split
  · dsimp only
    refine cc_seq (cc_map _ (cc_ringEndH _ _)) (fun _ _ ↦ ?_) (by omega)
    exact cc_pure trivial _
  · dsimp only
    refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun _ _ ↦ ?_
    exact cc_pure trivial _

theorem foldl_push_size {X Y A B C : Type} (l : List X) (F : A × B × Array Y × C → X → A × B × Array Y × C)
    (hF : ∀ acc x, (F acc x).2.2.1.size = acc.2.2.1.size + 1) :
    ∀ init, (l.foldl F init).2.2.1.size = init.2.2.1.size + l.length := by
  induction l with
  | nil => intro init; rfl
  | cons x l ih =>
    intro init
    rw [List.foldl_cons, ih, hF, List.length_cons]
    omega

theorem fold_openings_size {Y C : Type} (combined : List (Commitment × Combined)) (values : List E) (bs : C)
    (F : E × E × Array Y × C → (Commitment × Combined) × E → E × E × Array Y × C)
    (hF : ∀ acc x, (F acc x).2.2.1.size = acc.2.2.1.size + 1) :
    ((combined.zip values).foldl F (0, 1, #[], bs)).2.2.1.size ≤ combined.length := by
  rw [foldl_push_size _ F hF, List.length_zip]
  simp

/-- **The batching sumcheck**: `λ`, then rounds paid by their reads; at most one opening per combined claim. -/
theorem cc_batchH (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (pending : Option (Flock.Pending × List E)) :
    CC (batchH callKeccak256 combined layouts bitSlice ringMap pending) 2 0
      fun z ↦ z.1.length ≤ combined.length := by
  unfold batchH
  rcases pending with _ | ⟨p, flockPoint⟩ <;> dsimp only <;> repeat cc_step
  all_goals
    refine cc_pure ?_ _
    simp only [Array.length_toList, Array.size_map]
    refine fold_openings_size _ _ _ _ fun acc x ↦ ?_
    obtain ⟨s1, s2, os, bs⟩ := acc
    obtain ⟨⟨c, claim⟩, v⟩ := x
    simp

/-- The walk's challenges, but the sumchecks' rounds: `α ∈ E^4`, `β`, `γ`, Flock's (its sampled coordinates, `z`,
its `α`, the ring map's six), `t`, `ρ`, `λ`, two blocks each. -/
def walkCost (shape : Shape) (variant : Flock.Variant) : ℕ :=
  2 * (blake2sR1csLogSize + shape.heights.getD opBlake2s 0 - variant.skip - Flock.nFixed) + 34

/-- **The walk of the main line** (Flock deferred, point claims): at most `walkCost` blocks beyond the potential,
and at most three openings. -/
theorem cc_reduceWithH_flockPoint (shape : Shape) (publicWords : List E) (variant : Flock.Variant) :
    CC (reduceWithH callKeccak256 shape publicWords (.flock variant) .point) (walkCost shape variant) 0
      fun r ↦ r.openings.length ≤ 3 := by
  unfold reduceWithH walkCost
  dsimp only
  split
  · exact cc_throw_bind _ _ _ _ _
  · refine cc_free (cc_countBits _) fun _ _ ↦ ?_
    refine cc_free cc_nextRoot fun _ _ ↦ ?_
    refine cc_seq (cc_samplesH _) (fun _ _ ↦ ?_) (by omega)
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_seq (cc_verifyDeferredH _ _) (fun x _ ↦ ?_) (by omega)
    obtain ⟨point, end_, left⟩ := x
    dsimp only
    refine cc_free (cc_pure (P := fun a ↦ a = (some (point, end_, none), some (left, point))) rfl 0)
      fun a ha ↦ ?_
    subst ha
    refine cc_free cc_nextRoot fun _ _ ↦ ?_
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ cc_free (cc_tablePart _ _ _ _ _) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦ ?_
    iterate 7 refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    rcases end_ with _ | (⟨map, target⟩ | ⟨ws, value⟩) <;> dsimp only
    all_goals try split
    all_goals
      try dsimp only
      refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
      refine cc_seq (cc_batchH _ _ _ _ _) (fun z hz ↦ ?_) (by omega)
      obtain ⟨batched, deferred⟩ := z
      dsimp only at hz ⊢
      split <;> exact cc_pure (P := fun r : Reduced ↦ r.openings.length ≤ 3) (hz.trans (List.length_filterMap_le _ _)) _

end Parts


/-! ## The run, the openings, the deployed verifier -/

section Top

open E2ECompleteness.Cost (QC qc_pure)

theorem name_length : name.length = 16 := by decide +kernel

theorem ivTag_length : ivTag.length = 16 := by decide +kernel

theorem shapeBytes_length (s : Shape) : (shapeBytes s).length = 8 := by simp [shapeBytes]

theorem layoutWord_length (s : Shape) (code vars placed : ℕ) : (layoutWord s code vars placed).length = 32 := by
  simp [layoutWord, shapeBytes_length]

theorem layoutWords_length (s : Shape) : (layoutWords s).flatten.length = 160 := by
  simp [layoutWords, layoutWord_length]

theorem layoutWordVars_le (w : List UInt8) : layoutWordVars w ≤ 255 := by
  unfold layoutWordVars
  have := UInt8.toNat_lt (w.getD 24 0)
  omega

/-- Budget can only help a cost without postcondition. -/
theorem CostP.weaken {α : Type} {X : OracleComp KeccakCalls α} {n n' : ℕ} (hX : CostP X n fun _ _ ↦ True)
    (h : n ≤ n') : CostP X n' fun _ _ ↦ True := by
  have h' := costP_of_qc hX.toQC (n' - n)
  rw [show n + (n' - n) = n' by omega] at h'
  exact h'.mono fun _ _ _ ↦ trivial

/-- **The walk** from the start of a stream: the potential is three per byte. -/
theorem costP_walk (shape : Shape) (publicWords : List E) (variant : Flock.Variant) (seed : Digest)
    (stream : Array UInt8) (m : ℕ) :
    CostP ((do
        let r ← reduceWithH callKeccak256 shape publicWords (.flock variant) .point
        finish (m := OracleComp KeccakCalls)
        return r : CM Reduced).run.run (Chan.start seed stream))
      (walkCost shape variant + 3 * stream.size + m) fun z rem ↦
        ∀ a, z.1 = .ok a → a.openings.length ≤ 3 ∧ m ≤ rem := by
  have h := cc_mono (k' := walkCost shape variant) (g' := 0)
    (cc_bind (k₂ := 0) (g₂ := 0) (cc_reduceWithH_flockPoint shape publicWords variant) fun r hr ↦
      cc_free cc_finish fun _ _ ↦ cc_pure (P := fun r : Reduced ↦ r.openings.length ≤ 3) hr 0) (by omega) le_rfl
    fun _ h ↦ h
  have h2 := h (Chan.start seed stream) ⟨le_rfl, Nat.zero_le _⟩ m
  rw [show walkCost shape variant + pot (Chan.start seed stream) + m = walkCost shape variant + 3 * stream.size + m
    by simp [pot, Chan.start]] at h2
  exact h2.mono fun z rem hz a ha ↦ ⟨(hz a ha).1, by have := (hz a ha).2.2; omega⟩

/-- **The run on calldata**: the seed, then the walk; at most three openings, `m` blocks left. -/
theorem costP_runWithH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (variant : Flock.Variant) (m : ℕ) :
    CostP (runWithH callKeccak256 shape iv publicInput stream (.flock variant) .point)
      ((16 + iv.length + publicInput.length) / 136 + 1 + (walkCost shape variant + 3 * stream.size + m))
      fun o rem ↦ ∀ r, o.result = .ok r → r.openings.length ≤ 3 ∧ m ≤ rem := by
  unfold runWithH seedWithH callKeccak256
  rw [costP_query_bind]
  refine ⟨?_, fun seed ↦ ?_⟩
  · show (name ++ iv ++ publicInput).length / 136 + 1 ≤ _
    simp only [List.length_append, name_length]
    omega
  · rw [show (16 + iv.length + publicInput.length) / 136 + 1 + (walkCost shape variant + 3 * stream.size + m) -
        hashBlocks (Sum.inl (name ++ iv ++ publicInput)) = walkCost shape variant + 3 * stream.size + m by
      show _ - ((name ++ iv ++ publicInput).length / 136 + 1) = _
      simp only [List.length_append, name_length]
      omega]
    exact (costP_walk shape _ variant seed stream m).bind fun z rem hz r hr ↦ hz r hr

/-- `PCS_OPEN`'s cost: a claim of at most `255` coordinates (`46` blocks of IV), then the opening's run. -/
def openCost : ℕ := 46 + E2ECompleteness.Cost.vOpen

theorem qc_pcsOpenWithH (vars : ℕ) (hv : vars ≤ 255) (root : Digest) (pt : List E) (value : E)
    (p : LeanVM.Protocol.Compile.Proof) :
    QC (pcsOpenWithH callKeccak256 callKeccakF1600 vars root [⟨pt, value⟩] p) openCost :=
  E2ECompleteness.Cost.cost_openingWithH (plainLayout vars) root _ p
    (by
      show vars - PcsQuotient.laneFold + PcsQuotient.logInvRate ≤ 12 * LeanVM.Protocol.Verifier.costHeight
      simp only [PcsQuotient.laneFold, PcsQuotient.logInvRate, LeanVM.Protocol.Verifier.costHeight]
      omega) 46
    (by
      show 76 + 24 * (1 * (vars + 1)) < 136 * 46
      omega)

theorem qc_forIn_list {γ β : Type} (l : List γ) (b : β) (f : γ → β → OracleComp KeccakCalls (ForInStep β))
    {c : ℕ} (hf : ∀ a s, QC (f a s) c) : QC (forIn l b f) (l.length * c) := by
  induction l generalizing b with
  | nil => exact qc_pure _ _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (hf a b).bind_le (b := l.length * c) (fun s ↦ ?_) (by simp [Nat.succ_mul]; omega)
    cases s with
    | done b => exact qc_pure _ _
    | yield b => exact ih b

/-- **The verifier**: the run, then at most five openings. -/
theorem costP_verifyWithH (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) :
    CostP (verifyWithH callKeccak256 callKeccakF1600 shape iv roots publicInput proof)
      ((16 + iv.length + 32) / 136 + 1 + (walkCost shape flockMain + 3 * proof.stream.size + 5 * openCost))
      fun _ _ ↦ True := by
  unfold verifyWithH
  rw [show 16 + iv.length + 32 = 16 + iv.length + publicInput.toList.length by simp]
  refine CostP.bind (costP_runWithH shape iv publicInput.toList proof.stream flockMain (5 * openCost))
    fun o rem ho ↦ ?_
  split
  · trivial
  · split
    · trivial
    · rename_i r hr
      obtain ⟨hl, hrem⟩ := ho r hr
      refine CostP.weaken (n := 5 * openCost + 0) ((costP_of_qc ?_ 0).mono fun _ _ _ ↦ trivial) (by omega)
      refine (qc_forIn_list (c := openCost) _ _ _ fun x s ↦ ?_).bind_le (b := 2 * openCost) (fun s ↦ ?_) ?_
      · split
        split
        · exact (qc_pcsOpenWithH _ (layoutWordVars_le _) _ _ _ _).bind_le (fun _ ↦ qc_pure _ 0) (by omega)
        · exact qc_pure _ _
      · split
        · exact (qc_pcsOpenWithH _ (layoutWordVars_le _) _ _ _ _).bind_le (fun _ ↦
            (qc_pcsOpenWithH _ (layoutWordVars_le _) _ _ _ _).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) (by omega)
        · exact qc_pure _ _
      · have : r.openings.length * openCost ≤ 3 * openCost := Nat.mul_le_mul_right _ hl
        omega

/-- The contract's IV: the tag, the program's IV, three roots, the shape and the five layout words. -/
def ivCost (D : Deployment) : ℕ := (280 + D.programIv.length) / 136 + 1

/-- **The deployed verifier's block count** on a proof of a stream of at most `S` bytes: the IV, the seed (one
block), the walk, the openings. -/
def verifierCost (D : Deployment) (S : ℕ) : ℕ := ivCost D + 1 + walkCost D.shape flockMain + 3 * S + 5 * openCost

theorem ivInput_length (D : Deployment) (roots : SetupRoots) :
    (ivTag ++ D.programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++ digestBytes roots.b0 ++
      shapeBytes D.shape ++ (layoutWords D.shape).flatten).length = 280 + D.programIv.length := by
  simp only [List.length_append, ivTag_length, len_digestBytes, shapeBytes_length, layoutWords_length]
  omega

/-- **The deployed verifier over the two calls makes at most `verifierCost D S` block calls** on any proof whose
stream has at most `S` bytes, whatever its opening proofs. -/
theorem cost_verifierWithH (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32) (proof : UniProof)
    (S : ℕ) (hS : proof.stream.size ≤ S) :
    Common.QueryCostAtMost (Deployment.verifierWithH callKeccak256 callKeccakF1600 D roots input proof) hashBlocks
      (verifierCost D S) := by
  refine CostP.toQC (Q := fun _ _ ↦ True) ?_
  unfold Deployment.verifierWithH Deployment.ivWithH contractIvWithH callKeccak256
  rw [bind_assoc, costP_query_bind]
  refine ⟨?_, fun d ↦ ?_⟩
  · show (ivTag ++ D.programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
      digestBytes roots.b0 ++ shapeBytes D.shape ++ (layoutWords D.shape).flatten).length / 136 + 1 ≤ _
    rw [ivInput_length]
    unfold verifierCost ivCost
    omega
  · rw [pure_bind]
    refine (costP_verifyWithH D.shape (digestBytes d) roots input proof).weaken ?_
    show _ ≤ verifierCost D S - ((ivTag ++ D.programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
      digestBytes roots.b0 ++ shapeBytes D.shape ++ (layoutWords D.shape).flatten).length / 136 + 1)
    rw [ivInput_length, len_digestBytes]
    unfold verifierCost ivCost
    omega

/-- The setup's block count: the setup stack's tree and `A0`'s and `B0`'s (`5 · 2^(μ − 5)` blocks each). -/
def setupCost (D : Deployment) : ℕ :=
  5 * 2 ^ ((setupLayout D.shape).vars - 6 + 1) + 2 * (5 * 2 ^ (matrixVars - 6 + 1))

/-- **The setup over the two calls makes at most `setupCost D` block calls.** -/
theorem cost_setupTreesWithH (D : Deployment) :
    Common.QueryCostAtMost (setupTreesWithH callKeccak256 callKeccakF1600 D) hashBlocks (setupCost D) := by
  unfold setupTreesWithH setupCost
  exact (E2ECompleteness.Cost.qc_commitWithH _ _).bind_le (fun _ ↦ (E2ECompleteness.Cost.qc_commitWithH _ _).bind_le
    (fun _ ↦ (E2ECompleteness.Cost.qc_commitWithH _ _).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl) (by omega)

end Top

end UniComplete.Cost

/-- info: 'UniComplete.Cost.cost_verifierWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Cost.cost_verifierWithH

/-- info: 'UniComplete.Cost.cost_setupTreesWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Cost.cost_setupTreesWithH
