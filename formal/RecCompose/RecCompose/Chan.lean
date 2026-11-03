-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The channel is `formal/UniStatement`'s
-- (`UniStatement/Transcript.lean`).
import RecCompose.Holds

/-!
# The channel's reads, in any monad

`UniStatement`'s channel over any lawful monad: `takeBytes`, `finish` are pure functions of the channel
(`takeBytes_run`, `finish_run`), `sample` keeps the data and the cursor whatever Keccak-256 answers (`sample_run`).
`Reads X n V`: from any channel, `X` keeps the data, succeeds when `n` bytes are left, and when it does it has
advanced the cursor by `n` and its value satisfies `V` of the data and the cursor it started from; it composes through
binds (`reads_bind`) and `for` loops (`reads_forIn`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

@[simp] theorem chan_run_get (c : Chan) : ((get : ChanM m Chan).run).run c = pure (.ok c, c) := by
  show (ExceptT.lift (get : StateT Chan m Chan)).run.run c = _
  simp [ExceptT.run_lift]

@[simp] theorem chan_run_set (c c' : Chan) : ((set c' : ChanM m PUnit).run).run c = pure (.ok ⟨⟩, c') := by
  show (ExceptT.lift (set c' : StateT Chan m PUnit)).run.run c = _
  simp [ExceptT.run_lift]

@[simp] theorem chan_run_modify (c : Chan) (f : Chan → Chan) :
    ((modify f : ChanM m PUnit).run).run c = pure (.ok ⟨⟩, f c) := by
  show (ExceptT.lift (modify f : StateT Chan m PUnit)).run.run c = _
  simp [ExceptT.run_lift]

@[simp] theorem chan_run_liftM {α : Type} (x : m α) (c : Chan) :
    ((liftM x : ChanM m α).run).run c = (fun a ↦ (.ok a, c)) <$> x := by
  show (ExceptT.lift (StateT.lift x : StateT Chan m α)).run.run c = _
  simp [ExceptT.run_lift]

theorem takeBytes_run (n : ℕ) (c : Chan) :
    ((takeBytes (m := m) n).run).run c =
      pure (if c.cursor + n ≤ c.data.size then
        (.ok (c.data.extract c.cursor (c.cursor + n)), { c with cursor := c.cursor + n })
      else (.error .streamExhausted, c)) := by
  unfold takeBytes
  split_ifs with h <;> simp [h, Except.map]

theorem finish_run (c : Chan) :
    ((finish (m := m)).run).run c =
      pure (if c.cursor = c.data.size then (.ok (), c) else (.error .streamNotConsumed, c)) := by
  unfold finish
  split_ifs with h <;> simp [h]

/-- The channel after a challenge with the new state `st`. -/
def sampled (c : Chan) (st : Digest) : Chan :=
  ⟨c.data, c.cursor, c.cursor, st, c.challenges.push (PcsQuotient.Transcript.challengeOf st), c.zeros⟩

theorem sample_run (F : KeccakState → m KeccakState) (c : Chan) :
    ((sample F).run).run c =
      (fun st ↦ (.ok (PcsQuotient.Transcript.challengeOf st), sampled c st)) <$>
        keccak256With F (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList) := by
  unfold sample sampled
  simp [Except.map]

/-! ## Reading `n` bytes -/

/-- **`X` reads `n` bytes**: from any channel it keeps the data; when it succeeds it has advanced the cursor by `n`
and its value satisfies `V` of the data and the cursor it started from; it succeeds when `n` bytes are left. -/
def Reads {α : Type} (X : ChanM m α) (n : ℕ) (V : Array UInt8 → ℕ → α → Prop) : Prop :=
  ∀ c : Chan, Holds ((X.run).run c) fun p ↦ p.2.data = c.data ∧
    (∀ a, p.1 = .ok a → p.2.cursor = c.cursor + n ∧ V c.data c.cursor a) ∧
    (c.cursor + n ≤ c.data.size → ∃ a, p.1 = .ok a)

theorem reads_pure {α : Type} (a : α) : Reads (pure a : ChanM m α) 0 fun _ _ b ↦ b = a := by
  intro c
  have e : ((pure a : ChanM m α).run).run c = pure (.ok a, c) := by simp
  rw [e]
  refine holds_pure ⟨rfl, fun b hb ↦ ?_, fun _ ↦ ⟨a, rfl⟩⟩
  simp only [Except.ok.injEq] at hb
  exact ⟨by simp, hb.symm⟩

theorem reads_mono {α : Type} {X : ChanM m α} {n n' : ℕ} {V V' : Array UInt8 → ℕ → α → Prop} (hX : Reads X n V)
    (hn : n = n') (hV : ∀ d cur a, V d cur a → V' d cur a) : Reads X n' V' := by
  subst hn
  intro c
  refine holds_mono (hX c) ?_
  rintro p ⟨hd, hok, hfit⟩
  exact ⟨hd, fun a ha ↦ ⟨(hok a ha).1, hV _ _ _ (hok a ha).2⟩, hfit⟩

theorem reads_bind {α β : Type} {X : ChanM m α} {k : α → ChanM m β} {n n' : ℕ} {V : Array UInt8 → ℕ → α → Prop}
    {U : α → Array UInt8 → ℕ → β → Prop} (hX : Reads X n V)
    (hk : ∀ a, (∃ d cur, V d cur a) → Reads (k a) n' (U a)) :
    Reads (X >>= k) (n + n') fun d cur b ↦ ∃ a, V d cur a ∧ U a d (cur + n) b := by
  intro c
  rw [ExceptT.run_bind, StateT.run_bind]
  refine holds_bind (hX c) ?_
  rintro ⟨e, c'⟩ ⟨hd, hok, hfit⟩
  cases e with
  | error err =>
    simp only [StateT.run_pure]
    refine holds_pure ⟨hd, fun b hb ↦ absurd hb (by simp), fun hf ↦ ?_⟩
    obtain ⟨a, ha⟩ := hfit (by omega)
    exact absurd ha (by simp)
  | ok a =>
    simp only
    obtain ⟨hcur, hV⟩ := hok a rfl
    refine holds_mono (hk a ⟨_, _, hV⟩ c') ?_
    rintro ⟨e', c''⟩ ⟨hd', hok', hfit'⟩
    refine ⟨hd'.trans hd, fun b hb ↦ ?_, fun hf ↦ hfit' (by simp only at hcur hd ⊢; rw [hcur, hd]; omega)⟩
    obtain ⟨hc'', hU⟩ := hok' b hb
    simp only at hcur hd hc'' hU ⊢
    refine ⟨by rw [hc'', hcur]; omega, a, hV, ?_⟩
    rw [← hd, ← hcur]; exact hU

theorem reads_map {α β : Type} {X : ChanM m α} {n : ℕ} {V : Array UInt8 → ℕ → α → Prop} (hX : Reads X n V)
    (f : α → β) : Reads (f <$> X) n fun d cur b ↦ ∃ a, V d cur a ∧ b = f a := by
  rw [map_eq_bind_pure_comp]
  refine reads_mono (reads_bind hX fun a _ ↦ reads_pure (f a)) (Nat.add_zero n) ?_
  rintro d cur b ⟨a, hV, hb⟩
  exact ⟨a, hV, hb⟩

theorem reads_takeBytes (n : ℕ) :
    Reads (takeBytes (m := m) n) n fun d cur b ↦ b = d.extract cur (cur + n) := by
  intro c
  rw [takeBytes_run]
  split_ifs with h
  · refine holds_pure ⟨rfl, fun a ha ↦ ?_, fun _ ↦ ⟨_, rfl⟩⟩
    simp only [Except.ok.injEq] at ha
    exact ⟨rfl, ha.symm⟩
  · exact holds_pure ⟨rfl, fun a ha ↦ absurd ha (by simp), fun h' ↦ absurd h' h⟩

theorem reads_sample (F : KeccakState → m KeccakState) : Reads (sample F) 0 fun _ _ _ ↦ True := by
  intro c
  rw [sample_run]
  exact holds_map (holds_true _) fun st _ ↦ ⟨rfl, fun a _ ↦ ⟨rfl, trivial⟩, fun _ ↦ ⟨_, rfl⟩⟩

/-! ## The reads -/

/-- The scalar `next_scalar` reads at `cur`. -/
def scalarAt (d : Array UInt8) (cur : ℕ) : E :=
  let b := d.extract cur (cur + 24)
  eNew (beWordAt b 16) (beWordAt b 8) (beWordAt b 0)

/-- The integer `next_integer(bytes)` reads at `cur`. -/
def integerAt (d : Array UInt8) (cur bytes : ℕ) : ℕ :=
  (d.extract cur (cur + bytes)).foldl (fun acc x ↦ acc * 256 + x.toNat) 0

/-- A root's half at `cur`. -/
def halfAt (d : Array UInt8) (cur : ℕ) : E :=
  let b := d.extract cur (cur + 16)
  eNew (beWordAt b 8) (beWordAt b 0) 0

theorem reads_nextScalar : Reads (nextScalar (m := m)) 24 fun d cur x ↦ x = scalarAt d cur := by
  unfold nextScalar
  refine reads_mono (reads_bind (reads_takeBytes 24) fun b _ ↦ reads_pure _) rfl ?_
  rintro d cur x ⟨b, hb, hx⟩
  subst hb hx
  rfl

theorem reads_nextInteger (bytes : ℕ) :
    Reads (nextInteger (m := m) bytes) bytes fun d cur x ↦ x = integerAt d cur bytes := by
  unfold nextInteger
  refine reads_mono (reads_bind (reads_takeBytes bytes) fun b _ ↦ reads_pure _) rfl ?_
  rintro d cur x ⟨b, hb, hx⟩
  subst hb hx
  rfl

theorem reads_nextRoot : Reads (nextRoot (m := m)) 32 fun d cur x ↦ x = (halfAt d cur, halfAt d (cur + 16)) := by
  unfold nextRoot
  refine reads_mono (reads_bind (reads_takeBytes 16) fun lo _ ↦
    reads_bind (reads_takeBytes 16) fun hi _ ↦ reads_pure _) rfl ?_
  rintro d cur x ⟨lo, hlo, hi, hhi, hx⟩
  subst hlo hhi hx
  rfl

/-! ## `for` loops -/

/-- The value of a `for` loop over a list whose body reads `k x` bytes and yields `g d cur x b`. -/
def foldReads {γ β : Type} (k : γ → ℕ) (g : Array UInt8 → ℕ → γ → β → β) (d : Array UInt8) :
    ℕ → List γ → β → β
  | _, [], b => b
  | cur, x :: l, b => foldReads k g d (cur + k x) l (g d cur x b)

theorem reads_forIn {γ β : Type} (k : γ → ℕ) (g : Array UInt8 → ℕ → γ → β → β) (f : γ → β → ChanM m (ForInStep β))
    (hf : ∀ x b, Reads (f x b) (k x) fun d cur s ↦ s = .yield (g d cur x b)) :
    ∀ (l : List γ) (b : β), Reads (forIn l b f) ((l.map k).sum) fun d cur r ↦ r = foldReads k g d cur l b
  | [], b => by
    simp only [List.forIn_nil, List.map_nil, List.sum_nil, foldReads]
    exact reads_pure b
  | x :: l, b => by
    rw [List.forIn_cons]
    refine reads_mono (reads_bind (n' := (l.map k).sum)
      (U := fun s d cur r ↦ ∃ b', s = .yield b' ∧ r = foldReads k g d cur l b')
      (hf x b) fun s ⟨d, cur, hs⟩ ↦ ?_) (by simp [List.sum_cons]) ?_
    · subst hs
      simp only
      exact reads_mono (reads_forIn k g f hf l _) rfl fun d cur r hr ↦ ⟨_, rfl, hr⟩
    · rintro d cur r ⟨s, hs, b', hb', hr⟩
      subst hs
      cases hb'
      simp only [foldReads]
      exact hr

theorem reads_nextScalars (count : ℕ) : Reads (nextScalars (m := m) count) (24 * count) fun _ _ _ ↦ True := by
  unfold nextScalars
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine reads_mono (reads_bind (reads_forIn (fun _ ↦ 24) (fun d cur _ (out : Array E) ↦ out.push (scalarAt d cur))
    _ (fun x b ↦ ?_) _ _) fun out _ ↦ reads_pure _) ?_ fun _ _ _ _ ↦ trivial
  · refine reads_mono (reads_bind reads_nextScalar fun y _ ↦ reads_pure _) rfl ?_
    rintro d cur s ⟨y, hy, hs⟩
    subst hy hs
    rfl
  · simp [Nat.mul_comm]

end Generic

end RecCompose
