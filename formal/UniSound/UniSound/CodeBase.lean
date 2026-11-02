-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The loop lemmas extend
-- `formal/FlockSound/FlockSoundUni/Loops.lean` (`repeatM`, `nextScalars_eq`, `samples_eq`).
import UniSound.Fs
import FlockSoundUni.Decode

/-!
# The code-level link's toolkit

Lemmas about channel programs, for every lawful monad, used to put `reduceWith` in the form of a
chain program (`CodeLink.lean`):

* **fixed-length reads** (`fixLen`, `nextScalars_fix`, `nextScalars_add`): a read of `a + b`
  scalars is a read of `a` then of `b`, the first list of length `a`;
* **loops of fixed reads** (`consumeFold`, `forIn_reads`): a `for` loop whose body reads `k x`
  scalars and computes is one read of `Σ k x` scalars, consumed in order;
* **observational equivalence** (`ObsEq`): the same result and, on success, the same channel up to
  the order of the collected zeros (`obsOf`); `obsEq_requireZeros_nextRoot` moves the zeros a
  phase collects after its last challenge past the next root (Flock's tail zeros, collected before
  `C2`'s root, are the `C2` round's zeros in the chain program).
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## Lists of a fixed length -/

/-- A list cut or padded with zeros to length `n`. -/
def fixLen (n : ℕ) (l : List E) : List E := (List.range n).map fun i => l.getD i 0

@[simp] theorem length_fixLen (n : ℕ) (l : List E) : (fixLen n l).length = n := by
  simp [fixLen]

theorem fixLen_zero (l : List E) : fixLen 0 l = [] := by simp [fixLen]

theorem fixLen_succ_cons (n : ℕ) (a : E) (l : List E) : fixLen (n + 1) (a :: l) = a :: fixLen n l := by
  simp [fixLen, List.range_succ_eq_map, Function.comp_def]

theorem fixLen_of_length {n : ℕ} {l : List E} (h : l.length = n) : fixLen n l = l := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [fixLen, List.getD_eq_getElem?_getD, h2]

@[simp] theorem fixLen_fixLen (n : ℕ) (l : List E) : fixLen n (fixLen n l) = fixLen n l :=
  fixLen_of_length (length_fixLen n l)

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem repeatM_fix (act : ChanM m E) : ∀ n, repeatM act n = fixLen n <$> repeatM act n
  | 0 => by simp [FlockSound.Uni.repeatM, fixLen]
  | n + 1 => by
    conv_lhs => rw [FlockSound.Uni.repeatM, repeatM_fix act n]
    simp only [FlockSound.Uni.repeatM, map_bind, map_pure, bind_map_left, fixLen_succ_cons]

/-- A read of `n` scalars gives `n` of them. -/
theorem nextScalars_fix (n : ℕ) : nextScalars (m := m) n = fixLen n <$> nextScalars (m := m) n := by
  rw [nextScalars_eq]
  exact repeatM_fix _ n

/-- `n` draws give `n` challenges. -/
theorem samples_fix (F : KeccakState → m KeccakState) (n : ℕ) :
    samples F n = fixLen n <$> samples F n := by
  rw [samples_eq]
  exact repeatM_fix _ n

theorem nextScalars_zero : nextScalars (m := m) 0 = pure [] := by
  simp [nextScalars_eq, FlockSound.Uni.repeatM]

theorem nextScalars_one : nextScalars (m := m) 1 = (fun x => [x]) <$> nextScalar (m := m) := by
  simp [nextScalars_eq, FlockSound.Uni.repeatM, map_eq_bind_pure_comp]

/-- **A read of `a + b` scalars** is a read of `a`, then of `b`. -/
theorem nextScalars_add (a b : ℕ) : nextScalars (m := m) (a + b) = (do
    let x ← nextScalars (m := m) a
    let y ← nextScalars (m := m) b
    pure (fixLen a x ++ y)) := by
  simp only [nextScalars_eq, repeatM_add]
  conv_lhs => rw [repeatM_fix _ a]
  simp only [bind_map_left]

/-- **`a + b` draws** are `a` draws, then `b`. -/
theorem samples_add (F : KeccakState → m KeccakState) (a b : ℕ) : samples F (a + b) = (do
    let x ← samples F a
    let y ← samples F b
    pure (fixLen a x ++ y)) := by
  simp only [samples_eq, repeatM_add]
  conv_lhs => rw [repeatM_fix _ a]
  simp only [bind_map_left]

theorem samples_one (F : KeccakState → m KeccakState) :
    samples F 1 = (fun x => [x]) <$> sample F := by
  simp [samples_eq, FlockSound.Uni.repeatM, map_eq_bind_pure_comp]

/-! ## Loops of fixed reads -/

/-- **Consume a list of values in order**: each element `x` takes the next `k x` values. -/
def consumeFold {α β : Type} (k : α → ℕ) (g : α → β → List E → β) : List α → β → List E → β
  | [], b, _ => b
  | x :: xs, b, vs => consumeFold k g xs (g x b (vs.take (k x))) (vs.drop (k x))

theorem consumeFold_append {α β : Type} (k : α → ℕ) (g : α → β → List E → β) (x : α) (b : β)
    (xs : List α) (vs ws : List E) (h : vs.length = k x) :
    consumeFold k g (x :: xs) b (vs ++ ws) = consumeFold k g xs (g x b vs) ws := by
  simp [consumeFold, List.take_left' h, List.drop_left' h]

/-- **A loop of fixed reads** is one read, consumed in order. -/
theorem forIn_reads {α β : Type} (k : α → ℕ) (g : α → β → List E → β) :
    ∀ (l : List α) (init : β),
      forIn l init (fun x s => (fun vs => ForInStep.yield (g x s vs)) <$> nextScalars (m := m) (k x)) =
        (fun vs => consumeFold k g l init vs) <$> nextScalars (m := m) (l.map k).sum
  | [], init => by simp [consumeFold, nextScalars_eq, FlockSound.Uni.repeatM]
  | x :: xs, init => by
    rw [List.forIn_cons, List.map_cons, List.sum_cons, nextScalars_add, nextScalars_fix (k x)]
    simp only [bind_map_left, map_bind, map_pure, fixLen_fixLen]
    congr 1
    funext vs
    rw [forIn_reads k g xs]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    congr 1
    funext ws
    rw [consumeFold_append _ _ _ _ _ _ _ (length_fixLen _ _)]

/-! ## Observational equivalence -/

/-- **Observationally equal programs**: from every channel, the same result and, on success, the
same stream, cursor, absorbed bytes, state, challenges and verdict on the zeros (`obsOf`). -/
def ObsEq {α : Type} (p q : ChanM m α) : Prop :=
  ∀ c, obsOf <$> p.run.run c = obsOf <$> q.run.run c

omit [LawfulMonad m] in
theorem ObsEq.of_eq {α : Type} {p q : ChanM m α} (h : p = q) : ObsEq p q := fun _ => by rw [h]

omit [LawfulMonad m] in
theorem ObsEq.trans {α : Type} {p q r : ChanM m α} (h1 : ObsEq p q) (h2 : ObsEq q r) : ObsEq p r :=
  fun c => (h1 c).trans (h2 c)

theorem ObsEq.bind_right {α β : Type} (x : ChanM m β) {f g : β → ChanM m α}
    (h : ∀ b, ObsEq (f b) (g b)) : ObsEq (x >>= f) (x >>= g) := by
  intro c
  simp only [ExceptT.run_bind, StateT.run_bind, map_bind]
  congr 1
  funext p
  rcases p with ⟨r, c'⟩
  cases r with
  | error e => simp [obsOf]
  | ok b => exact h b c'

/-! ## The channel's state operations -/

theorem chan_get_run (c : Chan) : ((get : ChanM m Chan).run.run c) = pure (Except.ok c, c) := by
  have h : (StateT.get : StateT Chan m Chan).run c = pure (c, c) := rfl
  simp [get, getThe, MonadStateOf.get, h]

theorem chan_modify_run (c : Chan) (f : Chan → Chan) :
    ((modify f : ChanM m Unit).run.run c) = pure (Except.ok (), f c) := by
  have h : (StateT.modifyGet (fun s => (PUnit.unit, f s)) : StateT Chan m PUnit).run c =
    pure (PUnit.unit, f c) := rfl
  simp [modify, modifyGet, MonadStateOf.modifyGet, h]

theorem chan_set_run (c c' : Chan) :
    ((set c' : ChanM m PUnit).run.run c) = pure (Except.ok ⟨⟩, c') := by
  have h : (StateT.set c' : StateT Chan m PUnit).run c = pure (PUnit.unit, c') := rfl
  simp [set, MonadStateOf.set, h]

/-! ## Moving collected zeros past a root -/

/-- The channel with the values `zs` collected. -/
def collectZ (c : Chan) (zs : List E) : Chan := { c with zeros := zs.foldl Array.push c.zeros }

theorem requireZeros_run (zs : List E) (c : Chan) :
    (ChainProg.requireZeros (m := m) zs).run.run c = pure (.ok (), collectZ c zs) := by
  induction zs generalizing c with
  | nil => simp [ChainProg.requireZeros, collectZ]
  | cons z zs ih =>
    simp only [ChainProg.requireZeros, ExceptT.run_bind, StateT.run_bind, requireZero,
      chan_modify_run, pure_bind]
    rw [ih]
    rfl

theorem takeBytes_run (n : ℕ) (c : Chan) :
    (takeBytes (m := m) n).run.run c =
      if c.cursor + n ≤ c.data.size then
        pure (.ok (c.data.extract c.cursor (c.cursor + n)), { c with cursor := c.cursor + n })
      else pure (.error .streamExhausted, c) := by
  simp only [takeBytes, ExceptT.run_bind, StateT.run_bind, chan_get_run, pure_bind]
  by_cases h : c.cursor + n ≤ c.data.size
  · simp only [h, ite_true, ExceptT.run_bind, StateT.run_bind, chan_set_run, pure_bind]
    rfl
  · simp only [h, ite_false]
    rfl

theorem takeBytes_run_collect (n : ℕ) (c : Chan) (zs : List E) :
    (takeBytes (m := m) n).run.run (collectZ c zs) =
      (fun p => (p.1, collectZ p.2 zs)) <$> (takeBytes (m := m) n).run.run c := by
  rw [takeBytes_run, takeBytes_run]
  by_cases h : c.cursor + n ≤ c.data.size
  · have h' : (collectZ c zs).cursor + n ≤ (collectZ c zs).data.size := h
    rw [ite_eq_left h', ite_eq_left h, map_pure]
    rfl
  · have h' : ¬ (collectZ c zs).cursor + n ≤ (collectZ c zs).data.size := h
    rw [ite_eq_right h', ite_eq_right h, map_pure]

theorem nextRoot_run_collect (c : Chan) (zs : List E) :
    (nextRoot (m := m)).run.run (collectZ c zs) =
      (fun p => (p.1, collectZ p.2 zs)) <$> (nextRoot (m := m)).run.run c := by
  simp only [nextRoot, ExceptT.run_bind, StateT.run_bind, takeBytes_run_collect, bind_map_left,
    map_bind]
  congr 1
  funext p
  rcases p with ⟨r, c1⟩
  cases r with
  | error e => simp
  | ok lo =>
    simp only [StateT.run_bind, takeBytes_run_collect, bind_map_left, map_bind]
    congr 1
    funext q
    rcases q with ⟨r2, c2⟩
    cases r2 <;> simp

/-- **Zeros collected before a root are collected after it**, observationally. -/
theorem obsEq_requireZeros_nextRoot {α : Type} (zs : List E) (k : E × E → ChanM m α) :
    ObsEq (ChainProg.requireZeros zs >>= fun _ => nextRoot >>= k)
      (nextRoot >>= fun r => ChainProg.requireZeros zs >>= fun _ => k r) := by
  intro c
  simp only [ExceptT.run_bind, StateT.run_bind, requireZeros_run, pure_bind]
  rw [nextRoot_run_collect]
  simp only [bind_map_left, map_bind]
  congr 1
  funext p
  rcases p with ⟨r, c1⟩
  cases r with
  | error e => simp [obsOf]
  | ok rt => simp [requireZeros_run]

end Monad

end UniSound
