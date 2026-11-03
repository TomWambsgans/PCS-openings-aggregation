-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The channel is `formal/UniStatement`'s
-- (`Transcript.lean`); the toolkit is `CodeBase.lean`'s.
import UniSound.CodeTables

/-!
# The zeros a run collects are seen only by their verdict

A channel program never reads the zeros it collects: it pushes them, and the verdict (`obsOf`) reads
only whether they all vanish. **`Obl p`**: the run of `p`, its channel's zeros reduced to their verdict
(`normC`: `#[]` if they all vanish, else `#[1]`), depends only on the starting channel so reduced. It
holds of the channel's reads and draws (`takeBytes`, `nextRoot`, `nextScalars`, `samples`), of
`requireZeros`, and of every chain program's rounds and run (`obl_runRounds`, `obl_run`). Hence **a
zero pushed where the zeros so far vanish only if it does** is invisible to the verdict
(`obsOf_requireZeros_of`).
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
  FlockSound.Uni

/-! ## Channels alike but for their zeros -/

/-- A list of zeros reduced to its verdict: `#[]` if they all vanish, else `#[1]`. -/
def zf (z : Array E) : Array E := if z.all (· == 0) then #[] else #[1]

theorem all_one_E : (#[1] : Array E).all (· == 0) = false := by
  rw [show (#[1] : Array E) = (#[] : Array E).push 1 from rfl, Array.all_push]
  simp

theorem zf_all (z : Array E) : (zf z).all (· == 0) = z.all (· == 0) := by
  unfold zf
  split_ifs with h
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    rw [h, all_one_E]

theorem zf_zf (z : Array E) : zf (zf z) = zf z := by
  show (if (zf z).all (· == 0) then #[] else #[1]) = zf z
  rw [zf_all]
  rfl

theorem zf_push (z : Array E) (x : E) : zf (z.push x) = zf ((zf z).push x) := by
  show (if (z.push x).all (· == 0) then #[] else #[1]) =
    (if ((zf z).push x).all (· == 0) then #[] else #[1])
  rw [Array.all_push, Array.all_push, zf_all]

/-- **The channel with its zeros reduced to their verdict.** -/
def normC (c : Chan) : Chan := { c with zeros := zf c.zeros }

theorem normC_all (c : Chan) : (normC c).zeros.all (· == 0) = c.zeros.all (· == 0) := zf_all _

theorem normC_normC (c : Chan) : normC (normC c) = normC c := by
  simp only [normC, zf_zf]

/-- A result with its channel's zeros reduced. -/
def nrmP {α : Type} (q : Except UniError α × Chan) : Except UniError α × Chan := (q.1, normC q.2)

theorem obsOf_nrmP {α : Type} (q : Except UniError α × Chan) : obsOf (nrmP q) = obsOf q := by
  rcases q with ⟨r, c⟩
  cases r <;> simp [obsOf, nrmP, normC, zf_all]

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **Zeros-oblivious**: the run, its channel's zeros reduced, depends only on the channel with its
zeros reduced. -/
def Obl {α : Type} (p : ChanM m α) : Prop :=
  ∀ c, nrmP <$> p.run.run c = nrmP <$> p.run.run (normC c)

omit [LawfulMonad m] in
theorem Obl.eq {α : Type} {p : ChanM m α} (h : Obl p) {c c' : Chan} (hc : normC c = normC c') :
    nrmP <$> p.run.run c = nrmP <$> p.run.run c' := by
  rw [h c, h c', hc]

theorem obl_pure {α : Type} (a : α) : Obl (pure a : ChanM m α) := by
  intro c
  simp [nrmP, normC_normC]

theorem obl_bind {α β : Type} {x : ChanM m β} {f : β → ChanM m α} (hx : Obl x) (hf : ∀ b, Obl (f b)) :
    Obl (x >>= f) := by
  have key : ∀ d, nrmP <$> (x >>= f).run.run d = (nrmP <$> x.run.run d) >>= fun p =>
      match p.1 with
      | .ok b => nrmP <$> (f b).run.run p.2
      | .error e => pure (.error e, p.2) := by
    intro d
    simp only [ExceptT.run_bind, StateT.run_bind, map_bind, bind_map_left]
    congr 1
    funext p
    rcases p with ⟨r, c1⟩
    cases r with
    | error e => simp [nrmP]
    | ok b =>
      simp only [nrmP]
      exact hf b c1
  intro c
  rw [key c, key (normC c), hx c, hx (normC c), normC_normC]

theorem obl_map {α β : Type} (f : β → α) {x : ChanM m β} (hx : Obl x) : Obl (f <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact obl_bind hx fun _ => obl_pure _

theorem obl_takeBytes (n : ℕ) : Obl (takeBytes (m := m) n) := by
  intro c
  rw [takeBytes_run, takeBytes_run]
  show _ = nrmP <$> (if c.cursor + n ≤ c.data.size then _ else _)
  split_ifs <;> simp only [map_pure, nrmP]
  · congr 2
    simp only [normC, zf_zf]
  · rw [normC_normC]

theorem obl_nextRoot : Obl (nextRoot (m := m)) := by
  unfold nextRoot
  exact obl_bind (obl_takeBytes _) fun _ => obl_bind (obl_takeBytes _) fun _ => obl_pure _

theorem obl_nextScalar : Obl (nextScalar (m := m)) := by
  unfold nextScalar
  exact obl_bind (obl_takeBytes _) fun _ => obl_pure _

theorem obl_repeatM {α : Type} {act : ChanM m α} (h : Obl act) : ∀ n, Obl (repeatM act n)
  | 0 => obl_pure _
  | n + 1 => obl_bind h fun _ => obl_bind (obl_repeatM h n) fun _ => obl_pure _

theorem obl_nextScalars (n : ℕ) : Obl (nextScalars (m := m) n) := by
  rw [nextScalars_eq]
  exact obl_repeatM obl_nextScalar n

/-- The channel after a draw of the state `st`. -/
def sampled (c : Chan) (st : Digest) : Chan :=
  { c with absorbed := c.cursor, state := st, challenges := c.challenges.push (PcsQuotient.Transcript.challengeOf st) }

theorem sample_run (F : KeccakState → m KeccakState) (c : Chan) :
    (sample F).run.run c =
      (fun st : Digest => ((Except.ok (PcsQuotient.Transcript.challengeOf st) : Except UniError E),
        sampled c st)) <$>
        keccak256With F (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList) := by
  unfold sample
  simp only [ExceptT.run_bind, StateT.run_bind, chan_get_run, pure_bind]
  simp [StateT.run_lift, MonadLift.monadLift, ExceptT.lift, liftM, monadLift, chan_set_run,
    map_eq_bind_pure_comp, sampled]

theorem obl_sample (F : KeccakState → m KeccakState) : Obl (sample F) := by
  intro c
  rw [sample_run, sample_run]
  simp only [Functor.map_map, nrmP]
  congr 1
  funext st
  congr 1
  simp only [sampled, normC, zf_zf]

theorem obl_samples (F : KeccakState → m KeccakState) (n : ℕ) : Obl (samples F n) := by
  rw [samples_eq]
  exact obl_repeatM (obl_sample F) n

theorem obl_requireZero (z : E) : Obl (requireZero (m := m) z) := by
  intro c
  unfold requireZero
  rw [chan_modify_run, chan_modify_run]
  simp only [map_pure, nrmP]
  congr 2
  simp only [normC]
  rw [zf_push]

theorem obl_requireZeros : ∀ zs : List E, Obl (ChainProg.requireZeros (m := m) zs)
  | [] => obl_pure _
  | z :: zs => obl_bind (obl_requireZero z) fun _ => obl_requireZeros zs

theorem obl_rootRead (b : Bool) : Obl (rootRead (m := m) b) := by
  unfold rootRead
  split
  · exact obl_map _ obl_nextRoot
  · exact obl_pure _

/-- **A chain program's rounds never read the zeros.** -/
theorem obl_runRounds {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) :
    ∀ (rs : List Compose.RoundSpec) (d : Done), Obl (P.runRounds F rs d)
  | [], d => by
    rw [ChainProg.runRounds]
    exact obl_pure _
  | s :: rs, d => by
    rw [runRounds_cons]
    exact obl_bind (obl_rootRead _) fun _ => obl_bind (obl_nextScalars _) fun _ =>
      obl_bind (obl_requireZeros _) fun _ => obl_bind (obl_samples F _) fun _ => obl_runRounds P F rs _

/-- **A chain program's run never reads the zeros.** -/
theorem obl_run {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) : Obl (P.run F) := by
  unfold ChainProg.run
  exact obl_bind (obl_runRounds P F _ _) fun _ => obl_bind (obl_nextScalars _) fun _ =>
    obl_bind (obl_requireZeros _) fun _ => obl_pure _

/-- **A zero is invisible to the verdict** where the zeros so far vanish only if it does. -/
theorem obsOf_requireZeros_of {α : Type} (z : E) (G : ChanM m α) (hG : Obl G) (c : Chan)
    (hz : c.zeros.all (· == 0) = true → z = 0) :
    obsOf <$> (ChainProg.requireZeros [z] >>= fun _ => G).run.run c = obsOf <$> G.run.run c := by
  simp only [ExceptT.run_bind, StateT.run_bind, requireZeros_run, pure_bind]
  have hn : normC (collectZ c [z]) = normC c := by
    simp only [normC, collectZ, List.foldl_cons, List.foldl_nil]
    congr 1
    unfold zf
    rw [Array.all_push]
    by_cases h : c.zeros.all (· == 0) = true
    · rw [hz h, h]
      simp
    · simp only [Bool.not_eq_true] at h
      simp [h]
  have e1 : ∀ d, obsOf <$> G.run.run d = obsOf <$> (nrmP <$> G.run.run d) := fun d => by
    simp only [Functor.map_map, obsOf_nrmP]
  show obsOf <$> G.run.run (collectZ c [z]) = _
  rw [e1, e1 c, hG.eq hn]

/-! ## A zero in round `0` -/

/-- **A chain program with the zeros `zs` in round `0`** (before its first challenges), else its
own. -/
def ChainProg.withHead {α : Type} (P : ChainProg α) (zs : List E) : ChainProg α :=
  { P with zeros := fun done msg => if done = [] then zs else P.zeros done msg }

omit [LawfulMonad m] in
theorem withHead_zeros_ne {α : Type} (P : ChainProg α) (zs : List E) {d : Done} (hd : d ≠ []) :
    (P.withHead zs).zeros d = P.zeros d := by
  funext msg
  simp [ChainProg.withHead, hd]

omit [LawfulMonad m] in
theorem runRounds_withHead {α : Type} (P : ChainProg α) (zs : List E) (F : KeccakState → m KeccakState) :
    ∀ (rs : List Compose.RoundSpec) (d : Done), d ≠ [] →
      (P.withHead zs).runRounds F rs d = P.runRounds F rs d
  | [], d, _ => by simp [ChainProg.runRounds]
  | s :: rs, d, hd => by
    rw [runRounds_cons, runRounds_cons, withHead_zeros_ne P zs hd]
    congr 1
    funext root
    congr 1
    funext vals
    congr 1
    funext _
    congr 1
    funext chs
    exact runRounds_withHead P zs F rs _ (by simp)

/-- **The zeros of round `0` moved before its root**: with round `0` a root and no scalars, and no
zeros of its own there, the program with `zs` in round `0` is `zs` then the program,
observationally. -/
theorem obsEq_withHead {α : Type} (P : ChainProg α) (zs : List E) (F : KeccakState → m KeccakState)
    (ns : ℕ) (rs : List Compose.RoundSpec) (hr : P.rounds = ⟨true, 0, ns⟩ :: rs)
    (hz : P.zeros [] = fun _ => []) :
    ObsEq ((P.withHead zs).run F) (ChainProg.requireZeros zs >>= fun _ => P.run F) := by
  have hz' : (P.withHead zs).zeros [] = fun _ => zs := by
    funext msg
    simp [ChainProg.withHead]
  have hr' : (P.withHead zs).rounds = ⟨true, 0, ns⟩ :: rs := hr
  unfold ChainProg.run
  rw [hr, hr', runRounds_cons, runRounds_cons, hz, hz']
  simp only [rootRead, ite_true, nextScalars_zero, bind_map_left, pure_bind, bind_assoc,
    ChainProg.requireZeros]
  have hrr : ∀ (r : E × E) (chs : List E),
      (P.withHead zs).runRounds F rs ([] ++ [((some r, []), chs)]) =
        P.runRounds F rs ([] ++ [((some r, []), chs)]) := fun r chs =>
    runRounds_withHead P zs F rs _ (by simp)
  simp only [hrr]
  exact fun c => (obsEq_requireZeros_nextRoot zs _ c).symm

/-! ## The row counts' checks -/

/-- **The zeros all vanish.** -/
def Zall (c : Chan) : Prop := c.zeros.all (· == 0) = true

theorem run_bind_of {α β : Type} (x : ChanM m α) (f : α → ChanM m β) (c : Chan)
    (q : Except UniError α × Chan) (h : x.run.run c = pure q) :
    (x >>= f).run.run c = match q with
      | (.ok a, c1) => (f a).run.run c1
      | (.error e, c1) => pure (.error e, c1) := by
  simp only [ExceptT.run_bind, StateT.run_bind, h, pure_bind]
  rcases q with ⟨r, c1⟩
  cases r <;> rfl

/-- The count four bytes read at the cursor make. -/
def cnt4 (c : Chan) : ℕ := (c.data.extract c.cursor (c.cursor + 4)).foldl (fun acc x => acc * 256 + x.toNat) 0

/-- The channel after a row count's read and its two checks. -/
def rcChan (c : Chan) (r : ℕ) : Chan :=
  { c with
    cursor := c.cursor + 4
    zeros := (c.zeros.push (intBits (cnt4 c) (r + 1) 32)).push (intBits (cnt4 c) r 1 * intBits (cnt4 c) 0 r) }

theorem readCount_run (r : ℕ) (c : Chan) :
    (readCount (m := m) r).run.run c =
      if c.cursor + 4 ≤ c.data.size then pure (.ok (cnt4 c), rcChan c r)
      else pure (.error .streamExhausted, c) := by
  unfold readCount nextInteger
  simp only [ExceptT.run_bind, StateT.run_bind, takeBytes_run]
  split_ifs <;> simp [requireZero, chan_modify_run, cnt4, rcChan]

theorem eK_eq_zero {w : UInt64} (h : eK w = 0) : w = 0 := by
  unfold eK eNew at h
  rw [show K.ofLane 0 = 0 from rfl] at h
  have h1 := congrArg K.lane ((ofLimbs_eq_zero_iff _).mp h)
  exact h1

theorem intBits_eq_zero {n s w : ℕ} (h : intBits n s w = 0) : (n >>> s) % 2 ^ min w 64 = 0 := by
  have h1 := congrArg UInt64.toNat (eK_eq_zero h)
  have hlt : (n >>> s) % 2 ^ min w 64 < 2 ^ 64 :=
    (Nat.mod_lt _ (by positivity)).trans_le (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _))
  rwa [UInt64.toNat_ofNat_of_lt' hlt] at h1

/-- **A count passing `readCounts`' two checks is at most `2^r`.** -/
theorem le_of_checks {count r : ℕ} (hc : count < 2 ^ 32) (h1 : intBits count (r + 1) 32 = 0)
    (h2 : intBits count r 1 * intBits count 0 r = 0) : count ≤ 2 ^ r := by
  have e1 := intBits_eq_zero h1
  rw [show min 32 64 = 32 from rfl, Nat.shiftRight_eq_div_pow] at e1
  have hd : count / 2 ^ (r + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hc
  rw [Nat.mod_eq_of_lt hd, Nat.div_eq_zero_iff_lt (by positivity)] at e1
  have hq : count / 2 ^ r < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [pow_succ] at e1
    linarith
  have hdm := Nat.div_add_mod count (2 ^ r)
  have hml := Nat.mod_lt count (show 0 < 2 ^ r by positivity)
  rcases mul_eq_zero.mp h2 with h | h
  · have e2 := intBits_eq_zero h
    rw [show min 1 64 = 1 from rfl, Nat.shiftRight_eq_div_pow, pow_one] at e2
    have hq0 : count / 2 ^ r = 0 := by rwa [Nat.mod_eq_of_lt hq] at e2
    rw [hq0, mul_zero, zero_add] at hdm
    omega
  · have e2 := intBits_eq_zero h
    rw [Nat.shiftRight_zero] at e2
    by_cases hr : r ≤ 64
    · rw [min_eq_left hr] at e2
      rw [e2, add_zero] at hdm
      interval_cases hqv : count / 2 ^ r <;> omega
    · have : 2 ^ 32 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

theorem foldl_bytes_lt : ∀ (l : List UInt8) (acc : ℕ),
    l.foldl (fun acc x => acc * 256 + x.toNat) acc < (acc + 1) * 256 ^ l.length
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, List.length_cons, pow_succ]
    have ih := foldl_bytes_lt l (acc * 256 + x.toNat)
    have hx : x.toNat < 256 := (UInt8.toNat_lt x).trans_le (by decide)
    calc _ < (acc * 256 + x.toNat + 1) * 256 ^ l.length := ih
      _ ≤ ((acc + 1) * 256) * 256 ^ l.length := Nat.mul_le_mul_right _ (by omega)
      _ = (acc + 1) * (256 ^ l.length * 256) := by ring

theorem cnt4_lt (c : Chan) (h : c.cursor + 4 ≤ c.data.size) : cnt4 c < 2 ^ 32 := by
  unfold cnt4
  rw [← Array.foldl_toList]
  have := foldl_bytes_lt (c.data.extract c.cursor (c.cursor + 4)).toList 0
  rw [Array.length_toList, Array.size_extract] at this
  rw [show min (c.cursor + 4) c.data.size - c.cursor = 4 by omega] at this
  simpa using this

/-- **The row counts' checks** (`readCounts`): a function of the channel; on success as many counts as
heights, and the zeros vanish only if those before did and each count is at most `2^r`. -/
theorem readCounts_spec : ∀ (hs : List ℕ) (c : Chan), ∃ q, (readCounts (m := m) hs).run.run c = pure q ∧
    ∀ rows, q.1 = .ok rows → rows.length = hs.length ∧
      (Zall q.2 → Zall c ∧ ∀ j < hs.length, rows.getD j 0 ≤ 2 ^ hs.getD j 0)
  | [], c => ⟨(.ok [], c), by simp [readCounts_eq], fun rows h => by
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨rfl, fun hz => ⟨hz, fun j hj => absurd hj (Nat.not_lt_zero _)⟩⟩⟩
  | r :: hs, c => by
    rw [readCounts_eq, List.mapM_cons]
    by_cases hb : c.cursor + 4 ≤ c.data.size
    · have h0 := readCount_run (m := m) r c
      simp only [hb, ↓reduceIte] at h0
      rw [run_bind_of _ _ c _ h0]
      dsimp only
      obtain ⟨q1, hq1, hs1⟩ := readCounts_spec hs (rcChan c r)
      rw [readCounts_eq] at hq1
      rw [run_bind_of _ _ _ q1 hq1]
      rcases q1 with ⟨r1, c1⟩
      cases r1 with
      | error e => exact ⟨(.error e, c1), rfl, fun rows h => by cases h⟩
      | ok rows =>
        refine ⟨(.ok (cnt4 c :: rows), c1), by simp, fun rows' h => ?_⟩
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨hl, hz⟩ := hs1 rows rfl
        refine ⟨by simp [hl], fun hz1 => ?_⟩
        obtain ⟨hz2, hb2⟩ := hz hz1
        unfold Zall rcChan at hz2
        simp only [Array.all_push, Bool.and_eq_true, beq_iff_eq] at hz2
        obtain ⟨⟨hz3, e1⟩, e2⟩ := hz2
        refine ⟨hz3, fun j hj => ?_⟩
        rcases j with _ | j
        · exact le_of_checks (cnt4_lt c hb) e1 e2
        · simpa using hb2 j (by simpa using hj)
    · have h0 := readCount_run (m := m) r c
      simp only [hb, ↓reduceIte] at h0
      rw [run_bind_of _ _ c _ h0]
      exact ⟨(.error .streamExhausted, c), rfl, fun rows h => by cases h⟩

end Monad

end UniSound
