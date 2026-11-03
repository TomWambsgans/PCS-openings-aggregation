-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The program is `formal/UniStatement`'s `batchFs` at
-- `.rec3` (`Rec.lean`: `sampleNarrow`, `sumcheckPairsDrawn`, `pairRoundPoly`, `sumcheckDrawn`); the toolkit extends
-- `CodeBase.lean`'s and `CodeZeros.lean`'s (the main line's).
import UniSound.FinalLink
import UniSound.Rec3.Fs3
import UniSound.Rec3.Pairs

/-!
# π1-rec3's batch as reads, narrow draws and a result; the channel's challenges forgotten

**Narrow draws and the chain program.** π1-rec3's batch draws its challenges by `sampleNarrow`, which records the
narrow value `narrowE x` in the channel's `challenges` where a chain program's `samples` records the raw draw `x`.
Nothing the verifier computes reads `challenges` back, so a program that draws `narrowE x` is, up to that record, the
program that draws `x` and applies `narrowE` itself. Here:

* **`ChEq p q`**: from channels equal but for their `challenges` (`clrCh`), the runs of `p` and `q` are equal but for
  theirs (`clrP`); **`ChObl p`** (`ChEq p p`): `p` never reads `challenges`. It holds of the channel's reads, draws
  (`sample`, `sampleNarrow`) and zeros, and is closed under `bind` (`ChEq.bind`, `ChEq.bind_map`);
  **`chEq_sampleNarrow`**: `sampleNarrow F` is `narrowE <$> sample F` for `ChEq`.
* **`ObsEq3`**: equal `obsOf3` (the code-level link's observation, `Rec3/Fs3.lean`): from `ObsEq` (`ObsEq.obsEq3`)
  and from `ChEq` (`ChEq.obsEq3`).
* **The batch's rounds** (`readRoundN`, `readRoundsN`): `nv` scalars and one narrow draw a round;
  **`chEq_readRoundsN`**: they are the chain's rounds (`readRounds`) with each record's challenge narrowed
  (`narrowRec`).
* **`batchFs3_eq`**: `batchFs F .rec3 … none` is `λ`, the rounds `batchNvs vars` (`vars / 2` pairs of `8` scalars,
  `vars % 2` plain rounds of `2`), the stacks' values, the terminal zero and the result, a function of the records
  (`batchPureW id`: the pairs' claims `claimAfterPairs`, `pairCoeffs`, the point `pointAfter3`, the narrow values
  read as they are); **`batchPureW_narrow`**: on the records narrowed, it is `batchPureW narrowE` on the raw ones,
  the PIOP's reading (`BatchState3 cantorBeta1 narrowE`).
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash FlockSound.Uni

/-! ## Channels alike but for their challenges -/

/-- **The channel with its record of challenges cleared.** -/
def clrCh (c : Chan) : Chan := { c with challenges := #[] }

/-- A result with its channel's challenges cleared. -/
def clrP {α : Type} (q : Except UniError α × Chan) : Except UniError α × Chan := (q.1, clrCh q.2)

theorem clrCh_clrCh (c : Chan) : clrCh (clrCh c) = clrCh c := rfl

theorem clrCh_ext {c c' : Chan} (h : clrCh c = clrCh c') :
    c.data = c'.data ∧ c.cursor = c'.cursor ∧ c.absorbed = c'.absorbed ∧ c.state = c'.state ∧
      c.zeros = c'.zeros := by
  have h1 := congrArg Chan.data h
  have h2 := congrArg Chan.cursor h
  have h3 := congrArg Chan.absorbed h
  have h4 := congrArg Chan.state h
  have h5 := congrArg Chan.zeros h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- `obsOf3` does not read the channel's challenges. -/
theorem obsOf3_clrP {α : Type} (x : Except UniError α × Chan) : obsOf3 (clrP x) = obsOf3 x := by
  rcases x with ⟨r, c⟩
  cases r <;> rfl

/-- `obsOf3` is a function of `obsOf`. -/
def obsProj {α : Type} (o : Except UniError α × Option (Array UInt8 × ℕ × ℕ × Digest × Array E × Bool)) :
    Except UniError α × Option (Array UInt8 × ℕ × ℕ × Digest × Bool) :=
  (o.1, o.2.map fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2))

theorem obsOf3_eq_proj {α : Type} (x : Except UniError α × Chan) : obsOf3 x = obsProj (obsOf x) := by
  rcases x with ⟨r, c⟩
  cases r <;> rfl

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **Programs equal but for the challenges' record**: from channels equal but for their challenges, equal runs but
for theirs. -/
def ChEq {α : Type} (p q : ChanM m α) : Prop :=
  ∀ c c', clrCh c = clrCh c' → clrP <$> p.run.run c = clrP <$> q.run.run c'

/-- **A program that never reads the challenges' record.** -/
abbrev ChObl {α : Type} (p : ChanM m α) : Prop := ChEq p p

omit [LawfulMonad m] in
theorem ChEq.trans {α : Type} {p q r : ChanM m α} (h1 : ChEq p q) (h2 : ChEq q r) : ChEq p r :=
  fun c c' h => (h1 c c' h).trans (h2 c' c' rfl)

omit [LawfulMonad m] in
theorem ChEq.of_eq {α : Type} {p q : ChanM m α} (h : p = q) (hp : ChObl p) : ChEq p q := by
  subst h
  exact hp

omit [LawfulMonad m] in
theorem ChEq.symm {α : Type} {p q : ChanM m α} (h : ChEq p q) : ChEq q p :=
  fun c c' hc => (h c' c hc.symm).symm

theorem chEq_key {α β : Type} {x : ChanM m β} {f : β → ChanM m α} (hf : ∀ b, ChObl (f b)) (d : Chan) :
    clrP <$> (x >>= f).run.run d = (clrP <$> x.run.run d) >>= fun p => match p.1 with
      | .ok b => clrP <$> (f b).run.run p.2
      | .error e => pure (.error e, p.2) := by
  simp only [ExceptT.run_bind, StateT.run_bind, map_bind, bind_map_left]
  congr 1
  funext p
  rcases p with ⟨r, c1⟩
  cases r with
  | error e => simp [clrP]
  | ok b => exact hf b c1 (clrCh c1) rfl

/-- **`bind` of programs equal but for the challenges.** -/
theorem ChEq.bind {α β : Type} {x y : ChanM m β} {f g : β → ChanM m α} (hx : ChEq x y)
    (hf : ∀ b, ChEq (f b) (g b)) (hff : ∀ b, ChObl (f b)) (hgg : ∀ b, ChObl (g b)) :
    ChEq (x >>= f) (y >>= g) := by
  intro c c' h
  rw [chEq_key hff c, chEq_key hgg c', hx c c' h]
  congr 1
  funext p
  rcases p with ⟨r, c1⟩
  cases r with
  | error e => rfl
  | ok b => exact hf b c1 c1 rfl

theorem chObl_bind {α β : Type} {x : ChanM m β} {f : β → ChanM m α} (hx : ChObl x) (hf : ∀ b, ChObl (f b)) :
    ChObl (x >>= f) :=
  ChEq.bind hx hf hf hf

/-- **`bind` through a reading**: `x` is `φ <$> y` but for the challenges, and the continuations agree along `φ`. -/
theorem ChEq.bind_map {α β γ : Type} {x : ChanM m β} {y : ChanM m γ} {φ : γ → β} {f : β → ChanM m α}
    {g : γ → ChanM m α} (hx : ChEq x (φ <$> y)) (hf : ∀ b, ChEq (f (φ b)) (g b)) (hff : ∀ b, ChObl (f b))
    (hgg : ∀ b, ChObl (g b)) (hy : ChObl y) : ChEq (x >>= f) (y >>= g) := by
  have h1 : ChEq (x >>= f) ((φ <$> y) >>= f) := ChEq.bind hx hff hff hff
  rw [bind_map_left] at h1
  exact h1.trans (ChEq.bind hy hf (fun b => hff (φ b)) hgg)

theorem chObl_pure {α : Type} (a : α) : ChObl (pure a : ChanM m α) := by
  intro c c' h
  simp only [ExceptT.run_pure, StateT.run_pure, map_pure, clrP]
  rw [h]

theorem chObl_map {α β : Type} (f : β → α) {x : ChanM m β} (hx : ChObl x) : ChObl (f <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact chObl_bind hx fun _ => chObl_pure _

theorem chObl_takeBytes (n : ℕ) : ChObl (takeBytes (m := m) n) := by
  intro c c' h
  obtain ⟨hd, hc, ha, hs, hz⟩ := clrCh_ext h
  rw [takeBytes_run, takeBytes_run, hd, hc]
  split_ifs
  · simp only [map_pure, clrP, clrCh]
    rw [ha, hs, hz]
  · simp only [map_pure, clrP]
    rw [h]

theorem chObl_nextScalar : ChObl (nextScalar (m := m)) := by
  unfold nextScalar
  exact chObl_bind (chObl_takeBytes _) fun _ => chObl_pure _

theorem chObl_nextRoot : ChObl (nextRoot (m := m)) := by
  unfold nextRoot
  exact chObl_bind (chObl_takeBytes _) fun _ => chObl_bind (chObl_takeBytes _) fun _ => chObl_pure _

theorem chObl_repeatM {α : Type} {act : ChanM m α} (h : ChObl act) : ∀ n, ChObl (repeatM act n)
  | 0 => chObl_pure _
  | n + 1 => chObl_bind h fun _ => chObl_bind (chObl_repeatM h n) fun _ => chObl_pure _

theorem chObl_nextScalars (n : ℕ) : ChObl (nextScalars (m := m) n) := by
  rw [nextScalars_eq]
  exact chObl_repeatM chObl_nextScalar n

theorem chObl_sample (F : KeccakState → m KeccakState) : ChObl (sample F) := by
  intro c c' h
  obtain ⟨hd, hc, ha, hs, hz⟩ := clrCh_ext h
  rw [sample_run, sample_run, hd, hc, ha, hs]
  simp only [Functor.map_map, clrP]
  congr 1
  funext st
  simp only [sampled, clrCh]
  rw [hd, hc, hz]

theorem chObl_samples (F : KeccakState → m KeccakState) (n : ℕ) : ChObl (samples F n) := by
  rw [samples_eq]
  exact chObl_repeatM (chObl_sample F) n

theorem chObl_requireZero (z : E) : ChObl (requireZero (m := m) z) := by
  intro c c' h
  obtain ⟨hd, hc, ha, hs, hz⟩ := clrCh_ext h
  unfold requireZero
  rw [chan_modify_run, chan_modify_run]
  simp only [map_pure, clrP, clrCh]
  rw [hd, hc, ha, hs, hz]

theorem chObl_requireZeros : ∀ zs : List E, ChObl (ChainProg.requireZeros (m := m) zs)
  | [] => chObl_pure _
  | z :: zs => chObl_bind (chObl_requireZero z) fun _ => chObl_requireZeros zs

/-! ## The narrow draw -/

/-- The channel after a narrow draw of the state `st`. -/
def sampledN (c : Chan) (st : Digest) : Chan :=
  { c with
    absorbed := c.cursor
    state := st
    challenges := c.challenges.push (narrowE (PcsQuotient.Transcript.challengeOf st)) }

theorem sampleNarrow_run (F : KeccakState → m KeccakState) (c : Chan) :
    (sampleNarrow F).run.run c =
      (fun st : Digest => ((Except.ok (narrowE (PcsQuotient.Transcript.challengeOf st)) : Except UniError E),
        sampledN c st)) <$>
        keccak256With F (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList) := by
  unfold sampleNarrow
  simp only [ExceptT.run_bind, StateT.run_bind, chan_get_run, pure_bind]
  simp [StateT.run_lift, MonadLift.monadLift, ExceptT.lift, liftM, monadLift, chan_set_run,
    map_eq_bind_pure_comp, sampledN]

/-- **The narrow draw is the raw draw narrowed**, but for the challenges' record. -/
theorem chEq_sampleNarrow (F : KeccakState → m KeccakState) : ChEq (sampleNarrow F) (narrowE <$> sample F) := by
  intro c c' h
  obtain ⟨hd, hc, ha, hs, hz⟩ := clrCh_ext h
  rw [sampleNarrow_run, ExceptT.run_map, StateT.run_map, sample_run, hd, hc, ha, hs]
  simp only [Functor.map_map, clrP]
  congr 1
  funext st
  simp only [sampledN, sampled, clrCh, Except.map]
  rw [hd, hc, hz]

theorem chObl_sampleNarrow (F : KeccakState → m KeccakState) : ChObl (sampleNarrow F) :=
  (chEq_sampleNarrow F).trans (chEq_sampleNarrow F).symm

/-! ## Observations without the challenges -/

/-- **Programs alike for `obsOf3`.** -/
def ObsEq3 {α : Type} (p q : ChanM m α) : Prop :=
  ∀ c, obsOf3 <$> p.run.run c = obsOf3 <$> q.run.run c

omit [LawfulMonad m] in
theorem ObsEq3.trans {α : Type} {p q r : ChanM m α} (h1 : ObsEq3 p q) (h2 : ObsEq3 q r) : ObsEq3 p r :=
  fun c => (h1 c).trans (h2 c)

omit [LawfulMonad m] in
theorem ObsEq3.of_eq {α : Type} {p q : ChanM m α} (h : p = q) : ObsEq3 p q := fun _ => by rw [h]

theorem ObsEq.obsEq3 {α : Type} {p q : ChanM m α} (h : ObsEq p q) : ObsEq3 p q := fun c => by
  have e : ∀ x : ChanM m α, obsOf3 <$> x.run.run c = obsProj <$> (obsOf <$> x.run.run c) := fun x => by
    simp only [Functor.map_map]
    congr 1
    funext y
    exact obsOf3_eq_proj y
  rw [e, e, h c]

theorem ChEq.obsEq3 {α : Type} {p q : ChanM m α} (h : ChEq p q) : ObsEq3 p q := fun c => by
  have e : ∀ x : ChanM m α, obsOf3 <$> x.run.run c = obsOf3 <$> (clrP <$> x.run.run c) := fun x => by
    simp only [Functor.map_map, obsOf3_clrP]
  rw [e, e, h c c rfl]

theorem ObsEq3.bind_right {α β : Type} (x : ChanM m β) {f g : β → ChanM m α}
    (h : ∀ b, ObsEq3 (f b) (g b)) : ObsEq3 (x >>= f) (x >>= g) := by
  intro c
  simp only [ExceptT.run_bind, StateT.run_bind, map_bind]
  congr 1
  funext p
  rcases p with ⟨r, c'⟩
  cases r with
  | error e => simp [obsOf3]
  | ok b => exact h b c'

theorem ObsEq3.bind_eq {α β : Type} {x y : ChanM m β} {f g : β → ChanM m α} (h : x = y)
    (hf : ∀ b, ObsEq3 (f b) (g b)) : ObsEq3 (x >>= f) (y >>= g) := by
  subst h
  exact ObsEq3.bind_right x hf

/-! ## The batch's rounds -/

/-- **A narrow round of `nv` scalars**: its scalars, then one narrow draw. -/
def readRoundN (F : KeccakState → m KeccakState) (nv : ℕ) : ChanM m (UMsg × List E) := do
  let vals ← nextScalars (m := m) nv
  let z ← sampleNarrow F
  pure ((none, vals), [z])

/-- The narrow rounds, read one after the other. -/
def readRoundsN (F : KeccakState → m KeccakState) : List ℕ → ChanM m Done
  | [] => pure []
  | nv :: nvs => do
    let r ← readRoundN F nv
    let d ← readRoundsN F nvs
    pure (r :: d)

/-- **A record with its challenge narrowed.** -/
def narrowRec (x : UMsg × List E) : UMsg × List E := (x.1, [narrowE (x.2.headD 0)])

theorem chObl_readRoundN (F : KeccakState → m KeccakState) (nv : ℕ) : ChObl (readRoundN F nv) :=
  chObl_bind (chObl_nextScalars _) fun _ => chObl_bind (chObl_sampleNarrow F) fun _ => chObl_pure _

theorem chObl_readRoundsN (F : KeccakState → m KeccakState) : ∀ nvs : List ℕ, ChObl (readRoundsN F nvs)
  | [] => chObl_pure _
  | _ :: nvs => chObl_bind (chObl_readRoundN F _) fun _ =>
      chObl_bind (chObl_readRoundsN F nvs) fun _ => chObl_pure _

theorem chObl_readRound (F : KeccakState → m KeccakState) (s : Compose.RoundSpec) : ChObl (readRound F s) :=
  chObl_bind (chObl_nextScalars _) fun _ => chObl_bind (chObl_samples F _) fun _ => chObl_pure _

theorem chObl_readRounds (F : KeccakState → m KeccakState) :
    ∀ rs : List Compose.RoundSpec, ChObl (readRounds F rs)
  | [] => chObl_pure _
  | _ :: rs => chObl_bind (chObl_readRound F _) fun _ =>
      chObl_bind (chObl_readRounds F rs) fun _ => chObl_pure _

/-- **A narrow round is the chain's round, its challenge narrowed.** -/
theorem chEq_readRoundN (F : KeccakState → m KeccakState) (nv : ℕ) :
    ChEq (readRoundN F nv) (narrowRec <$> readRound F ⟨false, nv, 0⟩) := by
  have e : narrowRec <$> readRound F ⟨false, nv, 0⟩ = (do
      let vals ← nextScalars (m := m) nv
      let z ← narrowE <$> sample F
      pure ((none, vals), [z])) := by
    simp only [readRound, Nat.zero_add, samples_one, map_bind, bind_map_left, map_pure, narrowRec,
      List.headD_cons]
  rw [e]
  exact ChEq.bind (chObl_nextScalars _)
    (fun _ => ChEq.bind (chEq_sampleNarrow F) (fun _ => chObl_pure _) (fun _ => chObl_pure _)
      (fun _ => chObl_pure _))
    (fun _ => chObl_bind (chObl_sampleNarrow F) fun _ => chObl_pure _)
    (fun _ => chObl_bind (chObl_map _ (chObl_sample F)) fun _ => chObl_pure _)

/-- **The narrow rounds are the chain's rounds, their challenges narrowed.** -/
theorem chEq_readRoundsN (F : KeccakState → m KeccakState) : ∀ nvs : List ℕ,
    ChEq (readRoundsN F nvs) ((List.map narrowRec) <$> readRounds F (nvs.map fun nv => ⟨false, nv, 0⟩))
  | [] => by
    simp only [readRoundsN, List.map_nil, readRounds, map_pure]
    exact chObl_pure _
  | nv :: nvs => by
    have e : (List.map narrowRec) <$> readRounds F ((nv :: nvs).map fun nv => ⟨false, nv, 0⟩) =
        readRound F ⟨false, nv, 0⟩ >>= fun r =>
          ((List.map narrowRec) <$> readRounds F (nvs.map fun nv => ⟨false, nv, 0⟩)) >>= fun d =>
            pure (narrowRec r :: d) := by
      simp only [List.map_cons, readRounds, map_bind, bind_map_left, map_pure]
    rw [e]
    refine ChEq.bind_map (chEq_readRoundN F nv) (fun r => ?_)
      (fun _ => chObl_bind (chObl_readRoundsN F nvs) fun _ => chObl_pure _)
      (fun _ => chObl_bind (chObl_map _ (chObl_readRounds F _)) fun _ => chObl_pure _) (chObl_readRound F _)
    exact ChEq.bind (chEq_readRoundsN F nvs) (fun _ => chObl_pure _) (fun _ => chObl_pure _)
      (fun _ => chObl_pure _)

theorem readRoundsN_append (F : KeccakState → m KeccakState) (a b : List ℕ) :
    readRoundsN F (a ++ b) = (do
      let x ← readRoundsN F a
      let y ← readRoundsN F b
      pure (x ++ y)) := by
  induction a with
  | nil => simp [readRoundsN]
  | cons s a ih => simp only [List.cons_append, readRoundsN, ih, bind_assoc, pure_bind]

/-- **The narrow rounds complete one record each.** -/
theorem readRoundsN_fix (F : KeccakState → m KeccakState) :
    ∀ nvs : List ℕ, readRoundsN F nvs = (fun d => fixDone nvs.length d) <$> readRoundsN F nvs
  | [] => by simp [readRoundsN, fixDone]
  | nv :: nvs => by
    conv_lhs => rw [readRoundsN, readRoundsN_fix F nvs]
    simp only [readRoundsN, map_bind, map_pure, bind_map_left, List.length_cons, fixDone_succ_cons]

end Monad

/-! ## The batch's result from its records -/

/-- **The batch's rounds**: `vars / 2` pairs of `8` scalars, then `vars % 2` plain rounds of `2`. -/
def batchNvs (vars : ℕ) : List ℕ := List.replicate (vars / 2) 8 ++ List.replicate (vars % 2) 2

theorem batchNvs_odd (np : ℕ) : batchNvs (2 * np + 1) = List.replicate np 8 ++ [2] := by
  unfold batchNvs
  rw [show (2 * np + 1) / 2 = np by omega, show (2 * np + 1) % 2 = 1 by omega]
  rfl

/-- **What π1-rec3's batch computes** from `λ`, its records `brs` (each challenge read through `nw`) and the stacks'
values `tl`: the terminal zero `sum + last` and the point claims, the pairs' and the plain rounds' claims and point
`claimAfter3`, `pointAfter3` (at `vars / 2` pairs). -/
def batchPureW (nw : E → E) (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (lambda : E) (brs : Done) (tl : List E) :
    List E × List (Commitment × Opening) :=
  let fo := batchFold combined layouts bitSlice ringMap lambda
    (pointAfter3 cantorBeta1 nw (varsOf layouts / 2) (roundsOf brs)) (tl.take combined.length)
  ([fo.1 + claimAfter3 nw (varsOf layouts / 2) (batchTarget combined lambda).1 (roundsOf brs)], fo.2.2.1.toList)

/-! ### Narrowed records -/

/-- A round's record with its challenge narrowed, as the PIOP reads it. -/
def narrowRd (x : List E × List E) : List E × List E := (x.1, [narrowE (x.2.headD 0)])

theorem roundsOf_narrow (brs : Done) : roundsOf (brs.map narrowRec) = (roundsOf brs).map narrowRd := by
  simp [roundsOf, narrowRec, narrowRd]

theorem claimAfterPairs_narrow : ∀ (c : E) (rs : List (List E × List E)),
    claimAfterPairs id c (rs.map narrowRd) = claimAfterPairs narrowE c rs
  | _, [] => rfl
  | _, _ :: rs => claimAfterPairs_narrow _ rs

theorem pointAfterPairs_narrow (b : E) : ∀ rs : List (List E × List E),
    pointAfterPairs b id (rs.map narrowRd) = pointAfterPairs b narrowE rs
  | [] => rfl
  | x :: rs => by
    simp only [List.map_cons, pointAfterPairs, pointAfterPairs_narrow b rs]
    rfl

theorem claimAfterN_narrow : ∀ (c : E) (rs : List (List E × List E)),
    claimAfterN id c (rs.map narrowRd) = claimAfterN narrowE c rs
  | _, [] => rfl
  | _, _ :: rs => claimAfterN_narrow _ rs

theorem pointAfterN_narrow (rs : List (List E × List E)) :
    pointAfterN id (rs.map narrowRd) = pointAfterN narrowE rs := by
  simp [pointAfterN, narrowRd]

theorem claimAfter3_narrow (np : ℕ) (c : E) (rs : List (List E × List E)) :
    claimAfter3 id np c (rs.map narrowRd) = claimAfter3 narrowE np c rs := by
  unfold claimAfter3
  rw [← List.map_take, ← List.map_drop, claimAfterPairs_narrow, claimAfterN_narrow]

theorem pointAfter3_narrow (b : E) (np : ℕ) (rs : List (List E × List E)) :
    pointAfter3 b id np (rs.map narrowRd) = pointAfter3 b narrowE np rs := by
  unfold pointAfter3
  rw [← List.map_take, ← List.map_drop, pointAfterPairs_narrow, pointAfterN_narrow]

/-- **The batch's result on narrowed records is the PIOP's reading of the raw ones.** -/
theorem batchPureW_narrow (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (lambda : E) (brs : Done) (tl : List E) :
    batchPureW id combined layouts bitSlice ringMap lambda (brs.map narrowRec) tl =
      batchPureW narrowE combined layouts bitSlice ringMap lambda brs tl := by
  unfold batchPureW
  rw [roundsOf_narrow, claimAfter3_narrow, pointAfter3_narrow]

/-! ## The batch's code -/

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem fixLen_two (v : List E) : fixLen 2 v = [v.getD 0 0, v.getD 1 0] := by
  simp [fixLen, List.range_succ]

theorem decodeMsg_none_fix (c : E) (v : List E) :
    decodeMsg c none (fixLen 2 v) = roundCoeffs c ((fixLen 2 v).getD 0 0) ((fixLen 2 v).getD 1 0) := by
  rw [fixLen_two, decodeMsg_none_two]
  rfl

/-- **The pairs' loop** (`sumcheckPairsDrawn`'s `for`, its body `f`): its rounds' reads and narrow draws, the
point, the challenges and the claim a function of the records. -/
theorem pairs_loop (F : KeccakState → m KeccakState)
    (f : ℕ → Array E × Array E × E → ChanM m (ForInStep (Array E × Array E × E)))
    (hf : ∀ x s, f x s = (do
        let message ← pairRoundPoly (m := m) 2 s.2.2
        let z ← sampleDrawn F true
        pure (ForInStep.yield (s.1 ++ (UniStatement.pairPoint z).toArray, s.2.1.push z, polyEval message z)))) :
    ∀ (l : List ℕ) (pt chs : Array E) (cl : E),
    forIn l (pt, chs, cl) f =
      (fun d => ((pt.toList ++ pointAfterPairs cantorBeta1 id (roundsOf d)).toArray,
        (chs.toList ++ d.map fun x => x.2.headD 0).toArray, claimAfterPairs id cl (roundsOf d))) <$>
        readRoundsN F (List.replicate l.length 8)
  | [], pt, chs, cl => by
    simp [readRoundsN, roundsOf, pointAfterPairs, claimAfterPairs]
  | x :: l, pt, chs, cl => by
    rw [List.forIn_cons, hf x (pt, chs, cl), List.length_cons, List.replicate_succ, readRoundsN, readRoundN,
      show nextScalars (m := m) 8 = _ from nextScalars_add 3 5]
    simp only [pairRoundPoly, sampleDrawn, bind_assoc, pure_bind, map_bind, Nat.reduceMul, Nat.reduceSub]
    rw [nextScalars_fix 3, nextScalars_fix 5]
    simp only [bind_map_left, fixLen_fixLen]
    refine bind_congr fun a => bind_congr fun b => bind_congr fun z => ?_
    rw [pairs_loop F f hf l]
    simp only [map_pure]
    rw [map_eq_bind_pure_comp]
    refine bind_congr fun d => ?_
    rw [pairCoeffs_eq_rust _ _ _ (length_fixLen _ _) (length_fixLen _ _)]
    simp [roundsOf, pointAfterPairs, claimAfterPairs, pairPoint_cantorBeta1, List.append_assoc]

/-- **The last plain round** (`sumcheckDrawn` of one round, narrow): its reads and its draw. -/
theorem last_round (F : KeccakState → m KeccakState) (cl : E) :
    sumcheckDrawn F cl (2 + 1) [none] true =
      (fun d => (pointAfterN id (roundsOf d), claimAfterN id cl (roundsOf d))) <$> readRoundsN F [2] := by
  unfold sumcheckDrawn
  simp only [List.forIn_cons, List.forIn_nil, roundPoly_eq, sampleDrawn, readRoundsN, readRoundN, bind_assoc,
    map_bind, bind_map_left, pure_bind, map_pure, Nat.reduceAdd]
  rw [nextScalars_fix 2]
  simp only [bind_map_left]
  refine bind_congr fun v => bind_congr fun z => ?_
  rw [decodeMsg_none_fix]
  simp [roundsOf, pointAfterN, claimAfterN]

/-- **The paired batch's sumcheck** (`sumcheckPairsDrawn` at degree `2`, narrow): its point and last claim are a
function of the rounds' records, `vars / 2` pairs then `vars % 2` plain rounds. -/
theorem sumcheckPairsDrawn_eq (F : KeccakState → m KeccakState) (target : E) (vars : ℕ) :
    (fun x => (x.1, x.2.2)) <$> sumcheckPairsDrawn F target 2 vars true =
      (fun d => (pointAfter3 cantorBeta1 id (vars / 2) (roundsOf d),
        claimAfter3 id (vars / 2) target (roundsOf d))) <$> readRoundsN F (batchNvs vars) := by
  unfold sumcheckPairsDrawn
  simp only [forIn_range_eq]
  rw [pairs_loop F _ (fun _ _ => rfl) (List.range' 0 (vars / 2)), List.length_range', batchNvs,
    readRoundsN_append]
  rw [readRoundsN_fix F (List.replicate (vars / 2) 8)]
  simp only [map_bind, bind_map_left, List.length_replicate]
  congr 1
  funext d
  have hd : (roundsOf (fixDone (vars / 2) d)).length = vars / 2 := by simp [roundsOf]
  rcases Nat.mod_two_eq_zero_or_one vars with h | h
  · rw [h]
    simp only [show ¬ (0 = 1) by omega, ite_false, List.replicate_zero, readRoundsN, map_pure, pure_bind,
      List.append_nil]
    simp only [claimAfter3, pointAfter3, List.take_of_length_le hd.le, List.drop_of_length_le hd.le,
      claimAfterN, pointAfterN, List.map_nil, List.append_nil, List.nil_append]
  · rw [h]
    simp only [ite_true, List.replicate_one, last_round, map_bind, bind_map_left, map_pure]
    refine bind_congr fun e => ?_
    have e1 : roundsOf (fixDone (vars / 2) d ++ e) = roundsOf (fixDone (vars / 2) d) ++ roundsOf e := by
      simp [roundsOf]
    simp only [List.nil_append, Array.toList_append, claimAfter3, pointAfter3, e1, List.take_left' hd,
      List.drop_left' hd]

/-- **π1-rec3's batch** (`batchFs F .rec3`, no pending matrices): `λ`, the rounds `batchNvs vars`, the stacks'
values, the terminal zero, the result (`batchPureW id`). -/
theorem batchFs3_eq (F : KeccakState → m KeccakState) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (bitSlice : Option Combined) (ringMap : Option (List E)) :
    batchFs F .rec3 combined layouts bitSlice ringMap none = (do
      let lambda ← sample F
      let brs ← readRoundsN F (batchNvs (varsOf layouts))
      let tl ← nextScalars (m := m) combined.length
      ChainProg.requireZeros (batchPureW id combined layouts bitSlice ringMap lambda brs tl).1
      pure ((batchPureW id combined layouts bitSlice ringMap lambda brs tl).2, none)) := by
  unfold batchFs
  refine bind_congr fun lambda => ?_
  have hv : (layouts.map (·.2.vars)).foldl max 0 = varsOf layouts := rfl
  simp only [hv]
  rw [← bind_assoc, bind_pure_comp, sumcheckPairsDrawn_eq, bind_map_left]
  refine bind_congr fun brs => ?_
  rw [nextScalars_fix combined.length]
  simp only [bind_map_left, pure_bind]
  refine bind_congr fun values => ?_
  have ht : (fixLen combined.length values).take combined.length = fixLen combined.length values :=
    List.take_of_length_le (by rw [length_fixLen])
  simp [batchPureW, batchFold, batchTarget, layoutOf, varsOf, ChainProg.requireZeros, ht]

end Monad

end UniSound
