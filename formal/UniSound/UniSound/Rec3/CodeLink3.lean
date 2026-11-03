-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The program is `formal/UniStatement`'s `reduceWithFs`
-- at `.rec3` with the walk (`Rec.lean`); the proof follows `CodeLink.lean`'s (the main line's), Flock's phase cited
-- through `FlockSound3.link`.
import UniSound.Rec3.CodeBatch3

/-!
# The code-level link at π1-rec3: `reduceWithFs … .rec3 true` is a chain program (`UniCode3`)

**`uniCode3 D F3 hκ np hV : UniCode3 D F3 valsCount np`** (and `uniCode3At` at any `nV = valsCount`): after the row
counts, `reduceWithFs` at the deployment's shape, π1-rec3 (`.rec3`, the walk, point claims) is the chain program
`main3Prog` on `rec3Rounds F3.prog.rounds valsCount np`, with a tail of three, up to `obsOf3`, for every deployment
whose batch has `2 np + 1` variables (`hV`). Its rounds:

* `C1`'s root and **three** challenges `c, β, γ` (`drawRun .rec3 4` is one draw and `squares c 4`);
* Flock's rounds (`F3.link`: `Flock.verifyWalkedFs` is Flock's chain program; its zeros, the walk's, are the main
  program's there, its tail zeros the `C2` round's);
* `C2`'s root and `t`; the `valsCount` values at `t` (as the main line's) and `ρ, λ`;
* the batch's `np` pair rounds (`8` scalars, one draw) and its last plain round (`2` scalars, one draw): **the chain
  draws `x`, the program reads `narrowE x`** (`batchPureW narrowE`), where the verifier draws `narrowE x` itself
  (`sampleNarrow`); the two agree up to the channel's record of the challenges (`chEq_readRoundsN`), which `obsOf3`
  does not keep;

then the three stacks' values, the terminal zero `sum + last` collected (`batchPureW`), and the result (`main3Out`:
no matrices' claim). **`uniCode3_roots`**: the result names the roots of rounds `0` and `nF + 1` (`rfl`), the form
the Fiat–Shamir layer's `UniOutRoots` takes.
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## The program -/

/-- **Flock's claim at π1-rec3** (step 7: the walked Flock's point and end), as the main line's `flockClaim` reads
it (no pending reduction). -/
def flockClaim3 (rels : Array Relation) (fl : List E × Flock.End) :
    Array Relation × List Relation × Option (List E) :=
  flockClaim rels (fl.1, some fl.2, default)

/-- **The zeros after a round**: the Flock program's in its rounds, its tail zeros in `C2`'s round. -/
def zeros3 {β : Type} (Pf : ChainProg β) (done : Done) (msg : UMsg) : List E :=
  if 1 ≤ done.length ∧ done.length ≤ Pf.rounds.length then Pf.zeros (done.drop 1) msg
  else if done.length = Pf.rounds.length + 1 then Pf.tailZeros (done.drop 1) []
  else []

/-- **π1-rec3's zeros and result** from its rounds' records (`C1`'s round `r0`, Flock's `fd`, `C2`'s `r2`, the
values' `r3`, the batch's `brs`, raw draws) and the tail `tl`. -/
def main3Out (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (input : Vector UInt8 32) (rows : List ℕ)
    (r0 : UMsg × List E) (fd : Done) (r2 r3 : UMsg × List E) (brs : Done) (tl : List E) :
    List E × Reduced :=
  let fl := F3.prog.out fd []
  let mr := mainRels D.shape (publicWordsOf input.toList) (countsBits D.shape.heights rows)
    (squares (r0.2.headD 0) 4) (r0.2.getD 1 0) (r0.2.getD 2 0) (r2.2.headD 0) r3.1.2
  let fc := flockClaim3 mr.1 fl
  let combined := commitments.filterMap fun c => (combine fc.1.toList c (r3.2.headD 0)).map fun x => (c, x)
  let stackLayouts := layouts D.shape mr.2
  let bp := batchPureW narrowE combined stackLayouts (combine fc.2.1 .c1 1) fc.2.2 (r3.2.getD 1 0) brs tl
  (bp.1, ⟨(r0.1.1.getD default, r2.1.1.getD default), bp.2, none, fc.1.size,
    stackLayouts.map fun x => (x.1, x.2.vars), stackLayouts⟩)

/-- **π1-rec3's chain program without the counts' zero.** -/
def main3Prog0 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (np : ℕ) (input : Vector UInt8 32)
    (rows : List ℕ) : ChainProg Reduced where
  rounds := rec3Rounds F3.prog.rounds valsCount np
  zeros := zeros3 F3.prog
  tail := 3
  tailZeros done tl := (main3Out D F3 input rows (done.getD 0 default)
    ((done.drop 1).take F3.prog.rounds.length) (done.getD (F3.prog.rounds.length + 1) default)
    (done.getD (F3.prog.rounds.length + 2) default) (done.drop (F3.prog.rounds.length + 3)) tl).1
  out done tl := (main3Out D F3 input rows (done.getD 0 default)
    ((done.drop 1).take F3.prog.rounds.length) (done.getD (F3.prog.rounds.length + 1) default)
    (done.getD (F3.prog.rounds.length + 2) default) (done.drop (F3.prog.rounds.length + 3)) tl).2

/-- **π1-rec3's chain program**: `main3Prog0` with the counts' zero in round `0`. -/
def main3Prog (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (np : ℕ) (input : Vector UInt8 32)
    (rows : List ℕ) : ChainProg Reduced :=
  (main3Prog0 D F3 np input rows).withHead [countsZeroOf D rows]

theorem main3Prog_zeros_nil (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (np : ℕ) (input : Vector UInt8 32)
    (rows : List ℕ) (msg : UMsg) : (main3Prog D F3 np input rows).zeros [] msg = [countsZeroOf D rows] := by
  simp [main3Prog, ChainProg.withHead]

/-! ## The zeros -/

section Zeros

variable {β : Type} (Pf : ChainProg β)

theorem zeros3_nil (msg : UMsg) : zeros3 Pf [] msg = [] := by
  simp [zeros3]

theorem zeros3_flock (x : UMsg × List E) (e : Done) (msg : UMsg) (h : e.length < Pf.rounds.length) :
    zeros3 Pf ([] ++ [x] ++ e) msg = Pf.zeros e msg := by
  simp only [zeros3, List.nil_append, List.length_cons, List.singleton_append]
  rw [ite_eq_left ⟨by omega, by omega⟩]
  simp

theorem zeros3_c2 (x : UMsg × List E) (G : Done) (hG : G.length = Pf.rounds.length) (msg : UMsg) :
    zeros3 Pf ([x] ++ G) msg = Pf.tailZeros G [] := by
  have h1 : ([x] ++ G).length = Pf.rounds.length + 1 := by simp [hG]
  unfold zeros3
  rw [ite_eq_right (by omega), ite_eq_left h1]
  simp

theorem zeros3_vals (x x2 : UMsg × List E) (G : Done) (hG : G.length = Pf.rounds.length) (msg : UMsg) :
    zeros3 Pf ([x] ++ G ++ [x2]) msg = [] := by
  have h1 : ([x] ++ G ++ [x2]).length = Pf.rounds.length + 2 := by simp [hG]
  unfold zeros3
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem zeros3_batch (d : Done) (msg : UMsg) (h : Pf.rounds.length + 3 ≤ d.length) : zeros3 Pf d msg = [] := by
  unfold zeros3
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

end Zeros

/-! ## The link -/

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem samples_three (F : KeccakState → m KeccakState) : samples F 3 = (do
    let a ← sample F
    let b ← sample F
    let c ← sample F
    pure [a, b, c]) := by
  simp [samples_eq, FlockSound.Uni.repeatM]

section Main

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (np : ℕ) (input : Vector UInt8 32) (rows : List ℕ)

omit [LawfulMonad m] in
theorem main3Prog0_rounds : (main3Prog0 D F3 np input rows).rounds = [⟨true, 0, 2⟩] ++ F3.prog.rounds ++
    [⟨true, 0, 0⟩, ⟨false, valsCount, 1⟩] ++ (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) := by
  show rec3Rounds _ _ _ = _
  rw [rec3Rounds, List.append_assoc]

omit [LawfulMonad m] in
theorem main3Prog0_zeros : (main3Prog0 D F3 np input rows).zeros = zeros3 F3.prog := rfl

theorem main3Prog0_flock (F : KeccakState → m KeccakState) (x : UMsg × List E) :
    (main3Prog0 D F3 np input rows).runRounds F F3.prog.rounds ([] ++ [x]) =
      (fun d' => [] ++ [x] ++ d') <$> F3.prog.runRounds F F3.prog.rounds [] := by
  have h := runRounds_shift (main3Prog0 D F3 np input rows) F3.prog F ([] ++ [x]) F3.prog.rounds.length
    (fun e msg he => by rw [main3Prog0_zeros]; exact zeros3_flock F3.prog x e msg he) F3.prog.rounds []
    (by simp)
  rw [List.append_nil] at h
  exact h

theorem main3Prog0_batch (F : KeccakState → m KeccakState) (d : Done)
    (hd : F3.prog.rounds.length + 3 ≤ d.length) :
    (main3Prog0 D F3 np input rows).runRounds F (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) d =
      (fun e => d ++ e) <$> readRounds F (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]) := by
  refine runRounds_noZeros _ F (F3.prog.rounds.length + 3) (fun d msg h => ?_) _ d (fun s hs => ?_) hd
  · rw [main3Prog0_zeros]
    exact zeros3_batch F3.prog d msg h
  · simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hs
    rcases hs with ⟨-, rfl⟩ | rfl <;> rfl

end Main

/-- **`bind` through a reading, observationally**: `ChEq.bind_map`, then `obsOf3`. -/
theorem ObsEq3.bind_chEq {α β γ : Type} {x : ChanM m β} {y : ChanM m γ} {φ : γ → β} {f : β → ChanM m α}
    {g : γ → ChanM m α} (hx : ChEq x (φ <$> y)) (hf : ∀ b, ChEq (f (φ b)) (g b)) (hff : ∀ b, ChObl (f b))
    (hgg : ∀ b, ChObl (g b)) (hy : ChObl y) : ObsEq3 (x >>= f) (y >>= g) :=
  (ChEq.bind_map hx hf hff hgg hy).obsEq3

/-- **The batch's narrow rounds are the chain's**, the records narrowed. -/
theorem chEq_batchRounds (F : KeccakState → m KeccakState) (np : ℕ) :
    ChEq (readRoundsN F (List.replicate np 8 ++ [2]))
      ((List.map narrowRec) <$> readRounds F (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩])) := by
  have e : (List.replicate np 8 ++ [2]).map (fun nv => (⟨false, nv, 0⟩ : Compose.RoundSpec)) =
      List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩] := by
    simp [List.map_replicate]
  have h := chEq_readRoundsN F (List.replicate np 8 ++ [2])
  rwa [e] at h

/-- **The code-level link at π1-rec3, observationally**, for the program without the counts' zero. -/
theorem link3_obs0 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (hκ : D.shape.heights.getD opBlake2s 0 = κ)
    (np : ℕ) (hV : varsOf (layoutsOf D.shape) = 2 * np + 1) (input : Vector UInt8 32)
    (F : KeccakState → m KeccakState) :
    ObsEq3 (reduceWithFs F D.shape (publicWordsOf input.toList) (.flock flockMain) .point .rec3 true)
      (readCounts D.shape.heights >>= fun rows => (main3Prog0 D F3 np input rows).run F) := by
  have hv : D.shape.validate (Blake2s.flock flockMain != Blake2s.omitted) = true := D.valid.2
  have ht : (flockMain.slices == Flock.Slices.tower && ClaimsMode.point == ClaimsMode.point) = true :=
    rfl
  unfold reduceWithFs
  simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false, ht, ite_true, pure_bind, countBits_eq,
    bind_map_left, batchFs3_eq, tablePart_eq, hκ, F3.link, drawRun, OfNat.ofNat_ne_zero]
  refine ObsEq3.bind_right _ fun rows => ?_
  simp only [ChainProg.run]
  rw [main3Prog0_rounds, show (main3Prog0 D F3 np input rows).tail = 3 from rfl, runRounds_append,
    runRounds_append, runRounds_append, runRounds_cons, main3Prog0_zeros]
  simp only [rootRead, ite_true, zeros3_nil, nextScalars_zero, ChainProg.requireZeros, pure_bind,
    bind_map_left, bind_assoc, ChainProg.runRounds, Nat.reduceAdd, samples_three]
  -- Round 0: `C1`'s root, `c, β, γ`.
  refine ObsEq3.bind_right _ fun root1 => ?_
  refine ObsEq3.bind_right _ fun c => ?_
  refine ObsEq3.bind_right _ fun beta => ?_
  refine ObsEq3.bind_right _ fun gamma => ?_
  -- Flock's rounds (`F3.link`).
  rw [F3.tail_eq, nextScalars_zero, main3Prog0_flock, runRounds_fix F3.prog F F3.prog.rounds []]
  simp only [pure_bind, bind_map_left, List.nil_append, List.length_nil, List.drop_zero, main3Prog0_zeros]
  refine ObsEq3.bind_right _ fun fd => ?_
  -- `C2`'s root (Flock's tail zeros moved past it), `t`.
  refine ObsEq3.trans (ObsEq.obsEq3 (obsEq_requireZeros_nextRoot _ _)) ?_
  refine ObsEq3.bind_right _ fun root2 => ?_
  rw [zeros3_c2 F3.prog _ _ (length_fixDone _ _)]
  refine ObsEq3.bind_right _ fun _ => ?_
  rw [samples_one]
  simp only [bind_map_left]
  refine ObsEq3.bind_right _ fun t => ?_
  -- The values at `t`.
  rw [forIn_reads_of tableReads (tablesStep D.shape.heights (eqKernel (squares c 4)) beta
    (digits t (max D.shape.heap.h (D.shape.constraintVars + 4) + 2)))]
  swap
  · intro table s
    simp [map_eq_bind_pure_comp, tablesStep]
  simp only [Bool.false_eq_true, ite_false, bind_assoc, pure_bind, samples_two]
  simp only [zeros3_vals F3.prog _ _ _ (length_fixDone _ _)]
  rw [show valsCount = (tables.map tableReads).sum + 7 from rfl,
    nextScalars_add, nextScalars_seven, nextScalars_fix (tables.map tableReads).sum]
  simp only [ChainProg.requireZeros, bind_assoc, pure_bind, bind_map_left]
  refine ObsEq3.bind_right _ fun vt => ?_
  refine ObsEq3.bind_right _ fun a1 => ?_
  refine ObsEq3.bind_right _ fun a2 => ?_
  refine ObsEq3.bind_right _ fun a3 => ?_
  refine ObsEq3.bind_right _ fun a4 => ?_
  refine ObsEq3.bind_right _ fun a5 => ?_
  refine ObsEq3.bind_right _ fun a6 => ?_
  refine ObsEq3.bind_right _ fun a7 => ?_
  simp only [fixLen_fixLen]
  rcases hE : (F3.prog.out (fixDone F3.prog.rounds.length fd) []).2 with ⟨map, target⟩ | ⟨ws, value⟩
  all_goals
    simp only []
    refine ObsEq3.bind_right _ fun rho => ?_
    refine ObsEq3.bind_right _ fun lam => ?_
    rw [main3Prog0_batch D F3 np input rows F _ (by simp)]
    simp only [bind_map_left, Option.isSome_none, Bool.false_eq_true, ite_false]
    have hc2 := mainRels_c2 D (publicWordsOf input.toList) (countsBits D.shape.heights rows) (squares c 4)
      beta gamma t (fixLen (tables.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
    simp only [mainRels, tablesReads, getD_fixLen_append, getD_fixLen_append_zero, List.getD_cons_zero,
      List.getD_cons_succ, List.take_left', length_fixLen] at hc2
    have hlen := mainCombined_length D.shape (publicWordsOf input.toList) (countsBits D.shape.heights rows)
      (squares c 4) beta gamma t (fixLen (tables.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
      ((F3.prog.out (fixDone F3.prog.rounds.length fd) []).1,
        some (F3.prog.out (fixDone F3.prog.rounds.length fd) []).2, default) rho
    simp only [mainRels, flockClaim, hE, tablesReads, getD_fixLen_append, getD_fixLen_append_zero,
      List.getD_cons_zero, List.getD_cons_succ, List.take_left', length_fixLen] at hlen
    rw [hlen]
    refine ObsEq3.bind_chEq (φ := List.map narrowRec) ?_ (fun brs => ChEq.of_eq ?_ ?_)
      (fun _ => chObl_bind (chObl_nextScalars _) fun _ => chObl_bind (chObl_requireZeros _) fun _ =>
        chObl_pure _)
      (fun _ => chObl_bind (chObl_nextScalars _) fun _ => chObl_bind (chObl_requireZeros _) fun _ =>
        chObl_pure _)
      (chObl_readRounds F _)
    · rw [hc2, show layouts D.shape D.shape.c2Columns = layoutsOf D.shape from rfl, hV, batchNvs_odd]
      exact chEq_batchRounds F np
    · refine bind_congr fun tl => ?_
      simp only [batchPureW_narrow]
      simp only [main3Prog0, decode_r0, decode_fd _ _ _ _ _ _ (length_fixDone _ _),
        decode_r2 _ _ _ _ _ _ (length_fixDone _ _), decode_r3 _ _ _ _ _ _ (length_fixDone _ _),
        decode_brs _ _ _ _ _ _ (length_fixDone _ _)]
      simp only [main3Out, mainRels, flockClaim3, flockClaim, hE, tablesReads, getD_fixLen_append,
        getD_fixLen_append_zero, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons, Option.getD_some,
        List.take_left', length_fixLen]
    · exact chObl_bind (chObl_nextScalars _) fun _ => chObl_bind (chObl_requireZeros _) fun _ => chObl_pure _

/-- **The counts' zero is invisible** (as `link_counts`): after `readCounts`, whose zeros vanish only if the counts
are in range, the counts' zero in round `0` changes no verdict. -/
theorem link3_counts (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (np : ℕ) (input : Vector UInt8 32)
    (F : KeccakState → m KeccakState) :
    ObsEq (readCounts D.shape.heights >>= fun rows => (main3Prog0 D F3 np input rows).run F)
      (readCounts D.shape.heights >>= fun rows => (main3Prog D F3 np input rows).run F) := by
  intro c
  have h1 : ObsEq (readCounts (m := m) D.shape.heights >>= fun rows => (main3Prog D F3 np input rows).run F)
      (readCounts (m := m) D.shape.heights >>= fun rows =>
        ChainProg.requireZeros [countsZeroOf D rows] >>= fun _ => (main3Prog0 D F3 np input rows).run F) :=
    ObsEq.bind_right _ fun rows => obsEq_withHead (main3Prog0 D F3 np input rows) [countsZeroOf D rows] F 2 _
      rfl (funext fun msg => zeros3_nil F3.prog msg)
  rw [h1 c]
  obtain ⟨q, hq, hspec⟩ := readCounts_spec (m := m) D.shape.heights c
  rw [run_bind_of _ _ c q hq, run_bind_of _ _ c q hq]
  rcases q with ⟨r, c1⟩
  cases r with
  | error e => rfl
  | ok rows =>
    dsimp only
    refine (obsOf_requireZeros_of _ _ (obl_run _ F) c1 fun hz => ?_).symm
    obtain ⟨hl, hb⟩ := hspec rows rfl
    have h6 := D.valid.1
    have hfit : CountsInRange D.shape.heights rows :=
      ⟨by rw [hl, h6], fun j hj => (hb hz).2 j (by rw [h6]; exact hj)⟩
    simp [countsZeroOf, hfit]

/-- **The code-level link at π1-rec3, observationally.** -/
theorem link3_obs (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (hκ : D.shape.heights.getD opBlake2s 0 = κ)
    (np : ℕ) (hV : varsOf (layoutsOf D.shape) = 2 * np + 1) (input : Vector UInt8 32)
    (F : KeccakState → m KeccakState) :
    ObsEq3 (reduceWithFs F D.shape (publicWordsOf input.toList) (.flock flockMain) .point .rec3 true)
      (readCounts D.shape.heights >>= fun rows => (main3Prog D F3 np input rows).run F) :=
  (link3_obs0 D F3 hκ np hV input F).trans (link3_counts D F3 np input F).obsEq3

end Monad

/-! ## The code-level link -/

/-- **The code-level link at π1-rec3** (`UniCode3`), for every deployment whose `BLAKE2S` height is Flock's `κ` and
whose batch has `2 np + 1` variables: after the row counts, `reduceWithFs … .rec3 true` is `main3Prog` on
`rec3Rounds F3.prog.rounds valsCount np`, with a tail of three, up to `obsOf3`. -/
def uniCode3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (np : ℕ)
    (hV : varsOf (layoutsOf D.shape) = 2 * np + 1) : UniCode3 D F3 valsCount np where
  prog := main3Prog D F3 np
  rounds_eq _ _ := rfl
  tail_eq _ _ := rfl
  link := fun input {_} _ _ F c₀ => link3_obs D F3 hκ np hV input F c₀

/-- `uniCode3` at any number of values `nV = valsCount` (the identity model's `nVOf`, `Ids/Align.lean`'s
`nVOf_eq_of`). -/
def uniCode3At (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV np : ℕ)
    (hnV : nV = valsCount) (hV : varsOf (layoutsOf D.shape) = 2 * np + 1) : UniCode3 D F3 nV np where
  prog := main3Prog D F3 np
  rounds_eq _ _ := by rw [hnV]; rfl
  tail_eq _ _ := rfl
  link := (uniCode3 D F3 hκ np hV).link

/-- **The chain program's result names the roots the transcript carries** at rounds `0` (`C1`) and `nF + 1`
(`C2`): the form of the Fiat–Shamir layer's `UniOutRoots`. -/
theorem uniCode3_roots (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (hκ : D.shape.heights.getD opBlake2s 0 = κ)
    (np : ℕ) (hV : varsOf (layoutsOf D.shape) = 2 * np + 1) (input : Vector UInt8 32) (rows : List ℕ) (done : Done)
    (tl : List E) :
    (((uniCode3 D F3 hκ np hV).prog input rows).out done tl).roots =
      ((done.getD 0 default).1.1.getD default, (done.getD (F3.prog.rounds.length + 1) default).1.1.getD default) :=
  rfl

/-- `uniCode3_roots` at `uniCode3At`. -/
theorem uniCode3At_roots (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (hκ : D.shape.heights.getD opBlake2s 0 = κ)
    (nV np : ℕ) (hnV : nV = valsCount) (hV : varsOf (layoutsOf D.shape) = 2 * np + 1) (input : Vector UInt8 32)
    (rows : List ℕ) (done : Done) (tl : List E) :
    (((uniCode3At D F3 hκ nV np hnV hV).prog input rows).out done tl).roots =
      ((done.getD 0 default).1.1.getD default, (done.getD (F3.prog.rounds.length + 1) default).1.1.getD default) :=
  rfl

end UniSound

/-- info: 'UniSound.uniCode3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniCode3

/-- info: 'UniSound.uniCode3At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniCode3At

/-- info: 'UniSound.uniCode3_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniCode3_roots
