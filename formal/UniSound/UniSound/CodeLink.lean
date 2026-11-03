-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The program is `formal/UniStatement`'s
-- `reduceWith` (`Verifier.lean`); Flock's phase is cited through `FlockSound.link`.
import UniSound.CodeBatch
import UniSound.CodeShape

/-!
# The code-level link: `reduceWith` on the main line is a chain program (`UniCode`)

**`uniCode D hFlock hκ : UniCode D hFlock valsCount (varsOf (layoutsOf D.shape))`**: after the row
counts, `reduceWith` at the deployment's shape, main line (`flockMain`, point claims) is the chain
program `mainProg` on `uniRounds hFlock.prog.rounds valsCount V`, `V` the batch's variables at the
shape, with a tail of five, up to `obsOf`. Its rounds:

* `C1`'s root and `α ∈ E^4, β, γ`;
* Flock's rounds (`hFlock.link`: `Flock.verifyDeferred` is Flock's chain program; its zeros are the
  main line's there, its tail zeros the `C2` round's);
* `C2`'s root and `t`;
* the `valsCount` values at `t` (`tableReads` of each table, then the memory's three, the
  bytecode's two, `T(t)`, `Q_W(t)`) and `ρ, λ`;
* the batch's `V` rounds (`batch_eq`);

then the stacks' three values and `a`, `b`, the batch's terminal collected (`batchPure`), and the
result (`mainOut`). Each is a function of the transcript (`mainRels`, `flockClaim`, `batchPure`), the
verifier's own computations on the values read and drawn.
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## The values at `t` and the relations -/

/-- The tables' values at `t`. -/
def tablesReads : ℕ := (tables.map tableReads).sum

/-- **The row counts in range** (what `readCounts`' range checks accept, iteration 2's F1): six
counts, each at most `2^r` for its table's height `r`. -/
def CountsInRange (heights rows : List ℕ) : Prop :=
  rows.length = 6 ∧ ∀ j < 6, rows.getD j 0 ≤ 2 ^ heights.getD j 0

instance (heights rows : List ℕ) : Decidable (CountsInRange heights rows) := by
  unfold CountsInRange
  infer_instance

/-- **The values at `t`**: the tables', the memory's final counts, address and pull fingerprint,
the bytecode's final counts and pull fingerprint, `T(t)` and `Q_W(t)`. -/
def valsCount : ℕ := tablesReads + 7

/-- **The relations at `t` before Flock's claim (steps 4–6), and `C2`'s columns**, from the row
counts' bits, `α`, `β`, `γ`, `t` and the values. -/
def mainRels (shape : Shape) (pw : List E) (counts : List (List E)) (alphas : List E)
    (beta gamma t : E) (vals : List E) : Array Relation × List (Column × ℕ × Bool) :=
  let w := digits t (max shape.heap.h (shape.constraintVars + 4) + 2)
  let weights := eqKernel alphas
  let st := consumeFold tableReads (tablesStep shape.heights weights beta w) tables (#[], #[])
    (vals.take tablesReads)
  let memoryFinalCount := vals.getD tablesReads 0
  let address := vals.getD (tablesReads + 1) 0
  let memoryPull := vals.getD (tablesReads + 2) 0
  let bytecodeFinalCount := vals.getD (tablesReads + 3) 0
  let bytecodePull := vals.getD (tablesReads + 4) 0
  let heapValue := vals.getD (tablesReads + 5) 0
  let constraintValue := vals.getD (tablesReads + 6) 0
  let cr := constraintRelation shape st.2.toList pw gamma t constraintValue w
  let hr := heapRelations shape ((counts.zip shape.heights).map fun x => activeVanishingFromBits w x.1 x.2)
    st.2.toList weights beta heapValue constraintValue memoryPull
    (memoryPull + weights.getD 2 0 * (1 + memoryFinalCount)) bytecodePull
    (bytecodePull + weights.getD 2 0 * (1 + bytecodeFinalCount)) w (chunks (cr.2 + 1))
  let r1 := st.1.push (Relation.equal (.memory 3) (w.take shape.logMemory) memoryFinalCount)
  let r2 := r1.push (Relation.equal .address (w.take shape.logMemory) address)
  let r3 := r2.push ⟨(List.range 3).map (fun k => term (.memory k) (w.take shape.logMemory)
      (weights.getD (3 + k) 0)),
    memoryPull + beta + weights.getD 0 0 * sepMem + weights.getD 1 0 * address +
      weights.getD 2 0 * memoryFinalCount⟩
  let r4 := r3.push (Relation.equal .bytecodeFinal (w.take shape.logBytecode) bytecodeFinalCount)
  let r5 := r4.push (Relation.equal .bytecodeTuple (alphas ++ w.take shape.logBytecode)
    (bytecodePull + beta + weights.getD 2 0 * bytecodeFinalCount))
  (r5.push cr.1 ++ hr.1.toArray,
    [(.heap, shape.heap.h, true), (.treeQuotient 0, shape.heap.h, true), (.treeQuotient 1, 0, true)] ++
      List.map (fun x => (Column.constraintQuotient x.2, x.1, true))
        ((chunks (cr.2 + 1)).zip (List.range (chunks (cr.2 + 1)).length)) ++ hr.2)

/-- **Flock's claim on `q_flock`** (step 7, main line: the ring switch's one term), the bit-slice
relations, the ring map. -/
def flockClaim (rels : Array Relation) (fl : List E × Option Flock.End × Flock.Pending) :
    Array Relation × List Relation × Option (List E) :=
  match fl.2.1 with
  | some (.ring map target) =>
    (rels.push ⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩, [], some map)
  | some (.combination ws value) =>
    (rels, [⟨(ws.zip (List.range ws.length)).map fun x => ⟨.qflockBits, fl.1, x.2, x.1⟩, value⟩], none)
  | none => (rels, [], none)

/-- **The main line's zeros and result** from its rounds' records (`C1`'s round `r0`, Flock's `fd`,
`C2`'s `r2`, the values' `r3`, the batch's `brs`) and the tail `tl`. -/
def mainOut (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (input : Vector UInt8 32) (rows : List ℕ)
    (r0 : UMsg × List E) (fd : Done) (r2 r3 : UMsg × List E) (brs : Done) (tl : List E) :
    List E × Reduced :=
  let fl := Fl.prog.out fd []
  let mr := mainRels D.shape (publicWordsOf input.toList) (countsBits D.shape.heights rows) (r0.2.take 4)
    (r0.2.getD 4 0) (r0.2.getD 5 0) (r2.2.headD 0) r3.1.2
  let fc := flockClaim mr.1 fl
  let combined := commitments.filterMap fun c => (combine fc.1.toList c (r3.2.headD 0)).map fun x => (c, x)
  let stackLayouts := layouts D.shape mr.2
  let bp := batchPure combined stackLayouts (combine fc.2.1 .c1 1) fc.2.2 fl.2.2 fl.1 (r3.2.getD 1 0) brs tl
  (bp.1, ⟨(r0.1.1.getD default, r2.1.1.getD default), bp.2.1,
    if bp.2.2.isSome = true then bp.2.2 else none, fc.1.size, stackLayouts.map fun x => (x.1, x.2.vars),
    stackLayouts⟩)

/-! ## The run's `C2` columns and claims -/

/-- **`C2`'s columns in the run are the shape's** (whatever the values). -/
theorem mainRels_c2 (D : Deployment) (pw : List E) (counts : List (List E)) (alphas : List E)
    (beta gamma t : E) (vals : List E) :
    (mainRels D.shape pw counts alphas beta gamma t vals).2 = D.shape.c2Columns := by
  unfold mainRels
  simp only []
  exact c2Columns_run D.shape D.valid.1 _ (tables_parts_degrees _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _

theorem flockClaim_mem (rels : Array Relation) (fl : List E × Option Flock.End × Flock.Pending)
    (r : Relation) (h : r ∈ rels.toList) : r ∈ (flockClaim rels fl).1.toList := by
  unfold flockClaim
  split <;> simp [h]

/-- **One claim per commitment in the run.** -/
theorem mainCombined_length (shape : Shape) (pw : List E) (counts : List (List E)) (alphas : List E)
    (beta gamma t : E) (vals : List E) (fl : List E × Option Flock.End × Flock.Pending) (rho : E) :
    (commitments.filterMap fun c =>
      (combine (flockClaim (mainRels shape pw counts alphas beta gamma t vals).1 fl).1.toList c rho).map
        fun x => (c, x)).length = 3 := by
  apply combined_length
  · refine ⟨Relation.equal (.memory 3) ((digits t (max shape.heap.h (shape.constraintVars + 4) + 2)).take
      shape.logMemory) (vals.getD tablesReads 0), flockClaim_mem _ fl _ ?_, rfl⟩
    unfold mainRels
    simp
  · refine ⟨Relation.equal .heap ((digits t (max shape.heap.h (shape.constraintVars + 4) + 2)).take
      shape.heap.h) (vals.getD (tablesReads + 5) 0), flockClaim_mem _ fl _ ?_, rfl⟩
    unfold mainRels
    simp only [Array.toList_append, List.mem_append]
    exact Or.inr (heapRelations_mem _ _ _ _ _ _ _ _ _ _ _ _ _)
  · refine ⟨Relation.equal .address ((digits t (max shape.heap.h (shape.constraintVars + 4) + 2)).take
      shape.logMemory) (vals.getD (tablesReads + 1) 0), flockClaim_mem _ fl _ ?_, rfl⟩
    unfold mainRels
    simp

/-- The main line's zeros after a round: Flock's in its rounds, its tail zeros in `C2`'s round. -/
def mainZeros {κ : ℕ} (Fl : FlockSound κ) (done : Done) (msg : UMsg) : List E :=
  if 1 ≤ done.length ∧ done.length ≤ Fl.prog.rounds.length then Fl.prog.zeros (done.drop 1) msg
  else if done.length = Fl.prog.rounds.length + 1 then Fl.prog.tailZeros (done.drop 1) []
  else []

/-- **The main line's chain program** for a public input and the row counts. -/
def mainProg (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (input : Vector UInt8 32) (rows : List ℕ) :
    ChainProg Reduced where
  rounds := uniRounds Fl.prog.rounds valsCount (varsOf (layoutsOf D.shape))
  zeros := mainZeros Fl
  tail := 5
  tailZeros done tl := (mainOut D Fl input rows (done.getD 0 default)
    ((done.drop 1).take Fl.prog.rounds.length) (done.getD (Fl.prog.rounds.length + 1) default)
    (done.getD (Fl.prog.rounds.length + 2) default) (done.drop (Fl.prog.rounds.length + 3)) tl).1
  out done tl := (mainOut D Fl input rows (done.getD 0 default)
    ((done.drop 1).take Fl.prog.rounds.length) (done.getD (Fl.prog.rounds.length + 1) default)
    (done.getD (Fl.prog.rounds.length + 2) default) (done.drop (Fl.prog.rounds.length + 3)) tl).2

/-! ## Rounds of a fixed length -/

/-- A transcript cut or padded to `n` rounds. -/
def fixDone (n : ℕ) (l : Done) : Done := (List.range n).map fun i => l.getD i default

@[simp] theorem length_fixDone (n : ℕ) (l : Done) : (fixDone n l).length = n := by simp [fixDone]

theorem fixDone_succ_cons (n : ℕ) (x : UMsg × List E) (l : Done) :
    fixDone (n + 1) (x :: l) = x :: fixDone n l := by
  simp [fixDone, List.range_succ_eq_map, Function.comp_def]

theorem fixDone_of_length {n : ℕ} {l : Done} (h : l.length = n) : fixDone n l = l := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [fixDone, List.getD_eq_getElem?_getD, h2]

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **A chain program's rounds complete one record each.** -/
theorem runRounds_fix {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) :
    ∀ (rs : List Compose.RoundSpec) (d : Done),
      P.runRounds F rs d = (fun d' => d ++ fixDone rs.length (d'.drop d.length)) <$> P.runRounds F rs d
  | [], d => by simp [ChainProg.runRounds, fixDone]
  | s :: rs, d => by
    conv_lhs => rw [runRounds_cons]
    rw [runRounds_cons]
    simp only [map_bind]
    congr 1
    funext root
    congr 1
    funext vals
    congr 1
    funext _
    congr 1
    funext chs
    rw [runRounds_fix P F rs (d ++ [((root, vals), chs)])]
    simp only [Functor.map_map]
    congr 1
    funext d'
    have hF := length_fixDone rs.length (List.drop (List.length (d ++ [((root, vals), chs)])) d')
    generalize fixDone rs.length (List.drop (List.length (d ++ [((root, vals), chs)])) d') = G at hF ⊢
    rw [List.append_assoc, List.drop_left, List.singleton_append, List.length_cons, fixDone_succ_cons,
      fixDone_of_length hF]

theorem samples_six (F : KeccakState → m KeccakState) : samples F 6 = (do
    let a ← samples F 4
    let b ← sample F
    let c ← sample F
    pure (fixLen 4 a ++ [b, c])) := by
  rw [show 6 = 4 + 2 from rfl, samples_add]
  simp [samples_eq, FlockSound.Uni.repeatM]

theorem samples_two (F : KeccakState → m KeccakState) : samples F 2 = (do
    let a ← sample F
    let b ← sample F
    pure [a, b]) := by
  simp [samples_eq, FlockSound.Uni.repeatM]

theorem ObsEq.bind_eq {α β : Type} {x y : ChanM m β} {f g : β → ChanM m α} (h : x = y)
    (hf : ∀ b, ObsEq (f b) (g b)) : ObsEq (x >>= f) (y >>= g) := by
  subst h
  exact ObsEq.bind_right x hf

theorem mainZeros_nil {κ : ℕ} (Fl : FlockSound κ) (msg : UMsg) : mainZeros Fl [] msg = [] := by
  simp [mainZeros]

theorem mainZeros_flock {κ : ℕ} (Fl : FlockSound κ) (x : UMsg × List E) (e : Done) (msg : UMsg)
    (h : e.length < Fl.prog.rounds.length) : mainZeros Fl ([] ++ [x] ++ e) msg = Fl.prog.zeros e msg := by
  simp only [mainZeros, List.nil_append, List.length_cons, List.singleton_append]
  rw [ite_eq_left ⟨by omega, by omega⟩]
  simp

theorem mainZeros_c2 {κ : ℕ} (Fl : FlockSound κ) (x : UMsg × List E) (G : Done)
    (hG : G.length = Fl.prog.rounds.length) (msg : UMsg) :
    mainZeros Fl ([x] ++ G) msg = Fl.prog.tailZeros G [] := by
  have h1 : ([x] ++ G).length = Fl.prog.rounds.length + 1 := by simp [hG]
  unfold mainZeros
  rw [ite_eq_right (by omega), ite_eq_left h1]
  simp

theorem mainZeros_vals {κ : ℕ} (Fl : FlockSound κ) (x x2 : UMsg × List E) (G : Done)
    (hG : G.length = Fl.prog.rounds.length) (msg : UMsg) :
    mainZeros Fl ([x] ++ G ++ [x2]) msg = [] := by
  have h1 : ([x] ++ G ++ [x2]).length = Fl.prog.rounds.length + 2 := by simp [hG]
  unfold mainZeros
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem nextScalars_seven : nextScalars (m := m) 7 = (do
    let a1 ← nextScalar (m := m)
    let a2 ← nextScalar (m := m)
    let a3 ← nextScalar (m := m)
    let a4 ← nextScalar (m := m)
    let a5 ← nextScalar (m := m)
    let a6 ← nextScalar (m := m)
    let a7 ← nextScalar (m := m)
    pure [a1, a2, a3, a4, a5, a6, a7]) := by
  simp [nextScalars_eq, FlockSound.Uni.repeatM]

theorem runRounds_noZeros {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) (n : ℕ)
    (hz : ∀ d msg, n ≤ d.length → P.zeros d msg = []) :
    ∀ (rs : List Compose.RoundSpec) (d : Done), (∀ s ∈ rs, s.root = false) → n ≤ d.length →
      P.runRounds F rs d = (fun e => d ++ e) <$> readRounds F rs
  | [], d, _, _ => by simp [ChainProg.runRounds, readRounds]
  | s :: rs, d, hr, hn => by
    have hs : s.root = false := hr s (List.mem_cons_self ..)
    rw [runRounds_cons]
    simp only [rootRead, hs, Bool.false_eq_true, ite_false, pure_bind, hz d _ hn, ChainProg.requireZeros,
      readRounds, readRound, bind_assoc, map_bind]
    congr 1
    funext vals
    congr 1
    funext chs
    rw [runRounds_noZeros P F n hz rs _ (fun s hs => hr s (List.mem_cons_of_mem _ hs)) (by simp; omega)]
    simp

/-! ## Reading the transcript back -/

section Decode

variable (x0 x2 x3 : UMsg × List E) (G brs : Done)

theorem decode_r0 : ([x0] ++ G ++ [x2] ++ [x3] ++ brs).getD 0 default = x0 := by simp

theorem decode_fd (n : ℕ) (hG : G.length = n) :
    (([x0] ++ G ++ [x2] ++ [x3] ++ brs).drop 1).take n = G := by
  subst hG
  simp

theorem decode_r2 (n : ℕ) (hG : G.length = n) :
    ([x0] ++ G ++ [x2] ++ [x3] ++ brs).getD (n + 1) default = x2 := by
  subst hG
  simp [List.getD_eq_getElem?_getD]

theorem decode_r3 (n : ℕ) (hG : G.length = n) :
    ([x0] ++ G ++ [x2] ++ [x3] ++ brs).getD (n + 2) default = x3 := by
  subst hG
  simp [List.getD_eq_getElem?_getD]

theorem decode_brs (n : ℕ) (hG : G.length = n) :
    ([x0] ++ G ++ [x2] ++ [x3] ++ brs).drop (n + 3) = brs := by
  subst hG
  simp [List.drop_append]

end Decode

theorem getD_fixLen_append (T i : ℕ) (v l : List E) : (fixLen T v ++ l).getD (T + i) 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_fixLen_append_zero (T : ℕ) (v l : List E) : (fixLen T v ++ l).getD T 0 = l.getD 0 0 := by
  simpa using getD_fixLen_append T 0 v l

theorem getD_five (a : List E) (b c : E) : (fixLen 4 a ++ [b, c]).getD 5 0 = c :=
  getD_fixLen_append 4 1 a [b, c]

section Main

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (input : Vector UInt8 32) (rows : List ℕ)

omit [LawfulMonad m] in
theorem mainProg_rounds : (mainProg D Fl input rows).rounds = [⟨true, 0, 5⟩] ++ Fl.prog.rounds ++
    [⟨true, 0, 0⟩, ⟨false, valsCount, 1⟩] ++ List.replicate (varsOf (layoutsOf D.shape)) ⟨false, 2, 0⟩ :=
  rfl

omit [LawfulMonad m] in
theorem mainProg_zeros : (mainProg D Fl input rows).zeros = mainZeros Fl := rfl

theorem mainProg_flock (F : KeccakState → m KeccakState) (x : UMsg × List E) :
    (mainProg D Fl input rows).runRounds F Fl.prog.rounds ([] ++ [x]) =
      (fun d' => [] ++ [x] ++ d') <$> Fl.prog.runRounds F Fl.prog.rounds [] := by
  have h := runRounds_shift (mainProg D Fl input rows) Fl.prog F ([] ++ [x]) Fl.prog.rounds.length
    (fun e msg he => by rw [mainProg_zeros]; exact mainZeros_flock Fl x e msg he) Fl.prog.rounds []
    (by simp)
  rw [List.append_nil] at h
  exact h

theorem mainProg_batch (F : KeccakState → m KeccakState) (d : Done)
    (hd : Fl.prog.rounds.length + 3 ≤ d.length) :
    (mainProg D Fl input rows).runRounds F
        (List.replicate (varsOf (layoutsOf D.shape)) ⟨false, 2, 0⟩) d =
      (fun e => d ++ e) <$> readRounds F (List.replicate (varsOf (layoutsOf D.shape)) ⟨false, 2, 0⟩) := by
  refine runRounds_noZeros _ F (Fl.prog.rounds.length + 3) (fun d msg h => ?_) _ d
    (fun s hs => by rw [(List.mem_replicate.mp hs).2]) hd
  rw [mainProg_zeros]
  simp only [mainZeros]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

end Main

/-- **The code-level link, observationally.** -/
theorem link_obs (D : Deployment) {κ : ℕ} (Fl : FlockSound κ)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (input : Vector UInt8 32)
    (F : KeccakState → m KeccakState) :
    ObsEq (reduceWith F D.shape (publicWordsOf input.toList) (.flock flockMain) .point)
      (readCounts D.shape.heights >>= fun rows => (mainProg D Fl input rows).run F) := by
  have hv : D.shape.validate (Blake2s.flock flockMain != Blake2s.omitted) = true := D.valid.2
  have ht : (flockMain.slices == Flock.Slices.tower && ClaimsMode.point == ClaimsMode.point) = true :=
    rfl
  unfold reduceWith
  simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false, ht, ite_true, pure_bind, countBits_eq,
    bind_map_left, batch_eq, tablePart_eq, hκ, Fl.link]
  refine ObsEq.bind_right _ fun rows => ?_
  simp only [ChainProg.run]
  rw [mainProg_rounds, show (mainProg D Fl input rows).tail = 5 from rfl, runRounds_append,
    runRounds_append, runRounds_append, runRounds_cons, mainProg_zeros]
  rw [samples_fix F 4]
  simp only [rootRead, ite_true, mainZeros_nil, nextScalars_zero, ChainProg.requireZeros, pure_bind,
    bind_map_left, bind_assoc, ChainProg.runRounds, Nat.reduceAdd, samples_six]
  -- Round 0: `C1`'s root, `α, β, γ`.
  refine ObsEq.bind_right _ fun root1 => ?_
  refine ObsEq.bind_right _ fun alphas => ?_
  refine ObsEq.bind_right _ fun beta => ?_
  refine ObsEq.bind_right _ fun gamma => ?_
  -- Flock's rounds (`hFlock.link`).
  rw [Fl.tail_eq, nextScalars_zero, mainProg_flock, runRounds_fix Fl.prog F Fl.prog.rounds []]
  simp only [pure_bind, bind_map_left, List.nil_append, List.length_nil, List.drop_zero, mainProg_zeros]
  refine ObsEq.bind_right _ fun fd => ?_
  -- `C2`'s root (Flock's tail zeros moved past it), `t`.
  refine ObsEq.trans (obsEq_requireZeros_nextRoot _ _) ?_
  refine ObsEq.bind_right _ fun root2 => ?_
  rw [mainZeros_c2 Fl _ _ (length_fixDone _ _)]
  refine ObsEq.bind_right _ fun _ => ?_
  rw [samples_one]
  simp only [bind_map_left]
  refine ObsEq.bind_right _ fun t => ?_
  -- The values at `t`.
  rw [forIn_reads_of tableReads (tablesStep D.shape.heights (eqKernel (fixLen 4 alphas)) beta
    (digits t (max D.shape.heap.h (D.shape.constraintVars + 4) + 2)))]
  swap
  · intro table s
    simp [map_eq_bind_pure_comp, tablesStep]
  simp only [Bool.false_eq_true, ite_false, bind_assoc, pure_bind, samples_two]
  simp only [mainZeros_vals Fl _ _ _ (length_fixDone _ _)]
  rw [show valsCount = (tables.map tableReads).sum + 7 from rfl,
    nextScalars_add, nextScalars_seven, nextScalars_fix (tables.map tableReads).sum]
  simp only [ChainProg.requireZeros, bind_assoc, pure_bind, bind_map_left]
  refine ObsEq.bind_right _ fun vt => ?_
  refine ObsEq.bind_right _ fun a1 => ?_
  refine ObsEq.bind_right _ fun a2 => ?_
  refine ObsEq.bind_right _ fun a3 => ?_
  refine ObsEq.bind_right _ fun a4 => ?_
  refine ObsEq.bind_right _ fun a5 => ?_
  refine ObsEq.bind_right _ fun a6 => ?_
  refine ObsEq.bind_right _ fun a7 => ?_
  simp only [fixLen_fixLen]
  rcases hE : (Fl.prog.out (fixDone Fl.prog.rounds.length fd) []).2.1 with _ | ⟨map, target⟩ | ⟨ws, value⟩
  all_goals
    simp only []
    refine ObsEq.bind_right _ fun rho => ?_
    refine ObsEq.bind_right _ fun lam => ?_
    rw [mainProg_batch D Fl input rows F _ (by simp)]
    simp only [bind_map_left]
    refine ObsEq.bind_eq (by
      have h := mainRels_c2 D (publicWordsOf input.toList) (countsBits D.shape.heights rows) (fixLen 4 alphas)
        beta gamma t (fixLen (tables.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
      simp only [mainRels, tablesReads, getD_fixLen_append, getD_fixLen_append_zero, List.getD_cons_zero,
        List.getD_cons_succ, List.take_left', length_fixLen] at h
      rw [h]
      rfl) fun brs => ?_
    refine ObsEq.bind_eq (by
      have h := mainCombined_length D.shape (publicWordsOf input.toList) (countsBits D.shape.heights rows)
        (fixLen 4 alphas) beta gamma t (fixLen (tables.map tableReads).sum vt ++ [a1, a2, a3, a4, a5, a6, a7])
        (Fl.prog.out (fixDone Fl.prog.rounds.length fd) []) rho
      simp only [mainRels, flockClaim, hE, tablesReads, getD_fixLen_append, getD_fixLen_append_zero,
        List.getD_cons_zero, List.getD_cons_succ, List.take_left', length_fixLen] at h
      rw [h]) fun tl => ?_
    refine ObsEq.of_eq ?_
    simp only [mainProg, decode_r0, decode_fd _ _ _ _ _ _ (length_fixDone _ _),
      decode_r2 _ _ _ _ _ _ (length_fixDone _ _), decode_r3 _ _ _ _ _ _ (length_fixDone _ _),
      decode_brs _ _ _ _ _ _ (length_fixDone _ _)]
    simp only [mainOut, mainRels, flockClaim, hE, tablesReads, getD_fixLen_append,
      getD_fixLen_append_zero, getD_five, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons,
      Option.getD_some, List.take_left', length_fixLen]
    congr 1
    funext _
    split_ifs <;> rfl

end Monad

/-- **The code-level link** (`UniCode`) at the main line, for every deployment whose `BLAKE2S`
height is Flock's `κ`: after the row counts, `reduceWith` is `mainProg` on
`uniRounds hFlock.prog.rounds valsCount (varsOf (layoutsOf D.shape))`, with a tail of five, up to
`obsOf`. -/
def uniCode (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (hκ : D.shape.heights.getD opBlake2s 0 = κ) :
    UniCode D Fl valsCount (varsOf (layoutsOf D.shape)) where
  prog := mainProg D Fl
  rounds_eq _ _ := rfl
  tail_eq _ _ := rfl
  link := fun input {_} _ _ F c₀ => link_obs D Fl hκ input F c₀

end UniSound
