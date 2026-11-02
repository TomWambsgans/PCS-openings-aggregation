-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The programs are `formal/UniStatement`'s
-- (`Verifier.lean`: `countBits`, `tablePart`, `linearise`; `Prog.lean`'s chain programs).
import UniSound.CodeBase

/-!
# The row counts, a chain program's rounds, and the tables' values as fixed reads

* `countBits_eq`: the verifier's row counts are `readCounts`' (the statement's rows), their bits a
  function of them (`countsBits`);
* `runRounds_append`, `runRounds_shift`: a chain program's rounds split at a boundary, and the rounds
  of one program inside another whose zeros agree there (Flock's rounds in the main line's);
* **`tablePart_eq`**: a table's part of the values at `t` reads a fixed number of scalars
  (`tableReads`, a function of the table alone) and computes from them (`tablePartPure`). Which
  fingerprints are sent depends on `linearise`'s terms being empty, which depends only on which
  columns are sent (`linearise_isEmpty`, `SamePat`), not on the values or the weights.
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics FlockSound.Uni

/-! ## The row counts -/

/-- The bits `0 … r` of each row count (`countBits`' result). -/
def countsBits (heights rows : List ℕ) : List (List E) :=
  (rows.zip heights).map fun x => (List.range (x.2 + 1)).map fun b => intBits x.1 b 1

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- One row count's read and range checks (`readCounts`' step). -/
def readCount (r : ℕ) : ChanM m ℕ := do
  let count ← nextInteger (m := m) 4
  requireZero (m := m) (intBits count (r + 1) 32)
  requireZero (m := m) (intBits count r 1 * intBits count 0 r)
  pure count

omit [LawfulMonad m] in
theorem readCounts_eq (heights : List ℕ) :
    readCounts (m := m) heights = heights.mapM (readCount (m := m)) := rfl

theorem countBits_loop : ∀ (hs : List ℕ) (arr : Array (List E)),
    (forIn hs arr (fun r s => do
        let count ← nextInteger (m := m) 4
        requireZero (m := m) (intBits count (r + 1) 32)
        requireZero (m := m) (intBits count r 1 * intBits count 0 r)
        pure (ForInStep.yield (s.push ((List.range (r + 1)).map fun b => intBits count b 1)))) >>=
          fun s => pure s.toList) =
      (fun rows => arr.toList ++ countsBits hs rows) <$> hs.mapM (readCount (m := m))
  | [], arr => by simp [countsBits]
  | r :: hs, arr => by
    simp only [List.forIn_cons, List.mapM_cons, readCount, bind_assoc, map_bind, pure_bind]
    congr 1
    funext count
    congr 1
    funext _
    congr 1
    funext _
    rw [countBits_loop hs]
    simp only [map_eq_bind_pure_comp, Function.comp_def, pure_bind]
    congr 1
    funext rows
    simp [countsBits, Array.toList_push]

/-- **The verifier's row counts are `readCounts`'**, their bits a function of them. -/
theorem countBits_eq (heights : List ℕ) :
    countBits (m := m) heights = (fun rows => countsBits heights rows) <$> readCounts (m := m) heights := by
  have h := countBits_loop (m := m) heights #[]
  simp only [List.nil_append] at h
  rw [readCounts_eq, ← h]
  rfl

/-! ## A chain program's rounds -/

/-- A round's root, if it has one. -/
def rootRead (b : Bool) : ChanM m (Option (E × E)) := if b then some <$> nextRoot (m := m) else pure none

omit [LawfulMonad m] in
theorem runRounds_cons {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState)
    (s : Compose.RoundSpec) (rs : List Compose.RoundSpec) (d : Done) :
    P.runRounds F (s :: rs) d = (do
      let root ← rootRead (m := m) s.root
      let vals ← nextScalars (m := m) s.nv
      ChainProg.requireZeros (P.zeros d (root, vals))
      let chs ← samples F (s.ns + 1)
      P.runRounds F rs (d ++ [((root, vals), chs)])) := by
  rw [ChainProg.runRounds]
  rcases s with ⟨b, nv, ns⟩
  cases b <;> rfl

theorem runRounds_append {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) :
    ∀ (rs₁ rs₂ : List Compose.RoundSpec) (d : Done),
      P.runRounds F (rs₁ ++ rs₂) d = P.runRounds F rs₁ d >>= fun d' => P.runRounds F rs₂ d'
  | [], rs₂, d => by simp [ChainProg.runRounds]
  | s :: rs₁, rs₂, d => by
    simp only [List.cons_append, runRounds_cons, bind_assoc]
    congr 1
    funext root
    congr 1
    funext vals
    congr 1
    funext _
    congr 1
    funext chs
    exact runRounds_append P F rs₁ rs₂ _

/-- **The rounds of one program inside another** whose zeros there are the first's, after the
transcript `pre`. -/
theorem runRounds_shift {α β : Type} (P : ChainProg α) (Q : ChainProg β)
    (F : KeccakState → m KeccakState) (pre : Done) (n : ℕ)
    (hz : ∀ e msg, e.length < n → P.zeros (pre ++ e) msg = Q.zeros e msg) :
    ∀ (rs : List Compose.RoundSpec) (d : Done), d.length + rs.length ≤ n →
      P.runRounds F rs (pre ++ d) = (fun d' => pre ++ d') <$> Q.runRounds F rs d
  | [], d, _ => by simp [ChainProg.runRounds]
  | s :: rs, d, h => by
    simp only [List.length_cons] at h
    simp only [runRounds_cons, map_bind]
    congr 1
    funext root
    congr 1
    funext vals
    rw [hz d _ (by omega)]
    congr 1
    funext _
    congr 1
    funext chs
    rw [List.append_assoc]
    exact runRounds_shift P Q F pre n hz rs _ (by simp; omega)

end Monad

/-! ## Which fingerprints are sent -/

/-- `linearise`'s inner step (one monomial of a form). -/
def linInner (weight : E) (sent : Array (Option E)) (acc : E × List (ℕ × E)) (mc : List ℕ × E) :
    E × List (ℕ × E) :=
  match mc with
  | (monomial, coefficient) =>
    match acc with
    | (known, terms) =>
      if coefficient = 0 then acc
      else
        match monomial with
        | [] => (known + weight * coefficient, terms)
        | [i] =>
          match sent.getD i none with
          | some v => (known + weight * coefficient * v, terms)
          | none => (known, addTerm terms i (weight * coefficient))
        | [i, j] =>
          match sent.getD i none, sent.getD j none with
          | some a, some b => (known + weight * coefficient * a * b, terms)
          | some a, none => (known, addTerm terms j (weight * coefficient * a))
          | none, some b => (known, addTerm terms i (weight * coefficient * b))
          | none, none => (known, terms)
        | _ => acc

/-- `linearise`'s outer step (one form, its slot's weight). -/
def linOuter (weights : Array E) (sent : Array (Option E)) (acc : E × List (ℕ × E))
    (x : Form × ℕ) : E × List (ℕ × E) :=
  x.1.foldl (linInner (weights.getD x.2 0) sent) acc

theorem linearise_eq (tuple : List Form) (weights : Array E) (sent : Array (Option E)) :
    linearise tuple weights sent =
      (tuple.zip (List.range tuple.length)).foldl (linOuter weights sent) (0, []) := by
  unfold linearise linOuter linInner
  rfl

/-- **A monomial makes `linearise` add a term**: a nonzero coefficient on exactly one unsent
factor. -/
def addsTerm (sent : Array (Option E)) (mc : List ℕ × E) : Bool :=
  decide (mc.2 ≠ 0) &&
    match mc.1 with
    | [i] => (sent.getD i none).isNone
    | [i, j] => (sent.getD i none).isSome != (sent.getD j none).isSome
    | _ => false

theorem addTerm_isEmpty (terms : List (ℕ × E)) (i : ℕ) (c : E) :
    (addTerm terms i c).isEmpty = false := by
  unfold addTerm
  split
  · rename_i j hj
    have hne : terms ≠ [] := by
      rintro rfl
      simp at hj
    simp [hne]
  · simp

theorem linInner_isEmpty (weight : E) (sent : Array (Option E)) (acc : E × List (ℕ × E))
    (mc : List ℕ × E) :
    (linInner weight sent acc mc).2.isEmpty = (acc.2.isEmpty && !addsTerm sent mc) := by
  rcases mc with ⟨monomial, coefficient⟩
  rcases acc with ⟨known, terms⟩
  unfold linInner addsTerm
  by_cases hc : coefficient = 0
  · simp [hc]
  · simp only [hc, ite_false, ne_eq, not_false_eq_true, decide_true, Bool.true_and]
    rcases monomial with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
    · simp
    · simp only [Array.getD_eq_getD_getElem?]
      generalize (sent[i]?).getD none = oi
      cases oi <;> simp [addTerm_isEmpty]
    · simp only [Array.getD_eq_getD_getElem?]
      generalize (sent[i]?).getD none = oi
      generalize (sent[j]?).getD none = oj
      cases oi <;> cases oj <;> simp [addTerm_isEmpty]
    · simp

theorem foldl_linInner_isEmpty (weight : E) (sent : Array (Option E)) :
    ∀ (form : Form) (acc : E × List (ℕ × E)),
      (form.foldl (linInner weight sent) acc).2.isEmpty =
        (acc.2.isEmpty && form.all fun mc => !addsTerm sent mc)
  | [], acc => by simp
  | mc :: form, acc => by
    rw [List.foldl_cons, foldl_linInner_isEmpty weight sent form, linInner_isEmpty, List.all_cons,
      Bool.and_assoc]

theorem foldl_linOuter_isEmpty (weights : Array E) (sent : Array (Option E)) :
    ∀ (l : List (Form × ℕ)) (acc : E × List (ℕ × E)),
      (l.foldl (linOuter weights sent) acc).2.isEmpty =
        (acc.2.isEmpty && l.all fun x => x.1.all fun mc => !addsTerm sent mc)
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_linOuter_isEmpty weights sent l, linOuter, foldl_linInner_isEmpty,
      List.all_cons, Bool.and_assoc]

/-- **`linearise`'s terms are empty** exactly when no monomial has one unsent factor. -/
theorem linearise_isEmpty (tuple : List Form) (weights : Array E) (sent : Array (Option E)) :
    (linearise tuple weights sent).2.isEmpty =
      (tuple.zip (List.range tuple.length)).all fun x => x.1.all fun mc => !addsTerm sent mc := by
  rw [linearise_eq, foldl_linOuter_isEmpty]
  simp

/-- **The same columns sent.** -/
def SamePat (a b : Array (Option E)) : Prop :=
  a.size = b.size ∧ ∀ i, (a.getD i none).isSome = (b.getD i none).isSome

theorem isNone_eq_not_isSome (o : Option E) : o.isNone = !o.isSome := by cases o <;> rfl

theorem addsTerm_of_samePat {a b : Array (Option E)} (h : SamePat a b) (mc : List ℕ × E) :
    addsTerm a mc = addsTerm b mc := by
  unfold addsTerm
  rcases mc with ⟨monomial, c⟩
  rcases monomial with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
  · rfl
  · simp only [isNone_eq_not_isSome, h.2 i]
  · simp only [h.2 i, h.2 j]
  · rfl

theorem linearise_isEmpty_of_samePat {a b : Array (Option E)} (h : SamePat a b) (tuple : List Form)
    (wa wb : Array E) : (linearise tuple wa a).2.isEmpty = (linearise tuple wb b).2.isEmpty := by
  rw [linearise_isEmpty, linearise_isEmpty]
  simp only [addsTerm_of_samePat h]

theorem samePat_set {a b : Array (Option E)} (h : SamePat a b) (c : ℕ) (x y : E) :
    SamePat (a.set! c (some x)) (b.set! c (some y)) := by
  refine ⟨by simp [h.1], fun i => ?_⟩
  have hi := h.2 i
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, h.1] at hi ⊢
  split_ifs <;> simp_all

/-! ## A table's part of the values at `t` -/

/-- One sent column's read (`tablePart`'s first loop): the value set, and bound at `w[..r]`. -/
def sentStep (t : Table) (pt : List E) (column : ℕ) (s : Array (Option E) × Array Relation)
    (vs : List E) : Array (Option E) × Array Relation :=
  (s.1.set! column (some (vs.headD 0)),
    s.2.push (Relation.equal (.table t.opcode column) pt (vs.headD 0)))

/-- **The fingerprints of a flush that are sent**: the pull's if its tuple has a term in an unsent
column, the push's if the difference has. -/
def flushReads (weights : Array E) (sent : Array (Option E)) (x : List Form × List Form) : ℕ :=
  (if (linearise x.1 weights sent).2.isEmpty then 0 else 1) +
    (if (linearise (difference x.2 x.1) weights sent).2.isEmpty then 0 else 1)

/-- One flush (`tablePart`'s second loop) from its sent fingerprints `vs`. -/
def flushStep (t : Table) (pt : List E) (weights : Array E) (beta : E) (sent : Array (Option E))
    (x : List Form × List Form) (s : Array Relation × E × E × ℕ × ℕ) (vs : List E) :
    Array Relation × E × E × ℕ × ℕ :=
  let lp := linearise x.1 weights sent
  let rels1 := if lp.2.isEmpty then s.1 else
    s.1.push ⟨lp.2.map (fun ck => match ck with | (c, k) => term (.table t.opcode c) pt k),
      vs.headD 0 + beta + lp.1⟩
  let dPull := if lp.2.isEmpty then beta + lp.1 else vs.headD 0
  let ld := linearise (difference x.2 x.1) weights sent
  let vPush := vs.getD (if lp.2.isEmpty then 0 else 1) 0
  let lq := linearise x.2 weights sent
  let rels2 := if ld.2.isEmpty then rels1 else
    rels1.push ⟨lq.2.map (fun ck => match ck with | (c, k) => term (.table t.opcode c) pt k),
      vPush + beta + lq.1⟩
  let dPush := if ld.2.isEmpty then dPull + ld.1 else vPush
  (rels2, s.2.1 * dPull, s.2.2.1 * dPush, s.2.2.2.1 + tupleDegree x.1, s.2.2.2.2 + tupleDegree x.2)

/-- **A table's part of the values at `t`** (`tablePart`) from the values it reads. -/
def tablePartPure (t : Table) (logHeight : ℕ) (weights : Array E) (beta : E) (w : List E)
    (vs : List E) : TablePart × List Relation :=
  let s1 := consumeFold (fun _ => 1) (sentStep t (w.take logHeight)) (sentColumns t)
    (Array.replicate t.width none, #[]) (vs.take (sentColumns t).length)
  let s2 := consumeFold (flushReads weights s1.1) (flushStep t (w.take logHeight) weights beta s1.1)
    (t.flushes.pull.zip t.flushes.push) (s1.2, 1, 1, 1, 0) (vs.drop (sentColumns t).length)
  (⟨s2.2.1, s2.2.2.1, s2.2.2.2.1, s2.2.2.2.2, s1.1⟩, s2.1.toList)

/-- The columns a table sends. -/
def sentPat (t : Table) : Array (Option E) :=
  (consumeFold (fun _ => 1) (sentStep t []) (sentColumns t) (Array.replicate t.width none, #[]) []).1

/-- **The values a table's part reads**: its sent columns, and its flushes' sent fingerprints. -/
def tableReads (t : Table) : ℕ :=
  (sentColumns t).length + ((t.flushes.pull.zip t.flushes.push).map (flushReads #[] (sentPat t))).sum

theorem samePat_consume_sent (t : Table) : ∀ (cols : List ℕ) (pt pt' : List E)
    (s s' : Array (Option E) × Array Relation) (vs vs' : List E), SamePat s.1 s'.1 →
      SamePat (consumeFold (fun _ => 1) (sentStep t pt) cols s vs).1
        (consumeFold (fun _ => 1) (sentStep t pt') cols s' vs').1
  | [], _, _, _, _, _, _, h => h
  | c :: cols, pt, pt', s, s', vs, vs', h => by
    simp only [consumeFold]
    exact samePat_consume_sent t cols pt pt' _ _ _ _ (samePat_set h c _ _)

theorem samePat_refl (a : Array (Option E)) : SamePat a a := ⟨rfl, fun _ => rfl⟩

theorem sum_flushReads (t : Table) (weights : Array E) (sent : Array (Option E))
    (h : SamePat sent (sentPat t)) :
    ((t.flushes.pull.zip t.flushes.push).map (flushReads weights sent)).sum =
      ((t.flushes.pull.zip t.flushes.push).map (flushReads #[] (sentPat t))).sum := by
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  unfold flushReads
  rw [linearise_isEmpty_of_samePat h x.1 weights #[],
    linearise_isEmpty_of_samePat h (difference x.2 x.1) weights #[]]

theorem sum_map_one {α : Type} (l : List α) : (l.map fun _ => (1 : ℕ)).sum = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    omega

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem forIn_reads_of {α β : Type} (k : α → ℕ) (g : α → β → List E → β) (l : List α) (init : β)
    (f : α → β → ChanM m (ForInStep β))
    (hf : ∀ x s, f x s = (fun vs => ForInStep.yield (g x s vs)) <$> nextScalars (m := m) (k x)) :
    forIn l init f = (fun vs => consumeFold k g l init vs) <$> nextScalars (m := m) (l.map k).sum := by
  rw [show f = _ from funext fun x => funext fun s => hf x s]
  exact forIn_reads k g l init

theorem nextScalars_two : nextScalars (m := m) 2 = (do
    let a ← nextScalar (m := m)
    let b ← nextScalar (m := m)
    pure [a, b]) := by
  simp [nextScalars_eq, FlockSound.Uni.repeatM]

/-- **A table's part reads `tableReads t` values**, and computes from them. -/
theorem tablePart_eq (t : Table) (lh : ℕ) (weights : Array E) (beta : E) (w : List E) :
    tablePart (m := m) t lh weights beta w =
      (fun vs => tablePartPure t lh weights beta w vs) <$> nextScalars (m := m) (tableReads t) := by
  unfold tablePart
  simp only []
  rw [forIn_reads_of (fun _ => 1) (sentStep t (w.take lh))]
  swap
  · intro c s
    simp only [nextScalars_one, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    rfl
  rw [sum_map_one, tableReads, nextScalars_add, nextScalars_fix (sentColumns t).length]
  simp only [bind_map_left, map_bind, fixLen_fixLen]
  congr 1
  funext x
  have hpat := samePat_consume_sent t (sentColumns t) (List.take lh w) [] (Array.replicate t.width none, #[])
    (Array.replicate t.width none, #[]) (fixLen (sentColumns t).length x) [] (samePat_refl _)
  generalize hC : consumeFold (fun _ => 1) (sentStep t (List.take lh w)) (sentColumns t)
    (Array.replicate t.width none, #[]) (fixLen (sentColumns t).length x) = C at hpat
  rw [forIn_reads_of (flushReads weights C.1) (flushStep t (List.take lh w) weights beta C.1)]
  swap
  · intro xf s
    cases h1 : (linearise xf.1 weights C.1).2.isEmpty <;>
      cases h2 : (linearise (difference xf.2 xf.1) weights C.1).2.isEmpty <;>
      simp [flushReads, flushStep, h1, h2, nextScalars_two, nextScalars_one, nextScalars_zero]
  rw [sum_flushReads t weights C.1 hpat]
  simp only [map_pure, bind_map_left]
  congr 1
  funext y
  unfold tablePartPure
  simp only [List.take_left' (length_fixLen _ _), List.drop_left' (length_fixLen _ _), hC]

end Monad

end UniSound
