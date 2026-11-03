-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.SyncBasic

/-!
# The verifier's readers on the prover's bytes: the counts, a table's values at `t`

* **The counts** (`countBits_reads`): `countBits heights` reads the six 4-byte counts the prover writes
  (`integerWire n 4`, each `n < 2^32`), returns their bits (`countBitsOf`) and collects their range checks
  (`countChecks`: per table `intBits n (r + 1) 32`, `intBits n r 1 * intBits n 0 r`).
* **A table's values at `t`** (`tablePart_reads`): the verifier's `tablePart` reads exactly the values the prover's
  `tableValues` sends (its sent columns' values, then each flush's fingerprints when its tuple, or the difference,
  reads an unsent column: the same tests, on the same `sent` array, `sentOf`), and returns what it returns on
  those bytes alone (`runReader`, as the prover's `atTOf` runs it).
* **Loops in `Id`** (`id_forIn_eq`): a loop whose every pass yields `step s x` is the fold of `step`.

Decisions: the loop bodies are taken from the goal (unification up to `β`/`ζ`, never restated), the per-pass facts
proved on the reduced body; a table's result is an existential first (`tablePart_reads_ex`), named by `runReader`
after (`Reads.runReader`).
-/

namespace UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## Loops -/

/-- **A loop in `Id`** whose every pass yields `step s x` is the fold of `step`. -/
theorem id_forIn_eq {β γ : Type} (step : β → γ → β) (body : γ → β → Id (ForInStep β))
    (h : ∀ x s, body x s = Pure.pure (.yield (step s x))) :
    ∀ (xs : List γ) (s : β), (ForIn.forIn xs s body : Id β) = Pure.pure (xs.foldl step s)
  | [], _ => rfl
  | x :: xs, s => by
    rw [List.forIn_cons, h]
    exact id_forIn_eq step body h xs (step s x)

/-- **A loop whose every pass reads bytes of its element alone**, its states left unnamed. -/
theorem Reads.forIn_ex {β γ : Type} (bytes : γ → List UInt8) (body : γ → β → ChanM Id (ForInStep β)) :
    ∀ (xs : List γ), (∀ x ∈ xs, ∀ s, ∃ s', Reads (body x s) (bytes x) (.yield s') []) →
    ∀ s, ∃ s', Reads (ForIn.forIn xs s body) (xs.flatMap bytes) s' []
  | [], _, s => ⟨s, Reads.pure (α := β) s⟩
  | x :: xs, h, s => by
    rw [List.forIn_cons]
    obtain ⟨s1, h1⟩ := h x List.mem_cons_self s
    obtain ⟨s2, h2⟩ := Reads.forIn_ex bytes body xs (fun y hy ↦ h y (List.mem_cons_of_mem x hy)) s1
    exact ⟨s2, (h1.bind (f := fun r ↦ match r with
      | ForInStep.done b => Pure.pure b
      | ForInStep.yield b => ForIn.forIn xs b body) h2).congr (by simp) rfl rfl⟩

/-- **A reader's result is what it returns on its bytes alone** (`runReader`). -/
theorem Reads.runReader {α : Type} [Inhabited α] {v : ChanM Id α} {B : List UInt8} {a : α} {zs : List E}
    (h : Reads v B a zs) : UniComplete.runReader v B = a := by
  unfold UniComplete.runReader
  have hB : B <+: (Chan.start default B.toArray).data.toList.drop (Chan.start default B.toArray).cursor := by
    show B <+: B.toArray.toList.drop 0
    simp
  rw [h (Chan.start default B.toArray) (Nat.zero_le _) hB]

/-! ## The counts -/

/-- Each table's count's bits `0..=r`, as `countBits` returns them. -/
def countBitsOf (rows heights : List ℕ) : List (List E) :=
  List.zipWith (fun n r ↦ (List.range (r + 1)).map fun b ↦ intBits n b 1) rows heights

/-- **The values `countBits` collects**: per table, `c >> (r + 1)` and bit `r` times the low `r` bits. -/
def countChecks (rows heights : List ℕ) : List E :=
  (List.zipWith (fun n r ↦ [intBits n (r + 1) 32, intBits n r 1 * intBits n 0 r]) rows heights).flatten

/-- `countBits`'s loop body. -/
def countBody (r : ℕ) (out : Array (List E)) : ChanM Id (ForInStep (Array (List E))) := do
  let count ← nextInteger (m := Id) 4
  requireZero (m := Id) (intBits count (r + 1) 32)
  requireZero (m := Id) (intBits count r 1 * intBits count 0 r)
  Pure.pure (ForInStep.yield (out.push ((List.range (r + 1)).map fun b ↦ intBits count b 1)))

theorem countLoop_reads : ∀ (rows heights : List ℕ) (acc : Array (List E)), rows.length = heights.length →
    (∀ n ∈ rows, n < 2 ^ 32) →
    Reads (ForIn.forIn heights acc countBody) (rows.flatMap fun n ↦ integerWire n 4)
      (acc ++ (countBitsOf rows heights).toArray) (countChecks rows heights)
  | [], [], acc, _, _ => by
    simpa [countBitsOf, countChecks] using Reads.pure (α := Array (List E)) acc
  | n :: rows, r :: heights, acc, hlen, h32 => by
    rw [List.forIn_cons]
    have h1 : Reads (countBody r acc) (integerWire n 4)
        (.yield (acc.push ((List.range (r + 1)).map fun b ↦ intBits n b 1)))
        [intBits n (r + 1) 32, intBits n r 1 * intBits n 0 r] := by
      have := (nextInteger_reads (h32 n List.mem_cons_self)).bind (f := fun count ↦ do
          requireZero (m := Id) (intBits count (r + 1) 32)
          requireZero (m := Id) (intBits count r 1 * intBits count 0 r)
          Pure.pure (ForInStep.yield (acc.push ((List.range (r + 1)).map fun b ↦ intBits count b 1))))
        ((requireZero_reads _).bind ((requireZero_reads _).bind
          (Reads.pure (ForInStep.yield (acc.push ((List.range (r + 1)).map fun b ↦ intBits n b 1))))))
      exact this.congr (by simp) rfl (by simp)
    have h2 := countLoop_reads rows heights (acc.push ((List.range (r + 1)).map fun b ↦ intBits n b 1))
      (by simpa using hlen) (fun m hm ↦ h32 m (List.mem_cons_of_mem n hm))
    have e1 : acc ++ (countBitsOf (n :: rows) (r :: heights)).toArray =
        acc.push ((List.range (r + 1)).map fun b ↦ intBits n b 1) ++ (countBitsOf rows heights).toArray := by
      apply Array.toList_inj.mp
      simp [countBitsOf]
    have e2 : countChecks (n :: rows) (r :: heights) =
        [intBits n (r + 1) 32, intBits n r 1 * intBits n 0 r] ++ countChecks rows heights := by
      simp [countChecks]
    rw [List.flatMap_cons, e1, e2]
    refine Reads.bind h1 ?_
    exact h2
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

/-- **`countBits` reads the prover's counts**, returns their bits and collects their range checks. -/
theorem countBits_reads {rows heights : List ℕ} (hlen : rows.length = heights.length) (h32 : ∀ n ∈ rows, n < 2 ^ 32) :
    Reads (countBits (m := Id) heights) (rows.flatMap fun n ↦ integerWire n 4) (countBitsOf rows heights)
      (countChecks rows heights) := by
  have h := (countLoop_reads rows heights #[] hlen h32).bind_pure (f := Array.toList)
  exact h.congr rfl (by simp) rfl

/-! ## A table's values at `t` -/

/-- The `sent` array after the sent columns (`tablePart`'s first loop, `tableValues`'s). -/
def sentOf (t : Table) (val : ℕ → E) : Array (Option E) :=
  (sentColumns t).foldl (fun s c ↦ s.set! c (some (val c))) (Array.replicate t.width none)

/-- **A flush's values sent**: its pull fingerprint if its tuple reads an unsent column, its push fingerprint if
their difference does. -/
def flushValues (weights : Array E) (beta : E) (val : ℕ → E) (sent : Array (Option E)) (f : List Form × List Form) :
    List E :=
  (if (linearise f.1 weights sent).2.isEmpty then [] else [fpE f.1 weights beta val]) ++
    (if (linearise (difference f.2 f.1) weights sent).2.isEmpty then [] else [fpE f.2 weights beta val])

/-- `tableValues`'s second loop's pass, as a function. -/
def flushStep (weights : Array E) (beta : E) (val : ℕ → E) (sent : Array (Option E)) (out : Array E)
    (f : List Form × List Form) : Array E :=
  out ++ (flushValues weights beta val sent f).toArray

theorem foldl_pair_fst {α γ δ : Type} (f : α → γ → α) (g : δ → γ → δ) :
    ∀ (xs : List γ) (a : α) (d : δ), (xs.foldl (fun (s : α × δ) c ↦ (f s.1 c, g s.2 c)) (a, d)).1 = xs.foldl f a
  | [], _, _ => rfl
  | x :: xs, a, d => foldl_pair_fst f g xs (f a x) (g d x)

theorem foldl_pair_snd {α γ δ : Type} (f : α → γ → α) (g : δ → γ → δ) :
    ∀ (xs : List γ) (a : α) (d : δ), (xs.foldl (fun (s : α × δ) c ↦ (f s.1 c, g s.2 c)) (a, d)).2 = xs.foldl g d
  | [], _, _ => rfl
  | x :: xs, a, d => foldl_pair_snd f g xs (f a x) (g d x)

theorem foldl_append_toArray {α γ : Type} (g : γ → List α) :
    ∀ (xs : List γ) (acc : Array α), xs.foldl (fun out x ↦ out ++ (g x).toArray) acc = acc ++ (xs.flatMap g).toArray
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_append_toArray g xs]
    apply Array.toList_inj.mp
    simp

/-- **What `tableValues` sends**: the sent columns' values, then each flush's (`flushValues`). -/
theorem tableValues_eq (t : Table) (val : ℕ → E) (weights : Array E) (beta : E) :
    tableValues t val weights beta = (sentColumns t).map val ++
      (t.flushes.pull.zip t.flushes.push).flatMap (flushValues weights beta val (sentOf t val)) := by
  unfold tableValues
  dsimp only
  rw [id_forIn_eq (fun (s : Array (Option E) × Array E) c ↦ (s.1.set! c (some (val c)), s.2.push (val c))) _
    (fun _ _ ↦ rfl)]
  simp only [pure_bind]
  rw [id_forIn_eq (flushStep weights beta val (sentOf t val)) _ ?h2]
  case h2 =>
    intro f out
    obtain ⟨pulled, pushed⟩ := f
    have hs : (List.foldl (fun (s : Array (Option E) × Array E) c ↦ (s.1.set! c (some (val c)), s.2.push (val c)))
        (Array.replicate t.width none, #[]) (sentColumns t)).1 = sentOf t val :=
      foldl_pair_fst (α := Array (Option E)) (δ := Array E) (fun s c ↦ s.set! c (some (val c)))
        (fun s c ↦ s.push (val c)) _ _ _
    simp only [hs, flushStep, flushValues]
    by_cases h1 : (linearise pulled weights (sentOf t val)).2.isEmpty <;>
      by_cases h2 : (linearise (difference pushed pulled) weights (sentOf t val)).2.isEmpty <;>
      simp [h1, h2]
    congr 2
  show ((t.flushes.pull.zip t.flushes.push).foldl (flushStep weights beta val (sentOf t val))
    ((sentColumns t).foldl (fun (s : Array (Option E) × Array E) c ↦ (s.1.set! c (some (val c)), s.2.push (val c)))
      (Array.replicate t.width none, #[])).2).toList = _
  rw [foldl_pair_snd (α := Array (Option E)) (δ := Array E) (fun s c ↦ s.set! c (some (val c)))
    (fun s c ↦ s.push (val c)), foldl_push_map]
  unfold flushStep
  rw [foldl_append_toArray]
  simp

/-- A reader then a reader of bytes after it, results unnamed. -/
theorem Reads.bind_ex {α β : Type} {v : ChanM Id α} {f : α → ChanM Id β} {B1 B2 : List UInt8} {a : α}
    (h1 : Reads v B1 a []) (h2 : ∃ b, Reads (f a) B2 b []) : ∃ b, Reads (v >>= f) (B1 ++ B2) b [] :=
  let ⟨b, hb⟩ := h2
  ⟨b, (h1.bind hb).congr rfl rfl (by simp)⟩

/-- A reader, its result unnamed, then any reader of bytes after it. -/
theorem Reads.bind_ex2 {α β : Type} {v : ChanM Id α} {f : α → ChanM Id β} {B1 B2 : List UInt8}
    (h1 : ∃ a, Reads v B1 a []) (h2 : ∀ a, ∃ b, Reads (f a) B2 b []) : ∃ b, Reads (v >>= f) (B1 ++ B2) b [] :=
  let ⟨_, ha⟩ := h1
  Reads.bind_ex ha (h2 _)

/-- **`tablePart` reads the values `tableValues` sends** (on the same column values `val`), its result
unnamed. -/
theorem tablePart_reads_ex (t : Table) (r : ℕ) (weights : Array E) (beta : E) (w : List E) (val : ℕ → E) :
    ∃ res, Reads (tablePart (m := Id) t r weights beta w) ((tableValues t val weights beta).flatMap scalarWire)
      res [] := by
  rw [tableValues_eq, List.flatMap_append]
  have hA : ((sentColumns t).map val).flatMap scalarWire = (sentColumns t).flatMap (fun c ↦ scalarWire (val c)) := by
    simp [List.flatMap_map]
  have hB : ((t.flushes.pull.zip t.flushes.push).flatMap (flushValues weights beta val (sentOf t val))).flatMap
      scalarWire = (t.flushes.pull.zip t.flushes.push).flatMap
        (fun f ↦ (flushValues weights beta val (sentOf t val) f).flatMap scalarWire) ++ [] := by
    simp [List.flatMap_assoc]
  rw [hA, hB]
  unfold tablePart
  dsimp only
  refine Reads.bind_ex ((Reads.forIn (fun (s : Array (Option E) × Array Relation) c ↦
      (s.1.set! c (some (val c)), s.2.push (Relation.equal (Column.table t.opcode c) (w.take r) (val c))))
      (fun _ c ↦ scalarWire (val c)) (fun _ _ ↦ []) _ (sentColumns t) ?_ _).congr (loopBytes_const _ _ _ _)
      (show _ = (sentOf t val, (sentColumns t).foldl (fun s c ↦ s.push (Relation.equal (Column.table t.opcode c)
        (w.take r) (val c))) #[]) from ?_) (loopZeros_nil _ _ _)) ?_
  · intro c _ s
    exact (nextScalar_reads (val c)).bind_pure
  · exact Prod.ext (foldl_pair_fst (α := Array (Option E)) (δ := Array Relation) (fun s c ↦ s.set! c (some (val c)))
      (fun s c ↦ s.push (Relation.equal (Column.table t.opcode c) (w.take r) (val c))) _ _ _)
      (foldl_pair_snd (α := Array (Option E)) (δ := Array Relation) (fun s c ↦ s.set! c (some (val c)))
      (fun s c ↦ s.push (Relation.equal (Column.table t.opcode c) (w.take r) (val c))) _ _ _)
  dsimp only
  refine Reads.bind_ex2 (Reads.forIn_ex (fun f ↦ (flushValues weights beta val (sentOf t val) f).flatMap scalarWire)
    _ _ ?_ _) (fun _ ↦ ⟨_, Reads.pure _⟩)
  intro f _ s
  unfold flushValues
  cases h1 : (linearise f.1 weights (sentOf t val)).2.isEmpty <;>
    cases h2 : (linearise (difference f.2 f.1) weights (sentOf t val)).2.isEmpty <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  · exact ⟨_, ((nextScalar_reads (fpE f.1 weights beta val)).bind
      ((nextScalar_reads (fpE f.2 weights beta val)).bind_pure)).congr (by simp) rfl (by simp)⟩
  · exact ⟨_, ((nextScalar_reads (fpE f.1 weights beta val)).bind_pure).congr (by simp) rfl rfl⟩
  · exact ⟨_, ((nextScalar_reads (fpE f.2 weights beta val)).bind_pure).congr (by simp) rfl rfl⟩
  · exact ⟨_, (Reads.pure _).congr (by simp) rfl rfl⟩

/-- **`tablePart` reads the values `tableValues` sends and returns what it returns on them alone** (`runReader`,
as `atTOf` runs it). -/
theorem tablePart_reads (t : Table) (r : ℕ) (weights : Array E) (beta : E) (w : List E) (val : ℕ → E) :
    Reads (tablePart (m := Id) t r weights beta w) ((tableValues t val weights beta).flatMap scalarWire)
      (runReader (tablePart (m := Id) t r weights beta w) ((tableValues t val weights beta).flatMap scalarWire)) [] := by
  obtain ⟨res, h⟩ := tablePart_reads_ex t r weights beta w val
  rwa [h.runReader]

/-! ## The tables' values at `t`: the verifier's loop, `atTOf`'s -/

section Tables

variable (tr : Trace) (weights : Array E) (beta : E) (w : List E)

/-- Table `table`'s column values at `t` (`atTOf`'s `at_`). -/
def colAt (table : Table) (c : ℕ) : E :=
  evalB ((bCoefficients (tr.shape.heights.getD table.opcode 0) (tr.column table.opcode c)).map ofK)
    (tr.shape.heights.getD table.opcode 0) w

/-- What table `table` sends at `t` (`atTOf`'s `values`). -/
def tvals (table : Table) : List E := tableValues table (colAt tr w table) weights beta

/-- Table `table`'s part and relations, the verifier's `tablePart` on what it sends (`atTOf`'s). -/
def tres (table : Table) : TablePart × List Relation :=
  runReader (tablePart (m := Id) table (tr.shape.heights.getD table.opcode 0) weights beta w)
    ((tvals tr weights beta w table).flatMap scalarWire)

/-- A pass of the verifier's loop over the tables (`reduceWith`, step 4). -/
def vStep (s : Array Relation × Array TablePart) (table : Table) : Array Relation × Array TablePart :=
  (s.1 ++ (tres tr weights beta w table).2.toArray, s.2.push (tres tr weights beta w table).1)

/-- A pass of `atTOf`'s loop over the tables. -/
def atTStep (s : Array E × Array Relation × Array TablePart) (table : Table) :
    Array E × Array Relation × Array TablePart :=
  (s.1 ++ (tvals tr weights beta w table).toArray, s.2.1 ++ (tres tr weights beta w table).2.toArray,
    s.2.2.push (tres tr weights beta w table).1)

/-- **The verifier's loop over the tables reads every table's values**, in order, and folds `vStep`. -/
theorem tablesLoop_reads (body : Table → Array Relation × Array TablePart →
      ChanM Id (ForInStep (Array Relation × Array TablePart)))
    (hbody : ∀ table s, body table s =
      (tablePart (m := Id) table (tr.shape.heights.getD table.opcode 0) weights beta w >>= fun res ↦
        Pure.pure (ForInStep.yield (s.1 ++ res.2.toArray, s.2.push res.1)))) (ts : List Table)
    (s : Array Relation × Array TablePart) :
    Reads (ForIn.forIn ts s body) ((ts.flatMap (tvals tr weights beta w)).flatMap scalarWire)
      (ts.foldl (vStep tr weights beta w) s) [] := by
  have h := Reads.forIn (vStep tr weights beta w) (fun _ table ↦ (tvals tr weights beta w table).flatMap scalarWire)
    (fun _ _ ↦ []) body ts (fun table _ s ↦ by
      rw [hbody]
      exact (tablePart_reads table _ weights beta w (colAt tr w table)).bind_pure) s
  rw [loopBytes_const, loopZeros_nil] at h
  exact h.congr (by simp [List.flatMap_assoc]) rfl rfl

/-- `atTOf`'s loop folds `atTStep`. -/
theorem atTLoop_eq (body : Table → Array E × Array Relation × Array TablePart →
      Id (ForInStep (Array E × Array Relation × Array TablePart)))
    (hbody : ∀ table s, body table s = Pure.pure (ForInStep.yield (atTStep tr weights beta w s table)))
    (ts : List Table) (s : Array E × Array Relation × Array TablePart) :
    (ForIn.forIn ts s body : Id _) = Pure.pure (ts.foldl (atTStep tr weights beta w) s) :=
  id_forIn_eq _ body (fun x s ↦ hbody x s) ts s

/-- `atTOf`'s loop's values: every table's, in order. -/
theorem atTFold_fst : ∀ (ts : List Table) (s : Array E × Array Relation × Array TablePart),
    (ts.foldl (atTStep tr weights beta w) s).1 = s.1 ++ (ts.flatMap (tvals tr weights beta w)).toArray
  | [], s => by simp
  | t :: ts, s => by
    rw [List.foldl_cons, atTFold_fst ts]
    apply Array.toList_inj.mp
    simp [atTStep]

/-- `atTOf`'s loop's relations and parts are the verifier's loop's. -/
theorem atTFold_snd : ∀ (ts : List Table) (s : Array E × Array Relation × Array TablePart),
    (ts.foldl (atTStep tr weights beta w) s).2 = ts.foldl (vStep tr weights beta w) s.2
  | [], _ => rfl
  | t :: ts, s => by
    rw [List.foldl_cons, atTFold_snd ts, List.foldl_cons]
    rfl

end Tables

end UniComplete

/-- info: 'UniComplete.countBits_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.countBits_reads

/-- info: 'UniComplete.tablePart_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.tablePart_reads

/-- info: 'UniComplete.tablesLoop_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.tablesLoop_reads
