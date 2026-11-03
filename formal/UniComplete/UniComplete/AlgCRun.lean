-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The fixed-read toolkit (`runReads`, `runConsume`,
-- `runForIn_reads`, the `linearise` emptiness lemmas, `runTablePart_eq`) is ported from this repository's
-- `formal/UniSound/UniSound/{CodeBase,CodeTables}.lean` (branch `lean-uni-code`: `repeatM`, `consumeFold`,
-- `forIn_reads`, `linearise_isEmpty`, `tablePart_eq`), renamed with a `run` prefix and specialised to reads of
-- single scalars, so that `UniComplete` does not import `UniSound`.
import UniComplete.Honest
import UniComplete.Domain

/-!
# The honest prover's values at `t`, run through the verifier's own code (milestone 4, layer AlgC)

`atTOf` computes the relations the verifier states by running the verifier's `tablePart` (a channel program)
on the bytes of what each table sends (`runReader … (tableValues …).flatMap scalarWire`). Here that run is
computed, and `atTOf`'s relation list is written out piece by piece:

* **A1, reading back** (`beWordAt_be64`, `eNew_scalarWire`, `nextScalar_run`, `runReads_run`,
  `runReader_reads`): on a channel whose unread bytes are `vs.flatMap scalarWire ++ rest` (`ReadsAt`),
  `nextScalar` returns the next scalar and advances the cursor by `24`; `n` reads return the next `n`.
* **A2, `tablePart` on the honest values** (`tablePart_run`): `tablePart` reads a fixed number of scalars
  (`runTablePart_eq`, `runTableReads`, ported), `tableValues` is that many (`runTableReads_eq`,
  `tableValues_eq`), so the run is `tablePartOf`, the verifier's part with every read replaced by the honest
  value: a sent column `c` is `at_ c`, a sent fingerprint is `fpE` of its tuple at `at_`.
* **A3** (`tablePartOf_sent`, `runSentArr_some`): the sent array holds `at_ c` at every sent column, and only
  honest values.
* **A4, `linearise` is exact** (`RunShape`, `runShape_tables`, `linearise_exact`, `linearise_mem`): every
  monomial of every pull tuple, push tuple and their difference has degree at most two, a product has a sent
  factor, every index is a column (`decide +kernel` on the six tables, under a second); so `linearise`'s known
  part, plus its terms at the honest values, plus `β`, is the tuple's fingerprint `fpE`.
* **A5** (`tablePartOf_holds`, `tablePartOf_terms`, `tablePartOf_c1`): every relation a table states holds of
  any evaluation `ev` of its terms that gives its column `c` at `w[..r]` the value `at_ c`, and every term is a
  column of the table at `w[..r]` (so the relation is on `C1`); `tablePartOf_pull`, `tablePartOf_push`,
  `tablePartOf_degrees`: the leaf's products are the products of the flushes' pull and push fingerprints
  (`fpE_difference`: the difference tuple's fingerprint is the push's plus the pull's, `β` aside), its degrees
  `tableDegrees`.
* **A6, `atTOf` piece by piece, without Flock's output** (`atTOf_relations`, `atTOf_values`,
  `atTOf_c2Columns`, `atTOf_ringMap`, `atTOf_pending`): the tables' relations (`atTableRels`), the memory's
  three (`atMemoryRels`), the bytecode's two (`atBytecodeRels`), the constraint quotient's identity
  (`atConstraint`), the heap's (`atHeap`), each a small definition with `atTOf`'s own `let`s (`atW`,
  `atColumn`, `atParts`, …).
* **A7** (`heapRelations_c2`, `chunks_succ_ne_nil`): the heap's relations are on `C2` when the constraint
  quotient has a chunk, which it has (`chunks (n + 1) ≠ []`).

Decisions (recorded): `tablePartOf` is written explicitly (its relations a `flatMap` over the flushes, its
products folds), rather than as `runTablePartPure` of the values, so that A3–A5 are read off it; the shape
property is a `Bool` decided by the kernel on the tables (no `native_decide`); `tablePart` is proved equal to
a pure function of a fixed number of reads for every lawful monad (the ported `runTablePart_eq`), then run in
`Id`.
-/

open UniStatement LeanVM.Parameters

namespace UniComplete.AlgC

/-! ### Big-endian words read back -/

theorem run_shift_or (acc : UInt64) (b : UInt8) (h : acc.toNat < 2 ^ 56) :
    ((acc <<< 8) ||| b.toUInt64).toNat = acc.toNat * 256 + b.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
  rw [h8, Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by have := b.toNat_lt; simpa using this), Nat.shiftLeft_eq]

theorem run_be64_getD (u : UInt64) {k : ℕ} (hk : k < 8) :
    ((be64 u).getD k 0).toNat = u.toNat / 2 ^ (8 * (7 - k)) % 256 := by
  rw [be64, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have : (8 * (7 - k)).toUInt64.toNat % 64 = 8 * (7 - k) := by
    interval_cases k <;> rfl
  rw [this]

/-- The fold of `beWordAt` over the first `k` bytes of `be64 u`: the top `k` bytes of `u`. -/
theorem run_fold_be64 (u : UInt64) (f : ℕ → UInt8) (hf : ∀ k < 8, f k = (be64 u).getD k 0) :
    ∀ k ≤ 8, ((List.range k).foldl (fun (acc : UInt64) j ↦ (acc <<< 8) ||| (f j).toUInt64) 0).toNat =
      u.toNat / 2 ^ (8 * (8 - k))
  | 0, _ => by
    simp only [List.range_zero, List.foldl_nil, UInt64.toNat_zero]
    have := u.toNat_lt
    rw [Nat.div_eq_of_lt (by simpa using this)]
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := run_fold_be64 u f hf k (by omega)
    have hlt : u.toNat / 2 ^ (8 * (8 - k)) < 2 ^ 56 := by
      have := u.toNat_lt
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      calc u.toNat < 2 ^ 64 := by simpa using this
        _ ≤ 2 ^ (56 + 8 * (8 - k)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [run_shift_or _ _ (by rw [ih]; exact hlt), ih, hf k (by omega), run_be64_getD u (by omega)]
    have e : 8 * (8 - k) = 8 * (7 - k) + 8 := by omega
    rw [e, pow_add, ← Nat.div_div_eq_div_mul]
    have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
    rw [h256, show 8 - (k + 1) = 7 - k by omega]
    exact Nat.div_add_mod' _ _

/-- **`beWordAt` reads back `be64`.** -/
theorem beWordAt_be64 (pre post : List UInt8) (u : UInt64) :
    beWordAt (pre ++ be64 u ++ post).toArray pre.length = u := by
  unfold beWordAt
  apply UInt64.toNat_inj.mp
  have hb : (be64 u).length = 8 := by simp [be64]
  rw [run_fold_be64 u (fun k ↦ (pre ++ be64 u ++ post).toArray.getD (pre.length + k) 0) (fun k hk ↦ by
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]) 8 le_rfl]
  simp



/-! ### Reads of a fixed number of scalars -/

/-- A list cut or padded with zeros to length `n`. -/
def runFix (n : ℕ) (l : List E) : List E := (List.range n).map fun i => l.getD i 0

@[simp] theorem runFix_length (n : ℕ) (l : List E) : (runFix n l).length = n := by
  simp [runFix]

theorem runFix_succ_cons (n : ℕ) (a : E) (l : List E) : runFix (n + 1) (a :: l) = a :: runFix n l := by
  simp [runFix, List.range_succ_eq_map, Function.comp_def]

theorem runFix_of_length {n : ℕ} {l : List E} (h : l.length = n) : runFix n l = l := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [runFix, List.getD_eq_getElem?_getD, h2]

@[simp] theorem runFix_runFix (n : ℕ) (l : List E) : runFix n (runFix n l) = runFix n l :=
  runFix_of_length (runFix_length n l)

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- `n` reads of a scalar, in order. -/
def runReads : ℕ → ChanM m (List E)
  | 0 => pure []
  | n + 1 => do
    let a ← nextScalar (m := m)
    let l ← runReads n
    pure (a :: l)

theorem runReads_fix : ∀ n, runReads (m := m) n = runFix n <$> runReads (m := m) n
  | 0 => by simp [runReads, runFix]
  | n + 1 => by
    conv_lhs => rw [runReads, runReads_fix n]
    simp only [runReads, map_bind, map_pure, bind_map_left, runFix_succ_cons]

theorem runReads_add (a b : ℕ) : runReads (m := m) (a + b) = (do
    let x ← runReads (m := m) a
    let y ← runReads (m := m) b
    pure (runFix a x ++ y)) := by
  have h : ∀ a, runReads (m := m) (a + b) = (do
      let x ← runReads (m := m) a
      let y ← runReads (m := m) b
      pure (x ++ y)) := by
    intro a
    induction a with
    | zero => simp [runReads]
    | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega]
      simp only [runReads, ih, bind_assoc, pure_bind, List.cons_append]
  rw [h a]
  conv_lhs => rw [runReads_fix a]
  simp only [bind_map_left]

omit [LawfulMonad m] in
theorem runReads_zero : runReads (m := m) 0 = pure [] := rfl

theorem runReads_one : runReads (m := m) 1 = (fun x => [x]) <$> nextScalar (m := m) := by
  simp [runReads, map_eq_bind_pure_comp]

theorem runReads_two : runReads (m := m) 2 = (do
    let a ← nextScalar (m := m)
    let b ← nextScalar (m := m)
    pure [a, b]) := by
  simp [runReads]

/-! ### Loops of fixed reads -/

/-- **Consume a list of values in order**: each element `x` takes the next `k x` values. -/
def runConsume {α β : Type} (k : α → ℕ) (g : α → β → List E → β) : List α → β → List E → β
  | [], b, _ => b
  | x :: xs, b, vs => runConsume k g xs (g x b (vs.take (k x))) (vs.drop (k x))

theorem runConsume_append {α β : Type} (k : α → ℕ) (g : α → β → List E → β) (x : α) (b : β)
    (xs : List α) (vs ws : List E) (h : vs.length = k x) :
    runConsume k g (x :: xs) b (vs ++ ws) = runConsume k g xs (g x b vs) ws := by
  simp [runConsume, List.take_left' h, List.drop_left' h]

/-- **A loop of fixed reads** is one read, consumed in order. -/
theorem runForIn_reads {α β : Type} (k : α → ℕ) (g : α → β → List E → β) :
    ∀ (l : List α) (init : β),
      forIn l init (fun x s => (fun vs => ForInStep.yield (g x s vs)) <$> runReads (m := m) (k x)) =
        (fun vs => runConsume k g l init vs) <$> runReads (m := m) (l.map k).sum
  | [], init => by simp [runConsume, runReads]
  | x :: xs, init => by
    rw [List.forIn_cons, List.map_cons, List.sum_cons, runReads_add, runReads_fix (k x)]
    simp only [bind_map_left, map_bind, map_pure, runFix_runFix]
    congr 1
    funext vs
    rw [runForIn_reads k g xs]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    congr 1
    funext ws
    rw [runConsume_append _ _ _ _ _ _ _ (runFix_length _ _)]

theorem runForIn_reads_of {α β : Type} (k : α → ℕ) (g : α → β → List E → β) (l : List α) (init : β)
    (f : α → β → ChanM m (ForInStep β))
    (hf : ∀ x s, f x s = (fun vs => ForInStep.yield (g x s vs)) <$> runReads (m := m) (k x)) :
    forIn l init f = (fun vs => runConsume k g l init vs) <$> runReads (m := m) (l.map k).sum := by
  rw [show f = _ from funext fun x => funext fun s => hf x s]
  exact runForIn_reads k g l init

end Monad


def runLinInner (weight : E) (sent : Array (Option E)) (acc : E × List (ℕ × E)) (mc : List ℕ × E) :
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
def runLinOuter (weights : Array E) (sent : Array (Option E)) (acc : E × List (ℕ × E))
    (x : Form × ℕ) : E × List (ℕ × E) :=
  x.1.foldl (runLinInner (weights.getD x.2 0) sent) acc

theorem runLinearise_eq (tuple : List Form) (weights : Array E) (sent : Array (Option E)) :
    linearise tuple weights sent =
      (tuple.zip (List.range tuple.length)).foldl (runLinOuter weights sent) (0, []) := by
  unfold linearise runLinOuter runLinInner
  rfl

/-- **A monomial makes `linearise` add a term**: a nonzero coefficient on exactly one unsent
factor. -/
def runAddsTerm (sent : Array (Option E)) (mc : List ℕ × E) : Bool :=
  decide (mc.2 ≠ 0) &&
    match mc.1 with
    | [i] => (sent.getD i none).isNone
    | [i, j] => (sent.getD i none).isSome != (sent.getD j none).isSome
    | _ => false

theorem runAddTerm_isEmpty (terms : List (ℕ × E)) (i : ℕ) (c : E) :
    (addTerm terms i c).isEmpty = false := by
  unfold addTerm
  split
  · rename_i j hj
    have hne : terms ≠ [] := by
      rintro rfl
      simp at hj
    simp [hne]
  · simp

theorem runLinInner_isEmpty (weight : E) (sent : Array (Option E)) (acc : E × List (ℕ × E))
    (mc : List ℕ × E) :
    (runLinInner weight sent acc mc).2.isEmpty = (acc.2.isEmpty && !runAddsTerm sent mc) := by
  rcases mc with ⟨monomial, coefficient⟩
  rcases acc with ⟨known, terms⟩
  unfold runLinInner runAddsTerm
  by_cases hc : coefficient = 0
  · simp [hc]
  · simp only [hc, ite_false, ne_eq, not_false_eq_true, decide_true, Bool.true_and]
    rcases monomial with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
    · simp
    · simp only [Array.getD_eq_getD_getElem?]
      generalize (sent[i]?).getD none = oi
      cases oi <;> simp [runAddTerm_isEmpty]
    · simp only [Array.getD_eq_getD_getElem?]
      generalize (sent[i]?).getD none = oi
      generalize (sent[j]?).getD none = oj
      cases oi <;> cases oj <;> simp [runAddTerm_isEmpty]
    · simp

theorem runFoldl_linInner_isEmpty (weight : E) (sent : Array (Option E)) :
    ∀ (form : Form) (acc : E × List (ℕ × E)),
      (form.foldl (runLinInner weight sent) acc).2.isEmpty =
        (acc.2.isEmpty && form.all fun mc => !runAddsTerm sent mc)
  | [], acc => by simp
  | mc :: form, acc => by
    rw [List.foldl_cons, runFoldl_linInner_isEmpty weight sent form, runLinInner_isEmpty, List.all_cons,
      Bool.and_assoc]

theorem runFoldl_linOuter_isEmpty (weights : Array E) (sent : Array (Option E)) :
    ∀ (l : List (Form × ℕ)) (acc : E × List (ℕ × E)),
      (l.foldl (runLinOuter weights sent) acc).2.isEmpty =
        (acc.2.isEmpty && l.all fun x => x.1.all fun mc => !runAddsTerm sent mc)
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, runFoldl_linOuter_isEmpty weights sent l, runLinOuter, runFoldl_linInner_isEmpty,
      List.all_cons, Bool.and_assoc]

/-- **`linearise`'s terms are empty** exactly when no monomial has one unsent factor. -/
theorem runLinearise_isEmpty (tuple : List Form) (weights : Array E) (sent : Array (Option E)) :
    (linearise tuple weights sent).2.isEmpty =
      (tuple.zip (List.range tuple.length)).all fun x => x.1.all fun mc => !runAddsTerm sent mc := by
  rw [runLinearise_eq, runFoldl_linOuter_isEmpty]
  simp

/-- **The same columns sent.** -/
def RunSamePat (a b : Array (Option E)) : Prop :=
  a.size = b.size ∧ ∀ i, (a.getD i none).isSome = (b.getD i none).isSome

theorem runIsNone_eq_not_isSome (o : Option E) : o.isNone = !o.isSome := by cases o <;> rfl

theorem runAddsTerm_of_samePat {a b : Array (Option E)} (h : RunSamePat a b) (mc : List ℕ × E) :
    runAddsTerm a mc = runAddsTerm b mc := by
  unfold runAddsTerm
  rcases mc with ⟨monomial, c⟩
  rcases monomial with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
  · rfl
  · simp only [runIsNone_eq_not_isSome, h.2 i]
  · simp only [h.2 i, h.2 j]
  · rfl

theorem runLinearise_isEmpty_of_samePat {a b : Array (Option E)} (h : RunSamePat a b) (tuple : List Form)
    (wa wb : Array E) : (linearise tuple wa a).2.isEmpty = (linearise tuple wb b).2.isEmpty := by
  rw [runLinearise_isEmpty, runLinearise_isEmpty]
  simp only [runAddsTerm_of_samePat h]

theorem runSamePat_set {a b : Array (Option E)} (h : RunSamePat a b) (c : ℕ) (x y : E) :
    RunSamePat (a.set! c (some x)) (b.set! c (some y)) := by
  refine ⟨by simp [h.1], fun i => ?_⟩
  have hi := h.2 i
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, h.1] at hi ⊢
  split_ifs <;> simp_all

/-! ## A table's part of the values at `t` -/

/-- One sent column's read (`tablePart`'s first loop): the value set, and bound at `w[..r]`. -/
def runSentStep (t : Table) (pt : List E) (column : ℕ) (s : Array (Option E) × Array Relation)
    (vs : List E) : Array (Option E) × Array Relation :=
  (s.1.set! column (some (vs.headD 0)),
    s.2.push (Relation.equal (.table t.opcode column) pt (vs.headD 0)))

/-- **The fingerprints of a flush that are sent**: the pull's if its tuple has a term in an unsent
column, the push's if the difference has. -/
def runFlushReads (weights : Array E) (sent : Array (Option E)) (x : List Form × List Form) : ℕ :=
  (if (linearise x.1 weights sent).2.isEmpty then 0 else 1) +
    (if (linearise (difference x.2 x.1) weights sent).2.isEmpty then 0 else 1)

/-- One flush (`tablePart`'s second loop) from its sent fingerprints `vs`. -/
def runFlushStep (t : Table) (pt : List E) (weights : Array E) (beta : E) (sent : Array (Option E))
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
def runTablePartPure (t : Table) (logHeight : ℕ) (weights : Array E) (beta : E) (w : List E)
    (vs : List E) : TablePart × List Relation :=
  let s1 := runConsume (fun _ => 1) (runSentStep t (w.take logHeight)) (sentColumns t)
    (Array.replicate t.width none, #[]) (vs.take (sentColumns t).length)
  let s2 := runConsume (runFlushReads weights s1.1) (runFlushStep t (w.take logHeight) weights beta s1.1)
    (t.flushes.pull.zip t.flushes.push) (s1.2, 1, 1, 1, 0) (vs.drop (sentColumns t).length)
  (⟨s2.2.1, s2.2.2.1, s2.2.2.2.1, s2.2.2.2.2, s1.1⟩, s2.1.toList)

/-- The columns a table sends. -/
def runSentPat (t : Table) : Array (Option E) :=
  (runConsume (fun _ => 1) (runSentStep t []) (sentColumns t) (Array.replicate t.width none, #[]) []).1

/-- **The values a table's part reads**: its sent columns, and its flushes' sent fingerprints. -/
def runTableReads (t : Table) : ℕ :=
  (sentColumns t).length + ((t.flushes.pull.zip t.flushes.push).map (runFlushReads #[] (runSentPat t))).sum

theorem runSamePat_consume_sent (t : Table) : ∀ (cols : List ℕ) (pt pt' : List E)
    (s s' : Array (Option E) × Array Relation) (vs vs' : List E), RunSamePat s.1 s'.1 →
      RunSamePat (runConsume (fun _ => 1) (runSentStep t pt) cols s vs).1
        (runConsume (fun _ => 1) (runSentStep t pt') cols s' vs').1
  | [], _, _, _, _, _, _, h => h
  | c :: cols, pt, pt', s, s', vs, vs', h => by
    simp only [runConsume]
    exact runSamePat_consume_sent t cols pt pt' _ _ _ _ (runSamePat_set h c _ _)

theorem runSamePat_refl (a : Array (Option E)) : RunSamePat a a := ⟨rfl, fun _ => rfl⟩

theorem runSum_flushReads (t : Table) (weights : Array E) (sent : Array (Option E))
    (h : RunSamePat sent (runSentPat t)) :
    ((t.flushes.pull.zip t.flushes.push).map (runFlushReads weights sent)).sum =
      ((t.flushes.pull.zip t.flushes.push).map (runFlushReads #[] (runSentPat t))).sum := by
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  unfold runFlushReads
  rw [runLinearise_isEmpty_of_samePat h x.1 weights #[],
    runLinearise_isEmpty_of_samePat h (difference x.2 x.1) weights #[]]

theorem runSum_map_one {α : Type} (l : List α) : (l.map fun _ => (1 : ℕ)).sum = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    omega

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **A table's part reads `runTableReads t` values**, and computes from them. -/
theorem runTablePart_eq (t : Table) (lh : ℕ) (weights : Array E) (beta : E) (w : List E) :
    tablePart (m := m) t lh weights beta w =
      (fun vs => runTablePartPure t lh weights beta w vs) <$> runReads (m := m) (runTableReads t) := by
  unfold tablePart
  simp only []
  rw [runForIn_reads_of (fun _ => 1) (runSentStep t (w.take lh))]
  swap
  · intro c s
    simp only [runReads_one, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    rfl
  rw [runSum_map_one, runTableReads, runReads_add, runReads_fix (sentColumns t).length]
  simp only [bind_map_left, map_bind, runFix_runFix]
  congr 1
  funext x
  have hpat := runSamePat_consume_sent t (sentColumns t) (List.take lh w) [] (Array.replicate t.width none, #[])
    (Array.replicate t.width none, #[]) (runFix (sentColumns t).length x) [] (runSamePat_refl _)
  generalize hC : runConsume (fun _ => 1) (runSentStep t (List.take lh w)) (sentColumns t)
    (Array.replicate t.width none, #[]) (runFix (sentColumns t).length x) = C at hpat
  rw [runForIn_reads_of (runFlushReads weights C.1) (runFlushStep t (List.take lh w) weights beta C.1)]
  swap
  · intro xf s
    cases h1 : (linearise xf.1 weights C.1).2.isEmpty <;>
      cases h2 : (linearise (difference xf.2 xf.1) weights C.1).2.isEmpty <;>
      simp [runFlushReads, runFlushStep, h1, h2, runReads_two, runReads_one, runReads_zero]
  rw [runSum_flushReads t weights C.1 hpat]
  simp only [map_pure, bind_map_left]
  congr 1
  funext y
  unfold runTablePartPure
  simp only [List.take_left' (runFix_length _ _), List.drop_left' (runFix_length _ _), hC]

end Monad

/-! ### The channel's operations, run -/

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem runGet (c : Chan) : ((get : ChanM m Chan).run.run c) = pure (Except.ok c, c) := by
  have h : (StateT.get : StateT Chan m Chan).run c = pure (c, c) := rfl
  simp [get, getThe, MonadStateOf.get, h]

theorem runSet (c c' : Chan) :
    ((set c' : ChanM m PUnit).run.run c) = pure (Except.ok ⟨⟩, c') := by
  have h : (StateT.set c' : StateT Chan m PUnit).run c = pure (PUnit.unit, c') := rfl
  simp [set, MonadStateOf.set, h]

theorem runTakeBytes (n : ℕ) (c : Chan) :
    (takeBytes (m := m) n).run.run c =
      if c.cursor + n ≤ c.data.size then
        pure (.ok (c.data.extract c.cursor (c.cursor + n)), { c with cursor := c.cursor + n })
      else pure (.error .streamExhausted, c) := by
  simp only [takeBytes, ExceptT.run_bind, StateT.run_bind, runGet, pure_bind]
  by_cases h : c.cursor + n ≤ c.data.size
  · simp only [h, ite_true, ExceptT.run_bind, StateT.run_bind, runSet, pure_bind]
    rfl
  · simp only [h, ite_false]
    rfl

end Monad

/-! ### Scalars read back -/

@[simp] theorem runBe64_length (u : UInt64) : (be64 u).length = 8 := by simp [be64]

@[simp] theorem scalarWire_length (x : E) : (scalarWire x).length = 24 := by
  simp [scalarWire]

/-- **The channel's unread bytes** are the scalars `vs`, then `rest`. -/
def ReadsAt (c : Chan) (vs : List E) (rest : List UInt8) : Prop :=
  c.data.toList.drop c.cursor = vs.flatMap scalarWire ++ rest

/-- **A scalar's 24 bytes read back.** -/
theorem eNew_scalarWire (x : E) :
    eNew (beWordAt (scalarWire x).toArray 16) (beWordAt (scalarWire x).toArray 8)
      (beWordAt (scalarWire x).toArray 0) = x := by
  have h16 := beWordAt_be64 (be64 (x.limb 2).lane ++ be64 (x.limb 1).lane) [] (x.limb 0).lane
  have h8 := beWordAt_be64 (be64 (x.limb 2).lane) (be64 (x.limb 0).lane) (x.limb 1).lane
  have h0 := beWordAt_be64 [] (be64 (x.limb 1).lane ++ be64 (x.limb 0).lane) (x.limb 2).lane
  simp only [List.append_nil, List.length_append, runBe64_length, List.nil_append,
    List.length_nil] at h16 h8 h0
  rw [← List.append_assoc] at h0
  unfold scalarWire
  rw [h16, h8, h0]
  exact ofLimbs_limb x

/-- **`next_scalar` reads back `scalarWire`** (A1): on a channel whose unread bytes start with `scalarWire x`,
`nextScalar` returns `x` and advances the cursor by `24`, nothing else changed. -/
theorem nextScalar_run (c : Chan) (x : E) (vs : List E) (rest : List UInt8) (h : ReadsAt c (x :: vs) rest) :
    (nextScalar (m := Id)).run.run c = pure (.ok x, { c with cursor := c.cursor + 24 }) ∧
      ReadsAt { c with cursor := c.cursor + 24 } vs rest := by
  have hlen : c.cursor + 24 ≤ c.data.size := by
    have := congrArg List.length h
    simp only [List.length_drop, Array.length_toList, List.flatMap_cons, List.length_append,
      scalarWire_length] at this
    omega
  have hext : c.data.extract c.cursor (c.cursor + 24) = (scalarWire x).toArray := by
    apply Array.ext'
    rw [Array.toList_extract, List.extract_eq_take_drop, h, Nat.add_sub_cancel_left, List.flatMap_cons,
      List.append_assoc, List.take_left' (scalarWire_length x)]
  refine ⟨?_, ?_⟩
  · simp only [nextScalar, ExceptT.run_bind, StateT.run_bind, runTakeBytes, hlen, ite_true, pure_bind]
    rw [hext]
    simp only [ExceptT.run_pure, StateT.run_pure]
    rw [eNew_scalarWire]
  · unfold ReadsAt at h ⊢
    simp only
    rw [← List.drop_drop, h, List.flatMap_cons, List.append_assoc, List.drop_left' (scalarWire_length x)]

/-- **`n` reads** of the next `n` scalars. -/
theorem runReads_run : ∀ (vs ws : List E) (rest : List UInt8) (c : Chan), ReadsAt c (vs ++ ws) rest →
    (runReads (m := Id) vs.length).run.run c = pure (.ok vs, { c with cursor := c.cursor + 24 * vs.length }) ∧
      ReadsAt { c with cursor := c.cursor + 24 * vs.length } ws rest
  | [], ws, rest, c, h => by
    refine ⟨rfl, ?_⟩
    simpa using h
  | x :: vs, ws, rest, c, h => by
    obtain ⟨h1, h2⟩ := nextScalar_run c x (vs ++ ws) rest h
    obtain ⟨h3, h4⟩ := runReads_run vs ws rest _ h2
    simp only [List.length_cons] at h4 ⊢
    have hc : c.cursor + 24 + 24 * vs.length = c.cursor + 24 * (vs.length + 1) := by ring
    rw [hc] at h3 h4
    refine ⟨?_, h4⟩
    simp only [runReads, ExceptT.run_bind, StateT.run_bind, h1, pure_bind]
    simp only [h3, pure_bind, ExceptT.run_pure, StateT.run_pure]

/-- **The prover's reader on the bytes of `vs`** returns what a function of `|vs|` reads computes from `vs`. -/
theorem runReader_reads {α : Type} [Inhabited α] (f : List E → α) (vs : List E) :
    runReader (f <$> runReads (m := Id) vs.length) (vs.flatMap scalarWire) = f vs := by
  have h : ReadsAt (Chan.start default (vs.flatMap scalarWire).toArray) (vs ++ []) [] := by
    simp [ReadsAt, Chan.start]
  obtain ⟨h1, -⟩ := runReads_run vs [] [] _ h
  unfold runReader
  simp only [ExceptT.run_map, StateT.run_map, h1]
  rfl

/-! ### A table's honest values and part -/

/-- **The columns a table sends, at the honest values.** -/
def runSentArr (table : Table) (at_ : ℕ → E) : Array (Option E) :=
  (sentColumns table).foldl (fun s c ↦ s.set! c (some (at_ c))) (Array.replicate table.width none)

/-- A flush's sent fingerprints at the honest values: the pull's if its tuple reads an unsent column, the
push's if the difference does. -/
def runFlushVals (weights : Array E) (beta : E) (at_ : ℕ → E) (sent : Array (Option E))
    (x : List Form × List Form) : List E :=
  (if (linearise x.1 weights sent).2.isEmpty then [] else [fpE x.1 weights beta at_]) ++
    (if (linearise (difference x.2 x.1) weights sent).2.isEmpty then [] else [fpE x.2 weights beta at_])

theorem runFoldl_sent (at_ : ℕ → E) : ∀ (l : List ℕ) (s : Array (Option E)) (o : Array E),
    l.foldl (fun b a ↦ (b.1.set! a (some (at_ a)), b.2.push (at_ a))) (s, o) =
      (l.foldl (fun s c ↦ s.set! c (some (at_ c))) s, o ++ (l.map at_).toArray)
  | [], s, o => by simp
  | c :: l, s, o => by
    rw [List.foldl_cons, List.foldl_cons, runFoldl_sent at_ l]
    simp

theorem runForIn_flushVals (weights : Array E) (beta : E) (at_ : ℕ → E) (s : Array (Option E)) :
    ∀ (l : List (List Form × List Form)) (o : Array E),
      (forIn (m := Id) l o fun x o' ↦
        if (!(linearise x.1 weights s).2.isEmpty) = true then
          if (!(linearise (difference x.2 x.1) weights s).2.isEmpty) = true then
            pure (ForInStep.yield ((o'.push (fpE x.1 weights beta at_)).push (fpE x.2 weights beta at_)))
          else pure (ForInStep.yield (o'.push (fpE x.1 weights beta at_)))
        else
          if (!(linearise (difference x.2 x.1) weights s).2.isEmpty) = true then
            pure (ForInStep.yield (o'.push (fpE x.2 weights beta at_)))
          else pure (ForInStep.yield o')) = pure (o ++ (l.flatMap (runFlushVals weights beta at_ s)).toArray)
  | [], o => by simp
  | x :: l, o => by
    rw [List.forIn_cons]
    cases h1 : (linearise x.1 weights s).2.isEmpty <;>
      cases h2 : (linearise (difference x.2 x.1) weights s).2.isEmpty <;>
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, pure_bind,
        runForIn_flushVals weights beta at_ s l, List.flatMap_cons, runFlushVals, h1, h2] <;>
      simp

/-- **The values a table sends** (`tableValues`): its sent columns, then each flush's sent fingerprints. -/
theorem tableValues_eq (table : Table) (at_ : ℕ → E) (weights : Array E) (beta : E) :
    tableValues table at_ weights beta = (sentColumns table).map at_ ++
      (table.flushes.pull.zip table.flushes.push).flatMap
        (runFlushVals weights beta at_ (runSentArr table at_)) := by
  unfold tableValues
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, runFoldl_sent, pure_bind]
  rw [runForIn_flushVals]
  simp [runSentArr]
  rfl

/-- A pull fingerprint the verifier uses: computed from the sent values, or sent. -/
def runPullFactor (weights : Array E) (beta : E) (at_ : ℕ → E) (sent : Array (Option E))
    (x : List Form × List Form) : E :=
  if (linearise x.1 weights sent).2.isEmpty then beta + (linearise x.1 weights sent).1
  else fpE x.1 weights beta at_

/-- A push fingerprint the verifier uses: the pull's plus the difference, or sent. -/
def runPushFactor (weights : Array E) (beta : E) (at_ : ℕ → E) (sent : Array (Option E))
    (x : List Form × List Form) : E :=
  if (linearise (difference x.2 x.1) weights sent).2.isEmpty then
    runPullFactor weights beta at_ sent x + (linearise (difference x.2 x.1) weights sent).1
  else fpE x.2 weights beta at_

/-- `linearise`'s terms as the verifier's terms on table `opcode`'s columns at `pt`. -/
def runTerms (opcode : ℕ) (pt : List E) (ts : List (ℕ × E)) : List Term :=
  ts.map fun ck ↦ term (.table opcode ck.1) pt ck.2

/-- **A flush's relations** at the honest values: the pull's when it is sent, the push's when it is. -/
def runFlushRels (opcode : ℕ) (pt : List E) (weights : Array E) (beta : E) (at_ : ℕ → E)
    (sent : Array (Option E)) (x : List Form × List Form) : List Relation :=
  (if (linearise x.1 weights sent).2.isEmpty then []
    else [⟨runTerms opcode pt (linearise x.1 weights sent).2,
      fpE x.1 weights beta at_ + beta + (linearise x.1 weights sent).1⟩]) ++
  (if (linearise (difference x.2 x.1) weights sent).2.isEmpty then []
    else [⟨runTerms opcode pt (linearise x.2 weights sent).2,
      fpE x.2 weights beta at_ + beta + (linearise x.2 weights sent).1⟩])

/-- **A table's part of the values at `t`, at the honest values** (A2): `UniStatement.tablePart` with each
scalar it reads replaced by what the honest prover sends (`tableValues`): a sent column `c` is `at_ c`, a sent
pull (push) fingerprint is `fpE` of the pull (push) tuple at `at_`. Its relations: each sent column bound at
`w[..r]`, then each flush's sent fingerprints bound by `linearise`'s terms. -/
def tablePartOf (table : Table) (r : ℕ) (weights : Array E) (beta : E) (w : List E) (at_ : ℕ → E) :
    TablePart × List Relation :=
  (⟨((table.flushes.pull.zip table.flushes.push).map
        (runPullFactor weights beta at_ (runSentArr table at_))).foldl (· * ·) 1,
      ((table.flushes.pull.zip table.flushes.push).map
        (runPushFactor weights beta at_ (runSentArr table at_))).foldl (· * ·) 1,
      (tableDegrees table).1, (tableDegrees table).2, runSentArr table at_⟩,
    (sentColumns table).map (fun c ↦ Relation.equal (.table table.opcode c) (w.take r) (at_ c)) ++
      (table.flushes.pull.zip table.flushes.push).flatMap
        (runFlushRels table.opcode (w.take r) weights beta at_ (runSentArr table at_)))

/-! ### `tablePart` on the honest values is `tablePartOf` -/

theorem runConsume_sent (t : Table) (pt : List E) (at_ : ℕ → E) : ∀ (cols : List ℕ)
    (s : Array (Option E)) (rels : Array Relation),
    runConsume (fun _ ↦ 1) (runSentStep t pt) cols (s, rels) (cols.map at_) =
      (cols.foldl (fun s c ↦ s.set! c (some (at_ c))) s,
        rels ++ (cols.map fun c ↦ Relation.equal (.table t.opcode c) pt (at_ c)).toArray)
  | [], s, rels => by simp [runConsume]
  | c :: cols, s, rels => by
    rw [List.map_cons, show at_ c :: cols.map at_ = [at_ c] ++ cols.map at_ from rfl,
      runConsume_append (fun _ ↦ 1) (runSentStep t pt) c (s, rels) cols [at_ c] (cols.map at_) rfl,
      runConsume_sent t pt at_ cols]
    simp [runSentStep]

theorem runConsume_flatMap {α β : Type} (k : α → ℕ) (g : α → β → List E → β) (vals : α → List E) :
    ∀ (l : List α) (init : β), (∀ x ∈ l, (vals x).length = k x) →
      runConsume k g l init (l.flatMap vals) = l.foldl (fun s x ↦ g x s (vals x)) init
  | [], _, _ => rfl
  | x :: l, init, h => by
    rw [List.flatMap_cons, runConsume_append _ _ _ _ _ _ _ (h x (by simp)),
      runConsume_flatMap k g vals l _ fun y hy ↦ h y (by simp [hy]), List.foldl_cons]

theorem runFlushVals_length (weights : Array E) (beta : E) (at_ : ℕ → E) (sent : Array (Option E))
    (x : List Form × List Form) :
    (runFlushVals weights beta at_ sent x).length = runFlushReads weights sent x := by
  unfold runFlushVals runFlushReads
  split_ifs <;> simp

theorem runFoldl_flushStep (t : Table) (pt : List E) (weights : Array E) (beta : E) (at_ : ℕ → E)
    (sent : Array (Option E)) : ∀ (l : List (List Form × List Form)) (rels : Array Relation) (a b : E)
      (c d : ℕ),
    l.foldl (fun s x ↦ runFlushStep t pt weights beta sent x s (runFlushVals weights beta at_ sent x))
        (rels, a, b, c, d) =
      (rels ++ (l.flatMap (runFlushRels t.opcode pt weights beta at_ sent)).toArray,
        (l.map (runPullFactor weights beta at_ sent)).foldl (· * ·) a,
        (l.map (runPushFactor weights beta at_ sent)).foldl (· * ·) b,
        l.foldl (fun c x ↦ c + tupleDegree x.1) c, l.foldl (fun d x ↦ d + tupleDegree x.2) d)
  | [], rels, a, b, c, d => by simp
  | x :: l, rels, a, b, c, d => by
    rw [List.foldl_cons]
    have hstep : runFlushStep t pt weights beta sent x (rels, a, b, c, d)
        (runFlushVals weights beta at_ sent x) =
        (rels ++ (runFlushRels t.opcode pt weights beta at_ sent x).toArray,
          a * runPullFactor weights beta at_ sent x, b * runPushFactor weights beta at_ sent x,
          c + tupleDegree x.1, d + tupleDegree x.2) := by
      unfold runFlushStep runFlushVals runFlushRels runPushFactor runPullFactor runTerms
      by_cases h1 : (linearise x.1 weights sent).2 = [] <;>
        by_cases h2 : (linearise (difference x.2 x.1) weights sent).2 = [] <;>
        simp [h1, h2]
      all_goals (apply Array.ext'; simp)
    rw [hstep, runFoldl_flushStep t pt weights beta at_ sent l]
    simp [List.foldl_cons, Array.append_assoc]

theorem runTableDegrees (table : Table) :
    tableDegrees table = ((table.flushes.pull.zip table.flushes.push).foldl
        (fun c x ↦ c + tupleDegree x.1) 1,
      (table.flushes.pull.zip table.flushes.push).foldl (fun d x ↦ d + tupleDegree x.2) 0) := by
  unfold tableDegrees
  generalize table.flushes.pull.zip table.flushes.push = l
  suffices h : ∀ (a b : ℕ), l.foldl (fun (acc : ℕ × ℕ) (p : List Form × List Form) ↦
      (acc.1 + tupleDegree p.1, acc.2 + tupleDegree p.2)) (a, b) =
      (l.foldl (fun c x ↦ c + tupleDegree x.1) a, l.foldl (fun d x ↦ d + tupleDegree x.2) b) from h 1 0
  induction l with
  | nil => intro a b; rfl
  | cons x l ih => intro a b; exact ih _ _

/-- **The honest values are as many as `tablePart` reads.** -/
theorem runTableReads_eq (table : Table) (at_ : ℕ → E) (weights : Array E) (beta : E) :
    runTableReads table = (tableValues table at_ weights beta).length := by
  have hpat : RunSamePat (runSentArr table at_) (runSentPat table) := by
    have h := runSamePat_consume_sent table (sentColumns table) [] [] (Array.replicate table.width none, #[])
      (Array.replicate table.width none, #[]) ((sentColumns table).map at_) [] (runSamePat_refl _)
    rw [runConsume_sent] at h
    exact h
  rw [tableValues_eq, List.length_append, List.length_map, List.length_flatMap, runTableReads,
    ← runSum_flushReads table weights _ hpat]
  congr 1
  congr 1
  exact List.map_congr_left fun x _ ↦ (runFlushVals_length weights beta at_ _ x).symm

/-- **`tablePart` run on the honest values is `tablePartOf`** (A2): the verifier's own `tablePart`, run by the
prover's reader on the bytes of what `tableValues` sends, returns the part and the relations of
`tablePartOf`. -/
theorem tablePart_run (table : Table) (r : ℕ) (weights : Array E) (beta : E) (w : List E)
    (at_ : ℕ → E) :
    runReader (tablePart (m := Id) table r weights beta w)
        ((tableValues table at_ weights beta).flatMap scalarWire) =
      tablePartOf table r weights beta w at_ := by
  rw [runTablePart_eq, runTableReads_eq table at_ weights beta, runReader_reads]
  unfold runTablePartPure
  rw [tableValues_eq, List.take_left' (List.length_map _), List.drop_left' (List.length_map _),
    runConsume_sent]
  simp only [Array.empty_append]
  rw [show (sentColumns table).foldl (fun s c ↦ s.set! c (some (at_ c))) (Array.replicate table.width none) =
    runSentArr table at_ from rfl]
  rw [runConsume_flatMap _ _ _ _ _ fun x _ ↦ runFlushVals_length weights beta at_ _ x,
    runFoldl_flushStep]
  unfold tablePartOf
  rw [runTableDegrees]
  simp

/-! ### The tables' shape (A4) -/

/-- A monomial the verifier's `linearise` reads exactly when `sent` are the sent columns: of degree at most
two, a product having a sent factor, every index a column. -/
def RunMonoOK (sent : List ℕ) (width : ℕ) (mono : List ℕ) : Bool :=
  decide (mono.length ≤ 2) && (decide (mono.length ≠ 2) || mono.any (· ∈ sent)) && mono.all (· < width)

/-- **The tables' tuples are linearisable** (A4): every monomial of every pull tuple, push tuple and their
difference has degree at most two, a product has a sent factor, and every index is a column. -/
def RunShape (table : Table) : Bool :=
  (table.flushes.pull.zip table.flushes.push).all fun x ↦
    [x.1, x.2, difference x.2 x.1].all fun tup ↦ tup.all fun f ↦ f.all fun mc ↦
      RunMonoOK (sentColumns table) table.width mc.1

/-- **The six tables are linearisable** (`decide +kernel`, under a second). -/
theorem runShape_tables : tables.all RunShape = true := by
  decide +kernel

/-- Every sent column is a column. -/
theorem sentColumns_lt_tables : tables.all (fun t ↦ (sentColumns t).all (· < t.width)) = true := by
  decide +kernel

theorem runShape_of_mem {table : Table} (htab : table ∈ tables) {x : List Form × List Form}
    (hx : x ∈ table.flushes.pull.zip table.flushes.push) {tup : List Form}
    (htup : tup = x.1 ∨ tup = x.2 ∨ tup = difference x.2 x.1) :
    ∀ f ∈ tup, ∀ mc ∈ f, RunMonoOK (sentColumns table) table.width mc.1 = true := by
  have h := List.all_eq_true.mp runShape_tables table htab
  unfold RunShape at h
  have h2 := List.all_eq_true.mp h x hx
  have h3 := List.all_eq_true.mp h2 tup (by rcases htup with rfl | rfl | rfl <;> simp)
  intro f hf mc hmc
  exact List.all_eq_true.mp (List.all_eq_true.mp h3 f hf) mc hmc

theorem sentColumns_lt {table : Table} (htab : table ∈ tables) {i : ℕ} (hi : i ∈ sentColumns table) :
    i < table.width := by
  have h := List.all_eq_true.mp sentColumns_lt_tables table htab
  simpa using List.all_eq_true.mp h i hi

/-! ### The sent columns (A3) -/

theorem runFoldl_set_getD_of_not_mem (at_ : ℕ → E) : ∀ (l : List ℕ) (s : Array (Option E)) (i : ℕ), i ∉ l →
    (l.foldl (fun s c ↦ s.set! c (some (at_ c))) s).getD i none = s.getD i none
  | [], _, _, _ => rfl
  | c :: l, s, i, h => by
    rw [List.foldl_cons, runFoldl_set_getD_of_not_mem at_ l _ i (fun h' ↦ h (by simp [h']))]
    have hci : c ≠ i := fun h' ↦ h (by simp [h'])
    simp [Array.getD_eq_getD_getElem?, hci]

theorem runFoldl_set_size (at_ : ℕ → E) : ∀ (l : List ℕ) (s : Array (Option E)),
    (l.foldl (fun s c ↦ s.set! c (some (at_ c))) s).size = s.size
  | [], _ => rfl
  | c :: l, s => by rw [List.foldl_cons, runFoldl_set_size at_ l]; simp

theorem runFoldl_set_getD_of_mem (at_ : ℕ → E) : ∀ (l : List ℕ) (s : Array (Option E)) (i : ℕ), i ∈ l →
    i < s.size → (l.foldl (fun s c ↦ s.set! c (some (at_ c))) s).getD i none = some (at_ i)
  | [], _, _, h, _ => by simp at h
  | c :: l, s, i, h, hs => by
    rw [List.foldl_cons]
    by_cases hl : i ∈ l
    · exact runFoldl_set_getD_of_mem at_ l _ i hl (by simpa using hs)
    · have hci : c = i := by simp at h; tauto
      rw [runFoldl_set_getD_of_not_mem at_ l _ i hl, hci]
      simp [Array.getD_eq_getD_getElem?, hs]

theorem runFoldl_set_some (at_ : ℕ → E) : ∀ (l : List ℕ) (s : Array (Option E)),
    (∀ i v, s.getD i none = some v → v = at_ i) →
    ∀ i v, (l.foldl (fun s c ↦ s.set! c (some (at_ c))) s).getD i none = some v → v = at_ i
  | [], _, h => h
  | c :: l, s, h => by
    rw [List.foldl_cons]
    refine runFoldl_set_some at_ l _ fun i v hv ↦ ?_
    simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hv
    split_ifs at hv with h1 h2
    · subst h1
      simp at hv
      exact hv.symm
    · simp at hv
    · exact h i v (by rw [Array.getD_eq_getD_getElem?]; exact hv)

/-- **The sent array holds the honest values of the sent columns** (A3). -/
theorem runSentArr_getD {table : Table} (htab : table ∈ tables) (at_ : ℕ → E) {i : ℕ}
    (hi : i ∈ sentColumns table) : (runSentArr table at_).getD i none = some (at_ i) :=
  runFoldl_set_getD_of_mem at_ _ _ i hi (by simpa using sentColumns_lt htab hi)

/-- **The sent array holds honest values only.** -/
theorem runSentArr_some (table : Table) (at_ : ℕ → E) :
    ∀ i v, (runSentArr table at_).getD i none = some v → v = at_ i :=
  runFoldl_set_some at_ _ _ fun i v h ↦ by
    exfalso
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h
    split_ifs at h <;> simp at h

/-- **`tablePartOf`'s sent values are the honest ones** (A3). -/
theorem tablePartOf_sent {table : Table} (htab : table ∈ tables) (r : ℕ) (weights : Array E) (beta : E)
    (w : List E) (at_ : ℕ → E) :
    ∀ i ∈ sentColumns table, (tablePartOf table r weights beta w at_).1.sent.getD i none = some (at_ i) :=
  fun _ hi ↦ runSentArr_getD htab at_ hi

/-! ### `linearise` is exact (A4) -/

theorem runMonoOK_len {S : List ℕ} {w : ℕ} {mono : List ℕ} (h : RunMonoOK S w mono = true) :
    mono.length ≤ 2 := by
  simp only [RunMonoOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem runMonoOK_pair {S : List ℕ} {w i j : ℕ} (h : RunMonoOK S w [i, j] = true) : i ∈ S ∨ j ∈ S := by
  simp only [RunMonoOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simpa using h.1.2

theorem runMonoOK_lt {S : List ℕ} {w : ℕ} {mono : List ℕ} (h : RunMonoOK S w mono = true) :
    ∀ i ∈ mono, i < w := by
  simp only [RunMonoOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h.2

/-- The value of `linearise`'s terms at the honest values. -/
def runTermsVal (at_ : ℕ → E) (ts : List (ℕ × E)) : E := (ts.map fun ck ↦ ck.2 * at_ ck.1).sum

theorem runAddTerm_cons (t : ℕ × E) (ts : List (ℕ × E)) (i : ℕ) (c : E) :
    addTerm (t :: ts) i c = if t.1 = i then (t.1, t.2 + c) :: ts else t :: addTerm ts i c := by
  unfold addTerm
  rw [List.findIdx?_cons]
  by_cases h : t.1 = i
  · simp [h]
  · simp only [h, beq_iff_eq, ite_false]
    cases hf : List.findIdx? (fun x ↦ x.1 == i) ts with
    | none => simp
    | some j => simp

theorem runAddTerm_val (at_ : ℕ → E) : ∀ (ts : List (ℕ × E)) (i : ℕ) (c : E),
    runTermsVal at_ (addTerm ts i c) = runTermsVal at_ ts + c * at_ i
  | [], i, c => by simp [addTerm, runTermsVal]
  | t :: ts, i, c => by
    rw [runAddTerm_cons]
    split_ifs with h
    · simp only [runTermsVal, List.map_cons, List.sum_cons, h]
      ring
    · have := runAddTerm_val at_ ts i c
      simp only [runTermsVal, List.map_cons, List.sum_cons] at this ⊢
      rw [this]
      ring

theorem runAddTerm_mem (P : ℕ → Prop) : ∀ (ts : List (ℕ × E)) (i : ℕ) (c : E), (∀ ck ∈ ts, P ck.1) → P i →
    ∀ ck ∈ addTerm ts i c, P ck.1
  | [], i, c, _, hi => by simp [addTerm, hi]
  | t :: ts, i, c, h, hi => by
    rw [runAddTerm_cons]
    split_ifs with hti
    · intro ck hck
      simp only [List.mem_cons] at hck
      rcases hck with rfl | hck
      · exact h t (by simp)
      · exact h ck (by simp [hck])
    · intro ck hck
      simp only [List.mem_cons] at hck
      rcases hck with rfl | hck
      · exact h ck (by simp)
      · exact runAddTerm_mem P ts i c (fun ck' h' ↦ h ck' (by simp [h'])) hi ck hck

/-- A monomial's value at a row. -/
def runMonoVal (at_ : ℕ → E) (mono : List ℕ) : E := mono.foldl (fun p j ↦ p * at_ j) 1

theorem runLinInner_val (weight : E) (sent : Array (Option E)) (at_ : ℕ → E) (S : List ℕ) (width : ℕ)
    (hsent : ∀ i v, sent.getD i none = some v → v = at_ i)
    (hin : ∀ i ∈ S, (sent.getD i none).isSome = true) (acc : E × List (ℕ × E)) (mc : List ℕ × E)
    (hmc : RunMonoOK S width mc.1 = true) :
    (runLinInner weight sent acc mc).1 + runTermsVal at_ (runLinInner weight sent acc mc).2 =
      acc.1 + runTermsVal at_ acc.2 + weight * (mc.2 * runMonoVal at_ mc.1) := by
  rcases mc with ⟨mono, c⟩
  rcases acc with ⟨known, terms⟩
  unfold runLinInner
  by_cases hc : c = 0
  · simp [hc]
  simp only [hc, ite_false]
  rcases mono with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · simp only [runMonoVal, List.foldl_nil]
    ring
  · rcases hoi : sent.getD i none with _ | v
    · simp only [hoi, runAddTerm_val, runMonoVal, List.foldl_cons, List.foldl_nil]
      ring
    · simp only [hoi, runMonoVal, List.foldl_cons, List.foldl_nil, hsent i v hoi]
      ring
  · rcases hoi : sent.getD i none with _ | a <;> rcases hoj : sent.getD j none with _ | b
    · exfalso
      rcases runMonoOK_pair hmc with h | h
      · have := hin i h
        rw [hoi] at this
        simp at this
      · have := hin j h
        rw [hoj] at this
        simp at this
    · simp only [hoi, hoj, runAddTerm_val, runMonoVal, List.foldl_cons, List.foldl_nil, hsent j b hoj]
      ring
    · simp only [hoi, hoj, runAddTerm_val, runMonoVal, List.foldl_cons, List.foldl_nil, hsent i a hoi]
      ring
    · simp only [hoi, hoj, runMonoVal, List.foldl_cons, List.foldl_nil, hsent i a hoi, hsent j b hoj]
      ring
  · exfalso
    have := runMonoOK_len hmc
    simp at this

theorem formE_eq (f : Form) (at_ : ℕ → E) :
    formE f at_ = f.foldl (fun a mc ↦ a + mc.2 * runMonoVal at_ mc.1) 0 := rfl

theorem runFormAcc (at_ : ℕ → E) : ∀ (f : Form) (b : E),
    f.foldl (fun a mc ↦ a + mc.2 * runMonoVal at_ mc.1) b = b + formE f at_
  | [], b => by simp [formE]
  | mc :: f, b => by
    rw [List.foldl_cons, runFormAcc at_ f, formE_eq (mc :: f), List.foldl_cons,
      runFormAcc at_ f (0 + mc.2 * runMonoVal at_ mc.1)]
    ring

theorem runFoldl_linInner_val (weight : E) (sent : Array (Option E)) (at_ : ℕ → E) (S : List ℕ)
    (width : ℕ) (hsent : ∀ i v, sent.getD i none = some v → v = at_ i)
    (hin : ∀ i ∈ S, (sent.getD i none).isSome = true) :
    ∀ (f : Form) (acc : E × List (ℕ × E)), (∀ mc ∈ f, RunMonoOK S width mc.1 = true) →
      (f.foldl (runLinInner weight sent) acc).1 + runTermsVal at_ (f.foldl (runLinInner weight sent) acc).2 =
        acc.1 + runTermsVal at_ acc.2 + weight * formE f at_
  | [], acc, _ => by simp [formE]
  | mc :: f, acc, h => by
    rw [List.foldl_cons, runFoldl_linInner_val weight sent at_ S width hsent hin f _
      (fun mc' h' ↦ h mc' (by simp [h'])),
      runLinInner_val weight sent at_ S width hsent hin acc mc (h mc (by simp)), formE_eq (mc :: f),
      List.foldl_cons, runFormAcc]
    ring

/-- **`linearise` is exact** (A4): on a tuple whose monomials have degree at most two, a product having a sent
factor (`S` sent), its known part plus its terms at the honest values plus `β` is the tuple's fingerprint. -/
theorem linearise_exact (tuple : List Form) (weights : Array E) (sent : Array (Option E)) (at_ : ℕ → E)
    (beta : E) (S : List ℕ) (width : ℕ) (hsent : ∀ i v, sent.getD i none = some v → v = at_ i)
    (hin : ∀ i ∈ S, (sent.getD i none).isSome = true)
    (hshape : ∀ f ∈ tuple, ∀ mc ∈ f, RunMonoOK S width mc.1 = true) :
    (linearise tuple weights sent).1 + runTermsVal at_ (linearise tuple weights sent).2 + beta =
      fpE tuple weights beta at_ := by
  rw [runLinearise_eq]
  have step : ∀ (l : List (Form × ℕ)) (acc : E × List (ℕ × E)) (b : E), (∀ x ∈ l, x.1 ∈ tuple) →
      (l.foldl (runLinOuter weights sent) acc).1 + runTermsVal at_ (l.foldl (runLinOuter weights sent) acc).2 +
          b = l.foldl (fun a x ↦ a + weights.getD x.2 0 * formE x.1 at_) (b + acc.1 + runTermsVal at_ acc.2) := by
    intro l
    induction l with
    | nil => intro acc b _; simp only [List.foldl_nil]; ring
    | cons x l ih =>
      intro acc b hl
      rw [List.foldl_cons, List.foldl_cons, ih _ b fun y hy ↦ hl y (by simp [hy])]
      congr 1
      have hx := runFoldl_linInner_val (weights.getD x.2 0) sent at_ S width hsent hin x.1 acc
        (hshape x.1 (hl x (by simp)))
      unfold runLinOuter
      rw [add_assoc b, hx]
      ring
  have key := step (tuple.zip (List.range tuple.length)) (0, []) beta fun x hx ↦ (List.of_mem_zip hx).1
  have h0 : beta + ((0 : E), ([] : List (ℕ × E))).1 + runTermsVal at_ ((0 : E), ([] : List (ℕ × E))).2 =
      beta := by simp [runTermsVal]
  rw [h0] at key
  rw [key]
  rfl

/-- **`linearise`'s terms are in the tuple's columns.** -/
theorem linearise_mem (tuple : List Form) (weights : Array E) (sent : Array (Option E)) (P : ℕ → Prop)
    (hP : ∀ f ∈ tuple, ∀ mc ∈ f, ∀ i ∈ mc.1, P i) : ∀ ck ∈ (linearise tuple weights sent).2, P ck.1 := by
  rw [runLinearise_eq]
  suffices h : ∀ (l : List (Form × ℕ)) (acc : E × List (ℕ × E)), (∀ x ∈ l, x.1 ∈ tuple) →
      (∀ ck ∈ acc.2, P ck.1) → ∀ ck ∈ (l.foldl (runLinOuter weights sent) acc).2, P ck.1 from
    h _ (0, []) (fun x hx ↦ (List.of_mem_zip hx).1) (by simp)
  have inner : ∀ (weight : E) (f : Form) (acc : E × List (ℕ × E)), (∀ mc ∈ f, ∀ i ∈ mc.1, P i) →
      (∀ ck ∈ acc.2, P ck.1) → ∀ ck ∈ (f.foldl (runLinInner weight sent) acc).2, P ck.1 := by
    intro weight f
    induction f with
    | nil => intro acc _ h; simpa using h
    | cons mc f ih =>
      intro acc hf hacc
      rw [List.foldl_cons]
      refine ih _ (fun mc' h' ↦ hf mc' (by simp [h'])) ?_
      rcases mc with ⟨mono, c⟩
      rcases acc with ⟨known, terms⟩
      have hmc : ∀ i ∈ mono, P i := hf (mono, c) (by simp)
      unfold runLinInner
      dsimp only
      split_ifs
      · exact hacc
      · rcases mono with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
        · exact hacc
        · dsimp only
          split
          · exact hacc
          · exact runAddTerm_mem P terms i _ hacc (hmc i (by simp))
        · dsimp only
          split
          · exact hacc
          · exact runAddTerm_mem P terms j _ hacc (hmc j (by simp))
          · exact runAddTerm_mem P terms i _ hacc (hmc i (by simp))
          · exact hacc
        · exact hacc
  intro l
  induction l with
  | nil => intro acc _ h; simpa using h
  | cons x l ih =>
    intro acc hl hacc
    rw [List.foldl_cons]
    refine ih _ (fun y hy ↦ hl y (by simp [hy])) ?_
    unfold runLinOuter
    exact inner _ x.1 acc (hP x.1 (hl x (by simp))) hacc

/-! ### The tables' relations hold (A5) -/

theorem runTerms_sum (opcode : ℕ) (pt : List E) (ev : Term → E) (at_ : ℕ → E) (width : ℕ)
    (hev : ∀ c k, c < width → ev (term (.table opcode c) pt k) = k * at_ c) :
    ∀ ts : List (ℕ × E), (∀ ck ∈ ts, ck.1 < width) → ((runTerms opcode pt ts).map ev).sum = runTermsVal at_ ts
  | [], _ => by simp [runTerms, runTermsVal]
  | ck :: ts, h => by
    have ih := runTerms_sum opcode pt ev at_ width hev ts fun ck' h' ↦ h ck' (by simp [h'])
    simp only [runTerms, runTermsVal, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, hev ck.1 ck.2 (h ck (by simp))]

theorem runSentArr_isSome {table : Table} (htab : table ∈ tables) (at_ : ℕ → E) :
    ∀ i ∈ sentColumns table, ((runSentArr table at_).getD i none).isSome = true := fun _ hi ↦ by
  rw [runSentArr_getD htab at_ hi]
  rfl

theorem runFlushRel_value {table : Table} (htab : table ∈ tables) {x : List Form × List Form}
    (hx : x ∈ table.flushes.pull.zip table.flushes.push) (weights : Array E) (beta : E) (at_ : ℕ → E)
    (tup : List Form) (htup : tup = x.1 ∨ tup = x.2) (pt : List E) (ev : Term → E)
    (hev : ∀ c k, c < table.width → ev (term (.table table.opcode c) pt k) = k * at_ c) :
    ((runTerms table.opcode pt (linearise tup weights (runSentArr table at_)).2).map ev).sum =
      fpE tup weights beta at_ + beta + (linearise tup weights (runSentArr table at_)).1 := by
  have hshape := runShape_of_mem htab hx (tup := tup) (by rcases htup with h | h <;> simp [h])
  have hex := linearise_exact tup weights (runSentArr table at_) at_ beta (sentColumns table) table.width
    (runSentArr_some table at_) (runSentArr_isSome htab at_) hshape
  rw [runTerms_sum table.opcode pt ev at_ table.width hev _ (linearise_mem tup weights _ (· < table.width)
    fun f hf mc hmc ↦ runMonoOK_lt (hshape f hf mc hmc)), ← hex]
  linear_combination (-((linearise tup weights (runSentArr table at_)).1 + beta)) * Domain.two_eq_zero_E

/-- **Every relation a table states holds** (A5) of any evaluation of the terms that gives the table's column
`c` at `w[..r]` its honest value `at_ c`. -/
theorem tablePartOf_holds {table : Table} (htab : table ∈ tables) (r : ℕ) (weights : Array E) (beta : E)
    (w : List E) (at_ : ℕ → E) (ev : Term → E)
    (hev : ∀ c k, c < table.width → ev (term (.table table.opcode c) (w.take r) k) = k * at_ c) :
    ∀ rel ∈ (tablePartOf table r weights beta w at_).2, (rel.terms.map ev).sum = rel.value := by
  intro rel hrel
  simp only [tablePartOf, List.mem_append, List.mem_map, List.mem_flatMap] at hrel
  rcases hrel with ⟨c, hc, rfl⟩ | ⟨x, hx, hrel⟩
  · simp [Relation.equal, hev c 1 (sentColumns_lt htab hc)]
  · unfold runFlushRels at hrel
    simp only [List.mem_append] at hrel
    rcases hrel with h | h
    · split_ifs at h
      · simp at h
      · simp only [List.mem_singleton] at h
        subst h
        exact runFlushRel_value htab hx weights beta at_ x.1 (Or.inl rfl) _ ev hev
    · split_ifs at h
      · simp at h
      · simp only [List.mem_singleton] at h
        subst h
        exact runFlushRel_value htab hx weights beta at_ x.2 (Or.inr rfl) _ ev hev

/-- **Every term of a table's relations is one of its columns at `w[..r]`** (so every such relation is on
`C1`). -/
theorem tablePartOf_terms {table : Table} (htab : table ∈ tables) (r : ℕ) (weights : Array E) (beta : E)
    (w : List E) (at_ : ℕ → E) :
    ∀ rel ∈ (tablePartOf table r weights beta w at_).2, ∀ x ∈ rel.terms,
      ∃ c < table.width, x = term (.table table.opcode c) (w.take r) x.coefficient := by
  intro rel hrel
  simp only [tablePartOf, List.mem_append, List.mem_map, List.mem_flatMap] at hrel
  rcases hrel with ⟨c, hc, rfl⟩ | ⟨x, hx, hrel⟩
  · intro y hy
    simp only [Relation.equal, List.mem_singleton] at hy
    subst hy
    exact ⟨c, sentColumns_lt htab hc, rfl⟩
  · have key : ∀ tup, (tup = x.1 ∨ tup = x.2) → ∀ y ∈ runTerms table.opcode (w.take r)
        (linearise tup weights (runSentArr table at_)).2,
        ∃ c < table.width, y = term (.table table.opcode c) (w.take r) y.coefficient := by
      intro tup htup y hy
      have hshape := runShape_of_mem htab hx (tup := tup) (by rcases htup with h | h <;> simp [h])
      simp only [runTerms, List.mem_map] at hy
      obtain ⟨ck, hck, rfl⟩ := hy
      exact ⟨ck.1, linearise_mem tup weights _ (· < table.width)
        (fun f hf mc hmc ↦ runMonoOK_lt (hshape f hf mc hmc)) ck hck, rfl⟩
    unfold runFlushRels at hrel
    simp only [List.mem_append] at hrel
    rcases hrel with h | h
    · split_ifs at h
      · simp at h
      · simp only [List.mem_singleton] at h
        subst h
        exact key x.1 (Or.inl rfl)
    · split_ifs at h
      · simp at h
      · simp only [List.mem_singleton] at h
        subst h
        exact key x.2 (Or.inr rfl)

/-- **A table's relations are on `C1`.** -/
theorem tablePartOf_c1 {table : Table} (htab : table ∈ tables) (r : ℕ) (weights : Array E) (beta : E)
    (w : List E) (at_ : ℕ → E) : ∀ rel ∈ (tablePartOf table r weights beta w at_).2, rel.commitment = .c1 := by
  intro rel hrel
  have h := tablePartOf_terms htab r weights beta w at_ rel hrel
  unfold Relation.commitment
  rcases hrel' : rel.terms with _ | ⟨y, ys⟩
  · rfl
  · obtain ⟨c, -, hc⟩ := h y (by rw [hrel']; simp)
    rw [hc]
    rfl

/-! ### `atTOf`, piece by piece (A6) -/

/-- The digits at `t` the prover and the verifier read: `w_0(t), …` (`atTOf`'s `w`). -/
def atW (tr : Trace) (t : E) : List E := digits t (max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2)

/-- **Column `c` of `table` at the digits `w`** (`atTOf`'s `at_`): the multilinear extension of its basis-`B`
coefficients at `w[..r]`. -/
def atColumn (tr : Trace) (w : List E) (table : Table) (c : ℕ) : E :=
  evalB ((bCoefficients (tr.shape.heights.getD table.opcode 0) (tr.column table.opcode c)).map ofK)
    (tr.shape.heights.getD table.opcode 0) w

/-- A table's part and relations at `t` (the verifier's `tablePart` on what the table sends). -/
def atPart (tr : Trace) (weights : Array E) (beta : E) (w : List E) (table : Table) : TablePart × List Relation :=
  tablePartOf table (tr.shape.heights.getD table.opcode 0) weights beta w (atColumn tr w table)

/-- The six tables' parts (`atTOf`'s `parts`). -/
def atParts (tr : Trace) (weights : Array E) (beta : E) (w : List E) : List TablePart :=
  tables.map fun table ↦ (atPart tr weights beta w table).1

/-- The six tables' relations, in order. -/
def atTableRels (tr : Trace) (weights : Array E) (beta : E) (w : List E) : List Relation :=
  tables.flatMap fun table ↦ (atPart tr weights beta w table).2

/-- The six tables' values, in order. -/
def atTableValues (tr : Trace) (weights : Array E) (beta : E) (w : List E) : List E :=
  tables.flatMap fun table ↦ tableValues table (atColumn tr w table) weights beta

/-- The memory's column `k` at `w`. -/
def atMem (tr : Trace) (w : List E) (k : ℕ) : E :=
  evalB ((bCoefficients tr.shape.logMemory (tr.memory.getD k #[])).map ofK) tr.shape.logMemory w

/-- The addresses at `w`. -/
def atAddress (tr : Trace) (w : List E) : E :=
  evalB ((bCoefficients tr.shape.logMemory (addressColumn tr.shape.logMemory)).map ofK) tr.shape.logMemory w

/-- The memory's pull fingerprint at `t`. -/
def atMemoryPull (tr : Trace) (weights : Array E) (beta : E) (w : List E) : E :=
  memoryFp weights beta (atAddress tr w) (atMem tr w 3) ((List.range 3).map (atMem tr w))

/-- The memory's push fingerprint at `t`. -/
def atMemoryPush (tr : Trace) (weights : Array E) (beta : E) (w : List E) : E :=
  atMemoryPull tr weights beta w + weights.getD 2 0 * (1 + atMem tr w 3)

/-- **The memory's three relations**: its final counts and addresses at `w[..lm]`, its limbs' fingerprint. -/
def atMemoryRels (tr : Trace) (weights : Array E) (beta : E) (w : List E) : List Relation :=
  [Relation.equal (.memory 3) (w.take tr.shape.logMemory) (atMem tr w 3),
    Relation.equal .address (w.take tr.shape.logMemory) (atAddress tr w),
    ⟨(List.range 3).map (fun k ↦ term (.memory k) (w.take tr.shape.logMemory) (weights.getD (3 + k) 0)),
      atMemoryPull tr weights beta w + beta + weights.getD 0 0 * sepMem + weights.getD 1 0 * atAddress tr w +
        weights.getD 2 0 * atMem tr w 3⟩]

/-- The bytecode's final counts at `w`. -/
def atBytecodeFinal (tr : Trace) (w : List E) : E :=
  evalB ((bCoefficients tr.shape.logBytecode tr.bytecodeFinal).map ofK) tr.shape.logBytecode w

/-- The bytecode's slot `s` at `w`. -/
def atSlot (tr : Trace) (w : List E) (s : ℕ) : E :=
  evalB ((bCoefficients tr.shape.logBytecode (tr.slots.getD s #[])).map ofK) tr.shape.logBytecode w

/-- The bytecode's pull fingerprint at `t` (slot `2` its final count). -/
def atBytecodePull (tr : Trace) (weights : Array E) (beta : E) (w : List E) : E :=
  bytecodeFp weights beta fun s ↦ if s = 2 then atBytecodeFinal tr w else atSlot tr w s

/-- The bytecode's push fingerprint at `t`. -/
def atBytecodePush (tr : Trace) (weights : Array E) (beta : E) (w : List E) : E :=
  atBytecodePull tr weights beta w + weights.getD 2 0 * (1 + atBytecodeFinal tr w)

/-- **The bytecode's two relations**: its final counts at `w[..lb]`, its tuple at `(α, w[..lb])`. -/
def atBytecodeRels (tr : Trace) (alphas : List E) (beta : E) (w : List E) : List Relation :=
  [Relation.equal .bytecodeFinal (w.take tr.shape.logBytecode) (atBytecodeFinal tr w),
    Relation.equal .bytecodeTuple (alphas ++ w.take tr.shape.logBytecode)
      (atBytecodePull tr (eqKernel alphas) beta w + beta + (eqKernel alphas).getD 2 0 * atBytecodeFinal tr w)]

/-- `Q_W(t)` as the verifier reads it from the chunks the prover sends: `Q_0 + w_{e_0}(Q_1 + w_{e_1} Q_2)`. -/
def atConstraintValue (c2 : C2Data) (w : List E) : E :=
  ((c2.constraintChunks.zip c2.constraintSizes).foldl
    (fun (acc : E × E) x ↦ (acc.1 + acc.2 * evalB x.1 x.2 w, acc.2 * w.getD x.2 0)) (0, 1)).1

/-- **The constraint quotient's identity and the quotient's degree** at `t` (`constraintRelation` on the parts). -/
def atConstraint (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) : Relation × ℕ :=
  constraintRelation tr.shape (atParts tr (eqKernel alphas) beta (atW tr t)) (publicWordsOf tr.publicInput) gamma t
    (atConstraintValue c2 (atW tr t)) (atW tr t)

/-- Each table's `Z_act(t)` from its count's bits. -/
def atActive (tr : Trace) (w : List E) : List E :=
  (tr.rows.zip tr.shape.heights).map fun x ↦
    activeVanishingFromBits w ((List.range (x.2 + 1)).map fun b ↦ intBits x.1 b 1) x.2

/-- **The heap's relations and its leaf quotients' columns** at `t` (`heapRelations`). -/
def atHeap (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) :
    List Relation × List (Column × ℕ × Bool) :=
  heapRelations tr.shape (atActive tr (atW tr t)) (atParts tr (eqKernel alphas) beta (atW tr t)) (eqKernel alphas)
    beta (evalB c2.heapB tr.shape.heap.h (atW tr t)) (atConstraintValue c2 (atW tr t))
    (atMemoryPull tr (eqKernel alphas) beta (atW tr t)) (atMemoryPush tr (eqKernel alphas) beta (atW tr t))
    (atBytecodePull tr (eqKernel alphas) beta (atW tr t)) (atBytecodePush tr (eqKernel alphas) beta (atW tr t))
    (atW tr t) (chunks ((atConstraint tr c2 alphas beta gamma t).2 + 1))

theorem runFoldl_triple {α : Type} (f : α → List E) (g : α → List Relation) (h : α → TablePart) :
    ∀ (l : List α) (a : Array E) (b : Array Relation) (c : Array TablePart),
      l.foldl (fun s x ↦ (s.1 ++ (f x).toArray, s.2.1 ++ (g x).toArray, s.2.2.push (h x))) (a, b, c) =
        (a ++ (l.flatMap f).toArray, b ++ (l.flatMap g).toArray, c ++ (l.map h).toArray)
  | [], a, b, c => by simp
  | x :: l, a, b, c => by
    rw [List.foldl_cons, runFoldl_triple f g h l]
    simp [Array.append_assoc]

set_option maxHeartbeats 1000000 in
/-- **The relations at `t`, piece by piece** (A6, no Flock output): each table's (in order), the memory's
three, the bytecode's two, the constraint quotient's identity, the heap's. -/
theorem atTOf_relations (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) :
    (atTOf tr c2 alphas beta gamma t none).relations =
      atTableRels tr (eqKernel alphas) beta (atW tr t) ++ atMemoryRels tr (eqKernel alphas) beta (atW tr t) ++
        atBytecodeRels tr alphas beta (atW tr t) ++ [(atConstraint tr c2 alphas beta gamma t).1] ++
          (atHeap tr c2 alphas beta gamma t).1 := by
  unfold atTOf
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind, tablePart_run, runFoldl_triple]
  simp only [Array.toList_append, Array.toList_push, List.append_assoc, Array.empty_append,
    List.toList_toArray, List.cons_append]
  rfl

/-- **The values sent at `t`** (no Flock output): each table's (`tableValues`), the memory's final count,
address and pull fingerprint, the bytecode's final count and pull fingerprint, `T(t)` and `Q_W(t)`. -/
theorem atTOf_values (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) :
    (atTOf tr c2 alphas beta gamma t none).values =
      atTableValues tr (eqKernel alphas) beta (atW tr t) ++
        [atMem tr (atW tr t) 3, atAddress tr (atW tr t), atMemoryPull tr (eqKernel alphas) beta (atW tr t),
          atBytecodeFinal tr (atW tr t), atBytecodePull tr (eqKernel alphas) beta (atW tr t),
          evalB c2.heapB tr.shape.heap.h (atW tr t), atConstraintValue c2 (atW tr t)] := by
  unfold atTOf
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind, tablePart_run, runFoldl_triple]
  simp only [Array.toList_append, List.append_assoc, Array.empty_append, List.toList_toArray, List.cons_append]
  rfl

/-- **`C2`'s columns as the verifier lists them at `t`.** -/
theorem atTOf_c2Columns (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) :
    (atTOf tr c2 alphas beta gamma t none).c2Columns =
      [(.heap, tr.shape.heap.h, true), (.treeQuotient 0, tr.shape.heap.h, true), (.treeQuotient 1, 0, true)] ++
        ((chunks ((atConstraint tr c2 alphas beta gamma t).2 + 1)).zip
            (List.range (chunks ((atConstraint tr c2 alphas beta gamma t).2 + 1)).length)).map
          (fun x ↦ (Column.constraintQuotient x.2, x.1, true)) ++
        (atHeap tr c2 alphas beta gamma t).2 := by
  unfold atTOf
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind, tablePart_run, runFoldl_triple]
  simp only [Array.toList_append, List.append_assoc, Array.empty_append, List.toList_toArray]
  rfl

/-- **No ring map without Flock's output.** -/
theorem atTOf_ringMap (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) :
    (atTOf tr c2 alphas beta gamma t none).ringMap = none := by
  unfold atTOf
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

/-- **Nothing pending without Flock's output.** -/
theorem atTOf_pending (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) :
    (atTOf tr c2 alphas beta gamma t none).pending = none := by
  unfold atTOf
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

/-! ### The heap's relations are on `C2` (A7) -/

theorem runBind_inv {β γ : Type} (P : β → Prop) (Q : γ → Prop) (e : Id β) (g : β → Id γ) (he : P e)
    (hg : ∀ s, P s → Q (g s)) : Q (e >>= g) := hg e he

theorem runForIn_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ x s, P s → ∀ s', (f x s = .yield s' ∨ f x s = .done s') → P s') :
    ∀ (l : List α) (init : β), P init → P (forIn l init f)
  | [], _, h => h
  | x :: l, init, h => by
    rw [List.forIn_cons]
    rcases hfx : f x init with s' | s'
    · exact hf x init h s' (Or.inr hfx)
    · exact runForIn_inv P f hf l s' (hf x init h s' (Or.inl hfx))

theorem runQuotientTerms_columns (column : ℕ → Column) (w : List E) :
    ∀ (l : List (ℕ × ℕ)) (a : Array Term) (s : E),
      ((l.foldl (fun (acc : Array Term × E) x ↦
          (acc.1.push (term (column x.2) (w.take x.1) acc.2), acc.2 * w.getD x.1 0)) (a, s)).1.toList.map
          (·.column)) = a.toList.map (·.column) ++ l.map (fun x ↦ column x.2)
  | [], a, s => by simp
  | x :: l, a, s => by
    rw [List.foldl_cons, runQuotientTerms_columns column w l]
    simp [term]

/-- **`quotient_terms`' columns**: chunk `c`'s column for each chunk, in order. -/
theorem quotientTerms_columns (column : ℕ → Column) (sizes : List ℕ) (w : List E) (scale : E) :
    (quotientTerms column sizes w scale).map (·.column) = (List.range sizes.length).map column := by
  unfold quotientTerms
  have h := runQuotientTerms_columns column w (sizes.zip (List.range sizes.length)) #[] scale
  simp only [List.map_nil, List.nil_append] at h
  rw [h, show (fun x : ℕ × ℕ ↦ column x.2) = column ∘ Prod.snd from rfl, ← List.map_map,
    List.map_snd_zip (by simp)]

theorem commitment_of_columns (rel : Relation) (c : Column) (cs : List Column)
    (h : rel.terms.map (·.column) = c :: cs) : rel.commitment = c.commitment := by
  unfold Relation.commitment
  rcases hr : rel.terms with _ | ⟨t, ts⟩
  · rw [hr] at h
    simp at h
  · rw [hr] at h
    simp only [List.map_cons, List.cons.injEq] at h
    show t.column.commitment = c.commitment
    rw [h.1]

/-- **The heap's relations are on `C2`** (A7): `T(t)`, the tree, the root, every block's leaf identity (a term
on the heap first), and the constraint quotient's chunks (`constraintChunks` nonempty). -/
theorem heapRelations_c2 (shape : Shape) (active : List E) (parts : List TablePart) (weights : Array E)
    (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : E) (w : List E)
    (constraintChunks : List ℕ) (hchunks : constraintChunks ≠ []) :
    ∀ rel ∈ (heapRelations shape active parts weights beta heapValue constraintValue memoryPull memoryPush
      bytecodePull bytecodePush w constraintChunks).1, rel.commitment = .c2 := by
  unfold heapRelations
  simp only [Id.run]
  refine runBind_inv (fun s : Array Relation × Array (Column × ℕ × Bool) ↦ ∀ r ∈ s.1, r.commitment = .c2)
    (fun x : List Relation × List (Column × ℕ × Bool) ↦ ∀ rel ∈ x.1, rel.commitment = .c2) _ _ ?_ ?_
  · refine runForIn_inv (fun s : Array Relation × Array (Column × ℕ × Bool) ↦ ∀ r ∈ s.1, r.commitment = .c2)
      _ ?_ _ _ ?_
    · intro x s hs s' hs'
      split at hs'
      · rcases hs' with hs' | hs'
        · injection hs' with hs'
          subst hs'
          intro r hr
          simp only [Array.mem_push] at hr
          rcases hr with hr | rfl
          · exact hs r hr
          · rfl
        · cases hs'
      · rcases hs' with hs' | hs'
        · injection hs' with hs'
          subst hs'
          intro r hr
          simp only [Array.mem_push] at hr
          rcases hr with hr | rfl
          · exact hs r hr
          · rfl
        · cases hs'
    · intro r hr
      simp only [Array.mem_push] at hr
      rcases hr with (hr | rfl) | rfl
      · obtain rfl : r = Relation.equal Column.heap (List.take shape.heap.h w) heapValue := by simpa using hr
        rfl
      · rfl
      · rfl
  · intro s hs rel hrel
    have hrel2 : rel ∈ (s.1.push ⟨quotientTerms .constraintQuotient constraintChunks w 1,
        constraintValue⟩).toList := hrel
    have hrel' : rel ∈ s.1 ∨
        rel = ⟨quotientTerms .constraintQuotient constraintChunks w 1, constraintValue⟩ := by
      simpa using hrel2
    rcases hrel' with hr | rfl
    · exact hs rel hr
    · obtain ⟨n, hn⟩ : ∃ n, constraintChunks.length = n + 1 :=
        ⟨constraintChunks.length - 1, by have := List.length_pos_of_ne_nil hchunks; omega⟩
      have h := quotientTerms_columns Column.constraintQuotient constraintChunks w 1
      rw [hn, List.range_succ_eq_map, List.map_cons] at h
      exact commitment_of_columns ⟨quotientTerms .constraintQuotient constraintChunks w 1, constraintValue⟩
        _ _ h

/-- **`chunks` of a positive count is not empty.** -/
theorem chunks_succ_ne_nil (n : ℕ) : chunks (n + 1) ≠ [] := by
  unfold chunks
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine runBind_inv (fun s : Array ℕ × ℕ ↦ 1 ≤ s.1.size) (fun l : List ℕ ↦ l ≠ []) _ _ ?_ ?_
  · rw [show (Std.Legacy.Range.mk 0 4 1 (by omega)).size = 4 by rfl, List.range'_succ, List.forIn_cons]
    refine runBind_inv (fun st : ForInStep (Array ℕ × ℕ) ↦ 1 ≤ (match st with | .yield b => b | .done b => b).1.size)
      (fun s : Array ℕ × ℕ ↦ 1 ≤ s.1.size) _ _ ?_ ?_
    · simp only [Nat.lt_add_one_iff, zero_le, gt_iff_lt, ite_true]
      exact Nat.le_refl 1
    · intro st hst
      rcases st with b | b
      · exact hst
      · refine runForIn_inv (fun s : Array ℕ × ℕ ↦ 1 ≤ s.1.size) _ ?_ _ _ hst
        intro x s hs s' hs'
        split_ifs at hs' with h1 h2
        · rcases hs' with hs' | hs'
          · injection hs' with hs'
            subst hs'
            simp
          · cases hs'
        · rcases hs' with hs' | hs'
          · injection hs' with hs'
            subst hs'
            simp
          · cases hs'
        · rcases hs' with hs' | hs'
          · injection hs' with hs'
            subst hs'
            exact hs
          · cases hs'
  · intro s hs
    show s.1.toList ≠ []
    apply List.ne_nil_of_length_pos
    rw [Array.length_toList]
    exact hs

/-! ### A table's fingerprint products (for the heap) -/

theorem runFormE_cons (at_ : ℕ → E) (mc : List ℕ × E) (f : Form) :
    formE (mc :: f) at_ = mc.2 * runMonoVal at_ mc.1 + formE f at_ := by
  rw [formE_eq, List.foldl_cons, runFormAcc, zero_add]

theorem runFormE_addAt (at_ : ℕ → E) : ∀ (f : Form) (mono : List ℕ) (c : E),
    formE (f.addAt mono c) at_ = formE f at_ + c * runMonoVal at_ mono
  | [], mono, c => by simp [Form.addAt, formE, runMonoVal]
  | (k, v) :: rest, mono, c => by
    unfold Form.addAt
    by_cases hk : (k == mono) = true
    · have : k = mono := by simpa using hk
      subst this
      simp only [hk, ite_true, runFormE_cons]
      ring
    · simp only [hk, Bool.false_eq_true, ite_false]
      split_ifs
      · simp only [runFormE_cons]
        ring
      · simp only [runFormE_cons, runFormE_addAt at_ rest mono c]
        ring

theorem runFormE_addScaled (at_ : ℕ → E) (weight : E) : ∀ (g f : Form),
    formE (f.addScaled g weight) at_ = formE f at_ + weight * formE g at_
  | [], f => by simp [Form.addScaled, formE]
  | mc :: g, f => by
    have ih := runFormE_addScaled at_ weight g (f.addAt mc.1 (weight * mc.2))
    simp only [Form.addScaled, List.foldl_cons] at ih ⊢
    rw [ih, runFormE_addAt, runFormE_cons]
    ring

/-- A tuple's weighted forms from slot `o` on. -/
def runFpSum (weights : Array E) (at_ : ℕ → E) (l : List Form) (o : ℕ) : E :=
  ((l.zip (List.range' o l.length)).map fun x ↦ weights.getD x.2 0 * formE x.1 at_).sum

theorem runFpSum_cons (weights : Array E) (at_ : ℕ → E) (f : Form) (l : List Form) (o : ℕ) :
    runFpSum weights at_ (f :: l) o = weights.getD o 0 * formE f at_ + runFpSum weights at_ l (o + 1) := by
  simp [runFpSum, List.range'_succ]

theorem runFoldl_sum {α : Type} (h : α → E) (l : List α) (b : E) :
    l.foldl (fun a x ↦ a + h x) b = b + (l.map h).sum := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

theorem fpE_eq_runFpSum (tuple : List Form) (weights : Array E) (beta : E) (at_ : ℕ → E) :
    fpE tuple weights beta at_ = beta + runFpSum weights at_ tuple 0 := by
  unfold fpE runFpSum
  rw [List.range_eq_range']
  exact runFoldl_sum (fun x : Form × ℕ ↦ weights.getD x.2 0 * formE x.1 at_) _ beta

theorem runFpSum_difference (weights : Array E) (at_ : ℕ → E) : ∀ (a b : List Form) (o : ℕ), a.length = b.length →
    runFpSum weights at_ (difference a b) o = runFpSum weights at_ a o + runFpSum weights at_ b o
  | [], [], _, _ => by simp [difference, runFpSum]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: a, y :: b, o, h => by
    have hd : difference (x :: a) (y :: b) = x.addScaled y 1 :: difference a b := rfl
    rw [hd, runFpSum_cons, runFpSum_cons, runFpSum_cons, runFpSum_difference weights at_ a b (o + 1) (by simpa using h),
      runFormE_addScaled]
    ring

/-- The pull and push tuples of every flush of the six tables have the same length. -/
theorem flushLengths_tables :
    tables.all (fun t ↦ (t.flushes.pull.zip t.flushes.push).all fun x ↦ x.1.length == x.2.length) = true := by
  decide +kernel

/-- **A flush's difference has the fingerprint of the push's and the pull's difference.** -/
theorem fpE_difference {table : Table} (htab : table ∈ tables) {x : List Form × List Form}
    (hx : x ∈ table.flushes.pull.zip table.flushes.push) (weights : Array E) (beta : E) (at_ : ℕ → E) :
    fpE (difference x.2 x.1) weights beta at_ + beta = fpE x.2 weights beta at_ + fpE x.1 weights beta at_ := by
  have hl := List.all_eq_true.mp (List.all_eq_true.mp flushLengths_tables table htab) x hx
  rw [fpE_eq_runFpSum, fpE_eq_runFpSum, fpE_eq_runFpSum,
    runFpSum_difference weights at_ _ _ 0 (by simpa using (beq_iff_eq.mp hl).symm)]
  ring

theorem runPullFactor_eq {table : Table} (htab : table ∈ tables) {x : List Form × List Form}
    (hx : x ∈ table.flushes.pull.zip table.flushes.push) (weights : Array E) (beta : E) (at_ : ℕ → E) :
    runPullFactor weights beta at_ (runSentArr table at_) x = fpE x.1 weights beta at_ := by
  unfold runPullFactor
  split_ifs with h
  · have hex := linearise_exact x.1 weights (runSentArr table at_) at_ beta (sentColumns table) table.width
      (runSentArr_some table at_) (runSentArr_isSome htab at_) (runShape_of_mem htab hx (Or.inl rfl))
    rw [List.isEmpty_iff.mp h] at hex
    simp only [runTermsVal, List.map_nil, List.sum_nil, add_zero] at hex
    rw [← hex, add_comm]
  · rfl

theorem runPushFactor_eq {table : Table} (htab : table ∈ tables) {x : List Form × List Form}
    (hx : x ∈ table.flushes.pull.zip table.flushes.push) (weights : Array E) (beta : E) (at_ : ℕ → E) :
    runPushFactor weights beta at_ (runSentArr table at_) x = fpE x.2 weights beta at_ := by
  unfold runPushFactor
  split_ifs with h
  · have hex := linearise_exact (difference x.2 x.1) weights (runSentArr table at_) at_ beta (sentColumns table)
      table.width (runSentArr_some table at_) (runSentArr_isSome htab at_)
      (runShape_of_mem htab hx (Or.inr (Or.inr rfl)))
    rw [List.isEmpty_iff.mp h] at hex
    simp only [runTermsVal, List.map_nil, List.sum_nil, add_zero] at hex
    have hd := fpE_difference htab hx weights beta at_
    rw [runPullFactor_eq htab hx]
    linear_combination hex + hd + (fpE x.1 weights beta at_ - beta) * Domain.two_eq_zero_E
  · rfl

theorem runFoldl_mul_congr {α : Type} (f g : α → E) (l : List α) (hfg : ∀ x ∈ l, f x = g x) (a : E) :
    (l.map f).foldl (· * ·) a = (l.map g).foldl (· * ·) a := by
  rw [List.map_congr_left hfg]

/-- **A table's pull product is the product of its flushes' pull fingerprints.** -/
theorem tablePartOf_pull {table : Table} (htab : table ∈ tables) (r : ℕ) (weights : Array E) (beta : E)
    (w : List E) (at_ : ℕ → E) :
    (tablePartOf table r weights beta w at_).1.pull =
      ((table.flushes.pull.zip table.flushes.push).map fun p ↦ fpE p.1 weights beta at_).foldl (· * ·) 1 :=
  runFoldl_mul_congr _ _ _ (fun _ hx ↦ runPullFactor_eq htab hx weights beta at_) 1

/-- **A table's push product is the product of its flushes' push fingerprints.** -/
theorem tablePartOf_push {table : Table} (htab : table ∈ tables) (r : ℕ) (weights : Array E) (beta : E)
    (w : List E) (at_ : ℕ → E) :
    (tablePartOf table r weights beta w at_).1.push =
      ((table.flushes.pull.zip table.flushes.push).map fun p ↦ fpE p.2 weights beta at_).foldl (· * ·) 1 :=
  runFoldl_mul_congr _ _ _ (fun _ hx ↦ runPushFactor_eq htab hx weights beta at_) 1

/-- **A table's degrees are `tableDegrees`.** -/
theorem tablePartOf_degrees (table : Table) (r : ℕ) (weights : Array E) (beta : E) (w : List E) (at_ : ℕ → E) :
    ((tablePartOf table r weights beta w at_).1.pullDegree, (tablePartOf table r weights beta w at_).1.pushDegree) =
      tableDegrees table := rfl

end UniComplete.AlgC

/-- info: 'UniComplete.AlgC.nextScalar_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.nextScalar_run

/-- info: 'UniComplete.AlgC.tablePart_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.tablePart_run

/-- info: 'UniComplete.AlgC.tablePartOf_sent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.tablePartOf_sent

/-- info: 'UniComplete.AlgC.linearise_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.linearise_exact

/-- info: 'UniComplete.AlgC.tablePartOf_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.tablePartOf_holds

/-- info: 'UniComplete.AlgC.tablePartOf_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.tablePartOf_c1

/-- info: 'UniComplete.AlgC.tablePartOf_pull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.tablePartOf_pull

/-- info: 'UniComplete.AlgC.tablePartOf_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.tablePartOf_push

/-- info: 'UniComplete.AlgC.atTOf_relations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.atTOf_relations

/-- info: 'UniComplete.AlgC.atTOf_ringMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.atTOf_ringMap

/-- info: 'UniComplete.AlgC.heapRelations_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.heapRelations_c2

/-- info: 'UniComplete.AlgC.chunks_succ_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.chunks_succ_ne_nil
