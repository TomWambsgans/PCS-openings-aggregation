-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The two transcriptions are
-- `Rels.lean`'s `relsOf` (the identity model's) and `CodeLink.lean`'s `mainRels`, `flockClaim` (the
-- code-level link's), both of `formal/UniStatement`'s `reduceWith`, steps 4–7.
import UniSound.FinalLink
import UniSound.Ids.Build

/-!
# The identity model's batch is the verifier's (`BatchIsVerifiers`)

The relations at `t` are transcribed twice: by the identity model (`relsOf`: `tablePartOf` consumes
the values at `t` from a list, `flushStep` a fingerprint at a time) and by the code-level link
(`mainRels`: `tablePartPure` reads each table's `tableReads` values as one chunk, `consumeFold`).
**`relsAt_eq`**: they state the same relations, in the same order (a table's part reads exactly its
`tableReads` values, `tablePartOf_eq`; the values after the tables are `vals.drop tablesReads`).

Then the run's combined claims are the identity model's (`runClaims_eq`), and
**`batchIsVerifiers_of`**: an identity model whose batch is `Model.lean`'s `prodOf`, `targetOf` has the
verifier's batch (`batchProd`, `batchTargetOf`) where the counts are in range and Flock's result is the
main line's (`FlockGood`); `batchIsVerifiers_ids` for `idsRestOf`. **`nVOf_eq_of`**: the model's number
of values at `t` is the code's (`valsCount`) once the tables read at most `4096` values.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset

/-! ## Lists -/

namespace Align

theorem headD_drop : ∀ (V : List E) (i : ℕ), (V.drop i).headD 0 = V.getD i 0
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | _ :: _, _ + 1 => by simp

theorem take_one_headD : ∀ (V : List E), (V.take 1).headD 0 = V.headD 0
  | [] => rfl
  | _ :: _ => rfl

theorem getD_take (V : List E) (a j : ℕ) (h : j < a) : (V.take a).getD j 0 = V.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ↓reduceIte]

theorem getD_drop : ∀ (V : List E) (i j : ℕ), (V.drop i).getD j 0 = V.getD (i + j) 0
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: V, i + 1, j => by
    rw [show i + 1 + j = (i + j) + 1 by omega]
    simp

theorem take_take_add : ∀ (X : List E) (a m : ℕ), (X.take (a + m)).take a = X.take a
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: X, a + 1, m => by
    rw [show a + 1 + m = (a + m) + 1 by omega]
    simp [take_take_add X a m]

theorem drop_take_add : ∀ (X : List E) (a m : ℕ), (X.take (a + m)).drop a = (X.drop a).take m
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: X, a + 1, m => by
    rw [show a + 1 + m = (a + m) + 1 by omega]
    simp [drop_take_add X a m]

theorem drop_drop_add : ∀ (X : List E) (a b : ℕ), (X.drop a).drop b = X.drop (a + b)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: X, a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp [drop_drop_add X a b]

/-! ## A table's part -/

/-- **The sent columns, one value each** (`tablePartPure`'s first loop) from position `i`: the
columns set and their `equal` relations, as `sentOf` and `tablePartOf`'s first relations read them. -/
theorem sent_consume (t : Table) (pt : List E) : ∀ (l : List ℕ) (i : ℕ) (A : Array (Option E))
    (R : Array Relation) (V W : List E), (∀ j, i ≤ j → j < i + l.length → V.getD j 0 = W.getD j 0) →
    (consumeFold (fun _ => 1) (_root_.UniSound.sentStep t pt) l (A, R) (V.drop i)).1 =
        (l.zip (List.range' i l.length)).foldl (fun a p => a.set! p.1 (some (W.getD p.2 0))) A ∧
      (consumeFold (fun _ => 1) (_root_.UniSound.sentStep t pt) l (A, R) (V.drop i)).2.toList =
        R.toList ++ (l.zip (List.range' i l.length)).map fun p =>
          Relation.equal (.table t.opcode p.1) pt (W.getD p.2 0)
  | [], i, A, R, V, W, _ => by simp [consumeFold]
  | c :: l, i, A, R, V, W, h => by
    have hv : ((V.drop i).take 1).headD 0 = W.getD i 0 := by
      rw [take_one_headD, headD_drop, h i le_rfl (by simp only [List.length_cons]; omega)]
    have ih := sent_consume t pt l (i + 1) (A.set! c (some (W.getD i 0)))
      (R.push (Relation.equal (.table t.opcode c) pt (W.getD i 0))) V W
      (fun j h1 h2 => h j (by omega) (by simp only [List.length_cons]; omega))
    simp only [consumeFold, _root_.UniSound.sentStep, hv, drop_drop_add, List.length_cons,
      List.range'_succ, List.zip_cons_cons, List.foldl_cons, List.map_cons]
    refine ⟨ih.1, ?_⟩
    rw [ih.2, Array.toList_push, List.append_assoc]
    rfl

/-- **One flush**: `flushStep` (the identity model's) is `CodeTables.lean`'s `flushStep` on the
fingerprints it sends (`flushReads`), the values left after them. -/
theorem flush_step (t : Table) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) (x : List Form × List Form) (R : Array Relation) (P Q : E) (a b : ℕ)
    (X : List E) :
    Ids.flushStep (fun c ↦ .table t.opcode c) pt weights beta sent ⟨P, Q, a, b, R.toList, X⟩ x =
      ⟨(_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).2.1,
        (_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).2.2.1,
        (_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).2.2.2.1,
        (_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).2.2.2.2,
        (_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).1.toList,
        X.drop (flushReads weights sent x)⟩ := by
  rcases hA : (linearise x.1 weights sent).2.isEmpty <;>
    rcases hB : (linearise (difference x.2 x.1) weights sent).2.isEmpty <;>
    rcases X with _ | ⟨x0, _ | ⟨x1, X⟩⟩ <;>
    simp [Ids.flushStep, _root_.UniSound.flushStep, flushReads, hA, hB]

/-- **The flushes**: the identity model's fold is `consumeFold` of the code's flushes, the values
left after their sent fingerprints. -/
theorem flush_fold (t : Table) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) :
    ∀ (fls : List (List Form × List Form)) (R : Array Relation) (P Q : E) (a b : ℕ) (X : List E),
      fls.foldl (Ids.flushStep (fun c ↦ .table t.opcode c) pt weights beta sent)
          ⟨P, Q, a, b, R.toList, X⟩ =
        ⟨(consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).2.1,
          (consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).2.2.1,
          (consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).2.2.2.1,
          (consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).2.2.2.2,
          (consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).1.toList,
          X.drop (fls.map (flushReads weights sent)).sum⟩
  | [], R, P, Q, a, b, X => by simp [consumeFold]
  | x :: fls, R, P, Q, a, b, X => by
    rw [List.foldl_cons, flush_step, flush_fold t pt weights beta sent fls]
    simp only [consumeFold, List.map_cons, List.sum_cons, take_take_add, drop_take_add, drop_drop_add,
      Prod.mk.eta]

end Align

open Align in
/-- **A table's part reads exactly its `tableReads` values**: `tablePartOf` on a list is
`tablePartPure` on its first `tableReads t` values, the rest left. -/
theorem tablePartOf_eq (t : Table) (lh : ℕ) (weights : Array E) (beta : E) (w X : List E) :
    tablePartOf t lh weights beta w X =
      ((tablePartPure t lh weights beta w (X.take (tableReads t))).1,
        (tablePartPure t lh weights beta w (X.take (tableReads t))).2, X.drop (tableReads t)) := by
  have hk : tableReads t = (sentColumns t).length +
      ((t.flushes.pull.zip t.flushes.push).map (flushReads #[] (sentPat t))).sum := rfl
  obtain ⟨hs1, hs2⟩ := sent_consume t (w.take lh) (sentColumns t) 0 (Array.replicate t.width none) #[]
    ((X.take (tableReads t)).take (sentColumns t).length) X (fun j _ hj => by
      rw [Nat.zero_add] at hj
      rw [getD_take _ _ _ hj, getD_take _ _ _ (by omega)])
  rw [List.drop_zero, ← List.range_eq_range'] at hs1 hs2
  have hsent : (consumeFold (fun _ => 1) (_root_.UniSound.sentStep t (w.take lh)) (sentColumns t)
      (Array.replicate t.width none, #[]) ((X.take (tableReads t)).take (sentColumns t).length)).1 =
      sentOf t X := hs1
  have hpat : SamePat (sentOf t X) (sentPat t) := by
    rw [← hsent]
    exact samePat_consume_sent t (sentColumns t) (w.take lh) [] _ _ _ [] (samePat_refl _)
  have hsum := sum_flushReads t weights (sentOf t X) hpat
  have hfold := flush_fold t (w.take lh) weights beta (sentOf t X) (t.flushes.pull.zip t.flushes.push)
    (consumeFold (fun _ => 1) (_root_.UniSound.sentStep t (w.take lh)) (sentColumns t)
      (Array.replicate t.width none, #[]) ((X.take (tableReads t)).take (sentColumns t).length)).2
    1 1 1 0 (X.drop (sentColumns t).length)
  rw [hs2, Array.toList_empty, List.nil_append] at hfold
  have hdrop : (X.take (tableReads t)).drop (sentColumns t).length =
      (X.drop (sentColumns t).length).take
        ((t.flushes.pull.zip t.flushes.push).map (flushReads weights (sentOf t X))).sum := by
    rw [hsum, hk, drop_take_add]
  unfold tablePartOf tablePartPure
  simp only []
  rw [hfold, hsent, hdrop]
  simp only [drop_drop_add, hsum, ← hk]

open Align in
/-- **The tables' parts**: `tablesPart` on a list is `consumeFold tableReads (tablesStep …)` on its
first values, the rest left. -/
theorem tablesPart_eq (S : Shape) (weights : Array E) (beta : E) (w : List E) :
    ∀ (ts : List Table) (R : Array Relation) (P : Array TablePart) (X : List E),
      (consumeFold tableReads (tablesStep S.heights weights beta w) ts (R, P)
          (X.take (ts.map tableReads).sum)).1.toList = R.toList ++ (tablesPart S weights beta w ts X).2.1 ∧
        (consumeFold tableReads (tablesStep S.heights weights beta w) ts (R, P)
          (X.take (ts.map tableReads).sum)).2.toList = P.toList ++ (tablesPart S weights beta w ts X).1 ∧
        (tablesPart S weights beta w ts X).2.2 = X.drop (ts.map tableReads).sum
  | [], R, P, X => by simp [consumeFold, tablesPart]
  | t :: ts, R, P, X => by
    obtain ⟨i1, i2, i3⟩ := tablesPart_eq S weights beta w ts
      (R ++ (tablePartPure t (S.heights.getD t.opcode 0) weights beta w (X.take (tableReads t))).2.toArray)
      (P.push (tablePartPure t (S.heights.getD t.opcode 0) weights beta w (X.take (tableReads t))).1)
      (X.drop (tableReads t))
    have ht := tablePartOf_eq t (S.heights.getD t.opcode 0) weights beta w X
    simp only [consumeFold, List.map_cons, List.sum_cons, take_take_add, drop_take_add, tablesStep]
    simp only [tablesPart, ht]
    refine ⟨?_, ?_, ?_⟩
    · rw [i1]
      simp
    · rw [i2]
      simp
    · rw [i3, drop_drop_add]

/-! ## The relations at `t` -/

namespace Align

/-- The digits `t` is read through. -/
def wOf (shape : Shape) (t : E) : List E := digits t (max shape.heap.h (shape.constraintVars + 4) + 2)

/-- The tables' relations and parts as `mainRels` reads them. -/
def stOf (shape : Shape) (alphas : List E) (beta t : E) (vals : List E) :
    Array Relation × Array TablePart :=
  consumeFold tableReads (tablesStep shape.heights (eqKernel alphas) beta (wOf shape t)) tables (#[], #[])
    (vals.take tablesReads)

/-- The constraint quotient's relation as `mainRels` states it. -/
def crOf (shape : Shape) (pw : List E) (alphas : List E) (beta gamma t : E) (vals : List E) :
    Relation × ℕ :=
  constraintRelation shape (stOf shape alphas beta t vals).2.toList pw gamma t
    (vals.getD (tablesReads + 6) 0) (wOf shape t)

/-- The heap's relations as `mainRels` states them. -/
def hrOf (shape : Shape) (pw : List E) (counts : List (List E)) (alphas : List E) (beta gamma t : E)
    (vals : List E) : List Relation × List (Column × ℕ × Bool) :=
  heapRelations shape ((counts.zip shape.heights).map fun x => activeVanishingFromBits (wOf shape t) x.1 x.2)
    (stOf shape alphas beta t vals).2.toList (eqKernel alphas) beta (vals.getD (tablesReads + 5) 0)
    (vals.getD (tablesReads + 6) 0) (vals.getD (tablesReads + 2) 0)
    (vals.getD (tablesReads + 2) 0 + (eqKernel alphas).getD 2 0 * (1 + vals.getD tablesReads 0))
    (vals.getD (tablesReads + 4) 0)
    (vals.getD (tablesReads + 4) 0 + (eqKernel alphas).getD 2 0 * (1 + vals.getD (tablesReads + 3) 0))
    (wOf shape t) (chunks ((crOf shape pw alphas beta gamma t vals).2 + 1))

/-- **`mainRels`' relations**, as a list. -/
theorem mainRels_fst (shape : Shape) (pw : List E) (counts : List (List E)) (alphas : List E)
    (beta gamma t : E) (vals : List E) :
    (mainRels shape pw counts alphas beta gamma t vals).1.toList =
      (stOf shape alphas beta t vals).1.toList ++
        [Relation.equal (.memory 3) ((wOf shape t).take shape.logMemory) (vals.getD tablesReads 0),
          Relation.equal .address ((wOf shape t).take shape.logMemory) (vals.getD (tablesReads + 1) 0),
          ⟨(List.range 3).map (fun k => term (.memory k) ((wOf shape t).take shape.logMemory)
              ((eqKernel alphas).getD (3 + k) 0)),
            vals.getD (tablesReads + 2) 0 + beta + (eqKernel alphas).getD 0 0 * sepMem +
              (eqKernel alphas).getD 1 0 * vals.getD (tablesReads + 1) 0 +
              (eqKernel alphas).getD 2 0 * vals.getD tablesReads 0⟩,
          Relation.equal .bytecodeFinal ((wOf shape t).take shape.logBytecode)
            (vals.getD (tablesReads + 3) 0),
          Relation.equal .bytecodeTuple (alphas ++ (wOf shape t).take shape.logBytecode)
            (vals.getD (tablesReads + 4) 0 + beta + (eqKernel alphas).getD 2 0 * vals.getD (tablesReads + 3) 0),
          (crOf shape pw alphas beta gamma t vals).1] ++
        (hrOf shape pw counts alphas beta gamma t vals).1 := by
  unfold mainRels
  simp only [wOf, stOf, crOf, hrOf, Array.toList_append, Array.toList_push, List.append_assoc,
    List.cons_append, List.nil_append]

theorem tp_eq (inp : RelInput) :
    tablesPart inp.shape (eqKernel inp.alphas) inp.beta (wOf inp.shape inp.t) tables inp.vals = inp.tp :=
  rfl

theorem st_eq (inp : RelInput) :
    consumeFold tableReads (tablesStep inp.shape.heights (eqKernel inp.alphas) inp.beta (wOf inp.shape inp.t))
        tables (#[], #[]) (inp.vals.take (tables.map tableReads).sum) =
      stOf inp.shape inp.alphas inp.beta inp.t inp.vals :=
  rfl

/-- `tablesPart_eq` from the empty arrays, for any tables (a variable list: `tables` itself is never
reduced). -/
theorem tablesPart_fst (S : Shape) (w8 : Array E) (beta : E) (w : List E) (ts : List Table) (X : List E) :
    (consumeFold tableReads (tablesStep S.heights w8 beta w) ts (#[], #[])
      (X.take (ts.map tableReads).sum)).1.toList = (tablesPart S w8 beta w ts X).2.1 := by
  have k := (tablesPart_eq S w8 beta w ts #[] #[] X).1
  simp only [List.nil_append] at k
  exact k

theorem tablesPart_snd (S : Shape) (w8 : Array E) (beta : E) (w : List E) (ts : List Table) (X : List E) :
    (consumeFold tableReads (tablesStep S.heights w8 beta w) ts (#[], #[])
      (X.take (ts.map tableReads).sum)).2.toList = (tablesPart S w8 beta w ts X).1 := by
  have k := (tablesPart_eq S w8 beta w ts #[] #[] X).2.1
  simp only [List.nil_append] at k
  exact k

/-- The tables' relations. -/
theorem tp_fst (inp : RelInput) :
    (stOf inp.shape inp.alphas inp.beta inp.t inp.vals).1.toList = inp.tp.2.1 := by
  rw [← st_eq, ← tp_eq]
  exact tablesPart_fst _ _ _ _ tables _

/-- The tables' parts. -/
theorem tp_snd (inp : RelInput) :
    (stOf inp.shape inp.alphas inp.beta inp.t inp.vals).2.toList = inp.tp.1 := by
  rw [← st_eq, ← tp_eq]
  exact tablesPart_snd _ _ _ _ tables _

/-- The values after the tables'. -/
theorem rest_getD (inp : RelInput) (k : ℕ) : inp.rest.getD k 0 = inp.vals.getD (tablesReads + k) 0 := by
  have h3 := (tablesPart_eq inp.shape (eqKernel inp.alphas) inp.beta (wOf inp.shape inp.t) tables
    #[] #[] inp.vals).2.2
  rw [tp_eq] at h3
  have e : inp.rest = inp.tp.2.2 := rfl
  rw [e, h3]
  exact getD_drop _ _ _

/-- The constraint quotient's relation. -/
theorem constraint_eq (inp : RelInput) :
    inp.constraint = crOf inp.shape inp.publicWords inp.alphas inp.beta inp.gamma inp.t inp.vals := by
  have e : inp.constraint = constraintRelation inp.shape inp.tp.1 inp.publicWords inp.gamma inp.t
    (inp.rest.getD 6 0) (wOf inp.shape inp.t) := rfl
  rw [e, ← tp_snd, rest_getD]
  rfl

/-- The heap's relations. -/
theorem heap_eq (inp : RelInput) :
    inp.heap = hrOf inp.shape inp.publicWords inp.counts inp.alphas inp.beta inp.gamma inp.t inp.vals := by
  have e : inp.heap = heapRelations inp.shape
      ((inp.counts.zip inp.shape.heights).map fun p ↦ activeVanishingFromBits (wOf inp.shape inp.t) p.1 p.2)
      inp.tp.1 (eqKernel inp.alphas) inp.beta (inp.rest.getD 5 0) (inp.rest.getD 6 0) (inp.rest.getD 2 0)
      (inp.rest.getD 2 0 + (eqKernel inp.alphas).getD 2 0 * (1 + inp.rest.getD 0 0)) (inp.rest.getD 4 0)
      (inp.rest.getD 4 0 + (eqKernel inp.alphas).getD 2 0 * (1 + inp.rest.getD 3 0)) (wOf inp.shape inp.t)
      (chunks (inp.constraint.2 + 1)) := rfl
  rw [e, constraint_eq, ← tp_snd]
  simp only [rest_getD, Nat.add_zero]
  rfl

/-- **The identity model's relations but Flock's are `mainRels`'**. -/
theorem relsOf_fst (inp : RelInput) :
    inp.tp.2.1 ++ inp.memRels ++ inp.bcRels ++ [inp.constraint.1] ++ inp.heap.1 =
      (mainRels inp.shape inp.publicWords inp.counts inp.alphas inp.beta inp.gamma inp.t inp.vals).1.toList := by
  rw [mainRels_fst, ← tp_fst, constraint_eq, heap_eq]
  simp only [RelInput.memRels, RelInput.bcRels, RelInput.memoryFinalCount, RelInput.address,
    RelInput.memoryPull, RelInput.bytecodeFinalCount, RelInput.bytecodePull, RelInput.w, RelInput.weights,
    wOf, rest_getD, Nat.add_zero, List.append_assoc, List.cons_append, List.nil_append]

/-- **The identity model's relations are the code-level link's**, Flock's ring term (`ringRels`) the one
`flockClaim` adds. -/
theorem relsOf_eq (inp : RelInput) (fl : FlockOut) (h1 : fl.1 = inp.flockPoint)
    (h2 : fl.2.1 = inp.flockEnd) :
    relsOf inp = (flockClaim (mainRels inp.shape inp.publicWords inp.counts inp.alphas inp.beta inp.gamma
      inp.t inp.vals).1 fl).1.toList := by
  rw [show relsOf inp = (inp.tp.2.1 ++ inp.memRels ++ inp.bcRels ++ [inp.constraint.1] ++ inp.heap.1) ++
    inp.ringRels from rfl, relsOf_fst]
  obtain ⟨p, e, pend⟩ := fl
  simp only at h1 h2
  subst h1 h2
  unfold flockClaim RelInput.ringRels
  rcases h : inp.flockEnd with _ | (⟨map, target⟩ | ⟨ws, value⟩) <;> simp

theorem alphasOf_eq (ch : List E) (h : 4 ≤ ch.length) : alphasOf ch = ch.take 4 := by
  rcases ch with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rfl

/-- The run's claims when every commitment has one. -/
theorem flockClaim_ringMap (rels : Array Relation) {κ : ℕ} (Fl : FlockSound κ)
    (fd : Done) : (flockClaim rels (Fl.prog.out fd [])).2.2 = ringMapAt Fl fd := by
  unfold flockClaim ringMapAt
  rcases h : (Fl.prog.out fd []).2.1 with _ | (⟨map, target⟩ | ⟨ws, value⟩) <;> rfl

theorem filterMap_commitments (f : Commitment → Option Combined)
    (h : (commitments.filterMap fun c => (f c).map fun x => (c, x)).length = 3) :
    (commitments.filterMap fun c => (f c).map fun x => (c, x)) =
      commitments.map fun c => (c, (f c).getD zeroClaim) := by
  simp only [commitments] at h ⊢
  rcases h1 : f .c1 with _ | x1 <;> rcases h2 : f .c2 with _ | x2 <;> rcases h3 : f .setup with _ | x3 <;>
    simp_all [List.filterMap]

end Align

open Align

/-- **The batch's variables are the code's.** -/
theorem batchVars_eq (S : Shape) : batchVars S = varsOf (layoutsOf S) := rfl

/-- **A commitment's layout is the code's.** -/
theorem layoutOf_eq (S : Shape) (c : Commitment) :
    _root_.UniSound.layoutOf (layoutsOf S) c = Ids.layoutOf S c := rfl

section Model

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ)

/-- **The identity model's relations at `t` are the code-level link's** (`mainRels`, then Flock's
claim), for round `0`'s challenges `α = alphasOf ch`. -/
theorem relsAt_eq_alphas (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) :
    relsAt D Fl s ch fd t vals = (flockClaim (mainRels D.shape (publicWordsOf s.1.toList)
      (countsBits D.shape.heights s.2) (alphasOf ch) (ch.getD 4 0) (ch.getD 5 0) t vals).1
        (Fl.prog.out fd [])).1.toList :=
  relsOf_eq (relInput D s ch (Fl.prog.out fd []) t vals) (Fl.prog.out fd []) rfl rfl

/-- **The identity model's relations at `t` are the code-level link's**, for at least four challenges
in round `0` (`α` their first four, as the code reads them). -/
theorem relsAt_eq (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (hch : 4 ≤ ch.length) :
    relsAt D Fl s ch fd t vals = (flockClaim (mainRels D.shape (publicWordsOf s.1.toList)
      (countsBits D.shape.heights s.2) (ch.take 4) (ch.getD 4 0) (ch.getD 5 0) t vals).1
        (Fl.prog.out fd [])).1.toList := by
  rw [relsAt_eq_alphas, alphasOf_eq ch hch]

/-- **The run's combined claims are the identity model's** (`combAt`, one per commitment), its ring
map Flock's (`ringMapAt`). -/
theorem runClaims_eq (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (rho : E)
    (hch : 4 ≤ ch.length) :
    (runClaims D Fl s ch fd t vals rho).1 = commitments.map (fun c => (c, combAt D Fl s ch fd t vals rho c)) ∧
      (runClaims D Fl s ch fd t vals rho).2 = ringMapAt Fl fd := by
  have hl := mainCombined_length D.shape (publicWordsOf s.1.toList) (countsBits D.shape.heights s.2)
    (ch.take 4) (ch.getD 4 0) (ch.getD 5 0) t vals (Fl.prog.out fd []) rho
  rw [← relsAt_eq D Fl s ch fd t vals hch] at hl
  refine ⟨?_, ?_⟩
  · have e : (runClaims D Fl s ch fd t vals rho).1 = commitments.filterMap fun c =>
        (combine (relsAt D Fl s ch fd t vals) c rho).map fun x => (c, x) := by
      unfold runClaims
      rw [← relsAt_eq D Fl s ch fd t vals hch]
    rw [e, filterMap_commitments _ hl]
    rfl
  · exact flockClaim_ringMap _ Fl fd

theorem ProdSum.ext' {P Q : ProdSum} (h1 : P.vars = Q.vars) (h2 : P.n = Q.n) (h3 : P.coef = Q.coef)
    (h4 : P.A = Q.A) (h5 : P.B = Q.B) : P = Q := by
  obtain ⟨_, _, _, _, _⟩ := P
  obtain ⟨_, _, _, _, _⟩ := Q
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

theorem getD_cmb (f : Commitment → Combined) (k : ℕ) (hk : k < 3) :
    (commitments.map fun c => (c, f c)).getD k default = (cm k, f (cm k)) := by
  interval_cases k <;> rfl

/-- **The identity model's batch is the verifier's** (`prodOf` is `batchProd`) where the counts are in
range and Flock's result is the main line's. -/
theorem prodOf_eq_batchProd (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) (rho lam : E) (hcf : CountsInRange D.shape.heights s.2)
    (hgood : FlockGood κ (batchVars D.shape) (Fl.prog.out fd [])) (hch : 4 ≤ ch.length) :
    Ids.prodOf D Fl s c1 ch fd c2 t vals rho lam = batchProd D Fl s c1 ch fd c2 t vals rho lam := by
  have hg : CountsFit D.shape s.2 ∧ FlockGood κ (batchVars D.shape) (Fl.prog.out fd []) := ⟨hcf, hgood⟩
  obtain ⟨h1, h2⟩ := runClaims_eq D Fl s ch fd t vals rho hch
  have hlen : (commitments.map fun c => (c, combAt D Fl s ch fd t vals rho c)).length = 3 := rfl
  unfold Ids.prodOf batchProd _root_.UniSound.prodOf
  rw [ite_eq_left hg, h1, h2, hlen]
  refine ProdSum.ext' (batchVars_eq _) rfl rfl ?_ ?_
  · funext k u
    dsimp only
    by_cases hk : k < 3
    · rw [ite_eq_left hk, ite_eq_left hk, getD_cmb _ k hk]
      dsimp only
      rw [layoutOf_eq, ← batchVars_eq]
    · rw [ite_eq_right hk, ite_eq_right hk]
  · funext k u
    dsimp only
    by_cases hk : k < 3
    · rw [ite_eq_left hk, ite_eq_left hk, getD_cmb _ k hk]
      dsimp only
      rw [layoutOf_eq]
      rfl
    · rw [ite_eq_right hk, ite_eq_right hk]

/-- **The identity model's target is the verifier's** (`targetOf` is `batchTargetOf`). -/
theorem targetOf_eq_batchTargetOf (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) (rho lam : E) (hcf : CountsInRange D.shape.heights s.2)
    (hgood : FlockGood κ (batchVars D.shape) (Fl.prog.out fd [])) (hch : 4 ≤ ch.length) :
    Ids.targetOf D Fl s c1 ch fd c2 t vals rho lam = batchTargetOf D Fl s ch fd t vals rho lam := by
  have hg : CountsFit D.shape s.2 ∧ FlockGood κ (batchVars D.shape) (Fl.prog.out fd []) := ⟨hcf, hgood⟩
  obtain ⟨h1, -⟩ := runClaims_eq D Fl s ch fd t vals rho hch
  unfold Ids.targetOf batchTargetOf _root_.UniSound.targetOf
  rw [ite_eq_left hg, h1]
  simp only [batchTarget, commitments, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Finset.sum_range_succ, Finset.sum_range_zero, cm, List.getD_cons_zero, List.getD_cons_succ]
  ring

end Model

/-- **`BatchIsVerifiers`** for an identity model whose batch is `Model.lean`'s (`prodOf`, `targetOf`),
where Flock's result on every completed transcript is the main line's (`FlockGood`). -/
theorem batchIsVerifiers_of (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (B : BusModel D κ)
    (J : UniIdsRest D Fl B) (hp : J.prod = Ids.prodOf D Fl) (ht : J.target = Ids.targetOf D Fl)
    (hgood : ∀ fd, DoneFits Fl.prog.rounds fd → FlockGood κ (batchVars D.shape) (Fl.prog.out fd [])) :
    BatchIsVerifiers D Fl (UniIds.ofBus Fl B J) := by
  intro s c1 ch fd c2 t vals rho lam hcf hfd hch _
  refine ⟨?_, ?_⟩
  · show J.prod s c1 ch fd c2 t vals rho lam = _
    rw [hp]
    exact prodOf_eq_batchProd D Fl s c1 ch fd c2 t vals rho lam hcf (hgood fd hfd) (by omega)
  · show J.target s c1 ch fd c2 t vals rho lam = _
    rw [ht]
    exact targetOf_eq_batchTargetOf D Fl s c1 ch fd c2 t vals rho lam hcf (hgood fd hfd) (by omega)

/-- **`BatchIsVerifiers` for `idsRestOf`** (`Build.lean`). -/
theorem batchIsVerifiers_ids (D : Deployment) (N : ℕ) (h : IdsHyps D N)
    (Fl : FlockSound (D.shape.heights.getD opBlake2s 0)) (d n : ℕ) (g : IdsGaps D Fl d n)
    (hgood : ∀ fd, DoneFits Fl.prog.rounds fd →
      FlockGood (D.shape.heights.getD opBlake2s 0) (batchVars D.shape) (Fl.prog.out fd [])) :
    BatchIsVerifiers D Fl (UniIds.ofBus Fl (busModelOf D N h g.cvecOk) (idsRestOf D N h Fl d n g)) :=
  batchIsVerifiers_of D Fl _ _ rfl rfl hgood

/-- **The identity model's number of values at `t` is the code's**, once the tables read at most
`4096` (`GameNumbers.lean`'s `valsCount_le`: at most `122` in all). -/
theorem nVOf_eq_of (S : Shape) (h : tablesReads ≤ 4096) : nVOf S = valsCount := by
  have h3 := (tablesPart_eq S #[] 0 [] tables #[] #[] (List.replicate 4096 0)).2.2
  have htr : (tables.map tableReads).sum = tablesReads := rfl
  rw [htr] at h3
  have hl : (tablesPart S #[] 0 [] tables (List.replicate 4096 0)).2.2.length = 4096 - tablesReads := by
    rw [h3, List.length_drop, List.length_replicate]
  unfold nVOf valsCount
  simp only []
  rw [hl]
  omega

end UniSound.Ids

