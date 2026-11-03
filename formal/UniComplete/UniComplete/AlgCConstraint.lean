-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgCQuot

/-!
# The constraint quotient's identity at `t` (milestone 4, the algebra, item 2's last relation)

The verifier states the constraints' identity at `t` as one relation on `C1` (`constraintRelation`): its terms are
the unsent columns' parts (JUMP's `w`, every table's `z`, BLAKE2S's copies and `q_flock`'s slots, the memory's
limbs), its value `Q_W(t) w_{r_W}(t)` plus the known part (from the sent values). **`constraintRelation_eval`**: if
every term evaluates to its column's polynomial at `t` (on `C1`'s stack, `AlgCTerm`) and every sent value is its
column's polynomial at `t` (`AlgCRun`), then the terms' values plus the known part are the prover's numerator at
`t`, `N(t) = Σ_i γ^i M_i(t) lift_i(t)` (`constraintNumerator_eq`'s items, in the same order), and the relation's
degree is `Shape.constraintDegree`. With `Q_W w_{r_W} = N` (`AlgCQuot`) the relation holds.

The proof follows the verifier's two loops against the items (`forIn_id_spec`: a loop that always continues, related
step by step to a fold), without restating the loops' bodies.
-/

namespace UniComplete.AlgC

open UniStatement LeanVM.Parameters Polynomial Finset

/-! ### Evaluation helpers -/

theorem pE_add (t : E) (p q : Poly) : pEval t (p + q) = pEval t p + pEval t q := by
  rw [pEval_eq, pEval_eq, pEval_eq, tp_add, Polynomial.eval_add]

theorem pE_mul (t : E) (p q : Poly) : pEval t (p * q) = pEval t p * pEval t q := by
  rw [pEval_eq, pEval_eq, pEval_eq, tp_mul, Polynomial.eval_mul]

theorem pE_one (t : E) : pEval t (1 : Poly) = 1 := by rw [pEval_eq, tp_one, Polynomial.eval_one]

theorem pE_zero (t : E) : pEval t (0 : Poly) = 0 := by rw [pEval_eq, tp_zero, Polynomial.eval_zero]

theorem pE_C (t x : E) : pEval t (pC x) = x := by rw [pEval_eq, tp_C, Polynomial.eval_C]

theorem pE_X (t : E) : pEval t pX = t := by rw [pEval_eq, tp_X, Polynomial.eval_X]

theorem pE_foldl_mul {α : Type} (t : E) (l : List α) (f : α → Poly) (z : Poly) :
    pEval t (l.foldl (fun p c ↦ p * f c) z) = pEval t z * (l.map fun c ↦ pEval t (f c)).prod := by
  induction l generalizing z with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, pE_mul, List.map_cons, List.prod_cons, mul_assoc]

theorem foldl_mul_prod {α : Type} (l : List α) (f : α → E) (z : E) :
    l.foldl (fun acc c ↦ acc * f c) z = z * (l.map f).prod := by
  induction l generalizing z with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem sum_push (ev : Term → E) (a : Array Term) (x : Term) :
    ((a.push x).toList.map ev).sum = (a.toList.map ev).sum + ev x := by
  simp

/-! ### The items, evaluated -/

/-- The items' fold at `t`: `(Σ_i γ^i M_i(t) lift_i(t), γ^n)` from a start. -/
def evalItems (t gamma : E) (items : List Item) (s : E × E) : E × E :=
  items.foldl (fun (a : E × E) (it : Item) ↦ (a.1 + a.2 * pEval t (it.1 * it.2), a.2 * gamma)) s

theorem evalItems_append (t gamma : E) (l1 l2 : List Item) (s : E × E) :
    evalItems t gamma (l1 ++ l2) s = evalItems t gamma l2 (evalItems t gamma l1 s) := by
  unfold evalItems
  rw [List.foldl_append]

theorem evalItems_cons (t gamma : E) (it : Item) (l : List Item) (s : E × E) :
    evalItems t gamma (it :: l) s = evalItems t gamma l (s.1 + s.2 * pEval t (it.1 * it.2), s.2 * gamma) := rfl

theorem evalItems_nil (t gamma : E) (s : E × E) : evalItems t gamma [] s = s := rfl

/-- **The numerator at `t` is the items' fold at `t`.** -/
theorem pEval_foldl_addItem (t gamma : E) : ∀ (items : List Item) (s : Poly × E),
    (pEval t (items.foldl (addItem gamma) s).1, (items.foldl (addItem gamma) s).2) =
      evalItems t gamma items (pEval t s.1, s.2)
  | [], _ => rfl
  | it :: rest, s => by
    rw [List.foldl_cons, pEval_foldl_addItem t gamma rest, evalItems_cons]
    have h1 : pEval t (addItem gamma s it).1 = pEval t s.1 + s.2 * pEval t (it.1 * it.2) := by
      show pEval t (s.1 + pC s.2 * it.1 * it.2) = _
      rw [pE_add, mul_assoc, pE_mul, pE_C]
    rw [h1]
    rfl

theorem pEval_constraintNumerator (tr : Trace) (gamma t : E) (words : List E) :
    pEval t (constraintNumerator tr gamma words) = (evalItems t gamma (numItems tr words) (0, 1)).1 := by
  rw [constraintNumerator_eq]
  have h := pEval_foldl_addItem t gamma (numItems tr words) (0, 1)
  have h0 : pEval t ((0 : Poly), (1 : E)).1 = 0 := pE_zero t
  rw [h0] at h
  have h2 := congrArg Prod.fst h
  dsimp only at h2
  exact h2

/-! ### Loops related to folds -/

/-- **An `Id` loop that always continues, related step by step to a fold.** -/
theorem forIn_id_spec {α β γ : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (P : β → γ → Prop) (step : γ → α → γ) (c0 : γ) (h0 : P init c0)
    (h : ∀ a ∈ l, ∀ b c, P b c → ∃ b', f a b = pure (ForInStep.yield b') ∧ P b' (step c a)) :
    P (Id.run (forIn l init f)) (l.foldl step c0) := by
  induction l generalizing init c0 with
  | nil => exact h0
  | cons x xs ih =>
    obtain ⟨b', hb', hP⟩ := h x (by simp) init c0 h0
    rw [List.forIn_cons, hb', List.foldl_cons]
    exact ih b' (step c0 x) hP fun a ha b c hbc ↦ h a (List.mem_cons_of_mem _ ha) b c hbc

/-! ### The verifier's loop, restated -/

/-- BLAKE2S's inner step (a copy and its slot, at the power's `γ`). -/
def relInner (sh : Shape) (t gamma : E) (w : List E) (x : Table × TablePart) (s : Array Term × E) (c : ℕ) :
    Array Term × E :=
  match qflockSlot (x.1.columns.getD c "") with
  | some slot =>
    ((s.1.push (term (.table x.1.opcode c) (w.take (sh.heights.getD x.1.opcode 0))
        (s.2 * vanishingRatio w (sh.heights.getD x.1.opcode 0) sh.constraintVars))).push
      (term (.qflockSlot slot) (coordinatesAt t (coordinateFunctionals (sh.heights.getD x.1.opcode 0)))
        (s.2 * vanishingRatio w (sh.heights.getD x.1.opcode 0) sh.constraintVars)),
      s.2 * gamma)
  | none => s

/-- **The verifier's step over one table** (`constraintRelation`'s loop body, as a function): the known part, the
terms, the power, the degree. -/
def relBody (sh : Shape) (t gamma : E) (w : List E) (s : E × Array Term × E × ℕ) (x : Table × TablePart) :
    E × Array Term × E × ℕ :=
  let r := sh.heights.getD x.1.opcode 0
  let vR := vanishingRatio w r sh.constraintVars
  let cnt := x.1.countColumns.foldl (fun acc c ↦ acc * (x.2.sent.getD c none).getD 0) 1
  let cond := (x.2.sent.getD (colIdx x.1.columns "v_cond") none).getD 0
  let flag := (x.2.sent.getD (colIdx x.1.columns "b") none).getD 0
  if x.1.opcode = opJump then
    (s.1 + s.2.2.1 * vR * flag + s.2.2.1 * gamma * vR * cond * (flag + 1) + s.2.2.1 * gamma * gamma * vR,
      (s.2.1.push (term (.table x.1.opcode (colIdx x.1.columns "w")) (w.take r) (s.2.2.1 * vR * cond))).push
        (term (.inverse x.1.opcode) (w.take r) (s.2.2.1 * gamma * gamma * vR * cnt)),
      s.2.2.1 * gamma * gamma * gamma,
      max (max s.2.2.2 (degree (2 ^ r) 2)) (degree ((2 ^ r - 1) * (1 + x.1.countColumns.length)) (2 ^ r)))
  else if x.1.opcode = opBlake2s then
    (s.1 + s.2.2.1 * vR,
      ((List.range x.1.width).foldl (relInner sh t gamma w x)
        (s.2.1.push (term (.inverse x.1.opcode) (w.take r) (s.2.2.1 * vR * cnt)), s.2.2.1 * gamma)).1,
      ((List.range x.1.width).foldl (relInner sh t gamma w x)
        (s.2.1.push (term (.inverse x.1.opcode) (w.take r) (s.2.2.1 * vR * cnt)), s.2.2.1 * gamma)).2,
      max (max s.2.2.2 (degree ((2 ^ r - 1) * (1 + x.1.countColumns.length)) (2 ^ r)))
        (degree (r * (2 ^ r / 2)) (2 ^ r)))
  else
    (s.1 + s.2.2.1 * vR,
      s.2.1.push (term (.inverse x.1.opcode) (w.take r) (s.2.2.1 * vR * cnt)),
      s.2.2.1 * gamma,
      max s.2.2.2 (degree ((2 ^ r - 1) * (1 + x.1.countColumns.length)) (2 ^ r)))

/-- The public lines' step. -/
def relPublic (sh : Shape) (t gamma : E) (w : List E) (b : E × Array Term × E) (a : (E × E) × ℕ) :
    E × Array Term × E :=
  (b.1 + b.2.2 * vanishingRatio w 1 sh.constraintVars * (a.1.1 + t * (a.1.1 + a.1.2)),
    b.2.1.push (term (.memory a.2) (w.take sh.logMemory) (b.2.2 * vanishingRatio w 1 sh.constraintVars)),
    b.2.2 * gamma)

/-- **`constraintRelation` as folds** of `relBody` over the tables and `relPublic` over the lines. -/
theorem constraintRelation_eq (sh : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E) :
    constraintRelation sh parts pw gamma t cv w =
      let s := (tables.zip parts).foldl (relBody sh t gamma w) (0, #[], 1, 0)
      let p := ([(pw.getD 0 0, pw.getD 2 0), (pw.getD 1 0, pw.getD 3 0), ((0 : E), (0 : E))].zip
        (List.range 3)).foldl (relPublic sh t gamma w) (s.1, s.2.1, s.2.2.1)
      (⟨p.2.1.toList, cv * w.getD sh.constraintVars 0 + p.1⟩, max s.2.2.2 (degree (2 ^ sh.logMemory) 3)) := by
  unfold constraintRelation
  simp only [Id.run, List.forIn_pure_yield_eq_foldl]
  rw [forIn_id_yield _ _ _ (fun x s ↦ relBody sh t gamma w s x)]
  · rfl
  · intro x _ s
    by_cases hJ : x.1.opcode = opJump
    · have hB : ¬ x.1.opcode = opBlake2s := by rw [hJ]; decide
      simp only [Domain.ite_pos_of hJ, Domain.ite_neg_of hB, relBody]
    · by_cases hB : x.1.opcode = opBlake2s
      · simp only [Domain.ite_neg_of hJ, Domain.ite_pos_of hB, relBody]
        rw [forIn_id_yield _ _ _ (fun c s ↦ relInner sh t gamma w x s c)]
        · rfl
        · intro c _ s'
          unfold relInner
          cases qflockSlot (x.1.columns.getD c "") <;> rfl
      · simp only [Domain.ite_neg_of hJ, Domain.ite_neg_of hB, relBody]



/-! ### The loop against the items -/

/-- **What the constraint relation needs of a table at `t`**: its sent values are its columns' polynomials at `t`,
and every term it states evaluates to its column's polynomial at `t` (on `C1`'s stack); the lift is the
verifier's ratio. Heights as the verifier reads them, `shape.heights.getD`. -/
structure TableAt (tr : Trace) (t : E) (w : List E) (ev : Term → E) (x : Table × TablePart) : Prop where
  mem : x.1 ∈ tables
  sent : ∀ i ∈ sentColumns x.1, x.2.sent.getD i none = some (pEval t ((tablePolys tr x.1.opcode).getD i 0))
  col : ∀ c k, c < x.1.width →
    ev (term (.table x.1.opcode c) (w.take (tr.shape.heights.getD x.1.opcode 0)) k) =
      k * pEval t ((tablePolys tr x.1.opcode).getD c 0)
  inv : ∀ k, ev (term (.inverse x.1.opcode) (w.take (tr.shape.heights.getD x.1.opcode 0)) k) =
    k * pEval t (colPolyK (tr.shape.heights.getD x.1.opcode 0) (inverseColumn tr x.1.opcode))
  slot : ∀ c slot k, c < x.1.width → qflockSlot (x.1.columns.getD c "") = some slot →
    ev (term (.qflockSlot slot) (coordinatesAt t (coordinateFunctionals (tr.shape.heights.getD x.1.opcode 0))) k) =
      k * pEval t (mleP (Array.ofFn (n := 2 ^ tr.shape.heights.getD x.1.opcode 0) fun u ↦
          pC (ofK (tr.qflock.getD (slot + 256 * u.val) 0)))
        ((List.range (tr.shape.heights.getD x.1.opcode 0)).map
          (coordinateP (coordinateFunctionals (tr.shape.heights.getD x.1.opcode 0)))))
  lift : vanishingRatio w (tr.shape.heights.getD x.1.opcode 0) tr.shape.constraintVars =
    pEval t (liftP (tr.shape.heights.getD x.1.opcode 0) tr.shape.constraintVars)

theorem sent_value {tr : Trace} {t : E} {w : List E} {ev : Term → E} {x : Table × TablePart}
    (hx : TableAt tr t w ev x) {i : ℕ} (hi : i ∈ sentColumns x.1) :
    (x.2.sent.getD i none).getD 0 = pEval t ((tablePolys tr x.1.opcode).getD i 0) := by
  rw [hx.sent i hi]
  rfl

theorem cnt_value {tr : Trace} {t : E} {w : List E} {ev : Term → E} {x : Table × TablePart}
    (hx : TableAt tr t w ev x) :
    x.1.countColumns.foldl (fun acc c ↦ acc * (x.2.sent.getD c none).getD 0) 1 =
      (x.1.countColumns.map fun c ↦ pEval t ((tablePolys tr x.1.opcode).getD c 0)).prod := by
  rw [foldl_mul_prod, one_mul]
  congr 1
  exact List.map_congr_left fun c hc ↦ sent_value hx (List.mem_append_left _ hc)

theorem pEval_counter (tr : Trace) (t : E) (table : Table) :
    pEval t (counterPoly tr table) =
      pEval t (colPolyK (tr.shape.heights.getD table.opcode 0) (inverseColumn tr table.opcode)) *
        (table.countColumns.map fun c ↦ pEval t ((tablePolys tr table.opcode).getD c 0)).prod + 1 := by
  unfold counterPoly
  rw [pE_add, pE_foldl_mul, pE_one]
  rfl

/-- **BLAKE2S's inner loop against the copies' items.** -/
theorem relInner_spec (tr : Trace) (gamma t : E) (w : List E) (ev : Term → E) (x : Table × TablePart)
    (hx : TableAt tr t w ev x) (K : E) :
    ∀ (cs : List ℕ), (∀ c ∈ cs, c < x.1.width) → ∀ (s : Array Term × E),
      ((((cs.foldl (relInner tr.shape t gamma w x) s).1.toList.map ev).sum + K,
          (cs.foldl (relInner tr.shape t gamma w x) s).2)) =
        evalItems t gamma (cs.filterMap fun c ↦ (qflockSlot (x.1.columns.getD c "")).map fun slot ↦
            (copyPoly tr x.1 c slot, liftP (tr.height x.1.opcode) tr.shape.constraintVars))
          ((s.1.toList.map ev).sum + K, s.2)
  | [], _, s => rfl
  | c :: cs, hcs, s => by
    have hc : c < x.1.width := hcs c (by simp)
    have hrest : ∀ c ∈ cs, c < x.1.width := fun c' h ↦ hcs c' (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons, List.filterMap_cons]
    cases hq : qflockSlot (x.1.columns.getD c "") with
    | none =>
      have h1 : relInner tr.shape t gamma w x s c = s := by unfold relInner; rw [hq]
      rw [h1]
      exact relInner_spec tr gamma t w ev x hx K cs hrest s
    | some slot =>
      have h1 : relInner tr.shape t gamma w x s c =
          ((s.1.push (term (.table x.1.opcode c) (w.take (tr.shape.heights.getD x.1.opcode 0))
              (s.2 * vanishingRatio w (tr.shape.heights.getD x.1.opcode 0) tr.shape.constraintVars))).push
            (term (.qflockSlot slot) (coordinatesAt t (coordinateFunctionals (tr.shape.heights.getD x.1.opcode 0)))
              (s.2 * vanishingRatio w (tr.shape.heights.getD x.1.opcode 0) tr.shape.constraintVars)),
            s.2 * gamma) := by
        unfold relInner
        rw [hq]
      rw [h1, relInner_spec tr gamma t w ev x hx K cs hrest, Option.map_some, evalItems_cons]
      simp only [sum_push]
      rw [hx.col c _ hc, hx.slot c slot _ hc hq, hx.lift]
      unfold copyPoly Trace.height
      rw [pE_mul, pE_add]
      congr 2
      ring

/-- **One table of the verifier's loop against its items**: the terms' values plus the known part, and the power,
follow the items' fold at `t`; the degree is `degStep`'s. -/
theorem relBody_spec (tr : Trace) (gamma t : E) (w : List E) (ev : Term → E) (x : Table × TablePart)
    (hx : TableAt tr t w ev x) (s : E × Array Term × E × ℕ) :
    ((((relBody tr.shape t gamma w s x).2.1.toList.map ev).sum + (relBody tr.shape t gamma w s x).1,
      (relBody tr.shape t gamma w s x).2.2.1) =
      evalItems t gamma (tableItems tr x.1) ((s.2.1.toList.map ev).sum + s.1, s.2.2.1)) ∧
    (relBody tr.shape t gamma w s x).2.2.2 = degStep tr.shape s.2.2.2 x.1 := by
  obtain ⟨ht, hget⟩ := mem_tables hx.mem
  have hcnt := cnt_value hx
  by_cases hJ : x.1.opcode = opJump
  · have hB : ¬ x.1.opcode = opBlake2s := by rw [hJ]; decide
    have hx1 : x.1 = tables.getD opJump default := by rw [← hJ, hget]
    have hb : colIdx x.1.columns "b" ∈ sentColumns x.1 := by rw [hx1]; decide +kernel
    have hv : colIdx x.1.columns "v_cond" ∈ sentColumns x.1 := by rw [hx1]; decide +kernel
    have hw : colIdx x.1.columns "w" < x.1.width := by rw [hx1]; decide +kernel
    refine ⟨?_, ?_⟩
    · simp only [relBody, Domain.ite_pos_of hJ, tableItems, Domain.ite_neg_of hB, List.append_nil,
        List.cons_append, List.nil_append, evalItems_cons, evalItems_nil, sum_push]
      unfold Trace.height
      rw [hx.col _ _ hw, hx.inv, hcnt, sent_value hx hb, sent_value hx hv]
      simp only [pE_mul, pE_add, pE_one, pEval_counter, colP]
      rw [← hx.lift]
      refine Prod.ext ?_ rfl
      dsimp only
      ring
    · simp only [relBody, degStep, Domain.ite_pos_of hJ, Domain.ite_neg_of hB]
  · by_cases hB : x.1.opcode = opBlake2s
    · refine ⟨?_, ?_⟩
      · simp only [relBody, Domain.ite_neg_of hJ, Domain.ite_pos_of hB, tableItems, List.nil_append,
          List.cons_append, evalItems_cons]
        rw [relInner_spec tr gamma t w ev x hx _ (List.range x.1.width) (fun c hc ↦ List.mem_range.mp hc)]
        simp only [sum_push]
        unfold Trace.height
        rw [hx.inv, hcnt, pE_mul, pEval_counter, ← hx.lift]
        apply congrArg (evalItems t gamma _)
        refine Prod.ext ?_ rfl
        dsimp only
        ring
      · simp only [relBody, degStep, Domain.ite_neg_of hJ, Domain.ite_pos_of hB]
    · refine ⟨?_, ?_⟩
      · simp only [relBody, Domain.ite_neg_of hJ, Domain.ite_neg_of hB, tableItems, List.nil_append,
          List.append_nil, evalItems_cons, evalItems_nil, sum_push]
        unfold Trace.height
        rw [hx.inv, hcnt, pE_mul, pEval_counter, ← hx.lift]
        refine Prod.ext ?_ rfl
        dsimp only
        ring
      · simp only [relBody, degStep, Domain.ite_neg_of hJ, Domain.ite_neg_of hB]

/-- **The verifier's loop over the tables against the tables' items.** -/
theorem relFold_spec (tr : Trace) (gamma t : E) (w : List E) (ev : Term → E) :
    ∀ (l : List (Table × TablePart)), (∀ x ∈ l, TableAt tr t w ev x) → ∀ (s : E × Array Term × E × ℕ),
      (((l.foldl (relBody tr.shape t gamma w) s).2.1.toList.map ev).sum + (l.foldl (relBody tr.shape t gamma w) s).1,
        (l.foldl (relBody tr.shape t gamma w) s).2.2.1) =
        evalItems t gamma (l.flatMap fun x ↦ tableItems tr x.1) ((s.2.1.toList.map ev).sum + s.1, s.2.2.1) ∧
      (l.foldl (relBody tr.shape t gamma w) s).2.2.2 = (l.map Prod.fst).foldl (degStep tr.shape) s.2.2.2
  | [], _, s => ⟨rfl, rfl⟩
  | x :: l, hl, s => by
    obtain ⟨h1, h2⟩ := relBody_spec tr gamma t w ev x (hl x (by simp)) s
    obtain ⟨h3, h4⟩ := relFold_spec tr gamma t w ev l (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy))
      (relBody tr.shape t gamma w s x)
    rw [List.foldl_cons, List.flatMap_cons, evalItems_append, List.map_cons, List.foldl_cons, ← h1, ← h2]
    exact ⟨h3, h4⟩

/-- **The public lines' loop against their items.** -/
theorem relPublic_spec (tr : Trace) (gamma t : E) (w : List E) (ev : Term → E) (words : List E)
    (hmem : ∀ k c, k < 3 → ev (term (.memory k) (w.take tr.shape.logMemory) c) =
      c * pEval t (colPolyK tr.shape.logMemory (tr.memory.getD k #[])))
    (hlift : vanishingRatio w 1 tr.shape.constraintVars = pEval t (liftP 1 tr.shape.constraintVars))
    (s : E × Array Term × E) :
    let p := ([(words.getD 0 0, words.getD 2 0), (words.getD 1 0, words.getD 3 0), ((0 : E), (0 : E))].zip
        (List.range 3)).foldl (relPublic tr.shape t gamma w) s
    ((p.2.1.toList.map ev).sum + p.1, p.2.2) =
      evalItems t gamma (publicItems tr words) ((s.2.1.toList.map ev).sum + s.1, s.2.2) := by
  simp only [publicItems, show List.range 3 = [0, 1, 2] from rfl, List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, evalItems_cons, evalItems_nil, relPublic,
    sum_push]
  rw [hmem 0 _ (by norm_num), hmem 1 _ (by norm_num), hmem 2 _ (by norm_num), hlift]
  simp only [pE_mul, pE_add, pE_C, pE_X]
  refine Prod.ext ?_ rfl
  dsimp only
  ring

/-- **The constraint relation at `t` evaluates to the numerator**: if every table's part and terms are read at
`t` (`TableAt`) and the memory's terms too, the relation's terms' values plus its value are
`Q_W(t) w_{r_W}(t) + N(t)` (`cv` the sent `Q_W(t)`), and its degree is `Shape.constraintDegree`. -/
theorem constraintRelation_eval (tr : Trace) (gamma t cv : E) (w : List E) (ev : Term → E)
    (parts : List TablePart) (words : List E) (hlen : tables.length ≤ parts.length)
    (hparts : ∀ x ∈ tables.zip parts, TableAt tr t w ev x)
    (hmem : ∀ k c, k < 3 → ev (term (.memory k) (w.take tr.shape.logMemory) c) =
      c * pEval t (colPolyK tr.shape.logMemory (tr.memory.getD k #[])))
    (hlift : vanishingRatio w 1 tr.shape.constraintVars = pEval t (liftP 1 tr.shape.constraintVars)) :
    ((constraintRelation tr.shape parts words gamma t cv w).1.terms.map ev).sum +
        (constraintRelation tr.shape parts words gamma t cv w).1.value =
      cv * w.getD tr.shape.constraintVars 0 + pEval t (constraintNumerator tr gamma words) ∧
    (constraintRelation tr.shape parts words gamma t cv w).2 = tr.shape.constraintDegree := by
  rw [constraintRelation_eq]
  dsimp only
  obtain ⟨h1, h2⟩ := relFold_spec tr gamma t w ev (tables.zip parts) hparts (0, #[], 1, 0)
  have hfst : (tables.zip parts).map Prod.fst = tables := List.map_fst_zip hlen
  have hflat : ((tables.zip parts).flatMap fun x ↦ tableItems tr x.1) = tables.flatMap (tableItems tr) := by
    calc ((tables.zip parts).flatMap fun x ↦ tableItems tr x.1)
        = ((tables.zip parts).map Prod.fst).flatMap (tableItems tr) := by rw [List.flatMap_map]
      _ = tables.flatMap (tableItems tr) := by rw [hfst]
  rw [hflat] at h1
  have hz : (((0 : E), (#[] : Array Term), (1 : E), (0 : ℕ)).2.1.toList.map ev).sum +
      ((0 : E), (#[] : Array Term), (1 : E), (0 : ℕ)).1 = 0 := by simp
  rw [hz] at h1
  rw [hfst] at h2
  have h3 := relPublic_spec tr gamma t w ev words hmem hlift
    (((tables.zip parts).foldl (relBody tr.shape t gamma w) (0, #[], 1, 0)).1,
      ((tables.zip parts).foldl (relBody tr.shape t gamma w) (0, #[], 1, 0)).2.1,
      ((tables.zip parts).foldl (relBody tr.shape t gamma w) (0, #[], 1, 0)).2.2.1)
  dsimp only at h3
  rw [h1] at h3
  refine ⟨?_, ?_⟩
  · rw [pEval_constraintNumerator, numItems, evalItems_append, ← h3]
    simp
    ring
  · rw [h2, constraintDegree_eq]


end UniComplete.AlgC

/-- info: 'UniComplete.AlgC.constraintRelation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.constraintRelation_eq

/-- info: 'UniComplete.AlgC.constraintRelation_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.constraintRelation_eval
