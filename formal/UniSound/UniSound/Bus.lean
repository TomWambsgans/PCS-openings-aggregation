-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The bus is `formal/Heap`'s.
import UniSound.Piop

/-!
# Round `0`: the bus and the constraints' batching

After `C1`'s root the verifier draws `α ∈ E^4`, `β` (the bus) and `γ` (the constraints' batching).
The state after them (`BusModel.MainOK`): **the heap holds** at `(α, β)` (`Heap.HeapData.Sat`: some
heap values meet the tree, leaf and root identities, `formal/Heap`) for the heap the verifier reads
off `C1` (`hd`), and **the batched constraints vanish** on every row (`Σ_i γ^i C_i(x) = 0`, the
constraint quotient's numerator on the domain, `cvec`).

**`BusModel.mainSound`**: round `0` turns `¬ MainHolds` (`ConstraintsVanish ∧ Balanced ∧
CountsNonzero ∧ PublicLinesHold` of `C1`'s Lv42 stack) into `MainOK` with probability at most
`busError N + (ncv − 1) / |E|`: if every constraint vanishes (so the limb copies equal `q_flock`'s
slots and the heap realizes Lv42's bus, `realizes`), the bus is unbalanced and `Heap`'s
`card_sat_not_balanced_le` bounds the `(α, β)` that make the heap hold (`4N/|E|`); otherwise some
row's constraint vector is nonzero and at most `ncv − 1` values of `γ` cancel it
(`card_powComb_le`).

**`BusModel.rel_of`**: with Flock's predicate on `C1`'s `q_flock` (`aux_of_flock`), `MainHolds` is
the relation.

The model's fields are the bridges left (`formal/Heap`'s report: the verifier's leaves read as
Lv42's flushes with the copies, the padded rows' leaves `1`): `hd` well formed and realizing Lv42's
bus when the copies hold, the constraint vectors' vanishing giving the four clauses and the copies,
Flock's column read off `C1` as Lv42's region.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

/-- **The relation but for Flock's region**, of `C1`'s candidate's Lv42 stack. -/
def MainHoldsOf (D : Deployment) (s : USt) (c : Stk) : Prop :=
  (D.inst s.2).ConstraintsVanish (lv42Stack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).Balanced (lv42Stack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).CountsNonzero (lv42Stack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).PublicLinesHold (publicInputOf s.1.toList) (lv42Stack D.prog (D.sizes s.2) D.shape c)

/-- **The bus and constraint model of round `0`.** -/
structure BusModel (D : Deployment) (κ : ℕ) where
  /-- The heap the verifier reads off `C1` (its leaves from `C1`'s columns, the limbs' copies). -/
  hd : USt → Stk → Heap.HeapData
  wf : ∀ (s : USt) (c : Stk), (hd s c).WellFormed
  /-- `C1`'s limb copies equal `q_flock`'s slots. -/
  Copies : USt → Stk → Prop
  /-- With the copies, the heap realizes Lv42's bus of `C1`'s Lv42 stack. -/
  realizes : ∀ (s : USt) (c : Stk), Copies s c →
    Heap.Realizes (I := D.inst s.2) (lv42Stack D.prog (D.sizes s.2) D.shape c) (hd s c)
  /-- A bound on both sides' tuple counts. -/
  N : ℕ
  hpush : ∀ rows, Heap.busCount (D.inst rows) .push ≤ N
  hpull : ∀ rows, Heap.busCount (D.inst rows) .pull ≤ N
  /-- The rows the constraints are checked on, and each row's constraint vector. -/
  nrows : ℕ
  cvec : USt → Stk → ℕ → List E
  ncv : ℕ
  cvec_len : ∀ (s : USt) (c : Stk) (x : ℕ), (cvec s c x).length ≤ ncv
  cvec_ok : ∀ (s : USt) (c : Stk), (∀ x < nrows, ∀ v ∈ cvec s c x, v = 0) →
    (D.inst s.2).ConstraintsVanish (lv42Stack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).CountsNonzero (lv42Stack D.prog (D.sizes s.2) D.shape c) ∧
    (D.inst s.2).PublicLinesHold (publicInputOf s.1.toList)
      (lv42Stack D.prog (D.sizes s.2) D.shape c) ∧ Copies s c
  /-- `C1`'s column `q_flock`. -/
  qf : Stk → LeanVM.Protocol.Column (8 + κ)
  /-- Flock's predicate on `q_flock` is Lv42's Flock region's (`aux`). -/
  aux_of_flock : ∀ (s : USt) (c : Stk), FlockHolds κ (qf c) →
    (D.inst s.2).aux (lv42Stack D.prog (D.sizes s.2) D.shape c)

namespace BusModel

variable {D : Deployment} {κ : ℕ} (B : BusModel D κ)

/-- **The state after round `0`**: the heap holds at `(α, β)`, the batched constraints vanish at
`γ`. -/
def MainOK (s : USt) (c : Stk) (ch : List E) : Prop :=
  (B.hd s c).Sat (fun i => ch.getD i.val 0) (ch.getD 4 0) ∧
    ∀ x < B.nrows, powComb (B.cvec s c x) (ch.getD 5 0) = 0

/-- **Round `0`'s error.** -/
noncomputable def errMain : ℝ≥0∞ :=
  Heap.busError B.N + ((B.ncv - 1 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

theorem rel_of (s : USt) (c : Stk) (h : MainHoldsOf D s c) (hf : FlockHolds κ (B.qf c)) :
    Rel D s c :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, B.aux_of_flock s c hf⟩

/-- Five challenges are `(α, β)`. -/
theorem card_fin_five (P : (Fin 4 → E) → E → Prop) [∀ a b, Decidable (P a b)] :
    (univ.filter fun v : Fin (4 + 1) → E =>
      P (fun i => (List.ofFn v).getD i.val 0) ((List.ofFn v).getD 4 0)).card =
      (univ.filter fun ab : (Fin 4 → E) × E => P ab.1 ab.2).card := by
  refine Finset.card_bij (fun v _ => (fun i => v i.castSucc, v 4)) (fun v hv => ?_)
    (fun v _ w _ h => ?_) (fun ab hab => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hv ⊢
    have h1 : (fun i : Fin 4 => (List.ofFn v).getD i.val 0) = fun i => v i.castSucc := by
      funext i
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      rfl
    have h2 : (List.ofFn v).getD 4 0 = v 4 := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      rfl
    rw [h1, h2] at hv
    exact hv
  · simp only [Prod.mk.injEq] at h
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h.2
    · exact congrFun h.1 j
  · refine ⟨Fin.snoc ab.1 ab.2, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hab ⊢
      have h1 : (fun i : Fin 4 => (List.ofFn (Fin.snoc ab.1 ab.2 : Fin (4 + 1) → E)).getD i.val 0) =
          ab.1 := by
        funext i
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        exact Fin.snoc_castSucc (α := fun _ => E) ab.2 ab.1 i
      have h2 : (List.ofFn (Fin.snoc ab.1 ab.2 : Fin (4 + 1) → E)).getD 4 0 = ab.2 := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        exact Fin.snoc_last (α := fun _ => E) ab.2 ab.1
      rw [h1, h2]
      exact hab
    · refine Prod.ext (funext fun i => ?_) ?_
      · exact Fin.snoc_castSucc (α := fun _ => E) ab.2 ab.1 i
      · exact Fin.snoc_last (α := fun _ => E) ab.2 ab.1

/-- **Round `0` is sound**: the bus (`4N/|E|`) and the constraints' batching. -/
theorem mainSound (s : USt) (c : Stk) :
    Pr{let ch ← Compose.draws E 6}[¬ MainHoldsOf D s c ∧ B.MainOK s c ch] ≤ B.errMain := by
  classical
  unfold errMain
  by_cases hall : ∀ x < B.nrows, ∀ v ∈ B.cvec s c x, v = 0
  · obtain ⟨hcv, hcn, hpl, hcp⟩ := B.cvec_ok s c hall
    have hR := B.realizes s c hcp
    -- The bus: the event is on `(α, β)`.
    have hev : ∀ ch : List E, (¬ MainHoldsOf D s c ∧ B.MainOK s c ch) →
        ((B.hd s c).Sat (fun i => (ch.take 5).getD i.val 0) ((ch.take 5).getD 4 0) ∧
          ¬ (D.inst s.2).Balanced (lv42Stack D.prog (D.sizes s.2) D.shape c)) ∨ False := by
      intro ch ⟨hn, hok⟩
      refine Or.inl ⟨?_, fun hb => hn ⟨hcv, hb, hcn, hpl⟩⟩
      have h1 : (fun i : Fin 4 => (ch.take 5).getD i.val 0) = fun i => ch.getD i.val 0 := by
        funext i
        simp [List.getD_eq_getElem?_getD, show i.val < 5 by omega]
      have h2 : (ch.take 5).getD 4 0 = ch.getD 4 0 := by
        simp [List.getD_eq_getElem?_getD]
      rw [h1, h2]
      exact hok.1
    have hb := prEvent_draws_append_le 5 1 (fun l => (B.hd s c).Sat (fun i => l.getD i.val 0)
      (l.getD 4 0) ∧ ¬ (D.inst s.2).Balanced (lv42Stack D.prog (D.sizes s.2) D.shape c))
      (fun _ => False)
    refine (prEvent_mono _ _ _ hev).trans (hb.trans ?_)
    rw [prEvent_eq_zero_of_forall_not _ _ (fun _ h => h), add_zero]
    refine le_trans ?_ le_self_add
    have hc := Heap.card_sat_not_balanced_le (I := D.inst s.2) (B.wf s c) hR (B.hpush s.2) (B.hpull s.2)
    refine (prEvent_draws_le_of_card 4 _ (4 * B.N) ?_).trans (le_of_eq rfl)
    have h5 := card_fin_five (fun a b => (B.hd s c).Sat a b ∧
      ¬ (D.inst s.2).Balanced (lv42Stack D.prog (D.sizes s.2) D.shape c))
    exact (le_of_eq h5).trans hc
  · obtain ⟨x₀, hx₀, v, hv, hv0⟩ : ∃ x < B.nrows, ∃ v ∈ B.cvec s c x, v ≠ 0 := by
      by_contra hne
      exact hall fun x hx v hv => by
        by_contra h0
        exact hne ⟨x, hx, v, hv, h0⟩
    have hev : ∀ ch : List E, (¬ MainHoldsOf D s c ∧ B.MainOK s c ch) →
        False ∨ powComb (B.cvec s c x₀) ((ch.drop 5).headD 0) = 0 := by
      intro ch ⟨_, hok⟩
      refine Or.inr ?_
      have h1 : (ch.drop 5).headD 0 = ch.getD 5 0 := by
        simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
      rw [h1]
      exact hok.2 x₀ hx₀
    have hb := prEvent_draws_append_le 5 1 (fun _ => False)
      (fun l => powComb (B.cvec s c x₀) (l.headD 0) = 0)
    refine (prEvent_mono _ _ _ hev).trans (hb.trans ?_)
    rw [prEvent_eq_zero_of_forall_not _ _ (fun _ h => h), zero_add]
    refine le_trans ?_ le_add_self
    refine prEvent_draws_le_of_card 0 _ _ ?_
    rw [pow_zero, mul_one]
    convert (card_powComb_le _ ⟨v, hv, hv0⟩).trans (Nat.sub_le_sub_right (B.cvec_len s c x₀) 1)
      using 1
    convert card_filter_fin_one (fun ρ => powComb (B.cvec s c x₀) ρ = 0) using 2

/-- Round `0`'s error is at most `2^32 / |E|` when `4 N + ncv ≤ 2^32`. -/
theorem errMain_le (h : 4 * B.N + B.ncv ≤ 2 ^ 32) :
    B.errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  unfold errMain Heap.busError
  rw [ENNReal.div_add_div_same, ← Nat.cast_add]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _

end BusModel

/-- **The identity model but for round `0`**, over the bus model `B` (its `MainOK`): the fields of
`UniIds` from the identities as polynomials on. -/
structure UniIdsRest (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (B : BusModel D κ) where
  nV : ℕ
  V : ℕ
  polys : USt → Stk → List E → Stk → List (Polynomial E)
  degSum : ℕ
  deg_le : ∀ s c1 ch c2, ((polys s c1 ch c2).map Polynomial.natDegree).sum ≤ degSum
  main_of_polys : ∀ s c1 ch c2, (∀ P ∈ polys s c1 ch c2, P = 0) → B.MainOK s c1 ch
  diffs : USt → Stk → List E → Done → Stk → E → List E → List (List E)
  nRel : ℕ
  diffs_len : ∀ s c1 ch fd c2 t vals, ∀ d ∈ diffs s c1 ch fd c2 t vals, d.length ≤ nRel
  diffs_count : ∀ s c1 ch fd c2 t vals, (diffs s c1 ch fd c2 t vals).length ≤ 4
  diffs_eval : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    ∀ P ∈ polys s c1 ch c2, P.eval t = 0
  diffs_flock : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    FlockEndHolds (B.qf c1) (Fl.prog.out fd [])
  diffs_pending : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    PendingHolds (Fl.prog.out fd []).2.2
  prod : USt → Stk → List E → Done → Stk → E → List E → E → E → ProdSum
  prod_vars : ∀ s c1 ch fd c2 t vals ρ l, (prod s c1 ch fd c2 t vals ρ l).vars = V
  target : USt → Stk → List E → Done → Stk → E → List E → E → E → E
  batch_start : ∀ s c1 ch fd c2 t vals ρ l,
    (prod s c1 ch fd c2 t vals ρ l).T [] + target s c1 ch fd c2 t vals ρ l =
      powComb ((diffs s c1 ch fd c2 t vals).map fun d => powComb d ρ) l

/-- **The identity model from the bus model**: round `0`'s fields proved (`mainSound`,
`rel_of`). -/
noncomputable def UniIds.ofBus {D : Deployment} {κ : ℕ} (Fl : FlockSound κ) (B : BusModel D κ)
    (J : UniIdsRest D Fl B) : UniIds D Fl where
  nV := J.nV
  V := J.V
  qf := B.qf
  MainHolds := MainHoldsOf D
  rel_of := B.rel_of
  MainOK := B.MainOK
  errMain := B.errMain
  mainSound := B.mainSound
  polys := J.polys
  degSum := J.degSum
  deg_le := J.deg_le
  main_of_polys := J.main_of_polys
  diffs := J.diffs
  nRel := J.nRel
  diffs_len := J.diffs_len
  diffs_count := J.diffs_count
  diffs_eval := J.diffs_eval
  diffs_flock := J.diffs_flock
  diffs_pending := J.diffs_pending
  prod := J.prod
  prod_vars := J.prod_vars
  target := J.target
  batch_start := J.batch_start

end UniSound
