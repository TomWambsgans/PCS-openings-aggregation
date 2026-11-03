-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The bus is `formal/Heap`'s.
import UniSound.Bus
import FlockSound.Kronecker
import UniStatement.Rec

/-!
# Round `0` of π1-rec3: the bus with `α = (c, c², c⁴, c⁸)`

π1-rec3 (`crates/leanvm_rec/SPEC-REC.md` §1.4; `crates/leanvm_flock_gas/src/transcript.rs`,
`FsShape::draw`, `squares`; transcribed as `UniStatement.drawRun`, `UniStatement.squares`) draws
round `0`'s challenges as three, `[c, β, γ]`, and reads the bus's tuple weights as the squares
`α = (c, c², c⁴, c⁸)` of the one `c` (`β`, `γ` stay independent). The main line's round-`0` state
`BusModel.MainOK` reads six challenges, `α = ch[0..3]`, `β = ch[4]`, `γ = ch[5]`; `expandCh`
makes the six of the three.

* **The fingerprint at the squares is a polynomial in `c`** of degree at most `15`:
  `fingerprint (sqPt 4 c) t = (fpPoly t).eval c`, `fpPoly t = kron 4 (tupleTable t)`, the tuple read
  as a table on `Cube 4` (slot `i` at the cube point of its bits, low first: `slotEquiv`, CompPoly's
  `lagrangeBasis` order, `fingerprint_eq_mle`). Distinct tuples give distinct polynomials
  (`fpPoly_injective`, by `FlockSound.kron_injective`).
* **The side's product as a polynomial in `(β, c)`**: `sidePoly P = Π_{t ∈ P} (X − C (fpPoly t))`
  in `E[X][X]` (outer variable `β`); its roots are `P.map fpPoly`, so it determines `P`
  (`sidePoly_injective`); its degree in `β` is `|P|`, each coefficient's degree in `c` at most
  `15 |P|`.
* **`card_sideProduct_sq_collision_le`** (leanerVM's Theorem 5.1, `card_sideProduct_collision_le`,
  with `α` on the curve of squares): `P ≠ Q` of at most `N` tuples each have equal products at no
  more than `16·N·|E|` of the `|E|²` pairs `(c, β)`. A two-variable Schwartz–Zippel by hand: for
  each `c`, the difference is a nonzero polynomial in `β` of degree at most `N` (at most `N` roots),
  or `c` is a root of one fixed nonzero coefficient of degree at most `15 N`.
* **The heap** (`card_sat_le_sq`, `card_sat_not_balanced_le_sq`): `Heap.HeapData.card_sat_le` and
  `Heap.card_sat_not_balanced_le` with `α = sqPt 4 c`, `16·N·|E|` pairs `(c, β)`.
* **`BusModel.mainSoundSq`**: `BusModel.mainSound` with the three challenges, error
  `errMainSq = 16 N / |E| + (ncv − 1) / |E|`; `errMainSq_le`: at most `2^35 / |E|` when
  `16 N + ncv ≤ 2^35`.
* `squares_eq_ofFn`, `expandCh_take`: the transcription's `squares c 4` is `sqPt 4 c`, and is
  `expandCh`'s first four challenges.

Decisions: `expandCh` is the brief's literal list `[c, c², c⁴, c⁸, β, γ]` (with the defaults `0`
of `List.getD` for a short list); the bus model `B` and its fields are the main line's unchanged,
only the challenges' shape changes. Nothing here transcribes a source.
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Protocol UniStatement Finset Polynomial CompPoly
open scoped ENNReal

/-! ## A tuple's slots are the points of `Cube 4` -/

/-- The bits of a slot, low first: bit `i` is coordinate `i` (CompPoly's `lagrangeBasis` order). -/
def slotBits (a : Fin 16) : FlockSound.Cube 4 := fun i ↦ (a : ℕ).testBit i

theorem slotBits_injective : Function.Injective slotBits := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 4
  · exact congrFun h ⟨i, hi⟩
  · have h16 : (16 : ℕ) ≤ 2 ^ i :=
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le a.isLt h16),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b.isLt h16)]

theorem slotBits_bijective : Function.Bijective slotBits :=
  (Fintype.bijective_iff_injective_and_card _).mpr ⟨slotBits_injective, by simp⟩

/-- The slots and the cube points. -/
noncomputable def slotEquiv : Fin 16 ≃ FlockSound.Cube 4 :=
  Equiv.ofBijective slotBits slotBits_bijective

/-- **A tuple as a table on `Cube 4`**: at a cube point, the slot whose bits it is. -/
noncomputable def tupleTable (t : Vector K 16) : FlockSound.Cube 4 → E :=
  fun b ↦ ofK t[slotEquiv.symm b]

/-- **The fingerprint is the table's multilinear extension** (FlockSound's `mle`) at `α`. -/
theorem fingerprint_eq_mle (α : Fin 4 → E) (t : Vector K 16) :
    fingerprint α t = FlockSound.mle (tupleTable t) α := by
  rw [FlockSound.mle, ← Fintype.sum_equiv slotEquiv
    (fun a ↦ tupleTable t (slotEquiv a) * FlockSound.eqP α (slotEquiv a))
    (fun b ↦ tupleTable t b * FlockSound.eqP α b) (fun _ ↦ rfl)]
  simp only [fingerprint, fingerprintWeights, tupleTable, Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [lagrangeBasis_getElem_nat (Vector.ofFn α) (lt_of_lt_of_eq a.isLt (by norm_num)), mul_comm]
  congr 1

theorem tupleTable_injective : Function.Injective tupleTable := by
  intro s t h
  refine Vector.ext fun i hi ↦ ?_
  have := congrFun h (slotEquiv ⟨i, hi⟩)
  simp only [tupleTable, Equiv.symm_apply_apply] at this
  exact ofK_injective this

/-! ## The fingerprint at the squares: a polynomial in `c` -/

/-- **The fingerprint polynomial** of a tuple: `c ↦ fingerprint (sqPt 4 c) t`. -/
noncomputable def fpPoly (t : Vector K 16) : E[X] := FlockSound.kron 4 (tupleTable t)

theorem eval_fpPoly (t : Vector K 16) (c : E) :
    (fpPoly t).eval c = fingerprint (FlockSound.sqPt 4 c) t := by
  rw [fpPoly, FlockSound.eval_kron, fingerprint_eq_mle]

theorem natDegree_fpPoly_le (t : Vector K 16) : (fpPoly t).natDegree ≤ 15 :=
  (FlockSound.natDegree_kron_le 4 _).trans (by norm_num)

/-- **Distinct tuples have distinct fingerprint polynomials.** -/
theorem fpPoly_injective : Function.Injective fpPoly :=
  (FlockSound.kron_injective 4).comp tupleTable_injective

/-! ## A side's product as a polynomial in `(β, c)` -/

/-- **A side's product polynomial**: `Π_{t ∈ P} (X − C (fpPoly t))`, the outer variable `β`, the
coefficients polynomials in `c`. -/
noncomputable def sidePoly (P : Multiset (Vector K 16)) : E[X][X] :=
  ((P.map fpPoly).map fun a ↦ X - C a).prod

/-- **The product polynomial determines the multiset** (its roots). -/
theorem sidePoly_injective {P Q : Multiset (Vector K 16)} (h : sidePoly P = sidePoly Q) : P = Q := by
  have h' := congrArg Polynomial.roots h
  rw [sidePoly, sidePoly, roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h'
  exact Multiset.map_injective fpPoly_injective h'

/-- **The product polynomial at `(β, c)` is the side's product at `(sqPt 4 c, β)`.** -/
theorem eval_sidePoly (P : Multiset (Vector K 16)) (c β : E) :
    ((sidePoly P).map (evalRingHom c)).eval β = sideProduct (FlockSound.sqPt 4 c) β P := by
  rw [sidePoly, Polynomial.map_multiset_prod, eval_multiset_prod, sideProduct, Multiset.map_map,
    Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun t _ ↦ ?_
  simp [eval_fpPoly]

theorem natDegree_sidePoly (P : Multiset (Vector K 16)) : (sidePoly P).natDegree = P.card := by
  rw [sidePoly, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]

/-- The coefficients of `Π (X − C a)` have degree at most `d` times the number of factors when
each `a` has degree at most `d`. -/
theorem natDegree_coeff_prod_X_sub_C_le (d : ℕ) (s : Multiset E[X]) (hs : ∀ a ∈ s, a.natDegree ≤ d)
    (j : ℕ) : ((s.map fun a ↦ X - C a).prod.coeff j).natDegree ≤ d * Multiset.card s := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, coeff_one]
    split_ifs <;> simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    have ih' := ih fun b hb ↦ hs b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, mul_add_one, sub_mul, coeff_sub,
      coeff_C_mul]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rcases j with _ | j
      · rw [coeff_X_mul_zero, natDegree_zero]
        exact Nat.zero_le _
      · rw [coeff_X_mul]
        exact (ih' j).trans (Nat.le_add_right _ _)
    · refine natDegree_mul_le.trans ?_
      have := ih' j
      omega

theorem natDegree_coeff_sidePoly_le (P : Multiset (Vector K 16)) (j : ℕ) :
    ((sidePoly P).coeff j).natDegree ≤ 15 * P.card := by
  have h := natDegree_coeff_prod_X_sub_C_le 15 (P.map fpPoly) (fun a ha ↦ by
    obtain ⟨t, _, rfl⟩ := Multiset.mem_map.mp ha
    exact natDegree_fpPoly_le t) j
  rwa [Multiset.card_map] at h

/-! ## The squares collision -/

open Classical in
/-- **Theorem 5.1 with squares, counting form**: two different multisets of at most `N` tuples
each have equal products at `α = (c, c², c⁴, c⁸)` for no more than `16·N·|E|` of the pairs
`(c, β)`. -/
theorem card_sideProduct_sq_collision_le {P Q : Multiset (Vector K 16)} (hne : P ≠ Q) {N : ℕ}
    (hP : P.card ≤ N) (hQ : Q.card ≤ N) :
    (univ.filter fun cb : E × E ↦ sideProduct (FlockSound.sqPt 4 cb.1) cb.2 P =
      sideProduct (FlockSound.sqPt 4 cb.1) cb.2 Q).card ≤ 16 * N * Fintype.card E := by
  set Δ := sidePoly P - sidePoly Q with hΔ
  have hΔne : Δ ≠ 0 := sub_ne_zero.mpr fun h ↦ hne (sidePoly_injective h)
  obtain ⟨j, hj⟩ : ∃ j, Δ.coeff j ≠ 0 := by
    by_contra h
    push Not at h
    exact hΔne (Polynomial.ext fun j ↦ by rw [h j, coeff_zero])
  have hdeg : Δ.natDegree ≤ N :=
    (natDegree_sub_le _ _).trans (by rw [natDegree_sidePoly, natDegree_sidePoly]; omega)
  have hgdeg : (Δ.coeff j).natDegree ≤ 15 * N := by
    rw [hΔ, coeff_sub]
    have h1 := natDegree_coeff_sidePoly_le P j
    have h2 := natDegree_coeff_sidePoly_le Q j
    exact (natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
  have hfilt : (univ.filter fun cb : E × E ↦ sideProduct (FlockSound.sqPt 4 cb.1) cb.2 P =
      sideProduct (FlockSound.sqPt 4 cb.1) cb.2 Q) =
      univ.filter fun cb : E × E ↦ (Δ.map (evalRingHom cb.1)).eval cb.2 = 0 :=
    Finset.filter_congr fun cb _ ↦ by
      rw [hΔ, Polynomial.map_sub, Polynomial.eval_sub, eval_sidePoly, eval_sidePoly, sub_eq_zero]
  rw [hfilt, Finset.card_filter, Fintype.sum_prod_type]
  simp only [← Finset.card_filter]
  calc ∑ c : E, (univ.filter fun β ↦ (Δ.map (evalRingHom c)).eval β = 0).card
      ≤ ∑ c : E, (if Δ.map (evalRingHom c) = 0 then Fintype.card E else N) :=
        Finset.sum_le_sum fun c _ ↦ by
          split_ifs with h
          · exact card_le_univ _
          · exact (card_roots_le _ h).trans (natDegree_map_le.trans hdeg)
    _ ≤ (univ.filter fun c ↦ (Δ.coeff j).eval c = 0).card * Fintype.card E +
          Fintype.card E * N := by
        rw [Finset.sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul]
        refine add_le_add (Nat.mul_le_mul_right _ (card_le_card fun c hc ↦ ?_))
          (Nat.mul_le_mul_right _ (card_le_univ _))
        simp only [mem_filter, mem_univ, true_and] at hc ⊢
        have := congrArg (fun r ↦ r.coeff j) hc
        simpa [coeff_map] using this
    _ ≤ 15 * N * Fintype.card E + Fintype.card E * N :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ ((card_roots_le _ hj).trans hgdeg)) _
    _ = 16 * N * Fintype.card E := by ring

open Classical in
/-- **Fingerprint soundness with squares, counting form**: two lists of at most `N` tuples that
are not permutations of each other have equal fingerprint products at no more than `16·N·|E|`
pairs `(c, β)`. -/
theorem card_fpProd_eq_le_sq {l₁ l₂ : List (Vector K 16)} (h : ¬ l₁.Perm l₂) {N : ℕ}
    (h₁ : l₁.length ≤ N) (h₂ : l₂.length ≤ N) :
    (univ.filter fun cb : E × E ↦
        Heap.fpProd (Heap.fp (FlockSound.sqPt 4 cb.1) cb.2) l₁ =
          Heap.fpProd (Heap.fp (FlockSound.sqPt 4 cb.1) cb.2) l₂).card ≤
      16 * N * Fintype.card E := by
  have hne : (l₁ : Multiset (Vector K 16)) ≠ l₂ := fun he ↦ h (Multiset.coe_eq_coe.mp he)
  refine le_of_eq_of_le (congrArg Finset.card (Finset.filter_congr fun cb _ ↦ ?_))
    (card_sideProduct_sq_collision_le hne (N := N) (by simpa using h₁) (by simpa using h₂))
  rw [Heap.fpProd_fp_eq_sideProduct, Heap.fpProd_fp_eq_sideProduct]

open Classical in
/-- **The heap's soundness with squares, counting form**: `Heap.HeapData.card_sat_le` at
`α = sqPt 4 c`. -/
theorem card_sat_le_sq {D : Heap.HeapData} (hD : D.WellFormed) (hne : ¬ D.pushes.Perm D.pulls)
    {N : ℕ} (h₁ : D.pushes.length ≤ N) (h₂ : D.pulls.length ≤ N) :
    (univ.filter fun cb : E × E ↦ D.Sat (FlockSound.sqPt 4 cb.1) cb.2).card ≤
      16 * N * Fintype.card E :=
  (card_le_card fun cb hcb ↦ by
      rw [mem_filter] at hcb ⊢
      exact ⟨hcb.1, D.fpProd_eq_of_sat hD hcb.2⟩).trans
    (card_fpProd_eq_le_sq hne h₁ h₂)

open Classical in
/-- **The bus's soundness with squares, counting form**: `Heap.card_sat_not_balanced_le` at
`α = sqPt 4 c`: for a well-formed layout realizing the bus of `q`, at most `16·N·|E|` pairs
`(c, β)` make the heap hold while `q` is not balanced. -/
theorem card_sat_not_balanced_le_sq {I : Lv42.Protocol.M3Instance}
    {q : LeanVM.Protocol.Column I.μ} {D : Heap.HeapData} (hD : D.WellFormed)
    (hR : Heap.Realizes q D) {N : ℕ} (hpush : Heap.busCount I .push ≤ N)
    (hpull : Heap.busCount I .pull ≤ N) :
    (univ.filter fun cb : E × E ↦ D.Sat (FlockSound.sqPt 4 cb.1) cb.2 ∧ ¬ I.Balanced q).card ≤
      16 * N * Fintype.card E := by
  by_cases hb : I.Balanced q
  · simp [hb]
  · refine (card_le_card fun cb hcb ↦ ?_).trans (card_sat_le_sq hD
      (fun hp ↦ hb (hR.balanced_iff.mpr hp))
      (by rw [hR.push.length_eq, Heap.length_tuples]; exact hpush)
      (by rw [hR.pull.length_eq, Heap.length_tuples]; exact hpull))
    rw [mem_filter] at hcb ⊢
    exact ⟨hcb.1, hcb.2.1⟩

/-! ## Round `0`'s three challenges -/

/-- **`squares` is the point of squares.** -/
theorem squares_eq_ofFn : ∀ (c : E) (n : ℕ), squares c n = List.ofFn (FlockSound.sqPt n c)
  | _, 0 => by simp [squares]
  | c, n + 1 => by
    rw [squares, FlockSound.sqPt_succ, List.ofFn_succ, squares_eq_ofFn (c * c) n]
    simp [sq]

/-- **π1-rec3's round-`0` challenges as the main line's six**: `[c, β, γ]` read as
`[c, c², c⁴, c⁸, β, γ]`. -/
def expandCh (ch : List E) : List E :=
  [ch.getD 0 0, ch.getD 0 0 ^ 2, ch.getD 0 0 ^ 4, ch.getD 0 0 ^ 8, ch.getD 1 0, ch.getD 2 0]

/-- The first four are the squares of the first challenge. -/
theorem expandCh_alpha (ch : List E) :
    (fun i : Fin 4 ↦ (expandCh ch).getD i 0) = FlockSound.sqPt 4 (ch.getD 0 0) := by
  funext i
  fin_cases i <;> simp [expandCh, FlockSound.sqPt]

theorem expandCh_beta (ch : List E) : (expandCh ch).getD 4 0 = ch.getD 1 0 := by
  simp [expandCh]

theorem expandCh_gamma (ch : List E) : (expandCh ch).getD 5 0 = ch.getD 2 0 := by
  simp [expandCh]

/-- **`expandCh` agrees with the transcription**: its first four are `squares c 4`. -/
theorem expandCh_take (c β γ : E) : (expandCh [c, β, γ]).take 4 = squares c 4 := by
  have h := expandCh_alpha [c, β, γ]
  rw [List.getD_cons_zero] at h
  rw [squares_eq_ofFn, ← h]
  simp [expandCh, List.ofFn_succ]

namespace BusModel

variable {D : Deployment} {κ : ℕ} (B : BusModel D κ)

/-- **Round `0`'s error with squares**: the bus (`16 N / |E|`) and the constraints' batching. -/
noncomputable def errMainSq : ℝ≥0∞ :=
  ((16 * B.N : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) +
    ((B.ncv - 1 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

/-- Two challenges are `(c, β)`. -/
theorem card_fin_two_pair (P : E → E → Prop) [∀ a b, Decidable (P a b)] :
    (univ.filter fun v : Fin (1 + 1) → E =>
      P ((List.ofFn v).getD 0 0) ((List.ofFn v).getD 1 0)).card =
      (univ.filter fun cb : E × E => P cb.1 cb.2).card := by
  refine Finset.card_bij (fun v _ => (v 0, v 1)) (fun v hv => ?_) (fun v _ w _ h => ?_)
    (fun cb hcb => ?_)
  · simpa using hv
  · simp only [Prod.mk.injEq] at h
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  · exact ⟨![cb.1, cb.2], by simpa using hcb, rfl⟩

/-- **Round `0` with squares is sound**: three challenges `[c, β, γ]`, read as the main line's six
(`expandCh`), turn `¬ MainHolds` into `MainOK` with probability at most `errMainSq`. -/
theorem mainSoundSq (s : USt) (c : Stk) :
    Pr{let ch ← Compose.draws E 3}[¬ MainHoldsOf D s c ∧ B.MainOK s c (expandCh ch)] ≤
      B.errMainSq := by
  classical
  unfold errMainSq
  by_cases hall : ∀ x < B.nrows, ∀ v ∈ B.cvec s c x, v = 0
  · obtain ⟨hcv, hcn, hpl, hcp⟩ := B.cvec_ok s c hall
    have hR := B.realizes s c hcp
    -- The bus: the event is on `(c, β)`.
    have hev : ∀ ch : List E, (¬ MainHoldsOf D s c ∧ B.MainOK s c (expandCh ch)) →
        ((B.hd s c).Sat (FlockSound.sqPt 4 ((ch.take 2).getD 0 0)) ((ch.take 2).getD 1 0) ∧
          ¬ (D.inst s.2).Balanced (lv42Stack D.prog (D.sizes s.2) D.shape c)) ∨ False := by
      intro ch ⟨hn, hok⟩
      refine Or.inl ⟨?_, fun hb => hn ⟨hcv, hb, hcn, hpl⟩⟩
      have h1 : (ch.take 2).getD 0 0 = ch.getD 0 0 := by
        simp [List.getD_eq_getElem?_getD]
      have h2 : (ch.take 2).getD 1 0 = ch.getD 1 0 := by
        simp [List.getD_eq_getElem?_getD]
      rw [h1, h2, ← expandCh_alpha, ← expandCh_beta]
      exact hok.1
    have hb := prEvent_draws_append_le 2 1 (fun l => (B.hd s c).Sat
      (FlockSound.sqPt 4 (l.getD 0 0)) (l.getD 1 0) ∧
        ¬ (D.inst s.2).Balanced (lv42Stack D.prog (D.sizes s.2) D.shape c))
      (fun _ => False)
    refine (prEvent_mono _ _ _ hev).trans (hb.trans ?_)
    rw [prEvent_eq_zero_of_forall_not _ _ (fun _ h => h), add_zero]
    refine le_trans ?_ le_self_add
    have hc := card_sat_not_balanced_le_sq (I := D.inst s.2) (B.wf s c) hR (B.hpush s c hcp)
      (B.hpull s c hcp)
    refine prEvent_draws_le_of_card 1 _ (16 * B.N) ?_
    rw [pow_one]
    have h2 := card_fin_two_pair (fun a b => (B.hd s c).Sat (FlockSound.sqPt 4 a) b ∧
      ¬ (D.inst s.2).Balanced (lv42Stack D.prog (D.sizes s.2) D.shape c))
    exact (le_of_eq h2).trans hc
  · obtain ⟨x₀, hx₀, v, hv, hv0⟩ : ∃ x < B.nrows, ∃ v ∈ B.cvec s c x, v ≠ 0 := by
      by_contra hne
      exact hall fun x hx v hv => by
        by_contra h0
        exact hne ⟨x, hx, v, hv, h0⟩
    have hev : ∀ ch : List E, (¬ MainHoldsOf D s c ∧ B.MainOK s c (expandCh ch)) →
        False ∨ powComb (B.cvec s c x₀) ((ch.drop 2).headD 0) = 0 := by
      intro ch ⟨_, hok⟩
      refine Or.inr ?_
      have h1 : (ch.drop 2).headD 0 = (expandCh ch).getD 5 0 := by
        rw [expandCh_gamma]
        simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
      rw [h1]
      exact hok.2 x₀ hx₀
    have hb := prEvent_draws_append_le 2 1 (fun _ => False)
      (fun l => powComb (B.cvec s c x₀) (l.headD 0) = 0)
    refine (prEvent_mono _ _ _ hev).trans (hb.trans ?_)
    rw [prEvent_eq_zero_of_forall_not _ _ (fun _ h => h), zero_add]
    refine le_trans ?_ le_add_self
    refine prEvent_draws_le_of_card 0 _ _ ?_
    rw [pow_zero, mul_one]
    convert (card_powComb_le _ ⟨v, hv, hv0⟩).trans (Nat.sub_le_sub_right (B.cvec_len s c x₀) 1)
      using 1
    convert card_filter_fin_one (fun ρ => powComb (B.cvec s c x₀) ρ = 0) using 2

/-- Round `0`'s error with squares is at most `2^35 / |E|` when `16 N + ncv ≤ 2^35`. -/
theorem errMainSq_le (h : 16 * B.N + B.ncv ≤ 2 ^ 35) :
    B.errMainSq ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  unfold errMainSq
  rw [ENNReal.div_add_div_same, ← Nat.cast_add]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _

end BusModel

end UniSound

/-- info: 'UniSound.fingerprint_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fingerprint_eq_mle

/-- info: 'UniSound.fpPoly_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fpPoly_injective

/-- info: 'UniSound.card_sideProduct_sq_collision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.card_sideProduct_sq_collision_le

/-- info: 'UniSound.card_sat_not_balanced_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.card_sat_not_balanced_le_sq

/-- info: 'UniSound.squares_eq_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.squares_eq_ofFn

/-- info: 'UniSound.expandCh_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.expandCh_take

/-- info: 'UniSound.BusModel.mainSoundSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.BusModel.mainSoundSq

/-- info: 'UniSound.BusModel.errMainSq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.BusModel.errMainSq_le
