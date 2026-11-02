-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s bad-event budget (`Common.prEvent_run_bad_le`), whose proof
-- `prEvent_run_bad_le_pot` adapts.
import QuotientZk.Deployed.Fresh.Core

/-!
# Fresh Fiat–Shamir inputs: the probability of *bad*

A fresh answer `u` of the random oracle is uniform on `Out = Bytes32 × KSt`, so each of the
values `NoHit` forbids it is hit with probability at most `2^-256` (`pr_fst`, `pr_inj`: a digest,
or an injective image of one — its 32 bytes, its root words, its seed state; `pr_cap`: a
capacity, nine lanes, `2^-576 ≤ 2^-256`). With `|dom|` inputs held (`dom K0 st`):

* `pr_not_noHit`: `Pr[¬ NoHit] ≤ 6 (|dom| + 1) / 2^256`;
* `pr_not_noHitC`: `Pr[¬ NoHitC] ≤ (|dom| + 1) · 3 εc`, for claim windows `cw j` each hit with
  probability at most `εc`;
* `pr_step`: one tracked step from a state off *bad* raises it with probability at most
  `6 (|dom| + 1) / 2^256`, plus `(|dom| + 1) · 3 εc` at the reduction's fourth and fifth
  challenges (`Inc`).

`prEvent_run_bad_le_pot` is `common`'s budget with a potential: the extra term is paid only on the
steps that raise the potential `min |hist| 5 - min |hist| 3`, which rises by one at those two
challenges and never exceeds two. **`prEvent_bad_le`**: a run of at most `Q` operations from a
state with an empty log and no challenges ends in *bad* with probability at most

  `Q · 6 (|K0| + Q) / 2^256 + 2 (|K0| + Q) · 3 εc`.
-/

open OracleComp OracleSpec QuotientRpm MeasureTheory
open scoped ENNReal

namespace QuotientZk.Deployed.Fresh

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 2000

/-! ## Uniform answers -/

theorem card_uInt64 : Fintype.card UInt64 = 2 ^ 64 := by
  rw [← FinEnum.card_eq_fintypeCard]; rfl

theorem card_kSt : Fintype.card KSt = 2 ^ 1600 := by
  rw [instFintypeVector, Fintype.ofEquiv_card, Fintype.card_fun, Fintype.card_fin, card_uInt64,
    ← pow_mul]

theorem card_digest : Fintype.card Bytes32 = 2 ^ 256 := by
  rw [Common.card_vector_uInt8]; norm_num

theorem card_out : Fintype.card Out = 2 ^ 256 * 2 ^ 1600 := by
  rw [Fintype.card_prod, card_digest, card_kSt]

/-- A uniform answer satisfies an event of at most `|Out| / M` answers with probability at most
`1 / M`. -/
theorem pr_out_le (p : Out → Prop) [DecidablePred p] (M : ℕ) (hM : 0 < M)
    (h : (Finset.univ.filter p).card * M ≤ Fintype.card Out) :
    Pr{let u ← $ᵗ Out}[p u] ≤ (M : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample]
  refine ENNReal.div_le_of_le_mul ?_
  have hM' : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast hM.ne'
  calc ((Finset.univ.filter p).card : ℝ≥0∞)
      = ((Finset.univ.filter p).card : ℝ≥0∞) * M * (M : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hM' (ENNReal.natCast_ne_top _), mul_one]
    _ ≤ (Fintype.card Out : ℝ≥0∞) * (M : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast h
    _ = (M : ℝ≥0∞)⁻¹ * Fintype.card Out := mul_comm _ _

/-- **A digest is hit with probability `2^-256`.** -/
theorem pr_fst (d : Bytes32) : Pr{let u ← $ᵗ Out}[u.1 = d] ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  classical
  have hc : (Finset.univ.filter fun u : Out => u.1 = d).card ≤ Fintype.card KSt := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_le_of_injective (fun x : {u : Out // u.1 = d} => x.1.2)
      fun x y h => Subtype.ext (Prod.ext (x.2.trans y.2.symm) h)
  have h := pr_out_le (fun u : Out => u.1 = d) (2 ^ 256) (Nat.two_pow_pos 256) (by
    rw [card_out]; rw [card_kSt] at hc
    calc _ ≤ 2 ^ 1600 * 2 ^ 256 := Nat.mul_le_mul_right _ hc
      _ = _ := mul_comm _ _)
  rwa [Nat.cast_pow, Nat.cast_ofNat] at h

/-- **A capacity is hit with probability `2^-576 ≤ 2^-256`.** -/
theorem pr_cap (c : List UInt64) : Pr{let u ← $ᵗ Out}[capOf u.2 = c] ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  classical
  have hc : (Finset.univ.filter fun u : Out => capOf u.2 = c).card ≤
      Fintype.card (Bytes32 × (Fin 16 → UInt64)) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_le_of_injective
      (fun x : {u : Out // capOf u.2 = c} => (x.1.1, fun i : Fin 16 => x.1.2[i.1]'(by omega)))
      fun x y hab => Subtype.ext ?_
    obtain ⟨a, ha'⟩ := x
    obtain ⟨b, hb'⟩ := y
    simp only at hab ⊢
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    simp only at h1 h2
    refine Prod.ext h1 ?_
    have hd : a.2.toList.drop 16 = b.2.toList.drop 16 := ha'.trans hb'.symm
    have ht : a.2.toList.take 16 = b.2.toList.take 16 := by
      refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
      have hi : i < 16 := by simpa using hi1
      have := congrFun h2 ⟨i, hi⟩
      simpa [List.getElem_take] using this
    apply Vector.toList_inj.mp
    rw [← List.take_append_drop 16 a.2.toList, ← List.take_append_drop 16 b.2.toList, ht, hd]
  have hcard : Fintype.card (Bytes32 × (Fin 16 → UInt64)) = 2 ^ 256 * 2 ^ 1024 := by
    rw [Fintype.card_prod, card_digest, Fintype.card_fun, Fintype.card_fin, card_uInt64, ← pow_mul]
  have h := pr_out_le (fun u : Out => capOf u.2 = c) (2 ^ 256) (Nat.two_pow_pos 256) (by
    rw [card_out]; rw [hcard] at hc
    calc _ ≤ 2 ^ 256 * 2 ^ 1024 * 2 ^ 256 := Nat.mul_le_mul_right _ hc
      _ = 2 ^ 256 * 2 ^ 1280 := by rw [mul_assoc, ← pow_add]
      _ ≤ 2 ^ 256 * 2 ^ 1600 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  rwa [Nat.cast_pow, Nat.cast_ofNat] at h

/-- **An injective image of a digest is hit with probability `2^-256`.** -/
theorem pr_inj {X : Type} (f : Bytes32 → X) (hf : Function.Injective f) (x : X) :
    Pr{let u ← $ᵗ Out}[f u.1 = x] ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  by_cases h : ∃ d, f d = x
  · obtain ⟨d, rfl⟩ := h
    exact (prEvent_mono _ _ _ fun u hu => hf hu).trans (pr_fst d)
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => h ⟨u.1, hu⟩]
    exact zero_le

/-- The seed state determines the IV. -/
theorem seedInput_injective : Function.Injective seedInput := by
  intro a b h
  have hchunk : ∀ i, i < 4 → (a.toList.drop (8 * i)).take 8 = (b.toList.drop (8 * i)).take 8 := by
    intro i hi
    have e := congrArg (fun v : KSt => v[i]'(by omega)) h
    simp only [seedInput, Vector.getElem_ofFn, hi, ite_true] at e
    have e' := congrArg LeanVM.Protocol.KeccakHash.wordBytes e
    rw [QuotientRpm.wordBytes_bytesLane_take _ (by simp; omega),
      QuotientRpm.wordBytes_bytesLane_take _ (by simp; omega), List.take_take,
      List.take_take, min_self] at e'
    exact e'
  apply Vector.toList_inj.mp
  refine List.ext_getElem (by simp) fun k hk1 hk2 => ?_
  have hk : k < 32 := by simpa using hk1
  have hc := hchunk (k / 8) (by omega)
  have hr : k % 8 < ((a.toList.drop (8 * (k / 8))).take 8).length := by simp; omega
  have := List.getElem_of_eq hc hr
  simp only [List.getElem_take, List.getElem_drop] at this
  simpa only [show 8 * (k / 8) + k % 8 = k by omega] using this

/-! ## Union bounds -/

/-- **A union bound over a list.** -/
theorem pr_exists_mem_le {α β : Type} (mx : ProbComp α) (l : List β) (q : β → α → Prop)
    (ε : ℝ≥0∞) (h : ∀ y ∈ l, Pr{let x ← mx}[q y x] ≤ ε) :
    Pr{let x ← mx}[∃ y ∈ l, q y x] ≤ l.length * ε := by
  induction l with
  | nil =>
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun x _ hx => by simp at hx]
    exact zero_le
  | cons a l ih =>
    calc Pr{let x ← mx}[∃ y ∈ a :: l, q y x]
        ≤ Pr{let x ← mx}[q a x ∨ ∃ y ∈ l, q y x] :=
          prEvent_mono _ _ _ fun x hx => by simpa using hx
      _ ≤ Pr{let x ← mx}[q a x] + Pr{let x ← mx}[∃ y ∈ l, q y x] := prEvent_or_le _ _ _
      _ ≤ ε + l.length * ε :=
          add_le_add (h a List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))
      _ = (a :: l).length * ε := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-! ## Hitting a forbidden value -/

/-- **A fresh answer hits a value `NoHit` forbids with probability at most
`6 (|dom| + 1) / 2^256`.** -/
theorem pr_not_noHit (K0 : List Inp) (st : DSt) (t : Inp) :
    Pr{let u ← $ᵗ Out}[¬ NoHit K0 st t u] ≤
      6 * (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  set L := t :: dom K0 st
  set M := (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞)
  set ε := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have hL : (L.length : ℝ≥0∞) = M := by simp [L, M]
  -- the six events
  let E1 : Out → Prop := fun u => ∃ y ∈ L, ∃ b, y = .inl b ∧ u.1.toList = b.take 32
  let E2 : Out → Prop := fun u => ∃ y ∈ L, ∃ b, y = .inl b ∧ rootWords u.1 = b.drop 32
  let E3 : Out → Prop := fun u => ∃ y ∈ dom K0 st, ∃ v, st.cache y = some v ∧ u.1 = v.1
  let E4 : Out → Prop := fun u => ∃ y ∈ L, ∃ w, y = .inr w ∧ capOf u.2 = capOf w
  let E5 : Out → Prop := fun u => capOf u.2 = zeroCap
  let E6 : Out → Prop := fun u => ∃ y ∈ L, ∃ w, y = .inr w ∧ seedInput u.1 = w
  have himp : ∀ u, ¬ NoHit K0 st t u → E1 u ∨ E2 u ∨ E3 u ∨ E4 u ∨ E5 u ∨ E6 u := by
    intro u hn
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
    exact hn
      { left := fun y hy b hb he => h1 ⟨y, List.mem_cons.mpr hy, b, hb, he.symm⟩
        root := fun y hy b hb he => h2 ⟨y, List.mem_cons.mpr hy, b, hb, he.symm⟩
        dig := fun y hy v hv he => h3 ⟨y, hy, v, hv, he.symm⟩
        cap := fun y hy w hw he => h4 ⟨y, List.mem_cons.mpr hy, w, hw, he.symm⟩
        capz := h5
        seed := fun y hy he => h6 ⟨y, List.mem_cons.mpr hy, _, he, rfl⟩ }
  have hinj : Function.Injective (fun d : Bytes32 => d.toList) := fun a b h => Vector.toList_inj.mp h
  have p1 : Pr{let u ← $ᵗ Out}[E1 u] ≤ M * ε := by
    rw [← hL]
    refine pr_exists_mem_le _ L _ _ fun y _ => ?_
    cases y with
    | inl b =>
      refine (prEvent_mono _ _ _ fun u hu => ?_).trans (pr_inj _ hinj (b.take 32))
      obtain ⟨b', hb', he⟩ := hu
      cases hb'
      exact he
    | inr w =>
      rw [prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => by
        obtain ⟨b', hb', -⟩ := hu; cases hb']
      exact zero_le
  have p2 : Pr{let u ← $ᵗ Out}[E2 u] ≤ M * ε := by
    rw [← hL]
    refine pr_exists_mem_le _ L _ _ fun y _ => ?_
    cases y with
    | inl b =>
      refine (prEvent_mono _ _ _ fun u hu => ?_).trans (pr_inj _ rootWords_injective (b.drop 32))
      obtain ⟨b', hb', he⟩ := hu
      cases hb'
      exact he
    | inr w =>
      rw [prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => by
        obtain ⟨b', hb', -⟩ := hu; cases hb']
      exact zero_le
  have p3 : Pr{let u ← $ᵗ Out}[E3 u] ≤ M * ε := by
    refine (pr_exists_mem_le _ (dom K0 st) _ ε fun y _ => ?_).trans ?_
    · cases hy : st.cache y with
      | some v =>
        refine (prEvent_mono _ _ _ fun u hu => ?_).trans (pr_fst v.1)
        obtain ⟨v', hv', he⟩ := hu
        cases hv'
        exact he
      | none =>
        rw [prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => by
          obtain ⟨v', hv', -⟩ := hu; cases hv']
        exact zero_le
    · gcongr
      simp [M]
  have p4 : Pr{let u ← $ᵗ Out}[E4 u] ≤ M * ε := by
    rw [← hL]
    refine pr_exists_mem_le _ L _ _ fun y _ => ?_
    cases y with
    | inr w =>
      refine (prEvent_mono _ _ _ fun u hu => ?_).trans (pr_cap (capOf w))
      obtain ⟨w', hw', he⟩ := hu
      cases hw'
      exact he
    | inl b =>
      rw [prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => by
        obtain ⟨w', hw', -⟩ := hu; cases hw']
      exact zero_le
  have p5 : Pr{let u ← $ᵗ Out}[E5 u] ≤ M * ε :=
    (pr_cap zeroCap).trans (le_mul_of_one_le_left zero_le (by simp [M]))
  have p6 : Pr{let u ← $ᵗ Out}[E6 u] ≤ M * ε := by
    rw [← hL]
    refine pr_exists_mem_le _ L _ _ fun y _ => ?_
    cases y with
    | inr w =>
      refine (prEvent_mono _ _ _ fun u hu => ?_).trans (pr_inj _ seedInput_injective w)
      obtain ⟨w', hw', he⟩ := hu
      cases hw'
      exact he
    | inl b =>
      rw [prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => by
        obtain ⟨w', hw', -⟩ := hu; cases hw']
      exact zero_le
  calc Pr{let u ← $ᵗ Out}[¬ NoHit K0 st t u]
      ≤ Pr{let u ← $ᵗ Out}[E1 u ∨ E2 u ∨ E3 u ∨ E4 u ∨ E5 u ∨ E6 u] :=
        prEvent_mono _ _ _ himp
    _ ≤ Pr{let u ← $ᵗ Out}[E1 u] + (Pr{let u ← $ᵗ Out}[E2 u] + (Pr{let u ← $ᵗ Out}[E3 u] +
          (Pr{let u ← $ᵗ Out}[E4 u] + (Pr{let u ← $ᵗ Out}[E5 u] + Pr{let u ← $ᵗ Out}[E6 u])))) :=
        (prEvent_or_le _ _ _).trans (add_le_add le_rfl ((prEvent_or_le _ _ _).trans
          (add_le_add le_rfl ((prEvent_or_le _ _ _).trans (add_le_add le_rfl
            ((prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_or_le _ _ _))))))))
    _ ≤ M * ε + (M * ε + (M * ε + (M * ε + (M * ε + M * ε)))) := by
        gcongr
    _ = 6 * M * ε := by ring

/-- **A fresh answer at a claims' challenge hits a claim window with probability at most
`(|dom| + 1) · 3 εc`.** -/
theorem pr_not_noHitC (cw : Fin 3 → Bytes32 → List UInt8) (εc : ℝ≥0∞)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc) (K0 : List Inp) (st : DSt) (t : Inp) :
    Pr{let u ← $ᵗ Out}[¬ NoHitC cw K0 st t u] ≤
      (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) * (3 * εc) := by
  set L := t :: dom K0 st
  have hL : (L.length : ℝ≥0∞) = (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) := by simp [L]
  have himp : ∀ u, ¬ NoHitC cw K0 st t u → ∃ y ∈ L, ∃ b, y = .inl b ∧
      ∃ j ∈ List.finRange 3, cw j u.1 = (b.drop 76).take 24 := by
    intro u hn
    by_contra hc
    exact hn fun y hy b hb j he =>
      hc ⟨y, List.mem_cons.mpr hy, b, hb, j, List.mem_finRange j, he.symm⟩
  refine (prEvent_mono _ _ _ himp).trans ?_
  rw [← hL]
  refine pr_exists_mem_le _ L _ _ fun y _ => ?_
  cases y with
  | inl b =>
    refine (prEvent_mono _ _ _ fun u hu => ?_).trans
      ((pr_exists_mem_le _ (List.finRange 3) (fun j u => cw j u.1 = (b.drop 76).take 24) εc
        fun j _ => hcw j _).trans (by simp))
    obtain ⟨b', hb', he⟩ := hu
    cases hb'
    exact he
  | inr w =>
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => by
      obtain ⟨b', hb', -⟩ := hu; cases hb']
    exact zero_le

/-- **A fresh answer hits** with probability at most `6 (|dom| + 1) / 2^256`, plus
`(|dom| + 1) · 3 εc` at the claims' challenges. -/
theorem pr_hit (cw : Fin 3 → Bytes32 → List UInt8) (εc : ℝ≥0∞)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc) (n : ℕ) (K0 : List Inp)
    (op : Op Inp Tbl Pos) (st : DSt) (t : Inp) [Decidable (Inc n op st)] :
    Pr{let u ← $ᵗ Out}[Hit n cw K0 op st t u] ≤
      6 * (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ +
        (if Inc n op st then (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) * (3 * εc) else 0) := by
  refine (prEvent_or_le _ _ _).trans (add_le_add (pr_not_noHit K0 st t) ?_)
  split_ifs with hi
  · exact (prEvent_mono _ _ _ fun u hu => hu.2).trans (pr_not_noHitC cw εc hcw K0 st t)
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => hi hu.1]

/-! ## One step -/

/-- A step whose new log entry is `t`, answered `u`, hits only if `u` does. -/
theorem stepHit_imp (n : ℕ) (cw : Fin 3 → Bytes32 → List UInt8) (K0 : List Inp)
    (op : Op Inp Tbl Pos) (st st' : DSt) (t : Inp) (u : Out) (hlog : st'.log = t :: st.log)
    (hc : st'.cache t = some u) (h : StepHit n cw K0 op st st') : Hit n cw K0 op st t u := by
  obtain ⟨t', u', h1, h2, h3⟩ := h
  rw [hlog] at h1
  obtain ⟨rfl, -⟩ := List.cons.inj h1
  rw [hc] at h2
  cases h2
  exact h3

/-- A step that logs nothing does not hit. -/
theorem not_stepHit_of_log (n : ℕ) (cw : Fin 3 → Bytes32 → List UInt8) (K0 : List Inp)
    (op : Op Inp Tbl Pos) (st st' : DSt) (hlog : st'.log = st.log) :
    ¬ StepHit n cw K0 op st st' := by
  rintro ⟨t, u, h, -⟩
  have := congrArg List.length (hlog.symm.trans h)
  simp at this

section Step

open Classical

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (s : S) (cw : Fin 3 → Bytes32 → List UInt8)
  (K0 : List Inp) (εc : ℝ≥0∞) (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc)

include hcw in
/-- A public query hits as a fresh answer does. -/
theorem pr_roStep_hit (op : Op Inp Tbl Pos) (t : Inp) (st : DSt) :
    Pr{let z ← roStep (K := Tbl) (X := Pos) t st}[StepHit P.n cw K0 op st z.2] ≤
      6 * (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ +
        (if Inc P.n op st then (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) * (3 * εc) else 0) := by
  unfold roStep
  cases hc : st.cache t with
  | some v =>
    simp only
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact not_stepHit_of_log _ _ _ _ _ _ rfl]
    exact zero_le
  | none =>
    simp only [bind_pure_comp, prEvent_map]
    exact (prEvent_mono _ _ _ fun u hu => stepHit_imp _ _ _ _ _ _ t u rfl
      (by simp [QueryCache.cacheQuery]) hu).trans (pr_hit cw εc hcw P.n K0 op st t)

include hcw in
/-- **One tracked step from a state off *bad*** raises it with probability at most
`6 (|dom| + 1) / 2^256`, plus `(|dom| + 1) · 3 εc` at the claims' challenges. -/
theorem pr_step (op : Op Inp Tbl Pos) (st : DSt) :
    Pr{let z ← (implB P s cw K0 op).run (st, false)}[z.2.2 = true] ≤
      6 * (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ +
        (if Inc P.n op st then (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) * (3 * εc) else 0) := by
  rw [implB_run, prEvent_map]
  simp only [Bool.false_or, decide_eq_true_eq]
  cases op with
  | pub t => exact pr_roStep_hit P cw K0 εc hcw _ t st
  | msg =>
    simp only [implReal, StateT.run]
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact not_stepHit_of_log _ _ _ _ _ _ rfl]
    exact zero_le
  | leaf k x =>
    simp only [implReal, StateT.run]
    by_cases h : st.hist.length < P.cK k
    · rw [if_pos h]
      rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact not_stepHit_of_log _ _ _ _ _ _ rfl]
      exact zero_le
    · rw [if_neg h]
      exact pr_roStep_hit P cw K0 εc hcw _ _ st
  | chal t =>
    simp only [implReal, StateT.run]
    by_cases h : st.hist.length < P.n
    · rw [if_pos h]
      cases hc : st.cache t with
      | some v =>
        simp only
        rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
          simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact not_stepHit_of_log _ _ _ _ _ _ rfl]
        exact zero_le
      | none =>
        simp only [bind_pure_comp, prEvent_map]
        exact (prEvent_mono _ _ _ fun u hu => stepHit_imp _ _ _ _ _ _ t u rfl
          (by simp [QueryCache.cacheQuery]) hu).trans (pr_hit cw εc hcw P.n K0 _ st t)
    · rw [if_neg h]
      exact pr_roStep_hit P cw K0 εc hcw _ t st

end Step

/-! ## The budget with a potential -/

/-- **`common`'s bad-event budget, with a potential** (`Common.prEvent_run_bad_le`, adapted). Every
step from a state off `bad` of size at most `N - 1` reaches `bad` with probability at most `δ`, plus
`δ₂` on the steps `inc`; a step raises the size by at most one, and the potential `φ` (at most `Φ`)
by at least one on the steps `inc`, never lowering it. Then a run of at most `Q` operations, from a
state of size at most `N - Q`, ends in `bad` with probability at most
`[bad s₀] + Q δ + (Φ - φ s₀) δ₂`. -/
theorem prEvent_run_bad_le_pot {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop) [DecidablePred bad]
    (size φ : σ → ℕ) (inc : ι → σ → Prop) [∀ t s, Decidable (inc t s)] (N Φ : ℕ)
    (δ δ₂ : ℝ≥0∞)
    (hsize : ∀ t s, ∀ z ∈ support ((impl t).run s), size z.2 ≤ size s + 1)
    (hφ : ∀ t s, ∀ z ∈ support ((impl t).run s), φ s + (if inc t s then 1 else 0) ≤ φ z.2)
    (hΦ : ∀ s, φ s ≤ Φ)
    (hstep : ∀ t s, ¬ bad s → size s + 1 ≤ N →
      Pr{let z ← (impl t).run s}[bad z.2] ≤ δ + ((if inc t s then 1 else 0 : ℕ) : ℝ≥0∞) * δ₂)
    (oa : OracleComp spec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q) (s₀ : σ)
    (hN : size s₀ + Q ≤ N) :
    Pr{let z ← (simulateQ impl oa).run s₀}[bad z.2] ≤
      (if bad s₀ then 1 else 0) + Q * δ + ((Φ - φ s₀ : ℕ) : ℝ≥0∞) * δ₂ := by
  induction oa using OracleComp.inductionOn generalizing Q s₀ with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, prEvent_pure]
    exact le_add_right (le_add_right le_rfl)
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at hQ
    obtain ⟨hQ0, hk⟩ := hQ
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    let : MeasurableSpace (spec.Range t × σ) := ⊤
    rw [prEvent_bind_eq_lintegral_of_discrete]
    set i : ℕ := if inc t s₀ then 1 else 0 with hi
    set m : ℕ := Φ - φ s₀ - i with hm
    have hbound : ∀ z ∈ support ((impl t).run s₀),
        Pr{let y ← (simulateQ impl (k z.1)).run z.2}[bad y.2] ≤
          (if bad z.2 then 1 else 0) + (((Q - 1 : ℕ) : ℝ≥0∞) * δ + (m : ℝ≥0∞) * δ₂) :=
      fun z hz => by
        refine (ih z.1 (Q - 1) (hk z.1) z.2 (by have := hsize t s₀ z hz; omega)).trans ?_
        rw [add_assoc]
        gcongr
        have h1 := hφ t s₀ z hz
        have h2 := hΦ z.2
        omega
    have him : i + m = Φ - φ s₀ := by
      obtain ⟨z, hz⟩ := OracleComp.support_nonempty ((impl t).run s₀)
      have h1 := hφ t s₀ z hz
      have h2 := hΦ z.2
      omega
    calc ∫⁻ z, Pr{let y ← (simulateQ impl (k z.1)).run z.2}[bad y.2] ∂𝒟[(impl t).run s₀]
        ≤ ∫⁻ z, ((if bad z.2 then 1 else 0) +
            (((Q - 1 : ℕ) : ℝ≥0∞) * δ + (m : ℝ≥0∞) * δ₂)) ∂𝒟[(impl t).run s₀] := by
          apply lintegral_mono_ae
          filter_upwards [ae_evalDist_of_forall_mem_support _ hbound] with z hz using hz
      _ ≤ Pr{let z ← (impl t).run s₀}[bad z.2] +
            (((Q - 1 : ℕ) : ℝ≥0∞) * δ + (m : ℝ≥0∞) * δ₂) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const]
          refine add_le_add (le_of_eq ?_)
            (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _))
          rw [prEvent_eq_evalDist_of_discrete, ← lintegral_indicator_one MeasurableSet.of_discrete]
          exact lintegral_congr fun z ↦ by by_cases h : bad z.2 <;> simp [h, Set.indicator]
      _ ≤ ((if bad s₀ then 1 else 0) + (δ + (i : ℝ≥0∞) * δ₂)) +
            (((Q - 1 : ℕ) : ℝ≥0∞) * δ + (m : ℝ≥0∞) * δ₂) := by
          gcongr
          by_cases hb : bad s₀
          · simp only [hb, ite_true]
            exact (prEvent_le_one _).trans le_self_add
          · simp only [hb, ite_false, zero_add]
            exact hstep t s₀ hb (by omega)
      _ = (if bad s₀ then 1 else 0) + ((1 + (Q - 1) : ℕ) : ℝ≥0∞) * δ +
            ((i + m : ℕ) : ℝ≥0∞) * δ₂ := by
          push_cast; ring
      _ = _ := by rw [show 1 + (Q - 1) = Q by omega, him]

/-! ## The bound -/

section Bound

open Classical

/-- **The potential**: the claims' challenges drawn so far (the fourth and fifth challenges). -/
def phi (st : DSt) : ℕ := min st.hist.length 5 - min st.hist.length 3

theorem phi_le_two (st : DSt) : phi st ≤ 2 := by
  unfold phi; omega

@[simp] theorem phi_addE (st : DSt) (t : Inp) (u : Out) : phi (addE st t u) = phi st := rfl

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (s : S) (cw : Fin 3 → Bytes32 → List UInt8)
  (K0 : List Inp)

/-- A real step logs at most one input, and raises the potential at the claims' challenges. -/
theorem step_size_phi (op : Op Inp Tbl Pos) (st : DSt) (a : DSpec.Range op) (st' : DSt)
    (h : (a, st') ∈ support ((implReal P s op).run st)) :
    st'.log.length ≤ st.log.length + 1 ∧
      phi st + (if Inc P.n op st then 1 else 0) ≤ phi st' := by
  have hc := implReal_cases P s op st a st' h
  have nc : ∀ (op : Op Inp Tbl Pos), (∀ t, op ≠ .chal t) → ¬ Inc P.n op st :=
    fun op hop hi => by obtain ⟨⟨t, ht⟩, -⟩ := hi; exact hop t ht
  cases op with
  | pub t =>
    rw [if_neg (nc _ fun t' h => by cases h)]
    rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  | msg =>
    rw [if_neg (nc _ fun t' h => by cases h)]
    rw [hc.2]; simp
  | leaf k x =>
    rw [if_neg (nc _ fun t' h => by cases h)]
    rcases hc with ⟨-, -, rfl⟩ | ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ <;> simp
  | chal t =>
    rcases hc with ⟨hn, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨hn, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · refine ⟨by simp, ?_⟩
      unfold phi Inc
      simp only [List.length_append, List.length_singleton]
      split_ifs <;> omega
    · refine ⟨by simp, ?_⟩
      unfold phi Inc
      simp only [List.length_append, List.length_singleton]
      split_ifs <;> omega
    · rw [if_neg fun hi => by have := hi.2.2; omega]
      simp
    · rw [if_neg fun hi => by have := hi.2.2; omega]
      simp

theorem implB_support (op : Op Inp Tbl Pos) (b : DSt × Bool) (z : DSpec.Range op × (DSt × Bool))
    (hz : z ∈ support ((implB P s cw K0 op).run b)) :
    (z.1, z.2.1) ∈ support ((implReal P s op).run b.1) := by
  rw [implB_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact hy

/-- **The probability of *bad*.** A run of at most `Q` operations, from a state with an empty log
and no challenges, ends in *bad* with probability at most
`Q · 6 (|K0| + Q) / 2^256 + 2 (|K0| + Q) · 3 εc`. -/
theorem prEvent_bad_le (εc : ℝ≥0∞) (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc)
    {α : Type} (oa : OracleComp DSpec α) (Q : ℕ) (hQ : IsTotalQueryBound oa Q)
    (st : DSt) (hlog : st.log = []) (hhist : st.hist = []) :
    Pr{let z ← (simulateQ (implB P s cw K0) oa).run (st, false)}[z.2.2 = true] ≤
      (Q : ℝ≥0∞) * (6 * ((K0.length + Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        2 * (((K0.length + Q : ℕ) : ℝ≥0∞) * (3 * εc)) := by
  have hstep : ∀ (op : Op Inp Tbl Pos) (b : DSt × Bool), ¬ b.2 = true →
      b.1.log.length + 1 ≤ Q →
      Pr{let z ← (implB P s cw K0 op).run b}[z.2.2 = true] ≤
        6 * ((K0.length + Q : ℕ) : ℝ≥0∞) / 2 ^ 256 +
          ((if Inc P.n op b.1 then 1 else 0 : ℕ) : ℝ≥0∞) *
            (((K0.length + Q : ℕ) : ℝ≥0∞) * (3 * εc)) := by
    intro op b hb hN
    obtain ⟨st, bd⟩ := b
    simp only [Bool.not_eq_true] at hb
    simp only at hb hN ⊢
    subst hb
    refine (pr_step P s cw K0 εc hcw op st).trans ?_
    have hM : (((dom K0 st).length + 1 : ℕ) : ℝ≥0∞) ≤ ((K0.length + Q : ℕ) : ℝ≥0∞) := by
      have : (dom K0 st).length + 1 ≤ K0.length + Q := by
        simp only [dom, List.length_append]; omega
      exact_mod_cast this
    rw [div_eq_mul_inv]
    gcongr
    split_ifs
    · simp only [Nat.cast_one, one_mul]
      gcongr
    · simp
  have h := prEvent_run_bad_le_pot (implB P s cw K0) (fun b : DSt × Bool => b.2 = true)
    (fun b => b.1.log.length) (fun b => phi b.1) (fun op b => Inc P.n op b.1) Q 2
    (6 * ((K0.length + Q : ℕ) : ℝ≥0∞) / 2 ^ 256) (((K0.length + Q : ℕ) : ℝ≥0∞) * (3 * εc))
    (fun op b z hz => (step_size_phi P s op b.1 z.1 z.2.1 (implB_support P s cw K0 op b z hz)).1)
    (fun op b z hz => (step_size_phi P s op b.1 z.1 z.2.1 (implB_support P s cw K0 op b z hz)).2)
    (fun b => phi_le_two b.1) hstep oa Q hQ (st, false) (by simp [hlog])
  have hφ0 : phi st = 0 := by simp [phi, hhist]
  refine h.trans (le_of_eq ?_)
  simp only [Bool.false_eq_true, ite_false, zero_add, hφ0, Nat.sub_zero, Nat.cast_ofNat]

end Bound

end QuotientZk.Deployed.Fresh
