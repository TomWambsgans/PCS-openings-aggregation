-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Gates

/-!
# Packings on a satisfied circuit

A checked packing (`packOk`: Horner by 15-bit windows from the top, `acc·x^15 + Σ_(i<15) b_(15t+i) x^i`, the top
window `pack-top4`'s or a `pack` slot from a fresh zero, absent exponents a zero constant) is `Σ_e b_e x^e`
(`pack_val`); on bits, that is the word whose bit `e` is `b_e` (`pack_word`, through `F64.sum_testBit`).
-/

namespace RecCircuit

open Primitives

theorem List.sum_map_range {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, List.sum_map_range f n, Finset.sum_range_succ]; simp

/-- A sum whose terms vanish from `m` on is the same over any range past `m`. -/
theorem sum_range_trunc (f : ℕ → K) {m a b : ℕ} (ha : m ≤ a) (hb : m ≤ b) (h : ∀ i, m ≤ i → f i = 0) :
    ∑ i ∈ Finset.range a, f i = ∑ i ∈ Finset.range b, f i := by
  have key : ∀ c, m ≤ c → ∑ i ∈ Finset.range c, f i = ∑ i ∈ Finset.range m, f i := by
    intro c hc
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
    rw [Finset.sum_range_add]
    simp [h _ (Nat.le_add_right m _)]
  rw [key a ha, key b hb]

namespace Ctx

variable {X : Ctx} {w : ℕ → K}

/-- A packing's bit at exponent `e`: its value's word, or 0 if absent. -/
def bitAt (X : Ctx) (w : ℕ → K) (bits : List (ℕ × ℕ)) (e : ℕ) : K :=
  match bits.lookup e with
  | some u => X.val w u
  | none => 0

theorem lookup_none_of_gt {bits : List (ℕ × ℕ)} {e : ℕ} (h : bits.foldl (fun m t => max m t.1) 0 < e) :
    bits.lookup e = none := by
  rw [List.lookup_eq_none_iff]
  intro p hp
  have : p.1 ≤ bits.foldl (fun m t => max m t.1) 0 := by
    suffices ∀ (L : List (ℕ × ℕ)) (init : ℕ), (∀ q ∈ L, q.1 ≤ L.foldl (fun m t => max m t.1) init) ∧
        init ≤ L.foldl (fun m t => max m t.1) init by exact (this bits 0).1 p hp
    intro L
    induction L with
    | nil => intro init; simp
    | cons q L ih =>
      intro init
      simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
      obtain ⟨h1, h2⟩ := ih (max init q.1)
      exact ⟨⟨le_trans (le_max_right _ _) h2, h1⟩, le_trans (le_max_left _ _) h2⟩
  simp; omega

/-- A window's cells are the packing's bits at its exponents. -/
theorem window_cell (G : X.Good w) {bits : List (ℕ × ℕ)} {cells : Array ℕ} {e i : ℕ}
    (h : (match bits.lookup e with
      | some u => cells.getD i NONE == u
      | none => X.constOk (cells.getD i NONE) 0) = true) :
    X.val w (cells.getD i NONE) = X.bitAt w bits e := by
  unfold bitAt
  revert h
  cases bits.lookup e with
  | some u => intro h; simp only [beq_iff_eq] at h; rw [h]
  | none => intro h; exact const_val G h

theorem windowCells_lookup (base : ℕ) (cells : Array ℕ) (n i : ℕ) (hi : i < n) :
    (windowCells base cells n).lookup (base + i) = some (cells.getD i NONE) :=
  lookup_range_map (fun i => cells.getD i NONE) base n i hi

theorem windowCells_none (base : ℕ) (cells : Array ℕ) (n : ℕ) :
    (windowCells base cells n).lookup (base + n) = none :=
  lookup_range_map_none _ base n _ (Or.inr le_rfl)

/-- A window's cells are the packing's bits at its exponents. -/
theorem window_cells (G : X.Good w) {pk : PackT} {t' : ℕ} (hw : X.windowOk pk t' = true) :
    ∀ i < packKOf (packTopE pk) (packTopE pk / 15 - t'),
      X.val w ((pk.windows.getD t' default).1.getD i NONE) =
        X.bitAt w pk.bits (15 * (packTopE pk / 15 - t') + i) := by
  intro i hi
  unfold windowOk at hw
  simp only [Bool.and_eq_true] at hw
  exact window_cell G (allBelow_spec hw.1.2 i hi)

theorem sum_cells (G : X.Good w) {pk : PackT} {t' : ℕ} (hw : X.windowOk pk t' = true) (base n : ℕ)
    (hn : n ≤ packKOf (packTopE pk) (packTopE pk / 15 - t')) (rest : List (ℕ × ℕ)) :
    ((List.range n).map fun i => F64.G ^ i *
        X.cellVal w (windowCells base (pk.windows.getD t' default).1 n ++ rest) (base + i)).sum =
      ∑ i ∈ Finset.range n, X.bitAt w pk.bits (15 * (packTopE pk / 15 - t') + i) * F64.G ^ i := by
  rw [List.sum_map_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [cellVal_append_left (by rw [windowCells_lookup _ _ _ _ hi]; rfl), cellVal, windowCells_lookup _ _ _ _ hi,
    Option.getD_some, window_cells G hw i (by omega), mul_comm]

/-- The top window of `pack-top4`: `Σ_(i<4) b_(15t+i) x^i`. -/
theorem window_top (G : X.Good w) {pk : PackT} {t' : ℕ} (hw : X.windowOk pk t' = true) (h0 : t' = 0)
    (hk : packKOf (packTopE pk) (packTopE pk / 15 - t') = 4) :
    X.val w (pk.windows.getD t' default).2.2 =
      ∑ i ∈ Finset.range 4, X.bitAt w pk.bits (15 * (packTopE pk / 15 - t') + i) * F64.G ^ i := by
  have hw' := hw
  unfold windowOk at hw'
  subst h0
  simp only [Bool.and_eq_true, hk, beq_self_eq_true, Bool.and_self, ite_true, decide_eq_true_eq] at hw'
  obtain ⟨_, ⟨_, _⟩, hg⟩ := hw'
  rw [G.gate hg, eval_top, add_zero]
  have := sum_cells G hw (X.role (pk.windows.getD 0 default).2.2 - 4) 4 (by omega) []
  simp only [List.append_nil] at this
  exact this

/-- A `pack` window: `Σ_(i<15) b_(15t+i) x^i + x^15 · acc`. -/
theorem window_next (G : X.Good w) {pk : PackT} {t' : ℕ} (hw : X.windowOk pk t' = true)
    (ht : t' ≤ packTopE pk / 15) (hk : ¬ (t' = 0 ∧ packKOf (packTopE pk) (packTopE pk / 15 - t') = 4)) :
    ∃ a, (pk.windows.getD t' default).2.1 = some a ∧ (t' = 0 → X.val w a = 0) ∧
      (t' ≠ 0 → a = (pk.windows.getD (t' - 1) default).2.2) ∧
      X.val w (pk.windows.getD t' default).2.2 =
        ∑ i ∈ Finset.range 15, X.bitAt w pk.bits (15 * (packTopE pk / 15 - t') + i) * F64.G ^ i +
          F64.G ^ 15 * X.val w a := by
  have hw' := hw
  unfold windowOk at hw'
  have hc : (t' == 0 && packKOf (packTopE pk) (packTopE pk / 15 - t') == 4) = false := by
    simpa [Bool.and_eq_true, beq_iff_eq] using hk
  simp only [Bool.and_eq_true, hc, Bool.false_eq_true, ite_false] at hw'
  obtain ⟨⟨_, _⟩, hm⟩ := hw'
  revert hm
  cases hacc : (pk.windows.getD t' default).2.1 with
  | none => intro hm; simp at hm
  | some a =>
    intro hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨⟨hfirst, h15⟩, hg⟩ := hm
    refine ⟨a, rfl, ?_, ?_, ?_⟩
    · intro h0; simp only [h0, beq_self_eq_true, ite_true] at hfirst; exact const_val G hfirst
    · intro h0
      have : (t' == 0) = false := by simpa using h0
      simpa [this] using hfirst
    · have hk15' : 15 ≤ packKOf (packTopE pk) (packTopE pk / 15 - t') := by
        unfold packKOf at hc ⊢
        split
        · rename_i hcond
          exfalso
          apply hk
          have hc' := hcond
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
          refine ⟨by omega, ?_⟩
          unfold packKOf
          simp only [hcond, ite_true]
        · exact le_rfl
      rw [G.gate hg, eval_pack, add_zero, List.range_succ, List.map_append, List.sum_append]
      have hs := sum_cells G hw (X.role (pk.windows.getD t' default).2.2 - 15) 15 hk15'
        [(X.role (pk.windows.getD t' default).2.2, a)]
      rw [hs]
      have hb : X.role (pk.windows.getD t' default).2.2 - 15 + 15 = X.role (pk.windows.getD t' default).2.2 := by
        omega
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [hb, cellVal_append_right (by rw [← hb]; exact windowCells_none _ _ _), cellVal_cons_self]

/-- **A checked packing is `Σ_e b_e x^e`.** -/
theorem pack_val (G : X.Good w) {pk : PackT} (h : X.packOk pk = true) :
    X.val w pk.out = ∑ e ∈ Finset.range 64, X.bitAt w pk.bits e * F64.G ^ e := by
  unfold packOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hne, hbits⟩, _⟩, _⟩, hwin⟩, hout⟩ := h
  have htop64 : packTopE pk < 64 := by
    have hall : ∀ q ∈ pk.bits, q.1 < 64 := fun q hq => (hbits q hq).1
    unfold packTopE
    suffices ∀ (L : List (ℕ × ℕ)) (init : ℕ), init < 64 → (∀ q ∈ L, q.1 < 64) →
        L.foldl (fun m t => max m t.1) init < 64 by exact this _ 0 (by norm_num) hall
    intro L
    induction L with
    | nil => intro init h _; simpa using h
    | cons q L ih =>
      intro init hi hq
      simp only [List.foldl_cons]
      exact ih _ (max_lt hi (hq q (by simp))) (fun r hr => hq r (by simp [hr]))
  have hB : ∀ e, packTopE pk < e → X.bitAt w pk.bits e = 0 := by
    intro e he; simp [bitAt, lookup_none_of_gt he]
  -- Window `t'` (from the top, `t = tTop − t'`) holds `Σ_(i < 64 − 15t) b_(15t+i) x^i`.
  have hw : ∀ t' ≤ packTopE pk / 15, X.val w (pk.windows.getD t' default).2.2 =
      ∑ i ∈ Finset.range (64 - 15 * (packTopE pk / 15 - t')),
        X.bitAt w pk.bits (15 * (packTopE pk / 15 - t') + i) * F64.G ^ i := by
    intro t'
    induction t' with
    | zero =>
      intro _
      have hw0 := allBelow_spec hwin 0 (by omega)
      have trunc : ∀ n, packTopE pk - 15 * (packTopE pk / 15) + 1 ≤ n →
          ∑ i ∈ Finset.range n, X.bitAt w pk.bits (15 * (packTopE pk / 15 - 0) + i) * F64.G ^ i =
          ∑ i ∈ Finset.range (64 - 15 * (packTopE pk / 15 - 0)),
            X.bitAt w pk.bits (15 * (packTopE pk / 15 - 0) + i) * F64.G ^ i := by
        intro n hn
        apply sum_range_trunc _ hn (by omega)
        intro i hi
        rw [hB _ (by omega), zero_mul]
      by_cases hk : packKOf (packTopE pk) (packTopE pk / 15 - 0) = 4
      · rw [window_top G hw0 rfl hk]
        apply trunc
        unfold packKOf at hk
        split at hk
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          exact hcond.2
        · omega
      · obtain ⟨a, _, ha0, _, hv⟩ := window_next G hw0 (Nat.zero_le _) (fun h => hk h.2)
        rw [hv, ha0 rfl, mul_zero, add_zero]
        apply trunc
        omega
    | succ t' ih =>
      intro ht
      have hwt := allBelow_spec hwin (t' + 1) (by omega)
      obtain ⟨a, _, _, hprev, hv⟩ := window_next G hwt ht (fun h => absurd h.1 (Nat.succ_ne_zero _))
      rw [hv, hprev (Nat.succ_ne_zero _), Nat.add_sub_cancel, ih (by omega)]
      have e1 : 64 - 15 * (packTopE pk / 15 - (t' + 1)) = 15 + (64 - 15 * (packTopE pk / 15 - t')) := by omega
      rw [e1, Finset.sum_range_add, Finset.mul_sum, add_right_inj]
      apply Finset.sum_congr rfl
      intro i _
      have e2 : 15 * (packTopE pk / 15 - (t' + 1)) + (15 + i) = 15 * (packTopE pk / 15 - t') + i := by omega
      rw [e2, pow_add]; ring
  rw [hout, hw (packTopE pk / 15) le_rfl]
  simp

end Ctx

end RecCircuit
