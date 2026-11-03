-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecPiop.Dataflow
import Heap.Cantor

/-!
# The (block, role) indicators

SPEC-REC.md §2.3, `PI2.md` §1: every (block, role) pair whose formula is not a forward (`pairs`)
has an indicator `I_p`, one on its positions (`InPair`: role `k` of the block's rows) and zero on
the rest of `V_m`. Its positions are a coset of a subspace (an aligned block of rows, one role), so
the product over the **other** positions of `V_m` is constant on it, and

`I_p(X) = Π_{j ∉ p} (X + ω_j) / Π_{j ∉ p} (ω_{c_p} + ω_j)`, `c_p` the pair's first position

is the indicator (`ind_eval_mem`, `ind_eval_not_mem`), of degree at most `N − 2^s`
(`natDegree_ind_le`, `2^s` the block's rows). The verifier evaluates it as
`w_m(t)/(Ẑ_s(t) + Ẑ_s(c_p))` (`pi2::verifier`), the same polynomial (a transcription fact, not
used here).

The points are any `ω : ℕ → F` that is additive in the positions' bits and injective on
`[0, 2^n)` (`Points`), as the Cantor basis's `Heap.omega` is (`Points.ofCantor`). The pairs of a
valid layout cover exactly the positions that are not forwards, each once (`exists_pair`,
`pair_unique`), with the position's role (`role_of_inPair`).
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset Polynomial

variable {F : Type} [Field F] [CharP F 2]

/-- **The points of the positions**: additive in the bits, injective on `[0, 2^n)`. -/
structure Points (ω : ℕ → F) (n : ℕ) : Prop where
  xor : ∀ a b, ω (a ^^^ b) = ω a + ω b
  inj : ∀ a < 2 ^ n, ∀ b < 2 ^ n, ω a = ω b → a = b

/-- **A Cantor basis gives the points** (`Heap.omega_xor`, `Heap.omega_injOn`). -/
theorem Points.ofCantor {n : ℕ} (B : QuotientSecurity.CantorBasis F n) :
    Points (Heap.omega B) n :=
  ⟨Heap.omega_xor B, fun _ ha _ hb h => Heap.omega_injOn B ha hb h⟩

theorem Points.zero {ω : ℕ → F} {n : ℕ} (hP : Points ω n) : ω 0 = 0 := by
  have h := hP.xor 0 0
  rw [Nat.xor_self, CharTwo.add_self_eq_zero] at h
  exact h

theorem Points.add_ne_zero {ω : ℕ → F} {n : ℕ} (hP : Points ω n) {a b : ℕ} (ha : a < 2 ^ n)
    (hb : b < 2 ^ n) (hne : a ≠ b) : ω a + ω b ≠ 0 := fun h =>
  hne (hP.inj a ha b hb (CharTwo.add_eq_zero.mp h))

namespace Circuit

variable (G : Circuit F)

/-! ## The pairs -/

/-- **The (block, role) pairs with an indicator**: every role of every block that is not a
forward. -/
def pairs [DecidableEq F] : Finset (Block × ℕ) :=
  (G.blocks.toFinset ×ˢ range G.W).filter fun p => (G.regionRole p.1 p.2).isForward = false

/-- **The positions of a pair**: role `p.2` of the rows of block `p.1`. -/
def InPair (p : Block × ℕ) (i : ℕ) : Prop := i < G.N ∧ Covers p.1 (i / G.W) ∧ i % G.W = p.2

instance (p : Block × ℕ) (i : ℕ) : Decidable (G.InPair p i) := by
  unfold InPair Covers; infer_instance

/-- A pair's first position, `c_p`. -/
def pairBase (p : Block × ℕ) : ℕ := p.1.row * G.W + p.2

/-- The positions of `V_m` outside a pair. -/
def compl (p : Block × ℕ) : Finset ℕ := (range G.N).filter fun i => ¬ G.InPair p i

/-- **A pair's indicator** `I_p = Π_{j ∉ p} (X + ω_j) / Π_{j ∉ p} (ω_{c_p} + ω_j)`. -/
noncomputable def ind (ω : ℕ → F) (p : Block × ℕ) : F[X] :=
  C (∏ j ∈ G.compl p, (ω (G.pairBase p) + ω j))⁻¹ * ∏ j ∈ G.compl p, (X + C (ω j))

variable {G}

theorem mem_pairs [DecidableEq F] {p : Block × ℕ} :
    p ∈ G.pairs ↔ p.1 ∈ G.blocks ∧ p.2 < G.W ∧ (G.regionRole p.1 p.2).isForward = false := by
  simp [pairs, and_assoc]

theorem N_eq (hV : G.Valid) : G.N = G.rows * G.W := by
  unfold N rows W
  rw [← pow_add, Nat.sub_add_cancel hV.logW_lt.le]

/-- An aligned block covers `y` exactly when `y` and the block's first row agree above bit `s`. -/
theorem covers_iff {b : Block} (hb : 2 ^ b.logRows ∣ b.row) (y : ℕ) :
    Covers b y ↔ y / 2 ^ b.logRows = b.row / 2 ^ b.logRows := by
  obtain ⟨c, hc⟩ := hb
  have hp : 0 < 2 ^ b.logRows := Nat.two_pow_pos _
  unfold Covers
  rw [hc, Nat.mul_div_cancel_left c hp]
  constructor
  · rintro ⟨h1, h2⟩
    refine Nat.div_eq_of_lt_le (by rw [mul_comm]; exact h1) ?_
    rw [Nat.add_mul, one_mul, mul_comm]
    exact h2
  · intro h
    have h1 := Nat.div_mul_le_self y (2 ^ b.logRows)
    have h2 := Nat.lt_div_mul_add (a := y) hp
    rw [h] at h1 h2
    constructor <;> nlinarith

theorem pairBase_inPair [DecidableEq F] (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) :
    G.InPair p (G.pairBase p) := by
  obtain ⟨hb, hk, -⟩ := mem_pairs.mp hp
  have hW : 0 < G.W := Nat.two_pow_pos _
  have hr := hV.in_range _ hb
  have hrow : p.1.row < G.rows := by have := Nat.two_pow_pos p.1.logRows; omega
  have hdiv : G.pairBase p / G.W = p.1.row := by
    unfold pairBase
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hk, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · unfold pairBase
    rw [N_eq hV]
    nlinarith
  · rw [hdiv]
    exact ⟨le_refl _, by have := Nat.two_pow_pos p.1.logRows; omega⟩
  · unfold pairBase
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

/-- **A pair's positions are a coset**: the xor of two of its positions maps the other positions of
`V_m` to themselves. -/
theorem inPair_xor [DecidableEq F] (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) {i i' j : ℕ}
    (hi : G.InPair p i) (hi' : G.InPair p i') (hj : j < G.N) :
    j ^^^ (i ^^^ i') < G.N ∧ (G.InPair p (j ^^^ (i ^^^ i')) ↔ G.InPair p j) := by
  obtain ⟨hb, -, -⟩ := mem_pairs.mp hp
  have hal := hV.aligned _ hb
  have hlt : j ^^^ (i ^^^ i') < G.N :=
    Nat.xor_lt_two_pow hj (Nat.xor_lt_two_pow hi.1 hi'.1)
  refine ⟨hlt, ?_⟩
  have hmod : (j ^^^ (i ^^^ i')) % G.W = j % G.W := by
    unfold W
    rw [Nat.xor_mod_two_pow, Nat.xor_mod_two_pow]
    have e1 : i % 2 ^ G.logW = i' % 2 ^ G.logW := by
      have := hi.2.2; have := hi'.2.2; unfold W at *; omega
    rw [e1, Nat.xor_self, Nat.xor_zero]
  have hdiv : (j ^^^ (i ^^^ i')) / G.W / 2 ^ p.1.logRows = j / G.W / 2 ^ p.1.logRows := by
    unfold W
    rw [Nat.xor_div_two_pow, Nat.xor_div_two_pow, Nat.xor_div_two_pow, Nat.xor_div_two_pow]
    have e1 := (covers_iff hal _).mp hi.2.1
    have e2 := (covers_iff hal _).mp hi'.2.1
    unfold W at e1 e2
    rw [e1, e2, Nat.xor_self, Nat.xor_zero]
  unfold InPair
  rw [covers_iff hal, covers_iff hal, hdiv, hmod]
  exact ⟨fun h => ⟨hj, h.2⟩, fun h => ⟨hlt, h.2⟩⟩

/-! ## The indicator's values -/

variable {ω : ℕ → F} {n : ℕ}

theorem ind_eval_not_mem {p : Block × ℕ} {j : ℕ} (hj : j < G.N) (hn : ¬ G.InPair p j) :
    (G.ind ω p).eval (ω j) = 0 := by
  have hm : j ∈ G.compl p := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hn⟩
  unfold ind
  rw [eval_mul, eval_prod]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hm ?_)
  simp [CharTwo.add_self_eq_zero]

/-- **The indicator is one on its pair**: the product over the other positions is the same at
every position of the coset. -/
theorem ind_eval_mem [DecidableEq F] (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n)
    {p : Block × ℕ} (hp : p ∈ G.pairs) {i : ℕ} (hi : G.InPair p i) :
    (G.ind ω p).eval (ω i) = 1 := by
  have hc := pairBase_inPair hV hp
  have hNn : G.N ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set c := G.pairBase p
  set δ := i ^^^ c
  have hd : ∏ j ∈ G.compl p, (ω c + ω j) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    rw [compl, Finset.mem_filter, Finset.mem_range] at hj
    exact hP.add_ne_zero (by have := hc.1; omega) (by omega) fun h => hj.2 (h ▸ hc)
  have hshift : ∏ j ∈ G.compl p, (ω i + ω j) = ∏ j ∈ G.compl p, (ω c + ω j) := by
    have e : ∀ j, ω i + ω j = ω c + ω (j ^^^ δ) := by
      intro j
      rw [← hP.xor, ← hP.xor]
      congr 1
      simp only [δ]
      rw [Nat.xor_comm j, ← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_comm c i, Nat.xor_assoc i c c,
        Nat.xor_self, Nat.xor_zero]
    simp only [e]
    refine Finset.prod_nbij' (fun j => j ^^^ δ) (fun j => j ^^^ δ) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro j hj
      simp only [compl, Finset.mem_filter, Finset.mem_range] at hj ⊢
      obtain ⟨hlt, hiff⟩ := inPair_xor hV hp hi hc hj.1
      exact ⟨hlt, fun h => hj.2 (hiff.mp h)⟩
    · intro j hj
      simp only [compl, Finset.mem_filter, Finset.mem_range] at hj ⊢
      obtain ⟨hlt, hiff⟩ := inPair_xor hV hp hi hc hj.1
      exact ⟨hlt, fun h => hj.2 (hiff.mp h)⟩
    · intro j _
      simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · intro j _
      simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  unfold ind
  rw [eval_mul, eval_C, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  rw [hshift, inv_mul_cancel₀ hd]

/-! ## The indicator's degree -/

/-- **A pair has at least `2^s` positions**: role `p.2` of each of its block's rows. -/
theorem card_inPair_ge [DecidableEq F] (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) :
    2 ^ p.1.logRows ≤ ((range G.N).filter fun i => G.InPair p i).card := by
  obtain ⟨hb, hk, -⟩ := mem_pairs.mp hp
  have hW : 0 < G.W := Nat.two_pow_pos _
  have hr := hV.in_range _ hb
  have hinj : Set.InjOn (fun u => (p.1.row + u) * G.W + p.2) (range (2 ^ p.1.logRows) : Set ℕ) := by
    intro u _ v _ h
    simp only at h
    have : (p.1.row + u) * G.W = (p.1.row + v) * G.W := by omega
    have := Nat.eq_of_mul_eq_mul_right hW this
    omega
  calc 2 ^ p.1.logRows = ((range (2 ^ p.1.logRows)).image
        fun u => (p.1.row + u) * G.W + p.2).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ _ := by
      refine Finset.card_le_card fun i hi => ?_
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
      rw [Finset.mem_range] at hu
      have hdiv : ((p.1.row + u) * G.W + p.2) / G.W = p.1.row + u := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hk, zero_add]
      have hlt : (p.1.row + u) * G.W + p.2 < G.N := by
        rw [N_eq hV]
        have : p.1.row + u + 1 ≤ G.rows := by omega
        nlinarith
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hlt, ?_, ?_⟩
      · rw [hdiv]; unfold Covers; omega
      · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

/-- **The indicator's degree is at most `N − 2^s`.** -/
theorem natDegree_ind_le [DecidableEq F] (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) :
    (G.ind ω p).natDegree ≤ G.N - 2 ^ p.1.logRows := by
  have hcard : (G.compl p).card ≤ G.N - 2 ^ p.1.logRows := by
    have h := Finset.card_filter_add_card_filter_not (s := range G.N) (G.InPair p)
    rw [Finset.card_range] at h
    have h2 := card_inPair_ge hV hp
    have e : G.compl p = (range G.N).filter fun a => ¬ G.InPair p a := rfl
    rw [e]
    generalize 2 ^ p.1.logRows = S at h2 ⊢
    generalize ((range G.N).filter fun a => ¬ G.InPair p a).card = A at h ⊢
    generalize ((range G.N).filter fun a => G.InPair p a).card = B at h h2
    omega
  unfold ind
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (by rw [Finset.sum_const, smul_eq_mul, mul_one]; exact hcard)
  exact (natDegree_X_add_C _).le

theorem natDegree_ind_le' [DecidableEq F] (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) :
    (G.ind ω p).natDegree ≤ G.N - 1 :=
  (natDegree_ind_le hV hp).trans (Nat.sub_le_sub_left (Nat.one_le_two_pow) _)

/-! ## The pairs cover the positions that are not forwards -/

/-- Two blocks of a valid layout covering one row are the same block. -/
theorem block_unique (hV : G.Valid) {b b' : Block} (hb : b ∈ G.blocks) (hb' : b' ∈ G.blocks)
    {y : ℕ} (hy : Covers b y) (hy' : Covers b' y) : b = b' := by
  by_contra hne
  have : Std.Symm fun b b' : Block =>
      b.row + 2 ^ b.logRows ≤ b'.row ∨ b'.row + 2 ^ b'.logRows ≤ b.row := ⟨fun _ _ h => h.symm⟩
  have := hV.disjoint.forall hb hb' hne
  unfold Covers at hy hy'
  omega

/-- The block covering a row, found. -/
theorem blockAt_eq (hV : G.Valid) {b : Block} (hb : b ∈ G.blocks) {y : ℕ} (hy : Covers b y) :
    G.blockAt y = some b := by
  unfold blockAt
  cases h : G.blocks.find? (fun b => decide (Covers b y)) with
  | none =>
    have := List.find?_eq_none.mp h b hb
    simp only [decide_eq_true_eq] at this
    exact absurd hy this
  | some b' =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    simp only [decide_eq_true_eq] at h1
    rw [block_unique hV h2 hb h1 hy]

/-- **A position of a pair has the pair's role.** -/
theorem role_of_inPair [DecidableEq F] (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) {i : ℕ}
    (hi : G.InPair p i) : G.role i = G.regionRole p.1 p.2 := by
  rw [role_of_blockAt (blockAt_eq hV (mem_pairs.mp hp).1 hi.2.1), hi.2.2]

/-- **Every position that is not a forward is in a pair.** -/
theorem exists_pair [DecidableEq F] {i : ℕ} (hi : i < G.N) (hf : (G.role i).isForward = false) :
    ∃ p ∈ G.pairs, G.InPair p i := by
  cases hb : G.blockAt (i / G.W) with
  | none => rw [role_of_blockAt_none hb] at hf; simp [Role.isForward] at hf
  | some b =>
    rw [role_of_blockAt hb] at hf
    have h1 := List.find?_some hb
    simp only [decide_eq_true_eq] at h1
    refine ⟨(b, i % G.W), mem_pairs.mpr ⟨List.mem_of_find?_eq_some hb,
      Nat.mod_lt _ (Nat.two_pow_pos _), hf⟩, hi, h1, rfl⟩

/-- **A position is in at most one pair.** -/
theorem pair_unique [DecidableEq F] (hV : G.Valid) {p p' : Block × ℕ} (hp : p ∈ G.pairs)
    (hp' : p' ∈ G.pairs) {i : ℕ} (hi : G.InPair p i) (hi' : G.InPair p' i) : p = p' :=
  Prod.ext (block_unique hV (mem_pairs.mp hp).1 (mem_pairs.mp hp').1 hi.2.1 hi'.2.1)
    (hi.2.2.symm.trans hi'.2.2)

/-- **A forward is in no pair.** -/
theorem not_inPair_of_forward [DecidableEq F] (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs)
    {i : ℕ} (hf : (G.role i).isForward = true) : ¬ G.InPair p i := fun hi => by
  rw [role_of_inPair hV hp hi, (mem_pairs.mp hp).2.2] at hf
  exact absurd hf (by decide)

end Circuit

end RecPiop
