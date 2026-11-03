-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.AlgCBasis

/-!
# A quotient's chunks, as the verifier reads them (milestone 4, the algebra, item 1(a))

A quotient `Q` of degree `< Σ_k 2^(e_k)` is sent as its novel coefficients cut at the sizes `2^(e_k)`, each chunk in
basis `B` (`chunksB`); the verifier reads it at `t` as `Q_0(t) + w_{e_0}(t) (Q_1(t) + w_{e_1}(t) Q_2(t))`
(`quotientTerms`, `atTOf`'s `constraintValue`, here `chunksValue`). Here:

* **`chunks_eq`**: the verifier's `chunks n` (its loop of four steps) is `chunksSpec n`: `[a]`, `[a, b]` or
  `[a, b, c]` with `a = ⌊log₂ n⌋`, `b < a`, `c ≤ b` (**`chunks_shape`**, `ChunkShape`), covering `n`
  (**`chunks_cover`**: `n ≤ Σ 2^e`), every size at most `⌊log₂ n⌋` (**`chunks_le_log2`**).
* **`chunksValue_chunksB`**: for sizes of that shape and `deg Q < Σ 2^e`, the verifier's value of the chunks at the
  digits of `t` is `Q(t)` (the novel coefficients past the degree vanish, `novP_eq_zero_above`; the chunk at offset
  `2^(e_0) + …` is `w_{e_0} …` times its own novel polynomial since the sizes decrease).
-/

namespace UniComplete.AlgC

open UniStatement LeanVM.Parameters Polynomial Finset

/-! ### `log2Ceil` -/

theorem log2Ceil_two_pow (a : ℕ) : log2Ceil (2 ^ a) = a := by
  unfold log2Ceil
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rfl
  · have h2a : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    rw [Domain.ite_neg_of (by omega : ¬ 2 ^ a ≤ 1)]
    have h3 : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
    have h4 := Nat.one_le_two_pow (n := a - 1)
    have h2 : (2 ^ a - 1).log2 = a - 1 :=
      (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by rw [show a - 1 + 1 = a by omega]; omega⟩
    rw [h2]
    omega

theorem log2Ceil_of_lt_le {a v : ℕ} (h1 : 2 ^ a < v) (h2 : v ≤ 2 ^ (a + 1)) : log2Ceil v = a + 1 := by
  unfold log2Ceil
  have ha := Nat.one_le_two_pow (n := a)
  rw [Domain.ite_neg_of (by omega : ¬ v ≤ 1)]
  have : (v - 1).log2 = a := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
  rw [this]

/-! ### The verifier's chunk sizes -/

/-- **`chunks n`, closed form**: the top power of two, the next, and the rest rounded up to a power of two. -/
def chunksSpec (n : ℕ) : List ℕ :=
  if n = 0 then [] else
  if n - 2 ^ n.log2 = 0 then [n.log2] else
  if n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2 = 0 then [n.log2, (n - 2 ^ n.log2).log2] else
  if n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2 = 2 ^ (n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2).log2 then
    [n.log2, (n - 2 ^ n.log2).log2, (n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2).log2]
  else [n.log2, (n - 2 ^ n.log2).log2, (n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2).log2 + 1]

theorem chunks_eq (n : ℕ) : chunks n = chunksSpec n := by
  unfold chunks chunksSpec
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range', List.forIn_cons,
    List.forIn_nil]
  by_cases h0 : n = 0
  · subst h0
    simp
    rfl
  · have hn : 0 < n := Nat.pos_of_ne_zero h0
    by_cases h1 : n - 2 ^ n.log2 = 0
    · simp [h0, hn, h1]
      rfl
    · by_cases h2 : n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2 = 0
      · simp [h0, hn, h1, h2, Nat.pos_of_ne_zero h1]
        rfl
      · by_cases h3 : n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2 =
            2 ^ (n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2).log2
        · simp [h0, hn, h1, h2, h3.symm, Nat.pos_of_ne_zero h1, Nat.pos_of_ne_zero h2]
          rfl
        · simp [h0, hn, h1, h2, h3, Nat.pos_of_ne_zero h1, Nat.pos_of_ne_zero h2]
          rfl

/-- **The shapes of the chunk sizes**: one size; two, decreasing; three, the first two decreasing and the last at
most the second. -/
def ChunkShape (sizes : List ℕ) : Prop :=
  (∃ a, sizes = [a]) ∨ (∃ a b, sizes = [a, b] ∧ b < a) ∨ (∃ a b c, sizes = [a, b, c] ∧ b < a ∧ c ≤ b)

theorem log2_facts {n : ℕ} (hn : n ≠ 0) : 2 ^ n.log2 ≤ n ∧ n < 2 * 2 ^ n.log2 := by
  refine ⟨Nat.log2_self_le hn, ?_⟩
  have := Nat.lt_log2_self (n := n)
  rwa [pow_succ, mul_comm] at this

/-- **`chunks n`**: its shape, its cover `n ≤ Σ 2^e`, its sizes at most `⌊log₂ n⌋` (`n ≥ 1`). -/
theorem chunks_spec {n : ℕ} (hn : n ≠ 0) :
    ChunkShape (chunks n) ∧ n ≤ ((chunks n).map (2 ^ ·)).sum ∧ ∀ e ∈ chunks n, e ≤ n.log2 := by
  rw [chunks_eq]
  unfold chunksSpec
  obtain ⟨ha1, ha2⟩ := log2_facts hn
  rw [Domain.ite_neg_of hn]
  by_cases h1 : n - 2 ^ n.log2 = 0
  · rw [Domain.ite_pos_of h1]
    exact ⟨Or.inl ⟨_, rfl⟩, by simp; omega, by simp⟩
  · rw [Domain.ite_neg_of h1]
    obtain ⟨hb1, hb2⟩ := log2_facts h1
    have hba : (n - 2 ^ n.log2).log2 < n.log2 := by
      rw [Nat.log2_lt h1]
      have := Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.le_refl n.log2)
      omega
    by_cases h2 : n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2 = 0
    · rw [Domain.ite_pos_of h2]
      exact ⟨Or.inr (Or.inl ⟨_, _, rfl, hba⟩), by simp; omega, by simp; omega⟩
    · rw [Domain.ite_neg_of h2]
      obtain ⟨hc1, hc2⟩ := log2_facts h2
      have hcb : (n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2).log2 < (n - 2 ^ n.log2).log2 := by
        rw [Nat.log2_lt h2]
        omega
      by_cases h3 : n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2 =
          2 ^ (n - 2 ^ n.log2 - 2 ^ (n - 2 ^ n.log2).log2).log2
      · rw [Domain.ite_pos_of h3]
        exact ⟨Or.inr (Or.inr ⟨_, _, _, rfl, hba, hcb.le⟩), by simp; omega, by simp; omega⟩
      · rw [Domain.ite_neg_of h3]
        refine ⟨Or.inr (Or.inr ⟨_, _, _, rfl, hba, hcb⟩), ?_, by simp; omega⟩
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_succ]
        omega

/-- `chunks n` is never empty for `n ≥ 1`. -/
theorem chunks_ne_nil {n : ℕ} (hn : n ≠ 0) : chunks n ≠ [] := by
  obtain ⟨hs, -, -⟩ := chunks_spec hn
  rcases hs with ⟨a, h⟩ | ⟨a, b, h, -⟩ | ⟨a, b, c, h, -⟩ <;> rw [h] <;> simp

/-! ### The chunks' value -/

/-- **The verifier's value of a quotient from its chunks** at the digits `w` (`atTOf`'s `constraintValue`,
`quotientTerms` at scale `1`): `Q_0(t) + w_{e_0}(Q_1(t) + w_{e_1} Q_2(t))`. -/
def chunksValue (cs : List (Array E)) (sizes : List ℕ) (w : List E) : E :=
  ((cs.zip sizes).foldl (fun (acc : E × E) (x : Array E × ℕ) ↦
    (acc.1 + acc.2 * evalB x.1 x.2 w, acc.2 * w.getD x.2 0)) (0, 1)).1

/-- The chunk of `2^e` novel coefficients at `off`. -/
def chunkAt (novel : Array E) (off e : ℕ) : Array E := Array.ofFn (n := 2 ^ e) fun i ↦ novel.getD (off + i.val) 0

theorem chunkAt_size (novel : Array E) (off e : ℕ) : (chunkAt novel off e).size = 2 ^ e := by simp [chunkAt]

theorem chunkAt_getD (novel : Array E) (off e : ℕ) {i : ℕ} (hi : i < 2 ^ e) :
    (chunkAt novel off e).getD i 0 = novel.getD (off + i) 0 := by
  simp [chunkAt, Array.getD_eq_getD_getElem?, hi]

/-- **A chunk's value at the digits** is its novel polynomial at `t`. -/
theorem evalB_chunk (novel : Array E) (off e n : ℕ) (hen : e ≤ n) (t : E) :
    evalB (subsetSumsE e (chunkAt novel off e)) e (digits t n) =
      (novP e (fun i ↦ novel.getD (off + i) 0)).eval t := by
  rw [evalB_subsetSumsE e n _ (chunkAt_size _ _ _) hen, pEval_eq, ofNovel_toPoly,
    novP_congr e (fun i hi ↦ chunkAt_getD novel off e hi)]

theorem chunksB_one (q : Poly) (a : ℕ) :
    chunksB q [a] = [subsetSumsE a (chunkAt (toNovel (log2Ceil (2 ^ a + 0)) q) 0 a)] := rfl

theorem chunksB_two (q : Poly) (a b : ℕ) :
    chunksB q [a, b] = [subsetSumsE a (chunkAt (toNovel (log2Ceil (2 ^ a + (2 ^ b + 0))) q) 0 a),
      subsetSumsE b (chunkAt (toNovel (log2Ceil (2 ^ a + (2 ^ b + 0))) q) (0 + 2 ^ a) b)] := rfl

theorem chunksB_three (q : Poly) (a b c : ℕ) :
    chunksB q [a, b, c] =
      [subsetSumsE a (chunkAt (toNovel (log2Ceil (2 ^ a + (2 ^ b + (2 ^ c + 0)))) q) 0 a),
        subsetSumsE b (chunkAt (toNovel (log2Ceil (2 ^ a + (2 ^ b + (2 ^ c + 0)))) q) (0 + 2 ^ a) b),
        subsetSumsE c (chunkAt (toNovel (log2Ceil (2 ^ a + (2 ^ b + (2 ^ c + 0)))) q) (0 + 2 ^ a + 2 ^ b) c)] :=
  rfl

theorem digit_eq (t : E) {e n : ℕ} (hen : e < n) : (digits t n).getD e 0 = (Domain.wP e).eval t :=
  (Domain.wP_eval_digits t hen).symm

/-- **The chunks of `Q` read at `t` give `Q(t)`**: for sizes of the verifier's shape, `deg Q < Σ 2^e`, and digits
past every size. -/
theorem chunksValue_chunksB (q : Poly) (sizes : List ℕ) (hs : ChunkShape sizes)
    (hdeg : q.toPoly.natDegree < (sizes.map (2 ^ ·)).sum) (t : E) (n : ℕ) (hn : ∀ e ∈ sizes, e < n) :
    chunksValue (chunksB q sizes) sizes (digits t n) = pEval t q := by
  rcases hs with ⟨a, rfl⟩ | ⟨a, b, rfl, hba⟩ | ⟨a, b, c, rfl, hba, hcb⟩
  · -- one chunk
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hdeg
    have hL : log2Ceil (2 ^ a + 0) = a := by rw [add_zero, log2Ceil_two_pow]
    rw [chunksB_one, hL]
    obtain ⟨-, hq⟩ := toNovel_spec a q (by omega)
    simp only [chunksValue, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, zero_add,
      one_mul]
    rw [evalB_chunk _ _ _ _ (by have := hn a (by simp); omega), pEval_eq, ← hq]
    simp only [zero_add]
  · -- two chunks
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hdeg
    have hab : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) hba
    have hL : log2Ceil (2 ^ a + (2 ^ b + 0)) = a + 1 := by
      rw [add_zero]
      exact log2Ceil_of_lt_le (by have := Nat.one_le_two_pow (n := b); omega) (by rw [pow_succ]; omega)
    rw [chunksB_two, hL]
    set novel := toNovel (a + 1) q
    obtain ⟨-, hq⟩ := toNovel_spec (a + 1) q (by rw [pow_succ]; omega)
    have ha := hn a (by simp)
    have hb := hn b (by simp)
    simp only [chunksValue, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, zero_add,
      one_mul]
    rw [evalB_chunk _ _ _ _ (by omega), evalB_chunk _ _ _ _ (by omega), digit_eq t ha, pEval_eq, ← hq, novP_succ,
      Polynomial.eval_add, Polynomial.eval_mul]
    have hz : ∀ k, 2 ^ b ≤ k → k < 2 ^ a → novel.getD (2 ^ a + k) 0 = 0 := fun k hk hka ↦
      novP_eq_zero_above (a + 1) (fun k ↦ novel.getD k 0) (2 ^ a + 2 ^ b)
        (by rw [hq]; exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hdeg)) _ (by omega)
        (by rw [pow_succ]; omega)
    rw [novP_of_zero_above a _ hba.le hz]
    simp only [zero_add]
    rfl
  · -- three chunks
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hdeg
    have hdeg3 : q.toPoly.natDegree < 2 ^ a + 2 ^ b + 2 ^ c := by omega
    have hab : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) hba
    have hab' : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hba
    have hcb' : 2 ^ c ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hcb
    have hL : log2Ceil (2 ^ a + (2 ^ b + (2 ^ c + 0))) = a + 1 := by
      rw [add_zero]
      have hb1 := Nat.one_le_two_pow (n := b)
      have hc1 := Nat.one_le_two_pow (n := c)
      exact log2Ceil_of_lt_le (by omega) (by rw [pow_succ] at hab' ⊢; omega)
    rw [chunksB_three, hL]
    set novel := toNovel (a + 1) q
    obtain ⟨-, hq⟩ := toNovel_spec (a + 1) q (by rw [pow_succ] at hab' ⊢; omega)
    have ha := hn a (by simp)
    have hb := hn b (by simp)
    have hc := hn c (by simp)
    simp only [chunksValue, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, zero_add,
      one_mul]
    rw [evalB_chunk _ _ _ _ (by omega), evalB_chunk _ _ _ _ (by omega), evalB_chunk _ _ _ _ (by omega),
      digit_eq t ha, digit_eq t hb, pEval_eq, ← hq, novP_succ, Polynomial.eval_add, Polynomial.eval_mul]
    have hzero : ∀ k, 2 ^ a + 2 ^ b + 2 ^ c ≤ k → k < 2 ^ (a + 1) → novel.getD k 0 = 0 := fun k hk hka ↦
      novP_eq_zero_above (a + 1) (fun k ↦ novel.getD k 0) (2 ^ a + 2 ^ b + 2 ^ c)
        (by rw [hq]; exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hdeg3))
        k hk hka
    have h1 : novP a (fun k ↦ novel.getD (2 ^ a + k) 0) = novP (b + 1) (fun k ↦ novel.getD (2 ^ a + k) 0) :=
      novP_of_zero_above a _ hba (fun k hk hka ↦ hzero _ (by rw [pow_succ] at hk; omega)
        (by rw [pow_succ]; omega))
    have h2 : novP b (fun k ↦ novel.getD (2 ^ a + (2 ^ b + k)) 0) =
        novP c (fun k ↦ novel.getD (2 ^ a + (2 ^ b + k)) 0) :=
      novP_of_zero_above b _ hcb (fun k hk hkb ↦ hzero _ (by omega) (by rw [pow_succ]; omega))
    rw [h1, novP_succ, h2, Polynomial.eval_add, Polynomial.eval_mul,
      novP_congr c (d := fun k ↦ novel.getD (2 ^ a + (2 ^ b + k)) 0)
        (d' := fun k ↦ novel.getD (2 ^ a + 2 ^ b + k) 0) (fun k _ ↦ by rw [Nat.add_assoc])]
    simp only [zero_add]
    ring

end UniComplete.AlgC

/-- info: 'UniComplete.AlgC.chunks_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.chunks_spec

/-- info: 'UniComplete.AlgC.chunksValue_chunksB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.chunksValue_chunksB
