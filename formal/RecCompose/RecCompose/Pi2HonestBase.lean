-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The transforms' lemmas are `formal/EndToEnd/Bridge`'s
-- (`Bridge.Ntt.values_getD_E`, `values_coefficients_E`) at `formal/UniComplete`'s Cantor basis (`AlgC.cantorUpTo`,
-- `novX_ofK`, `Ppoint_eq`).
import RecCompose.Pi2Prover

/-!
# π2's honest prover: the transforms, the coset, the stacks

The facts the honest prover's algebra (`Pi2Honest.lean`) reads its computations through:

* **interpolation**: two polynomials of degree below `n` agreeing at `n` distinct points are equal (`poly_eq_of_eval_eq`);
* **the transform** (`PcsQuotient.Domain.values`, `coefficients`): `values k offset c` at `p` is the novel-basis
  polynomial of `c` at `offset + B(p)` (`values_getD_novP`), and the polynomial of `coefficients k offset v` takes `v`
  there (`novP_coefficients_eval`);
* **the coset** `β_{m+2} + V_{m+2}`: its point `p` is `ω_{2^(m+2) ⊕ p}` (`cosetPoint_eq`), a cell moves it by `ω_c`
  (`cosetPoint_xor`), and it is off `V_m` (`cosetPoint_ne`);
* **the stacks**: a public layout reads back the table it placed (`readEntry_placePublic`), at `W`'s and `Q`'s layouts
  (`wTab_place`, `qTable_place`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial

/-! ## Interpolation -/

theorem degree_lt_of_natDegree_lt {p : E[X]} {n : ℕ} (h : p.natDegree < n) : p.degree < n :=
  lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr h)

/-- **Two polynomials of degree below `n` agreeing at `n` distinct points are equal.** -/
theorem poly_eq_of_eval_eq {p q : E[X]} {n : ℕ} (hp : p.natDegree < n) (hq : q.natDegree < n) (f : ℕ → E)
    (hf : ∀ a < n, ∀ b < n, f a = f b → a = b) (h : ∀ i < n, p.eval (f i) = q.eval (f i)) : p = q := by
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ((range n).image f) ?_ ?_
  · rw [card_image_of_injOn (fun a ha b hb hab ↦ hf a (mem_range.mp ha) b (mem_range.mp hb) hab), card_range]
    exact lt_of_le_of_lt (degree_sub_le p q) (max_lt (degree_lt_of_natDegree_lt hp) (degree_lt_of_natDegree_lt hq))
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact h i (mem_range.mp hi)

/-! ## The transform -/

/-- **`values` is the novel-basis polynomial on the coset**: entry `p` of `values k offset c` is `Σ_j c_j X_j` at
`offset + B(p)`. -/
theorem values_getD_novP {k : ℕ} (hk : k ≤ 28) (offset : K) (c : Array E) (hc : c.size = 2 ^ k) {p : ℕ}
    (hp : p < 2 ^ k) :
    (PcsQuotient.Domain.values k offset c).getD p 0 =
      (UniComplete.AlgC.novP k fun j ↦ c.getD j 0).eval (ofK (offset + PcsQuotient.Domain.point p)) := by
  rw [Bridge.Ntt.values_getD_E (UniComplete.AlgC.cantorUpTo hk) hk offset c hc hp, UniComplete.AlgC.novP_eval]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [UniComplete.AlgC.novX_ofK, mul_comm]

/-- **The coefficients' polynomial takes the values**: `Σ_j (coefficients k offset v)_j X_j` is `v_p` at
`offset + B(p)`. -/
theorem novP_coefficients_eval {k : ℕ} (hk : k ≤ 28) (offset : K) (v : Array E) (hv : v.size = 2 ^ k) {p : ℕ}
    (hp : p < 2 ^ k) :
    (UniComplete.AlgC.novP k fun j ↦ (PcsQuotient.Domain.coefficients k offset v).getD j 0).eval
      (ofK (offset + PcsQuotient.Domain.point p)) = v.getD p 0 := by
  rw [← values_getD_novP hk offset _ (by rw [Bridge.Ntt.coefficients_size, hv]) hp,
    Bridge.Ntt.values_coefficients_E k offset v hv]

/-- The statement's point, embedded, is `pi2Omega` below `2^28`. -/
theorem ofK_point_eq {i : ℕ} (hi : i < 2 ^ 28) : ofK (PcsQuotient.Domain.point i) = pi2Omega i := by
  rw [UniComplete.AlgC.Ppoint_eq hi, pi2Omega_eq]
  rfl

/-- **The novel-basis polynomial of an interpolation's coefficients** takes the values on `V_k`. -/
theorem novP_values_omega {k : ℕ} (hk : k ≤ 28) (v : Array E) (hv : v.size = 2 ^ k) {i : ℕ} (hi : i < 2 ^ k) :
    (UniComplete.AlgC.novP k fun j ↦ (UniComplete.novelOfValuesE k v).getD j 0).eval (pi2Omega i) = v.getD i 0 := by
  have h := novP_coefficients_eval hk 0 v hv hi
  rw [zero_add, ofK_point_eq (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk))] at h
  exact h

/-- The same for a `K`-column. -/
theorem novP_valuesK_omega {k : ℕ} (hk : k ≤ 28) (v : Array K) (hv : v.size = 2 ^ k) {i : ℕ} (hi : i < 2 ^ k) :
    (UniComplete.AlgC.novP k fun j ↦ (UniComplete.novelOfValuesK k v).getD j 0).eval (pi2Omega i) =
      ofK (v.getD i 0) := by
  have h := UniComplete.AlgC.pEval_colPolyK_pointE hk v hv hi
  rw [UniComplete.AlgC.pEval_eq, UniComplete.colPolyK, UniComplete.AlgC.ofNovel_toPoly] at h
  rw [pi2Omega_eq]
  exact h

/-! ## The coset -/

theorem xor_lt_pow {a b n : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) : a ^^^ b < 2 ^ n := Nat.xor_lt_two_pow ha hb

/-- **The coset's point `p` is `ω_{2^(m+2) ⊕ p}`.** -/
theorem cosetPoint_eq {m p : ℕ} (hm : m + 2 < 28) (hp : p < 2 ^ (m + 2)) :
    cosetPoint m p = pi2Omega (2 ^ (m + 2) ^^^ p) := by
  have hp28 : p < 2 ^ 28 := lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold cosetPoint cosetOffset
  rw [UniComplete.Domain.embed_add, ← UniComplete.Domain.point_two_pow (by omega), ofK_point_eq hp28, pi2Omega_eq,
    pi2Omega_eq, UniComplete.Domain.pointE_xor]
  rfl

/-- **A cell moves a coset point by `ω_c`.** -/
theorem cosetPoint_xor {m p c : ℕ} (hm : m + 2 < 28) (hp : p < 2 ^ (m + 2)) (hc : c < 2 ^ (m + 2)) :
    cosetPoint m (p ^^^ c) = cosetPoint m p + pi2Omega c := by
  rw [cosetPoint_eq hm (xor_lt_pow hp hc), cosetPoint_eq hm hp, pi2Omega_eq, pi2Omega_eq, pi2Omega_eq,
    ← UniComplete.Domain.pointE_xor, Nat.xor_assoc]

theorem two_pow_xor_testBit {m p : ℕ} (hp : p < 2 ^ (m + 2)) : (2 ^ (m + 2) ^^^ p).testBit (m + 2) = true := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self, Nat.testBit_eq_false_of_lt hp]
  rfl

/-- The coset's indices are distinct. -/
theorem cosetPoint_inj {m : ℕ} (hm : m + 2 < 28) {a b : ℕ} (ha : a < 2 ^ (m + 2)) (hb : b < 2 ^ (m + 2))
    (h : cosetPoint m a = cosetPoint m b) : a = b := by
  rw [cosetPoint_eq hm ha, cosetPoint_eq hm hb] at h
  have h32 : ∀ x < 2 ^ (m + 2), 2 ^ (m + 2) ^^^ x < 2 ^ 32 := fun x hx ↦
    lt_of_lt_of_le (xor_lt_pow (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)) (lt_trans hx
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)))) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have := (RecPiop.Points.ofCantor UniComplete.Domain.basisE).inj _ (h32 a ha) _ (h32 b hb) h
  have e := congrArg (2 ^ (m + 2) ^^^ ·) this
  simpa [← Nat.xor_assoc] using e

/-- **The coset is off `V_m`.** -/
theorem cosetPoint_ne {m p j : ℕ} (hm : m + 2 < 28) (hp : p < 2 ^ (m + 2)) (hj : j < 2 ^ m) :
    cosetPoint m p ≠ pi2Omega j := by
  rw [cosetPoint_eq hm hp]
  intro h
  have h32a : 2 ^ (m + 2) ^^^ p < 2 ^ 32 :=
    lt_of_lt_of_le (xor_lt_pow (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)) (lt_trans hp
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)))) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h32b : j < 2 ^ 32 := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))
  have := (RecPiop.Points.ofCantor UniComplete.Domain.basisE).inj _ h32a _ h32b h
  have hb := two_pow_xor_testBit hp
  rw [this, Nat.testBit_eq_false_of_lt (lt_trans hj (Nat.pow_lt_pow_right (by norm_num) (by omega)))] at hb
  exact absurd hb (by decide)

/-! ## The stacks -/

/-- **A public layout reads back the table it placed**, at an entry whose block one of its lanes holds. -/
theorem readEntry_placePublic (L : PcsQuotient.Layout) (hL : L.logPiece = none) (T : ℕ → K) (i : ℕ)
    (h : PcsQuotient.Lane.block (i / 2 ^ L.logLane) ∈ L.lanes) :
    L.readEntry (fun j ↦ (placePublic L T).getD j 0) i = T i := by
  obtain ⟨l, hl⟩ : ∃ l, L.lanes.findIdx? (· = PcsQuotient.Lane.block (i / 2 ^ L.logLane)) = some l := by
    rw [← Option.isSome_iff_exists, List.findIdx?_isSome]
    exact List.any_eq_true.mpr ⟨_, h, by simp⟩
  obtain ⟨hlen, hget, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hl
  have hpos : 0 < 2 ^ L.logLane := Nat.two_pow_pos _
  have hmod := Nat.mod_lt i hpos
  have hidx : l * 2 ^ L.logLane + i % 2 ^ L.logLane < L.lanes.length * 2 ^ L.logLane := by
    have : (l + 1) * 2 ^ L.logLane ≤ L.lanes.length * 2 ^ L.logLane := Nat.mul_le_mul_right _ hlen
    rw [Nat.add_mul, one_mul] at this
    omega
  have hdiv : (l * 2 ^ L.logLane + i % 2 ^ L.logLane) / 2 ^ L.logLane = l := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hmod, zero_add]
  have hmod' : (l * 2 ^ L.logLane + i % 2 ^ L.logLane) % 2 ^ L.logLane = i % 2 ^ L.logLane := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  have hlane : L.lanes.getD l PcsQuotient.Lane.random = PcsQuotient.Lane.block (i / 2 ^ L.logLane) := by
    rw [List.getD_eq_getElem _ _ hlen]
    simpa using hget
  simp only [PcsQuotient.Layout.readEntry, hL, hl]
  unfold placePublic
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hidx, dite_true, Option.getD_some, hdiv, hmod', hlane]
  rw [Nat.mul_comm, Nat.div_add_mod]

theorem placePublic_logPiece (vars lc logN : ℕ) (chunks : List (ℕ × ℕ)) :
    (PcsQuotient.Layout.ofChunks vars lc logN chunks).logPiece = none := rfl

/-- A chunk's lanes: a public layout of chunks of `2^lc` (its lanes at most a chunk) holds the block of every entry
of a listed chunk. -/
theorem block_mem_ofChunks {vars lc logN : ℕ} {chunks : List (ℕ × ℕ)} (hlane : logN - PcsQuotient.laneFold ≤ lc)
    {c : ℕ} (hc : (c, 2 ^ lc) ∈ chunks) {i : ℕ} (hi : i / 2 ^ lc = c) :
    PcsQuotient.Lane.block (i / 2 ^ (PcsQuotient.Layout.ofChunks vars lc logN chunks).logLane) ∈
      (PcsQuotient.Layout.ofChunks vars lc logN chunks).lanes := by
  obtain ⟨d, hd⟩ : ∃ d, lc = (logN - PcsQuotient.laneFold) + d := ⟨lc - (logN - PcsQuotient.laneFold), by omega⟩
  set a := logN - PcsQuotient.laneFold with ha
  have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
  have hll : (PcsQuotient.Layout.ofChunks vars lc logN chunks).logLane = a := rfl
  rw [hll]
  simp only [PcsQuotient.Layout.ofChunks, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨(c, 2 ^ lc), hc, (i % 2 ^ lc) / 2 ^ a, ?_, ?_⟩
  · have hcount : (2 ^ lc + 2 ^ a - 1) / 2 ^ a = 2 ^ d := by
      rw [hd, pow_add]
      have : 2 ^ a * 2 ^ d + 2 ^ a - 1 = 2 ^ d * 2 ^ a + (2 ^ a - 1) := by
        have : 1 ≤ 2 ^ a := hpos; rw [mul_comm]; omega
      rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), zero_add]
    rw [← ha, hcount]
    rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, show d + a = lc by omega]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · congr 1
    have hd' : lc - a = d := by omega
    have hpow : 2 ^ lc = 2 ^ a * 2 ^ d := by rw [hd, pow_add]
    have h0 := Nat.mod_add_div i (2 ^ lc)
    rw [hi] at h0
    rw [hd']
    generalize i % 2 ^ lc = r at h0 ⊢
    subst h0
    rw [hpow, Nat.mul_assoc, Nat.add_mul_div_left _ _ hpos]
    ring

end RecCompose

/-- info: 'RecCompose.readEntry_placePublic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.readEntry_placePublic

/-- info: 'RecCompose.cosetPoint_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.cosetPoint_ne

/-- info: 'RecCompose.novP_coefficients_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.novP_coefficients_eval
