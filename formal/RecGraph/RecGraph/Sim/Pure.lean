-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Chan

/-!
# The simulation: the pure helpers

Each of `Pi1/Ops.lean`'s pure helpers (no byte read, no challenge drawn) from a state with the recorder's invariants
(`Good`) and its operands represented (`Rp`, `RpL`): a pure step whose output represents `UniStatement`'s function
of the operands' values (`PSim`, `Sim/Chan.lean`):

* `sum_psim` (`esum`), `dot_psim`, `eqEval_psim`, `polyEval_psim` (Horner from the top, `foldr`), `pow_psim`
  (`epow`, an exponent below `2^64`: the Rust's 65 rounds of square and multiply, against `epowAux`'s fuel),
  `pairPoint_psim`;
* `eqKernel_psim`: the Rust's in-place doubling (`out[i + 2^k] = out[i] r_k`, `out[i] += out[i + 2^k]`) against
  `UniStatement.eqKernel`'s `out.map (· * (1 + r)) ++ out.map (· * r)`, entry for entry (`v + v r = v (1 + r)`);
* `squares_psim`, `digits_psim`, `coordinatesAt_psim`, `vanishingRatio_psim`, `activeVanishingFromBits_psim`.

The values are `E`'s operations on the operands' values (`PSim.add`, `PSim.mul`, … from `op_pstep`), so each
identity is `ring` in `E`, or `rfl`.
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

section Pure

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-! ## Lists and arrays of nodes -/

theorem RpL.length {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) :
    is.length = xs.length :=
  List.Forall₂.length_eq h

theorem RpL.get {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) (i : Nat)
    (hi : i < is.length) (hj : i < xs.length) : Rp π iv publicInput stream st is[i] xs[i] := by
  have := (List.forall₂_iff_get.mp h).2 i hi hj
  simpa using this

/-- Arrays entry for entry. -/
theorem rpL_of_getD {st : RecState} {a : Array Nat} {b : Array E} (hs : a.size = b.size)
    (h : ∀ j < a.size, Rp π iv publicInput stream st (a.getD j 0) (b.getD j 0)) :
    RpL π iv publicInput stream st a.toList b.toList := by
  refine List.forall₂_iff_get.mpr ⟨by simp [hs], fun i h1 h2 ↦ ?_⟩
  have hi : i < a.size := by simpa using h1
  have hi' : i < b.size := by simpa using h2
  have := h i hi
  simp only [Array.getD, hi, hi', ↓reduceDIte] at this
  simpa using this

theorem getD_set! (a : Array Nat) (i j v : Nat) :
    (a.set! i v).getD j 0 = if i = j ∧ i < a.size then v else a.getD j 0 := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem size_set! (a : Array Nat) (i v : Nat) : (a.set! i v).size = a.size := by
  simp [Array.set!]

/-! The constants, the section's variables named (no operand fixes them). -/

theorem constP (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) {st : RecState}
    (hg : Good st) (x : E) : PSim st (Pi1.const x) x (Rp π iv publicInput stream) := PSim.const hg x

theorem zeroP (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) {st : RecState}
    (hg : Good st) : PSim st Pi1.zero 0 (Rp π iv publicInput stream) := PSim.zero hg

theorem oneP (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) {st : RecState}
    (hg : Good st) : PSim st Pi1.one 1 (Rp π iv publicInput stream) := PSim.one hg

/-! ## Sums, products, polynomials -/

/-- **`Scalar::sum`** is `esum`. -/
theorem sum_psim (st : RecState) (hg : Good st) {vs : List Nat} {xs : List E}
    (hv : RpL π iv publicInput stream st vs xs) :
    PSim st (Pi1.sum vs) (esum xs) (Rp π iv publicInput stream) := by
  have hlen := hv.length
  unfold Pi1.sum
  refine PSim.bind (zeroP π iv publicInput stream hg) fun st1 z hst1 hz ↦ ?_
  refine PSim.bind (PSim.forIn_list st1 vs xs (fun _ st (s : Nat) (t : E) ↦ Rp π iv publicInput stream st s t) _
    (· + ·) hlen ?_ st1 z 0 (PStep.refl st1 hst1.good) hz) fun st2 a hst2 ha ↦ PSim.pure hst2.good ha
  intro i hi hj st' s t hst' hI
  have hx := (hv.get i hi hj).pgrow hg (hst1.trans hst')
  exact PSim.bind (PSim.add hst'.good hI hx) fun st'' q hst'' hq ↦ PSim.pure hst''.good ⟨q, rfl, hq⟩

theorem dot_eq (xs ys : List E) : UniStatement.dot xs ys = (xs.zip ys).foldl (fun acc p ↦ acc + p.1 * p.2) 0 := by
  unfold UniStatement.dot
  congr 1

theorem eqEval_eq (xs ys : List E) :
    UniStatement.eqEval xs ys = (xs.zip ys).foldl (fun acc p ↦ acc * (1 + p.1 + p.2)) 1 := by
  unfold UniStatement.eqEval
  congr 1

/-- **`dot(left, right)`**. -/
theorem dot_psim (st : RecState) (hg : Good st) {ls rs : List Nat} {xs ys : List E}
    (hl : RpL π iv publicInput stream st ls xs) (hr : RpL π iv publicInput stream st rs ys) :
    PSim st (Pi1.dot ls rs) (UniStatement.dot xs ys) (Rp π iv publicInput stream) := by
  have hlen : (ls.zip rs).length = (xs.zip ys).length := by simp [hl.length, hr.length]
  rw [dot_eq]
  unfold Pi1.dot
  refine PSim.bind (zeroP π iv publicInput stream hg) fun st1 z hst1 hz ↦ ?_
  refine PSim.bind (PSim.forIn_list st1 (ls.zip rs) (xs.zip ys)
    (fun _ st (s : Nat) (t : E) ↦ Rp π iv publicInput stream st s t) _ (fun acc p ↦ acc + p.1 * p.2) hlen ?_ st1 z 0
    (PStep.refl st1 hst1.good) hz) fun st2 a hst2 ha ↦ PSim.pure hst2.good ha
  intro i hi hj st' s t hst' hI
  simp only [List.getElem_zip]
  simp only [List.length_zip] at hi hj
  have h1 := (hl.get i (by omega) (by omega)).pgrow hg (hst1.trans hst')
  have h2 := (hr.get i (by omega) (by omega)).pgrow hg (hst1.trans hst')
  refine PSim.bind (PSim.mul hst'.good h1 h2) fun st'' p hst'' hp ↦ ?_
  exact PSim.bind (PSim.add hst''.good (hI.pgrow hst'.good hst'') hp) fun st''' q hst''' hq ↦
    PSim.pure hst'''.good ⟨q, rfl, hq⟩

/-- **`eq_eval(left, right) = Π (1 + x + y)`**. -/
theorem eqEval_psim (st : RecState) (hg : Good st) {ls rs : List Nat} {xs ys : List E}
    (hl : RpL π iv publicInput stream st ls xs) (hr : RpL π iv publicInput stream st rs ys) :
    PSim st (Pi1.eqEval ls rs) (UniStatement.eqEval xs ys) (Rp π iv publicInput stream) := by
  have hlen : (ls.zip rs).length = (xs.zip ys).length := by simp [hl.length, hr.length]
  rw [eqEval_eq]
  unfold Pi1.eqEval
  refine PSim.bind (oneP π iv publicInput stream hg) fun st1 z hst1 hz ↦ ?_
  refine PSim.bind (PSim.forIn_list st1 (ls.zip rs) (xs.zip ys)
    (fun _ st (s : Nat) (t : E) ↦ Rp π iv publicInput stream st s t) _ (fun acc p ↦ acc * (1 + p.1 + p.2)) hlen ?_
    st1 z 1 (PStep.refl st1 hst1.good) hz) fun st2 a hst2 ha ↦ PSim.pure hst2.good ha
  intro i hi hj st' s t hst' hI
  simp only [List.getElem_zip]
  simp only [List.length_zip] at hi hj
  have h1 := (hl.get i (by omega) (by omega)).pgrow hg (hst1.trans hst')
  have h2 := (hr.get i (by omega) (by omega)).pgrow hg (hst1.trans hst')
  refine PSim.bind (oneP π iv publicInput stream hst'.good) fun s1 o hs1 ho ↦ ?_
  refine PSim.bind (PSim.add hs1.good ho (h1.pgrow hst'.good hs1)) fun s2 a ha2 ha ↦ ?_
  refine PSim.bind (PSim.add ha2.good ha ((h2.pgrow hst'.good hs1).pgrow hs1.good ha2)) fun s3 b hb3 hb ↦ ?_
  have hI3 := ((hI.pgrow hst'.good hs1).pgrow hs1.good ha2).pgrow ha2.good hb3
  exact PSim.bind (PSim.mul hb3.good hI3 hb) fun s4 q hq4 hq ↦ PSim.pure hq4.good ⟨q, rfl, hq⟩

theorem polyEval_eq (xs : List E) (x : E) :
    UniStatement.polyEval xs x = xs.reverse.foldl (fun acc c ↦ acc * x + c) 0 := by
  rw [List.foldl_reverse]
  rfl

/-- **`poly_eval(coefficients, x)`**: Horner from `S::zero()`, the highest coefficient first. -/
theorem polyEval_psim (st : RecState) (hg : Good st) {cs : List Nat} {xs : List E} {a : Nat} {x : E}
    (hc : RpL π iv publicInput stream st cs xs) (ha : Rp π iv publicInput stream st a x) :
    PSim st (Pi1.polyEval cs a) (UniStatement.polyEval xs x) (Rp π iv publicInput stream) := by
  have hrev : RpL π iv publicInput stream st cs.reverse xs.reverse := List.rel_reverse hc
  rw [polyEval_eq]
  unfold Pi1.polyEval
  refine PSim.bind (zeroP π iv publicInput stream hg) fun st1 z hst1 hz ↦ ?_
  refine PSim.bind (PSim.forIn_list st1 cs.reverse xs.reverse
    (fun _ st (s : Nat) (t : E) ↦ Rp π iv publicInput stream st s t) _ (fun acc c ↦ acc * x + c) hrev.length ?_
    st1 z 0 (PStep.refl st1 hst1.good) hz) fun st2 b hst2 hb ↦ PSim.pure hst2.good hb
  intro i hi hj st' s t hst' hI
  have h1 := (hrev.get i hi hj).pgrow hg (hst1.trans hst')
  have hx := ha.pgrow hg (hst1.trans hst')
  refine PSim.bind (PSim.mul hst'.good hI hx) fun st'' p hst'' hp ↦ ?_
  exact PSim.bind (PSim.add hst''.good hp (h1.pgrow hst'.good hst'')) fun st''' q hst''' hq ↦
    PSim.pure hst'''.good ⟨q, rfl, hq⟩

/-- **`pair_point(z)`**: `[z + β_1 (z² + z), z² + z]`. -/
theorem pairPoint_psim (st : RecState) (hg : Good st) {a : Nat} {z : E} (ha : Rp π iv publicInput stream st a z) :
    PSim st (Pi1.pairPoint a) (UniStatement.pairPoint z) (RpL π iv publicInput stream) := by
  unfold Pi1.pairPoint
  refine PSim.bind (PSim.square hg ha) fun s1 zz h1 hzz ↦ ?_
  refine PSim.bind (PSim.add h1.good hzz (ha.pgrow hg h1)) fun s2 y1 h2 hy1 ↦ ?_
  refine PSim.bind (constP π iv publicInput stream h2.good cantorBeta1) fun s3 b h3 hb ↦ ?_
  refine PSim.bind (PSim.mul h3.good hb (hy1.pgrow h2.good h3)) fun s4 p h4 hp ↦ ?_
  have ha4 := ((ha.pgrow hg h1).pgrow h1.good h2 |>.pgrow h2.good h3).pgrow h3.good h4
  refine PSim.bind (PSim.add h4.good ha4 hp) fun s5 y0 h5 hy0 ↦ PSim.pure h5.good ?_
  exact List.Forall₂.cons hy0 (List.Forall₂.cons (((hy1.pgrow h2.good h3).pgrow h3.good h4).pgrow h4.good h5)
    List.Forall₂.nil)

/-! ## `Scalar::pow` -/

theorem epowAux_fuel (b o : E) (n f f' : Nat) (hf : n < 2 ^ f) (hf' : n < 2 ^ f') :
    epowAux f b o n = epowAux f' b o n := by
  induction f generalizing f' b o n with
  | zero =>
    have hn : n = 0 := by simp at hf; omega
    subst hn
    cases f' <;> simp [epowAux]
  | succ f ih =>
    cases f' with
    | zero =>
      have hn : n = 0 := by simp at hf'; omega
      subst hn
      simp [epowAux]
    | succ f' =>
      simp only [epowAux]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        apply ih
        · rw [Nat.pow_succ] at hf; omega
        · rw [Nat.pow_succ] at hf'; omega

/-- **The square-and-multiply loop** (`Pi1.pow`'s body, by its shape), against `epowAux` with as much fuel as rounds. -/
theorem pow_loop (body : Nat → Nat × Nat × Nat → Prog (ForInStep (Nat × Nat × Nat)))
    (hb : ∀ i s, body i s = if s.2.2 = 0 then pure (ForInStep.done (s.1, s.2.1, s.2.2)) else
      if s.2.2 % 2 = 1 then
        Pi1.mul s.2.1 s.1 >>= fun out ↦
          (Pi1.square s.1 >>= fun base ↦ pure (ForInStep.yield (base, out, s.2.2 / 2)))
      else Pi1.square s.1 >>= fun base ↦ pure (ForInStep.yield (base, s.2.1, s.2.2 / 2))) :
    ∀ (m a : Nat) (st : RecState) (base out n : Nat) (b o : E), Good st →
      Rp π iv publicInput stream st base b → Rp π iv publicInput stream st out o → n < 2 ^ m →
      PSim st (forIn (List.range' a m) (base, out, n) body) (epowAux m b o n)
        (fun st' s v ↦ Rp π iv publicInput stream st' s.2.1 v) := by
  intro m
  induction m with
  | zero =>
    intro a st base out n b o hg _ ho _
    simp only [List.range'_zero, List.forIn_nil]
    exact PSim.pure hg ho
  | succ m ih =>
    intro a st base out n b o hg hb' ho hn
    rw [List.range'_succ, List.forIn_cons, hb]
    simp only [epowAux]
    by_cases h0 : n = 0
    · simp only [h0, ↓reduceIte]
      exact PSim.pure hg ho
    · simp only [h0, ↓reduceIte]
      have hn' : n / 2 < 2 ^ m := by rw [Nat.pow_succ] at hn; omega
      by_cases h1 : n % 2 = 1
      · simp only [h1, ↓reduceIte]
        rw [prog_bind_assoc]
        refine PSim.bind (PSim.mul hg ho hb') fun s1 out' hs1 ho' ↦ ?_
        rw [prog_bind_assoc]
        refine PSim.bind (PSim.square hs1.good (hb'.pgrow hg hs1)) fun s2 base' hs2 hb2 ↦ ?_
        exact ih (a + 1) s2 base' out' (n / 2) (b * b) (o * b) hs2.good hb2 (ho'.pgrow hs1.good hs2) hn'
      · simp only [h1, ↓reduceIte]
        rw [prog_bind_assoc]
        refine PSim.bind (PSim.square hg hb') fun s2 base' hs2 hb2 ↦ ?_
        exact ih (a + 1) s2 base' out (n / 2) (b * b) o hs2.good hb2 (ho.pgrow hg hs2) hn'

/-- **`Scalar::pow(exponent)`** (an exponent below `2^64`: the Rust's are `u64`) is `epow`. -/
theorem pow_psim (st : RecState) (hg : Good st) {a : Nat} {x : E} (ha : Rp π iv publicInput stream st a x)
    (e : Nat) (he : e < 2 ^ 64) :
    PSim st (Pi1.pow a e) (epow x e) (Rp π iv publicInput stream) := by
  unfold Pi1.pow
  refine PSim.bind (oneP π iv publicInput stream hg) fun st1 o hst1 ho ↦ ?_
  have h65 : (2 : Nat) ^ 64 < 2 ^ (65 - 0) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have hfuel : epow x e = epowAux (65 - 0) x 1 e :=
    epowAux_fuel x 1 e _ _ Nat.lt_log2_self (by omega)
  rw [hfuel]
  exact PSim.bind (PSim.congr (forIn_range 0 65 _ _).symm rfl
    (pow_loop _ (fun _ _ ↦ rfl) (65 - 0) 0 st1 a o e x 1 hst1.good (ha.pgrow hg hst1) ho (by omega)))
    fun st2 s hst2 hs ↦ PSim.pure hst2.good hs

/-! ## `eq_kernel` -/

theorem getD_double (t : Array E) (x : E) (j : Nat) (hj : j < 2 * t.size) :
    (t.map (· * (1 + x)) ++ t.map (· * x)).getD j 0 =
      if j < t.size then t.getD j 0 * (1 + x) else t.getD (j - t.size) 0 * x := by
  by_cases h : j < t.size
  · rw [ite_eq_left h, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_append_left (by simpa using h), Array.getElem?_map, Array.getElem?_eq_getElem h]
    rfl
  · have h' : j - t.size < t.size := by omega
    rw [ite_eq_right h, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_append_right (by simp; omega), Array.getElem?_map, Array.size_map,
      Array.getElem?_eq_getElem h']
    rfl

/-- **`eq_kernel(point)`**: the Rust's in-place doubling is `UniStatement.eqKernel`, entry for entry. -/
theorem eqKernel_psim (st : RecState) (hg : Good st) {ps : List Nat} {xs : List E}
    (hp : RpL π iv publicInput stream st ps xs) :
    PSim st (Pi1.eqKernel ps) (UniStatement.eqKernel xs)
      (fun st' a b ↦ RpL π iv publicInput stream st' a.toList b.toList) := by
  have hL : ps.length = xs.length := hp.length
  unfold Pi1.eqKernel
  refine PSim.bind (zeroP π iv publicInput stream hg) fun st1 z hst1 _ ↦ ?_
  refine PSim.bind (oneP π iv publicInput stream hst1.good) fun st2 o hst2 ho ↦ ?_
  have hst12 := hst1.trans hst2
  refine PSim.bind (PSim.forIn_list st2 (ps.zip (List.range ps.length)) xs
    (fun k st (out : Array Nat) (t : Array E) ↦ out.size = 2 ^ ps.length ∧ t.size = 2 ^ k ∧
      ∀ j < 2 ^ k, Rp π iv publicInput stream st (out.getD j 0) (t.getD j 0)) _
    (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) (by simp [hL]) ?_ st2 _ #[1]
    (PStep.refl st2 hst2.good) ?_) fun st3 a hst3 ha ↦ PSim.pure hst3.good ?_
  · -- One round: `k`, `r = ps[k]`.
    intro k hk hj st' out t hst' ⟨hos, hts, hI⟩
    simp only [List.length_zip, List.length_range, Nat.min_self] at hk
    simp only [List.getElem_zip, List.getElem_range]
    rw [forIn_range]
    have hr := (hp.get k hk hj).pgrow hg (hst12.trans hst')
    have hkL : 2 ^ k < 2 ^ ps.length := Nat.pow_lt_pow_right (by norm_num) hk
    have hk1 : 2 ^ (k + 1) ≤ 2 ^ ps.length := Nat.pow_le_pow_right (by norm_num) hk
    have hk2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    refine PSim.bind (PSim.forIn_inv st' (List.range' 0 (2 ^ k - 0))
      (fun i st (out' : Array Nat) ↦ out'.size = 2 ^ ps.length ∧
        (∀ j < i, Rp π iv publicInput stream st (out'.getD j 0) (t.getD j 0 * (1 + xs[k])) ∧
          Rp π iv publicInput stream st (out'.getD (j + 2 ^ k) 0) (t.getD j 0 * xs[k])) ∧
        (∀ j, i ≤ j → j < 2 ^ k → out'.getD j 0 = out.getD j 0)) _ ?_ st' out (PStep.refl st' hst'.good)
      ⟨hos, fun j hj ↦ absurd hj (Nat.not_lt_zero j), fun _ _ _ ↦ rfl⟩) fun st'' out' hst'' hJ ↦
        PSim.pure hst''.good ⟨out', rfl, ?_⟩
    · intro i hi s1 out1 hs1 ⟨hsz, hdone, hrest⟩
      simp only [List.length_range', Nat.sub_zero] at hi
      simp only [List.getElem_range', Nat.zero_add, Nat.one_mul]
      have hv : Rp π iv publicInput stream s1 (out1.getD i 0) (t.getD i 0) := by
        rw [hrest i (le_refl i) hi]
        exact (hI i hi).pgrow hst'.good hs1
      refine PSim.bind (PSim.mul hs1.good hv (hr.pgrow hst'.good hs1)) fun s2 h hs2 hh ↦ ?_
      refine PSim.bind (PSim.add hs2.good (hv.pgrow hs1.good hs2) hh) fun s3 a3 hs3 ha3 ↦ PSim.pure hs3.good ?_
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · rw [size_set!, size_set!, hsz]
      · intro j hj
        have hsz' : (out1.set! (i + 2 ^ k) h).size = 2 ^ ps.length := by rw [size_set!, hsz]
        rcases Nat.lt_or_ge j i with hji | hji
        · obtain ⟨h1, h2⟩ := hdone j hji
          refine ⟨?_, ?_⟩
          · rw [getD_set!, ite_eq_right (by omega), getD_set!, ite_eq_right (by omega)]
            exact (h1.pgrow hs1.good hs2).pgrow hs2.good hs3
          · rw [getD_set!, ite_eq_right (by omega), getD_set!, ite_eq_right (by omega)]
            exact (h2.pgrow hs1.good hs2).pgrow hs2.good hs3
        · have hji' : j = i := by omega
          subst hji'
          refine ⟨?_, ?_⟩
          · rw [getD_set!, ite_eq_left ⟨rfl, by rw [hsz']; omega⟩]
            have e : t.getD j 0 + t.getD j 0 * xs[k] = t.getD j 0 * (1 + xs[k]) := by ring
            rw [← e]; exact ha3
          · rw [getD_set!, ite_eq_right (by omega), getD_set!, ite_eq_left ⟨rfl, by rw [hsz]; omega⟩]
            exact hh.pgrow hs2.good hs3
      · intro j hj1 hj2
        rw [getD_set!, ite_eq_right (by omega), getD_set!, ite_eq_right (by omega)]
        exact hrest j (by omega) hj2
    · -- After the round: the doubled kernel.
      obtain ⟨hsz, hdone, _⟩ := hJ
      simp only [List.length_range', Nat.sub_zero] at hdone
      refine ⟨hsz, by simp [hts, hk2]; omega, fun j hj ↦ ?_⟩
      rw [getD_double t xs[k] j (by rw [hts]; omega)]
      by_cases hjk : j < t.size
      · rw [ite_eq_left hjk]
        exact (hdone j (by omega)).1
      · rw [ite_eq_right hjk]
        have := (hdone (j - t.size) (by omega)).2
        rw [show j - t.size + 2 ^ k = j by omega] at this
        exact this
  · -- The start: `out[0] = 1`.
    refine ⟨by simp, rfl, fun j hj ↦ ?_⟩
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    have hpos : 0 < 2 ^ ps.length := Nat.two_pow_pos _
    rw [getD_set!, ite_eq_left ⟨rfl, by rw [Array.size_replicate]; exact hpos⟩]
    exact ho
  · -- The end: entry for entry.
    obtain ⟨hos, hts, hI⟩ := ha
    simp only [List.length_zip, List.length_range, Nat.min_self] at hos hts hI
    unfold UniStatement.eqKernel
    exact rpL_of_getD (by rw [hos, hts]) fun j hj ↦ hI j (by rw [hos] at hj; exact hj)

/-! ## Squares, digits, the coordinates -/

theorem sqn_succ' (x : E) (k : Nat) : sqn x (k + 1) = sqn x k * sqn x k := by
  induction k generalizing x with
  | zero => simp only [sqn]
  | succ k ih => rw [sqn.eq_2 x (k + 1), sqn.eq_2 x k]; exact ih (x * x)

theorem squares_eq (x : E) (n : Nat) : UniStatement.squares x n = (List.range n).map (sqn x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show x :: UniStatement.squares (x * x) n = _
    rw [ih]
    rfl

theorem map_range_succ {α : Type} (f : Nat → α) (i : Nat) :
    (List.range (i + 1)).map f = (List.range i).map f ++ [f i] := by
  rw [List.range_succ, List.map_append, List.map_singleton]

/-- **`squares(first, count)`**: `first, first², first⁴, …`. -/
theorem squares_psim (st : RecState) (hg : Good st) {a : Nat} {x : E} (ha : Rp π iv publicInput stream st a x)
    (count : Nat) :
    PSim st (Pi1.squares a count) (UniStatement.squares x count) (RpL π iv publicInput stream) := by
  rw [squares_eq]
  cases count with
  | zero => exact PSim.pure hg List.Forall₂.nil
  | succ n =>
    unfold Pi1.squares
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    refine PSim.bind (PSim.congr (forIn_range 1 (n + 1) _ _).symm rfl
      (PSim.forIn_inv st (List.range' 1 (n + 1 - 1))
        (fun i st (s : Array Nat × Nat) ↦ RpL π iv publicInput stream st s.1.toList ((List.range (i + 1)).map (sqn x)) ∧
          Rp π iv publicInput stream st s.2 (sqn x i)) _ ?_ st _ (PStep.refl st hg)
        ⟨List.Forall₂.cons ha List.Forall₂.nil, ha⟩)) fun st' s hst' hs ↦ PSim.pure hst'.good ?_
    · intro i _ st1 s hst1 ⟨hout, hlast⟩
      refine PSim.bind (PSim.square hst1.good hlast) fun st2 l hst2 hl ↦ PSim.pure hst2.good ⟨_, rfl, ?_, ?_⟩
      · rw [Array.toList_push, map_range_succ (sqn x) (i + 1), sqn_succ']
        exact (hout.pgrow hst1.good hst2).snoc hl
      · rw [sqn_succ']; exact hl
    · have h := hs.1
      simp only [List.length_range', Nat.add_sub_cancel] at h
      exact h

/-- The digits' sequence: `w_0 = t`, `w_(l+1) = w_l² + w_l`. -/
def wseq (t : E) : Nat → E
  | 0 => t
  | k + 1 => wseq t k * wseq t k + wseq t k

theorem digits_fold (t : E) (k : Nat) :
    ((List.range k).foldl (fun (ws : Array E) _ ↦ let w := ws.back?.getD t; ws.push (w * w + w)) #[t]).toList =
      (List.range (k + 1)).map (wseq t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hA : (List.range k).foldl (fun (ws : Array E) _ ↦ let w := ws.back?.getD t; ws.push (w * w + w)) #[t] = A
      at ih
    have hb : A.back? = some (wseq t k) := by
      have hsz : A.size = k + 1 := by rw [← Array.length_toList, ih]; simp
      rw [Array.back?_eq_getElem?, hsz, Nat.add_sub_cancel, ← Array.getElem?_toList, ih]
      simp
    simp only [Array.toList_push, hb, Option.getD_some]
    rw [ih, map_range_succ (wseq t) (k + 1)]
    rfl

theorem digits_eq (t : E) (count : Nat) : UniStatement.digits t count = (List.range count).map (wseq t) := by
  unfold UniStatement.digits
  rw [digits_fold]
  cases count with
  | zero => rfl
  | succ c =>
    rw [Nat.add_sub_cancel]
    exact List.take_of_length_le (by simp)

/-- **`digits(t, count)`**: `w_0 = t`, `w_(l+1) = w_l² + w_l`. -/
theorem digits_psim (st : RecState) (hg : Good st) {a : Nat} {t : E} (ha : Rp π iv publicInput stream st a t)
    (count : Nat) :
    PSim st (Pi1.digits a count) (UniStatement.digits t count) (RpL π iv publicInput stream) := by
  rw [digits_eq]
  unfold Pi1.digits
  refine PSim.bind (PSim.congr (forIn_range 0 count _ _).symm rfl
    (PSim.forIn_inv st (List.range' 0 (count - 0))
      (fun i st (s : Array Nat × Nat) ↦ RpL π iv publicInput stream st s.1.toList ((List.range i).map (wseq t)) ∧
        Rp π iv publicInput stream st s.2 (wseq t i)) _ ?_ st _ (PStep.refl st hg)
      ⟨List.Forall₂.nil, ha⟩)) fun st' s hst' hs ↦ PSim.pure hst'.good ?_
  · intro i _ st1 s hst1 ⟨hout, hw⟩
    refine PSim.bind (PSim.mul hst1.good hw hw) fun st2 ww hst2 hww ↦ ?_
    refine PSim.bind (PSim.add hst2.good hww (hw.pgrow hst1.good hst2)) fun st3 w' hst3 hw' ↦
      PSim.pure hst3.good ⟨_, rfl, ?_, hw'⟩
    rw [Array.toList_push, map_range_succ]
    exact ((hout.pgrow hst1.good hst2).pgrow hst2.good hst3).snoc ((hw.pgrow hst1.good hst2).pgrow hst2.good hst3)
  · have h := hs.1
    simp only [List.length_range', Nat.sub_zero] at h
    exact h

/-- A row's coordinate (`coordinates_at`'s inner sum). -/
def rowValue (frobenius : List E) (row : Array K) : E :=
  (row.toList.zip frobenius).foldl (fun acc p ↦ if p.1 ≠ 0 then acc + ofK p.1 * p.2 else acc) 0

theorem coordinatesAt_eq (t : E) (functionals : Array (Array K)) :
    UniStatement.coordinatesAt t functionals =
      functionals.toList.map (rowValue ((List.range functionals.size).map (sqn t))) := by
  unfold UniStatement.coordinatesAt rowValue
  rfl

theorem take_succ_map {α β : Type} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).map f = (l.take i).map f ++ [f l[i]] := by
  rw [List.take_add_one, List.map_append, List.getElem?_eq_getElem h]
  rfl

/-- **`coordinates_at(t, functionals)`**: `t`'s Frobenius powers, then each functional's sum. -/
theorem coordinatesAt_psim (st : RecState) (hg : Good st) {a : Nat} {t : E} (ha : Rp π iv publicInput stream st a t)
    (functionals : Array (Array K)) :
    PSim st (Pi1.coordinatesAt a functionals) (UniStatement.coordinatesAt t functionals)
      (RpL π iv publicInput stream) := by
  rw [coordinatesAt_eq]
  unfold Pi1.coordinatesAt
  refine PSim.bind (PSim.congr (forIn_range 0 functionals.size _ _).symm rfl
    (PSim.forIn_inv st (List.range' 0 (functionals.size - 0))
      (fun i st (s : Array Nat × Nat) ↦ RpL π iv publicInput stream st s.1.toList ((List.range i).map (sqn t)) ∧
        Rp π iv publicInput stream st s.2 (sqn t i)) _ ?_ st _ (PStep.refl st hg)
      ⟨List.Forall₂.nil, ha⟩)) fun st1 s hst1 hs ↦ ?_
  · intro i _ st1 s hst1 ⟨hout, hx⟩
    refine PSim.bind (PSim.square hst1.good hx) fun st2 x' hst2 hx' ↦ PSim.pure hst2.good ⟨_, rfl, ?_, ?_⟩
    · rw [Array.toList_push, map_range_succ]
      exact (hout.pgrow hst1.good hst2).snoc (hx.pgrow hst1.good hst2)
    · rw [sqn_succ']; exact hx'
  · obtain ⟨hfrob, _⟩ := hs
    simp only [List.length_range', Nat.sub_zero] at hfrob
    -- The functionals, one row each.
    refine PSim.bind (PSim.forIn_inv st1 functionals.toList
      (fun i st (out : Array Nat) ↦ RpL π iv publicInput stream st out.toList
        ((functionals.toList.take i).map (rowValue ((List.range functionals.size).map (sqn t))))) _ ?_ st1 #[]
      (PStep.refl st1 hst1.good) List.Forall₂.nil) fun st2 out hst2 hout ↦ PSim.pure hst2.good ?_
    · intro i hi st' out' hst' hI
      have hfrob' := hfrob.pgrow hst1.good hst'
      refine PSim.bind (zeroP π iv publicInput stream hst'.good) fun s1 z hs1 hz ↦ ?_
      have hfr1 := hfrob'.pgrow hst'.good hs1
      have hlen : (functionals.toList[i].toList.zip s.1.toList).length =
          (functionals.toList[i].toList.zip ((List.range functionals.size).map (sqn t))).length := by
        simp [hfr1.length]
      refine PSim.bind (PSim.forIn_list s1 _ _ (fun _ st (u : Nat) (v : E) ↦ Rp π iv publicInput stream st u v) _
        (fun acc p ↦ if p.1 ≠ 0 then acc + ofK p.1 * p.2 else acc) hlen ?_ s1 z 0 (PStep.refl s1 hs1.good) hz)
        fun s2 acc hs2 hacc ↦ PSim.pure hs2.good ⟨_, rfl, ?_⟩
      · intro j hj hj' s3 u v hs3 huv
        simp only [List.getElem_zip]
        simp only [List.length_zip] at hj hj'
        have hf := (hfr1.get j (by omega) (by omega)).pgrow hs1.good hs3
        by_cases h0 : functionals.toList[i].toList[j] ≠ 0
        · simp only [h0, ↓reduceIte, ne_eq, not_false_eq_true]
          refine PSim.bind (constP π iv publicInput stream hs3.good _) fun s4 c hs4 hc ↦ ?_
          refine PSim.bind (PSim.mul hs4.good hc (hf.pgrow hs3.good hs4)) fun s5 p hs5 hp ↦ ?_
          exact PSim.bind (PSim.add hs5.good ((huv.pgrow hs3.good hs4).pgrow hs4.good hs5) hp) fun s6 q hs6 hq ↦
            PSim.pure hs6.good ⟨q, rfl, hq⟩
        · simp only [h0, ↓reduceIte]
          exact PSim.pure hs3.good ⟨u, rfl, huv⟩
      · rw [Array.toList_push, take_succ_map _ _ i hi]
        exact ((hI.pgrow hst'.good hs1).pgrow hs1.good hs2).snoc hacc
    · rw [List.take_length] at hout
      exact hout

/-! ## The vanishing polynomials -/

/-- **`vanishing_ratio(w, r, m)`**: `Π_(r ≤ j < m) (w_j + 1)` (the digits held to `m`). -/
theorem vanishingRatio_psim (st : RecState) (hg : Good st) {w : List Nat} {ws : List E}
    (hw : RpL π iv publicInput stream st w ws) (r m : Nat) (hm : m ≤ ws.length) :
    PSim st (Pi1.vanishingRatio w r m) (UniStatement.vanishingRatio ws r m) (Rp π iv publicInput stream) := by
  unfold Pi1.vanishingRatio UniStatement.vanishingRatio
  refine PSim.bind (oneP π iv publicInput stream hg) fun st1 o hst1 ho ↦ ?_
  refine PSim.bind (PSim.congr (forIn_range r m _ _).symm rfl
    (PSim.forIn_list st1 (List.range' r (m - r)) (List.range' r (m - r))
      (fun _ st (s : Nat) (t : E) ↦ Rp π iv publicInput stream st s t) _
      (fun acc j ↦ acc * (ws.getD j 0 + 1)) rfl ?_ st1 o 1 (PStep.refl st1 hst1.good) ho))
    fun st2 a hst2 ha ↦ PSim.pure hst2.good ha
  intro i hi _ s1 s t hs1 hI
  simp only [List.getElem_range', Nat.one_mul]
  simp only [List.length_range'] at hi
  have hj : r + i < w.length := by rw [hw.length]; omega
  have hwj := (hw.get (r + i) hj (by omega)).pgrow hg (hst1.trans hs1)
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by omega)]
  refine PSim.bind (oneP π iv publicInput stream hs1.good) fun s2 o' hs2 ho' ↦ ?_
  refine PSim.bind (PSim.add hs2.good (hwj.pgrow hs1.good hs2) ho') fun s3 sv hs3 hsv ↦ ?_
  exact PSim.bind (PSim.mul hs3.good ((hI.pgrow hs1.good hs2).pgrow hs2.good hs3) hsv) fun s4 q hs4 hq ↦
    PSim.pure hs4.good ⟨q, rfl, hq⟩

/-- **`active_vanishing_from_bits(w, bits, r)`** (the digits and the count's bits held past `r`). -/
theorem activeVanishingFromBits_psim (st : RecState) (hg : Good st) {w bits : List Nat} {ws bs : List E}
    (hw : RpL π iv publicInput stream st w ws) (hb : RpL π iv publicInput stream st bits bs) (r : Nat)
    (hrw : r < ws.length) (hrb : r < bs.length) :
    PSim st (Pi1.activeVanishingFromBits w bits r) (UniStatement.activeVanishingFromBits ws bs r)
      (Rp π iv publicInput stream) := by
  have hwl := hw.length
  have hbl := hb.length
  unfold Pi1.activeVanishingFromBits UniStatement.activeVanishingFromBits
  rw [List.getD_eq_getElem _ _ (by omega : r < w.length), List.getD_eq_getElem _ _ hrw,
    List.getD_eq_getElem _ _ (by omega : r < bits.length), List.getD_eq_getElem _ _ hrb]
  refine PSim.bind (oneP π iv publicInput stream hg) fun s1 o hs1 ho ↦ ?_
  refine PSim.bind (PSim.add hs1.good ((hw.get r (by omega) hrw).pgrow hg hs1) ho) fun s2 sv hs2 hsv ↦ ?_
  refine PSim.bind (PSim.mul hs2.good (((hb.get r (by omega) hrb).pgrow hg hs1).pgrow hs1.good hs2) hsv)
    fun s3 p hs3 hp ↦ ?_
  have hs13 := hs2.trans hs3
  refine PSim.bind (PSim.add hs3.good (ho.pgrow hs1.good hs13) hp) fun s4 prod hs4 hprod ↦ ?_
  have hs14 := hs13.trans hs4
  have hlen : ((bits.take r).zip (List.range r)).length = (List.range r).length := by simp; omega
  refine PSim.bind (PSim.forIn_list s4 ((bits.take r).zip (List.range r)) (List.range r)
    (fun _ st (s : Nat) (t : E) ↦ Rp π iv publicInput stream st s t) _
    (fun product b ↦ product * (1 + bs.getD b 0 * (ws.getD b 0 + (cosetOffset r b + 1)))) hlen ?_ s4 prod _
    (PStep.refl s4 hs4.good) hprod) fun s5 a hs5 ha ↦ PSim.pure hs5.good ha
  intro i hi hj s6 u v hs6 huv
  simp only [List.getElem_zip, List.getElem_take, List.getElem_range]
  simp only [List.length_range] at hj
  have hs16 := hs14.trans hs6
  have hbi := (hb.get i (by omega) (by omega)).pgrow hg ((hs1.trans hs16))
  have hwi := (hw.get i (by omega) (by omega)).pgrow hg ((hs1.trans hs16))
  have ho6 := ho.pgrow hs1.good hs16
  rw [List.getD_eq_getElem _ _ (by omega : i < w.length), List.getD_eq_getElem _ _ (by omega : i < ws.length),
    List.getD_eq_getElem _ _ (by omega : i < bs.length)]
  refine PSim.bind (constP π iv publicInput stream hs6.good _) fun t1 c ht1 hc ↦ ?_
  refine PSim.bind (PSim.add ht1.good (hwi.pgrow hs6.good ht1) hc) fun t2 sv ht2 hsv ↦ ?_
  refine PSim.bind (PSim.mul ht2.good ((hbi.pgrow hs6.good ht1).pgrow ht1.good ht2) hsv) fun t3 p ht3 hp ↦ ?_
  have ht13 := (ht1.trans ht2).trans ht3
  refine PSim.bind (PSim.add ht3.good (ho6.pgrow hs6.good ht13) hp) fun t4 f ht4 hf ↦ ?_
  exact PSim.bind (PSim.mul ht4.good ((huv.pgrow hs6.good ht13).pgrow ht3.good ht4) hf) fun t5 q ht5 hq ↦
    PSim.pure ht5.good ⟨q, rfl, hq⟩

end Pure

end RecGraph.Sim
