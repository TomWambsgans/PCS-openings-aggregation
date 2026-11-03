-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The circuit is `formal/Lv42`'s (leanerVM `mumbai`
-- f0393df4's `Blake2sCircuit`, MIT OR Apache-2.0); the walk is `formal/UniStatement`'s (`UniStatement/Rec.lean`).
import FlockSoundUni.WalkCode

namespace FlockSound.Uni.Walk

open UniStatement UniStatement.Flock UniSound LeanVM.Parameters Finset
open Lv42.Protocol Lv42.Protocol.ProductCircuit

/-! ## Arrays -/

section Arrays

variable {α : Type}

theorem getD_set! (a : Array α) (i j : ℕ) (v d : α) :
    (a.set! i v).getD j d = if i = j ∧ i < a.size then v else a.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  by_cases h : i = j
  · subst h
    by_cases hi : i < a.size <;> simp [hi, Array.set!]
  · simp [h, Array.set!, Array.getElem?_setIfInBounds_ne h]

theorem size_set! (a : Array α) (i : ℕ) (v : α) : (a.set! i v).size = a.size := by
  simp [Array.set!]

theorem getD_set!_self (a : Array α) {i : ℕ} (v d : α) (h : i < a.size) : (a.set! i v).getD i d = v := by
  rw [getD_set!, if_pos ⟨rfl, h⟩]

theorem getD_set!_ne (a : Array α) {i j : ℕ} (v d : α) (h : i ≠ j) : (a.set! i v).getD j d = a.getD j d := by
  rw [getD_set!, if_neg (fun h' ↦ h h'.1)]

theorem getD_replicate (n j : ℕ) (v d : α) : (Array.replicate n v).getD j d = if j < n then v else d := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases h : j < n <;> simp [h]

theorem getD_ofFn {n : ℕ} (f : Fin n → α) (j : ℕ) (d : α) :
    (Array.ofFn f).getD j d = if h : j < n then f ⟨j, h⟩ else d := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases h : j < n <;> simp [h]

theorem foldl_range'_succ {β : Type} (f : β → ℕ → β) (b : β) (s n : ℕ) :
    (List.range' s (n + 1)).foldl f b = (List.range' (s + 1) n).foldl f (f b s) := by
  rw [List.range'_succ, List.foldl_cons]

end Arrays

/-! ## The block's positions and the forms' linear evaluation -/

/-- The block's log-size. -/
abbrev bm : ℕ := Blake2sCircuit.m

theorem two_pow_bm : (2 : ℕ) ^ bm = 16384 := rfl

theorem constPos_val : ((Lv42.Parameters.Flock.constPos : ProductCircuit.Pos bm) : ℕ) = 512 := rfl

/-- **The linear evaluation of a form** at the column weights `cw`: `Σ_{j ∈ L} cw[j]`. The walk computes the
circuit's forms this way: a gate's output form `var(pos)` is `cw[pos]`, an XOR of forms the sum (characteristic
two), a rotation a permutation. -/
@[irreducible] def lev (cw : Array E) (L : Form bm) : E := ∑ i : ProductCircuit.Pos bm, if L.getLsbD i then cw.getD i 0 else 0

theorem lev_zero (cw : Array E) : lev cw 0 = 0 := by
  unfold lev
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have h0 : (0 : Form bm).getLsbD i = false := BitVec.getLsbD_zero
  rw [h0]
  rfl

theorem lev_xor (cw : Array E) (a b : Form bm) : lev cw (a ^^^ b) = lev cw a + lev cw b := by
  unfold lev
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> simp [add_self_E]

theorem lev_var (cw : Array E) (k : ProductCircuit.Pos bm) : lev cw (Form.var k) = cw.getD k 0 := by
  unfold lev
  simp only [getLsbD_var, decide_eq_true_eq, Fin.val_inj]
  rw [Finset.sum_ite_eq]
  simp

theorem lev_var_pos (cw : Array E) {n : ℕ} (h : n < 2 ^ bm) : lev cw (Form.var (pos n)) = cw.getD n 0 := by
  rw [lev_var, pos_val h]

/-! ## Words -/

/-- **A walk word is a builder word's evaluation**: bit `i` of the walk is the linear evaluation of the builder's
form for bit `i`. -/
def WRel (cw : Array E) (ww : Array E) (x : Word bm) : Prop := ∀ i (h : i < 32), ww.getD i 0 = lev cw (x[i]'h)

theorem wrel_xor {cw a b : Array E} {x y : Word bm} (ha : WRel cw a x) (hb : WRel cw b y) :
    WRel cw (walkXor a b) (xorW x y) := by
  intro i h
  rw [walkXor, getD_ofFn, dif_pos h, ha i h, hb i h, xorW, Vector.getElem_ofFn, lev_xor]
  rfl

theorem wrel_rotr {cw a : Array E} {x : Word bm} (ha : WRel cw a x) (n : ℕ) :
    WRel cw (walkRotr a n) (rotrW x n) := by
  intro i h
  rw [walkRotr, getD_ofFn, dif_pos h, ha _ (Nat.mod_lt _ (by decide)), rotrW, Vector.getElem_ofFn]

theorem wrel_slots (cw : Array E) {b : ℕ} (hb : b + 32 ≤ 2 ^ bm) : WRel cw (walkSlots cw b) (inW b) := by
  intro i h
  rw [walkSlots, getD_ofFn, dif_pos h, inW, Vector.getElem_ofFn, lev_var_pos cw (by omega)]

theorem wrel_lit (cw : Array E) (c : UInt32) {v : ℕ} (hv : v = c.toNat) :
    WRel cw (walkLiteral cw v) (litW Lv42.Parameters.Flock.constPos c) := by
  intro i h
  rw [walkLiteral, getD_ofFn, dif_pos h, litW, Vector.getElem_ofFn, hv]
  split_ifs
  · rw [lev_var, constPos_val, constantColumn]
  · rw [lev_zero]

/-! ## The simulation relation -/

/-- **A run of the walk follows a run of the builder** recording `k` gates: the builder's state goes from `σ` to
`σ'`, recording `k` gates at the positions `σ.next, …, σ.next + k − 1`, and the walk's rows go from `(l, r)` to
`(l', r')`, the rows of the new gates holding their forms' evaluations and every other row unchanged. -/
structure Grow (cw : Array E) (l r : Array E) (σ : BuildState bm) (l' r' : Array E) (σ' : BuildState bm)
    (k : ℕ) : Prop where
  next : σ'.next = σ.next + k
  gates : ∃ new : List (ProductCircuit.Pos bm × Gate bm), σ'.gates.toList = σ.gates.toList ++ new ∧
    new.map (fun g ↦ (g.1 : ℕ)) = List.range' σ.next k ∧
    ∀ g ∈ new, l'.getD g.1 0 = lev cw g.2.a ∧ r'.getD g.1 0 = lev cw g.2.b
  frame : ∀ j, (j < σ.next ∨ σ.next + k ≤ j) → l'.getD j 0 = l.getD j 0 ∧ r'.getD j 0 = r.getD j 0
  lsize : l'.size = l.size
  rsize : r'.size = r.size

theorem Grow.refl (cw l r : Array E) (σ : BuildState bm) : Grow cw l r σ l r σ 0 where
  next := rfl
  gates := ⟨[], by simp, by simp, by simp⟩
  frame _ _ := ⟨rfl, rfl⟩
  lsize := rfl
  rsize := rfl

theorem Grow.trans {cw l r l' r' l'' r'' : Array E} {σ σ' σ'' : BuildState bm} {k k' : ℕ}
    (h : Grow cw l r σ l' r' σ' k) (h' : Grow cw l' r' σ' l'' r'' σ'' k') :
    Grow cw l r σ l'' r'' σ'' (k + k') where
  next := by rw [h'.next, h.next, Nat.add_assoc]
  gates := by
    obtain ⟨n1, e1, p1, v1⟩ := h.gates
    obtain ⟨n2, e2, p2, v2⟩ := h'.gates
    refine ⟨n1 ++ n2, by rw [e2, e1, List.append_assoc], ?_, fun g hg ↦ ?_⟩
    · rw [List.map_append, p1, p2, h.next]
      first
        | exact List.range'_append_1 _ _ _
        | simpa using (List.range'_append (s := σ.next) (m := k) (n := k') (step := 1))
    · rcases List.mem_append.mp hg with hg | hg
      · have hpos : (g.1 : ℕ) ∈ List.range' σ.next k := by
          rw [← p1]; exact List.mem_map_of_mem hg
        rw [List.mem_range'_1] at hpos
        have := h'.frame g.1 (Or.inl (by rw [h.next]; omega))
        rw [this.1, this.2]
        exact v1 g hg
      · exact v2 g hg
  frame j hj := by
    have e1 := h.frame j (by omega)
    have e2 := h'.frame j (by rw [h.next]; omega)
    exact ⟨e2.1.trans e1.1, e2.2.trans e1.2⟩
  lsize := h'.lsize.trans h.lsize
  rsize := h'.rsize.trans h.rsize

theorem Grow.cast {cw l r l' r' : Array E} {σ σ' : BuildState bm} {k k' : ℕ}
    (h : Grow cw l r σ l' r' σ' k) (hk : k = k') : Grow cw l r σ l' r' σ' k' := hk ▸ h

/-- **One gate**: recording `(a, b)` at `next`, the walk writes its forms' evaluations there. -/
theorem Grow.push0 (cw : Array E) {l r : Array E} (σ : BuildState bm) (a b : Form bm) {va vb : E}
    (ha : va = lev cw a) (hb : vb = lev cw b) (hl : σ.next < l.size) (hr : σ.next < r.size)
    (hm : σ.next < 2 ^ bm) :
    Grow cw l r σ (l.set! σ.next va) (r.set! σ.next vb)
      { next := σ.next + 1, gates := σ.gates.push (pos σ.next, ⟨a, b⟩) } 1 where
  next := rfl
  gates := by
    refine ⟨[(pos σ.next, ⟨a, b⟩)], by simp, by simp [pos_val hm], fun g hg ↦ ?_⟩
    rw [List.mem_singleton] at hg
    subst hg
    simp only [pos_val hm]
    rw [getD_set!_self _ _ _ hl, getD_set!_self _ _ _ hr]
    exact ⟨ha, hb⟩
  frame j hj := ⟨getD_set!_ne _ _ _ (by omega), getD_set!_ne _ _ _ (by omega)⟩
  lsize := size_set! _ _ _
  rsize := size_set! _ _ _

/-- `Grow.push0` with the walk's row index given as `i = next`. -/
theorem Grow.push (cw : Array E) {l r : Array E} (σ : BuildState bm) {i : ℕ} (hi : σ.next = i) (a b : Form bm)
    {va vb : E} (ha : va = lev cw a) (hb : vb = lev cw b) (hl : σ.next < l.size) (hr : σ.next < r.size)
    (hm : σ.next < 2 ^ bm) :
    Grow cw l r σ (l.set! i va) (r.set! i vb)
      { next := σ.next + 1, gates := σ.gates.push (pos σ.next, ⟨a, b⟩) } 1 := by
  subst hi
  exact Grow.push0 cw σ a b ha hb hl hr hm

/-! ## The builder's runs (Words.lean's, restated: they are private there) -/

section Runs

variable (x y z p q : Word bm) (σ : BuildState bm)

theorem run_addCarries_zero' (c : Form bm) : (addCarries x y 0 c).run σ = ([c], σ) := rfl

theorem run_addCarries_succ' (n : ℕ) (c : Form bm) :
    (addCarries x y (n + 1) c).run σ =
      (c :: ((addCarries x y n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push (pos σ.next, ⟨x[30 - n]'(by omega) ^^^ c, y[30 - n]'(by omega) ^^^ c⟩) }).1,
       ((addCarries x y n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push (pos σ.next, ⟨x[30 - n]'(by omega) ^^^ c, y[30 - n]'(by omega) ^^^ c⟩) }).2) :=
  rfl

theorem run_addW' : (addW x y).run σ =
    (sumW x y ((addCarries x y 31 0).run σ).1, ((addCarries x y 31 0).run σ).2) := by
  rw [addW, StateT.run_map]
  rfl

theorem run_majorities_zero' : (majorities x y z 0).run σ = ([], σ) := rfl

theorem run_majorities_succ' (n : ℕ) :
    (majorities x y z (n + 1)).run σ =
      ((Form.var (pos σ.next) ^^^ z[30 - n]'(by omega)) :: ((majorities x y z n).run
        { next := σ.next + 1,
          gates := σ.gates.push (pos σ.next,
            ⟨x[30 - n]'(by omega) ^^^ z[30 - n]'(by omega), y[30 - n]'(by omega) ^^^ z[30 - n]'(by omega)⟩) }).1,
       ((majorities x y z n).run
        { next := σ.next + 1,
          gates := σ.gates.push (pos σ.next,
            ⟨x[30 - n]'(by omega) ^^^ z[30 - n]'(by omega), y[30 - n]'(by omega) ^^^ z[30 - n]'(by omega)⟩) }).2) :=
  rfl

theorem run_rippleCarries_zero' (c : Form bm) : (rippleCarries p q 0 c).run σ = ([c], σ) := rfl

theorem run_rippleCarries_gate' (n : ℕ) (c : Form bm) (h : 1 ≤ 30 - n) :
    (rippleCarries p q (n + 1) c).run σ =
      (c :: ((rippleCarries p q n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push (pos σ.next, ⟨p[30 - n]'(by omega) ^^^ c, q[30 - n]'(by omega) ^^^ c⟩) }).1,
       ((rippleCarries p q n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push (pos σ.next, ⟨p[30 - n]'(by omega) ^^^ c, q[30 - n]'(by omega) ^^^ c⟩) }).2) := by
  simp only [rippleCarries, h, ↓reduceIte]
  rfl

theorem run_rippleCarries_skip' (n : ℕ) (c : Form bm) (h : ¬ 1 ≤ 30 - n) :
    (rippleCarries p q (n + 1) c).run σ =
      (c :: ((rippleCarries p q n c).run σ).1, ((rippleCarries p q n c).run σ).2) := by
  simp only [rippleCarries, h, ↓reduceIte]
  rfl

theorem run_add3W' : (add3W x y z).run σ =
    (sumW (xor3W x y z) (shiftW ((majorities x y z 31).run σ).1)
        ((rippleCarries (xor3W x y z) (shiftW ((majorities x y z 31).run σ).1) 31 0).run
          ((majorities x y z 31).run σ).2).1,
      ((rippleCarries (xor3W x y z) (shiftW ((majorities x y z 31).run σ).1) 31 0).run
          ((majorities x y z 31).run σ).2).2) := by
  rw [add3W, StateT.run_bind]
  simp only [StateT.run_map]
  rfl

end Runs

/-! ## The ripple adder (`walkAdd` against `addW`) -/

theorem addStep_lt (cw : Array E) (x y : WalkWord) (cb : ℕ) (st : Array E × Array E × E × Array E) {bit : ℕ}
    (h : bit < 31) :
    addStep cw x y cb st bit =
      (st.1.set! (cb + bit) (x.getD bit 0 + st.2.2.1), st.2.1.set! (cb + bit) (y.getD bit 0 + st.2.2.1),
        st.2.2.1 + cw.getD (cb + bit) 0, st.2.2.2.set! bit (x.getD bit 0 + y.getD bit 0 + st.2.2.1)) := by
  simp [addStep, h]

theorem addStep_31 (cw : Array E) (x y : WalkWord) (cb : ℕ) (st : Array E × Array E × E × Array E) :
    addStep cw x y cb st 31 = (st.1, st.2.1, st.2.2.1, st.2.2.2.set! 31 (x.getD 31 0 + y.getD 31 0 + st.2.2.1)) := by
  simp [addStep]

/-- What the carry recursion from bit `31 − n` leaves: the gates, the output's bits from `31 − n` on (the sums of
the operands' bits and the carries), the lower bits unchanged. -/
structure AddSim (cw xw yw : Array E) (n : ℕ) (l r o : Array E) (σ : BuildState bm)
    (st : Array E × Array E × E × Array E) (res : List (Form bm) × BuildState bm) : Prop where
  grow : Grow cw l r σ st.1 st.2.1 res.2 n
  osize : st.2.2.2.size = 32
  low : ∀ i < 31 - n, st.2.2.2.getD i 0 = o.getD i 0
  out : ∀ j ≤ n, st.2.2.2.getD (31 - n + j) 0 =
    xw.getD (31 - n + j) 0 + yw.getD (31 - n + j) 0 + lev cw (res.1.getD j 0)

theorem sim_addCarries (cw : Array E) {x y : Word bm} {xw yw : Array E} (hx : WRel cw xw x) (hy : WRel cw yw y)
    (cb : ℕ) (hcb : cb + 31 ≤ 2 ^ bm) :
    ∀ n ≤ 31, ∀ (l r o : Array E) (cv : E) (σ : BuildState bm) (c : Form bm),
      lev cw c = cv → σ.next = cb + (31 - n) → l.size = 2 ^ bm → r.size = 2 ^ bm → o.size = 32 →
      AddSim cw xw yw n l r o σ ((List.range' (31 - n) (n + 1)).foldl (addStep cw xw yw cb) (l, r, cv, o))
        ((addCarries x y n c).run σ) := by
  intro n
  induction n with
  | zero =>
    intro _ l r o cv σ c hc _ _ _ ho
    rw [show List.range' (31 - 0) (0 + 1) = [31] from rfl, List.foldl_cons, List.foldl_nil, addStep_31,
      run_addCarries_zero']
    dsimp only
    refine ⟨Grow.refl _ _ _ _, by rw [size_set!, ho], fun i hi ↦ getD_set!_ne _ _ _ (by omega), fun j hj ↦ ?_⟩
    obtain rfl : j = 0 := by omega
    rw [getD_set!_self _ _ _ (by rw [ho]; omega)]
    simp [hc]
  | succ n ih =>
    intro hn l r o cv σ c hc hσ hl hr ho
    have ha : 31 - (n + 1) + 1 = 31 - n := by omega
    have hnext : σ.next = cb + (30 - n) := by omega
    rw [foldl_range'_succ, ha, run_addCarries_succ', addStep_lt _ _ _ _ _ (by omega)]
    dsimp only
    have h30 : 31 - (n + 1) = 30 - n := by omega
    rw [h30]
    have hlev : lev cw (c ^^^ Form.var (pos σ.next)) = cv + cw.getD (cb + (30 - n)) 0 := by
      rw [lev_xor, hc, lev_var_pos _ (by omega), hnext]
    have H := ih (by omega) (l.set! (cb + (30 - n)) (xw.getD (30 - n) 0 + cv))
      (r.set! (cb + (30 - n)) (yw.getD (30 - n) 0 + cv))
      (o.set! (30 - n) (xw.getD (30 - n) 0 + yw.getD (30 - n) 0 + cv)) _
      { next := σ.next + 1,
        gates := σ.gates.push (pos σ.next, ⟨x[30 - n]'(by omega) ^^^ c, y[30 - n]'(by omega) ^^^ c⟩) } _
      hlev (by show σ.next + 1 = cb + (31 - n); omega) (by rw [size_set!, hl])
      (by rw [size_set!, hr]) (by rw [size_set!, ho])
    have hpush := Grow.push cw (l := l) (r := r) σ hnext (x[30 - n]'(by omega) ^^^ c) (y[30 - n]'(by omega) ^^^ c)
      (va := xw.getD (30 - n) 0 + cv) (vb := yw.getD (30 - n) 0 + cv)
      (by rw [lev_xor, ← hx _ (by omega), hc]) (by rw [lev_xor, ← hy _ (by omega), hc])
      (by rw [hl]; omega) (by rw [hr]; omega) (by omega)
    refine ⟨(hpush.trans H.grow).cast (by omega : 1 + n = n + 1), H.osize, fun i hi ↦ ?_, fun j hj ↦ ?_⟩
    · rw [H.low i (by omega), getD_set!_ne _ _ _ (by omega)]
    · rcases j with _ | j
      · rw [show 31 - (n + 1) + 0 = 30 - n by omega, H.low _ (by omega), getD_set!_self _ _ _ (by rw [ho]; omega)]
        simp [hc]
      · rw [show 31 - (n + 1) + (j + 1) = 31 - n + j by omega, H.out j (by omega)]
        simp

theorem sim_addW (cw : Array E) {x y : Word bm} {xw yw : Array E} (hx : WRel cw xw x) (hy : WRel cw yw y)
    (l r : Array E) (σ : BuildState bm) (hl : l.size = 2 ^ bm) (hr : r.size = 2 ^ bm)
    (hfit : σ.next + 31 ≤ 2 ^ bm) :
    Grow cw l r σ (walkAdd cw l r xw yw σ.next).1 (walkAdd cw l r xw yw σ.next).2.1 ((addW x y).run σ).2 31 ∧
      WRel cw (walkAdd cw l r xw yw σ.next).2.2 ((addW x y).run σ).1 := by
  rw [walkAdd_eq, run_addW', addModel]
  dsimp only
  have H := sim_addCarries cw hx hy σ.next hfit 31 le_rfl l r (Array.replicate 32 0) 0 σ 0 (lev_zero cw)
    (by omega) hl hr (by simp)
  rw [show 31 - 31 = 0 from rfl, show 31 + 1 = 32 from rfl] at H
  refine ⟨H.grow, fun i hi ↦ ?_⟩
  have := H.out i (by omega)
  simp only [Nat.sub_self, Nat.zero_add] at this
  rw [this, sumW, Vector.getElem_ofFn]
  simp only [Fin.getElem_fin, lev_xor, hx i hi, hy i hi]

/-! ## The three-operand adder (`walkAdd3` against `add3W`) -/

theorem rippleStep_gate (cw : Array E) (x y z : WalkWord) (maj : Array E) (rb : ℕ)
    (st : Array E × Array E × E × Array E) {bit : ℕ} (h1 : 1 ≤ bit) (h2 : bit ≤ 30) :
    rippleStep cw x y z maj rb st bit =
      (st.1.set! (rb + bit - 1) (x.getD bit 0 + y.getD bit 0 + z.getD bit 0 + st.2.2.1),
        st.2.1.set! (rb + bit - 1) (maj.getD (bit - 1) 0 + st.2.2.1),
        st.2.2.1 + cw.getD (rb + bit - 1) 0,
        st.2.2.2.set! bit (x.getD bit 0 + y.getD bit 0 + z.getD bit 0 + st.2.2.1 + maj.getD (bit - 1) 0)) := by
  have h0 : bit ≠ 0 := by omega
  simp [rippleStep, h1, h2, h0]

theorem rippleStep_0 (cw : Array E) (x y z : WalkWord) (maj : Array E) (rb : ℕ)
    (st : Array E × Array E × E × Array E) :
    rippleStep cw x y z maj rb st 0 =
      (st.1, st.2.1, st.2.2.1, st.2.2.2.set! 0 (x.getD 0 0 + y.getD 0 0 + z.getD 0 0 + st.2.2.1)) := by
  simp [rippleStep]

theorem rippleStep_31 (cw : Array E) (x y z : WalkWord) (maj : Array E) (rb : ℕ)
    (st : Array E × Array E × E × Array E) :
    rippleStep cw x y z maj rb st 31 =
      (st.1, st.2.1, st.2.2.1,
        st.2.2.2.set! 31 (x.getD 31 0 + y.getD 31 0 + z.getD 31 0 + st.2.2.1 + maj.getD 30 0)) := by
  simp [rippleStep]

/-- What the majority layer from bit `31 − n` leaves. -/
structure MajSim (cw : Array E) (n : ℕ) (l r mj : Array E) (σ : BuildState bm) (st : Array E × Array E × Array E)
    (res : List (Form bm) × BuildState bm) : Prop where
  grow : Grow cw l r σ st.1 st.2.1 res.2 n
  msize : st.2.2.size = 31
  low : ∀ i < 31 - n, st.2.2.getD i 0 = mj.getD i 0
  out : ∀ j < n, st.2.2.getD (31 - n + j) 0 = lev cw (res.1.getD j 0)

theorem sim_majorities (cw : Array E) {x y z : Word bm} {xw yw zw : Array E} (hx : WRel cw xw x)
    (hy : WRel cw yw y) (hz : WRel cw zw z) (base : ℕ) (hb : base + 61 ≤ 2 ^ bm) :
    ∀ n ≤ 31, ∀ (l r mj : Array E) (σ : BuildState bm),
      σ.next = base + (31 - n) → l.size = 2 ^ bm → r.size = 2 ^ bm → mj.size = 31 →
      MajSim cw n l r mj σ ((List.range' (31 - n) n).foldl (majStep cw xw yw zw base) (l, r, mj))
        ((majorities x y z n).run σ) := by
  intro n
  induction n with
  | zero =>
    intro _ l r mj σ _ _ _ hm
    rw [show List.range' (31 - 0) 0 = [] from rfl, List.foldl_nil, run_majorities_zero']
    exact ⟨Grow.refl _ _ _ _, hm, fun _ _ ↦ rfl, fun j hj ↦ absurd hj (by omega)⟩
  | succ n ih =>
    intro hn l r mj σ hσ hl hr hm
    have ha : 31 - (n + 1) + 1 = 31 - n := by omega
    have hnext : σ.next = base + (30 - n) := by omega
    rw [foldl_range'_succ, ha, run_majorities_succ', majStep]
    dsimp only
    have h30 : 31 - (n + 1) = 30 - n := by omega
    rw [h30]
    have H := ih (by omega) (l.set! (base + (30 - n)) (xw.getD (30 - n) 0 + zw.getD (30 - n) 0))
      (r.set! (base + (30 - n)) (yw.getD (30 - n) 0 + zw.getD (30 - n) 0))
      (mj.set! (30 - n) (cw.getD (base + (30 - n)) 0 + zw.getD (30 - n) 0))
      { next := σ.next + 1,
        gates := σ.gates.push (pos σ.next,
          ⟨x[30 - n]'(by omega) ^^^ z[30 - n]'(by omega), y[30 - n]'(by omega) ^^^ z[30 - n]'(by omega)⟩) }
      (by show σ.next + 1 = base + (31 - n); omega) (by rw [size_set!, hl]) (by rw [size_set!, hr])
      (by rw [size_set!, hm])
    have hpush := Grow.push cw (l := l) (r := r) σ hnext (x[30 - n]'(by omega) ^^^ z[30 - n]'(by omega))
      (y[30 - n]'(by omega) ^^^ z[30 - n]'(by omega))
      (va := xw.getD (30 - n) 0 + zw.getD (30 - n) 0) (vb := yw.getD (30 - n) 0 + zw.getD (30 - n) 0)
      (by rw [lev_xor, ← hx _ (by omega), ← hz _ (by omega)])
      (by rw [lev_xor, ← hy _ (by omega), ← hz _ (by omega)])
      (by rw [hl]; omega) (by rw [hr]; omega) (by omega)
    refine ⟨(hpush.trans H.grow).cast (by omega : 1 + n = n + 1), H.msize, fun i hi ↦ ?_, fun j hj ↦ ?_⟩
    · rw [H.low i (by omega), getD_set!_ne _ _ _ (by omega)]
    · rcases j with _ | j
      · rw [show 31 - (n + 1) + 0 = 30 - n by omega, H.low _ (by omega), getD_set!_self _ _ _ (by rw [hm]; omega),
          List.getD_cons_zero, lev_xor, lev_var_pos cw (show σ.next < 2 ^ bm by omega), hnext,
          hz (30 - n) (by omega)]
      · rw [show 31 - (n + 1) + (j + 1) = 31 - n + j by omega, H.out j (by omega)]
        simp

/-- What the ripple layer from bit `31 − n` (`n ≤ 30`) leaves. -/
structure RipSim (cw xw yw zw maj : Array E) (n : ℕ) (l r o : Array E) (σ : BuildState bm)
    (st : Array E × Array E × E × Array E) (res : List (Form bm) × BuildState bm) : Prop where
  grow : Grow cw l r σ st.1 st.2.1 res.2 n
  osize : st.2.2.2.size = 32
  low : ∀ i < 31 - n, st.2.2.2.getD i 0 = o.getD i 0
  out : ∀ j ≤ n, st.2.2.2.getD (31 - n + j) 0 =
    xw.getD (31 - n + j) 0 + yw.getD (31 - n + j) 0 + zw.getD (31 - n + j) 0 + lev cw (res.1.getD j 0) +
      maj.getD (31 - n + j - 1) 0

theorem sim_ripple (cw : Array E) {p q : Word bm} {xw yw zw maj : Array E}
    (hp : ∀ i (h : i < 32), lev cw (p[i]'h) = xw.getD i 0 + yw.getD i 0 + zw.getD i 0)
    (hq : ∀ i (h : i < 32), 1 ≤ i → lev cw (q[i]'h) = maj.getD (i - 1) 0) (rb : ℕ) (hb : rb + 30 ≤ 2 ^ bm) :
    ∀ n ≤ 30, ∀ (l r o : Array E) (cv : E) (σ : BuildState bm) (c : Form bm),
      lev cw c = cv → σ.next = rb + (30 - n) → l.size = 2 ^ bm → r.size = 2 ^ bm → o.size = 32 →
      RipSim cw xw yw zw maj n l r o σ
        ((List.range' (31 - n) (n + 1)).foldl (rippleStep cw xw yw zw maj rb) (l, r, cv, o))
        ((rippleCarries p q n c).run σ) := by
  intro n
  induction n with
  | zero =>
    intro _ l r o cv σ c hc _ _ _ ho
    rw [show List.range' (31 - 0) (0 + 1) = [31] from rfl, List.foldl_cons, List.foldl_nil, rippleStep_31,
      run_rippleCarries_zero']
    dsimp only
    refine ⟨Grow.refl _ _ _ _, by rw [size_set!, ho], fun i hi ↦ getD_set!_ne _ _ _ (by omega), fun j hj ↦ ?_⟩
    obtain rfl : j = 0 := by omega
    rw [getD_set!_self _ _ _ (by rw [ho]; omega)]
    simp [hc]
  | succ n ih =>
    intro hn l r o cv σ c hc hσ hl hr ho
    have ha : 31 - (n + 1) + 1 = 31 - n := by omega
    have hnext : σ.next = rb + (30 - n) - 1 := by omega
    have h30 : 31 - (n + 1) = 30 - n := by omega
    rw [foldl_range'_succ, ha, run_rippleCarries_gate' _ _ _ _ _ (by omega), h30,
      rippleStep_gate _ _ _ _ _ _ _ (by omega) (by omega)]
    dsimp only
    have hlev : lev cw (c ^^^ Form.var (pos σ.next)) = cv + cw.getD (rb + (30 - n) - 1) 0 := by
      rw [lev_xor, hc, lev_var_pos _ (by omega), hnext]
    have H := ih (by omega)
      (l.set! (rb + (30 - n) - 1) (xw.getD (30 - n) 0 + yw.getD (30 - n) 0 + zw.getD (30 - n) 0 + cv))
      (r.set! (rb + (30 - n) - 1) (maj.getD (30 - n - 1) 0 + cv))
      (o.set! (30 - n) (xw.getD (30 - n) 0 + yw.getD (30 - n) 0 + zw.getD (30 - n) 0 + cv +
        maj.getD (30 - n - 1) 0)) _
      { next := σ.next + 1,
        gates := σ.gates.push (pos σ.next, ⟨p[30 - n]'(by omega) ^^^ c, q[30 - n]'(by omega) ^^^ c⟩) } _
      hlev (by show σ.next + 1 = rb + (30 - n); omega) (by rw [size_set!, hl])
      (by rw [size_set!, hr]) (by rw [size_set!, ho])
    have hpush := Grow.push cw (l := l) (r := r) σ hnext (p[30 - n]'(by omega) ^^^ c) (q[30 - n]'(by omega) ^^^ c)
      (va := xw.getD (30 - n) 0 + yw.getD (30 - n) 0 + zw.getD (30 - n) 0 + cv)
      (vb := maj.getD (30 - n - 1) 0 + cv)
      (by rw [lev_xor, hp _ (by omega), hc]) (by rw [lev_xor, hq _ (by omega) (by omega), hc])
      (by rw [hl]; omega) (by rw [hr]; omega) (by omega)
    refine ⟨(hpush.trans H.grow).cast (by omega : 1 + n = n + 1), H.osize, fun i hi ↦ ?_, fun j hj ↦ ?_⟩
    · rw [H.low i (by omega), getD_set!_ne _ _ _ (by omega)]
    · rcases j with _ | j
      · rw [show 31 - (n + 1) + 0 = 30 - n by omega, H.low _ (by omega), getD_set!_self _ _ _ (by rw [ho]; omega)]
        simp [hc]
      · rw [show 31 - (n + 1) + (j + 1) = 31 - n + j by omega, H.out j (by omega)]
        simp

theorem lev_xor3W (cw : Array E) (x y z : Word bm) (i : ℕ) (h : i < 32) :
    lev cw ((xor3W x y z)[i]'h) = lev cw (x[i]'h) + lev cw (y[i]'h) + lev cw (z[i]'h) := by
  rw [xor3W, Vector.getElem_ofFn, lev_xor, lev_xor]
  rfl

theorem lev_sumW (cw : Array E) (p q : Word bm) (cs : List (Form bm)) (i : ℕ) (h : i < 32) :
    lev cw ((sumW p q cs)[i]'h) = lev cw (p[i]'h) + lev cw (q[i]'h) + lev cw (cs.getD i 0) := by
  rw [sumW, Vector.getElem_ofFn, lev_xor, lev_xor]
  rfl

theorem shiftW_getElem (ms : List (Form bm)) (i : ℕ) (h : i < 32) :
    (shiftW ms)[i]'h = if i = 0 then 0 else ms.getD (i - 1) 0 := by
  rw [shiftW, Vector.getElem_ofFn]

theorem wrel_xor3W {cw xw yw zw : Array E} {x y z : Word bm} (hx : WRel cw xw x) (hy : WRel cw yw y)
    (hz : WRel cw zw z) (i : ℕ) (h : i < 32) :
    lev cw ((xor3W x y z)[i]'h) = xw.getD i 0 + yw.getD i 0 + zw.getD i 0 := by
  rw [lev_xor3W, hx i h, hy i h, hz i h]

theorem MajSim.out31 {cw l r : Array E} {σ : BuildState bm} {m : Array E × Array E × Array E}
    {ms : List (Form bm) × BuildState bm} (HM : MajSim cw 31 l r (Array.replicate 31 0) σ m ms) :
    ∀ j < 31, m.2.2.getD j 0 = lev cw (ms.1.getD j 0) := fun j hj ↦ by
  have := HM.out j hj
  rwa [Nat.sub_self, Nat.zero_add] at this

theorem lev_shiftW_maj {cw mj : Array E} {ms : List (Form bm)}
    (hmaj : ∀ j < 31, mj.getD j 0 = lev cw (ms.getD j 0)) (i : ℕ) (h : i < 32) (hi : 1 ≤ i) :
    lev cw ((shiftW ms)[i]'h) = mj.getD (i - 1) 0 := by
  rw [shiftW_getElem, if_neg (show i ≠ 0 by omega), hmaj (i - 1) (by omega)]

/-- The ripple layer of `add3W` after its majority layer (`m`, `ms` the two sides' results, kept abstract so that
no fold is compared with another). -/
theorem sim_add3W_ripple (cw : Array E) {x y z : Word bm} {xw yw zw : Array E} (hx : WRel cw xw x)
    (hy : WRel cw yw y) (hz : WRel cw zw z) (l r : Array E) (σ : BuildState bm) (hl : l.size = 2 ^ bm)
    (hr : r.size = 2 ^ bm) (hfit : σ.next + 61 ≤ 2 ^ bm) (m : Array E × Array E × Array E)
    (ms : List (Form bm) × BuildState bm) (HM : MajSim cw 31 l r (Array.replicate 31 0) σ m ms) :
    Grow cw l r σ
        ((List.range' 0 32).foldl (rippleStep cw xw yw zw m.2.2 (σ.next + 31)) (m.1, m.2.1, 0, Array.replicate 32 0)).1
        ((List.range' 0 32).foldl (rippleStep cw xw yw zw m.2.2 (σ.next + 31))
          (m.1, m.2.1, 0, Array.replicate 32 0)).2.1
        ((rippleCarries (xor3W x y z) (shiftW ms.1) 31 0).run ms.2).2 61 ∧
      WRel cw
        ((List.range' 0 32).foldl (rippleStep cw xw yw zw m.2.2 (σ.next + 31))
          (m.1, m.2.1, 0, Array.replicate 32 0)).2.2.2
        (sumW (xor3W x y z) (shiftW ms.1) ((rippleCarries (xor3W x y z) (shiftW ms.1) 31 0).run ms.2).1) := by
  have hq := lev_shiftW_maj (MajSim.out31 HM)
  rw [run_rippleCarries_skip' _ _ _ _ _ (by omega), foldl_range'_succ, rippleStep_0]
  dsimp only
  have HR := sim_ripple cw (wrel_xor3W hx hy hz) hq (σ.next + 31) (by omega) 30 le_rfl m.1 m.2.1
    ((Array.replicate 32 0).set! 0 (xw.getD 0 0 + yw.getD 0 0 + zw.getD 0 0 + 0)) 0 ms.2 0 (lev_zero cw)
    (by have := HM.grow.next; omega) (by rw [HM.grow.lsize, hl]) (by rw [HM.grow.rsize, hr]) (by simp)
  rw [show 31 - 30 = 0 + 1 from rfl, show 30 + 1 = 31 from rfl] at HR
  refine ⟨(HM.grow.trans HR.grow).cast (by omega : 31 + 30 = 61), fun i hi ↦ ?_⟩
  rw [lev_sumW, wrel_xor3W hx hy hz i hi]
  rcases i with _ | i
  · rw [HR.low 0 (by omega), getD_set!_self _ _ _ (by simp), shiftW_getElem, if_pos rfl, lev_zero,
      List.getD_cons_zero, lev_zero]
    ring
  · have := HR.out i (by omega)
    rw [show 31 - 30 + i = i + 1 by omega] at this
    rw [this, hq _ hi (by omega), List.getD_cons_succ]
    ring

theorem sim_add3W (cw : Array E) {x y z : Word bm} {xw yw zw : Array E} (hx : WRel cw xw x) (hy : WRel cw yw y)
    (hz : WRel cw zw z) (l r : Array E) (σ : BuildState bm) (hl : l.size = 2 ^ bm) (hr : r.size = 2 ^ bm)
    (hfit : σ.next + 61 ≤ 2 ^ bm) :
    Grow cw l r σ (walkAdd3 cw l r xw yw zw σ.next).1 (walkAdd3 cw l r xw yw zw σ.next).2.1
        ((add3W x y z).run σ).2 61 ∧
      WRel cw (walkAdd3 cw l r xw yw zw σ.next).2.2 ((add3W x y z).run σ).1 := by
  rw [walkAdd3_eq, run_add3W', add3Model]
  dsimp only
  have HM := sim_majorities cw hx hy hz σ.next hfit 31 le_rfl l r (Array.replicate 31 0) σ (by omega) hl hr
    (by simp)
  rw [show 31 - 31 = 0 from rfl] at HM
  exact sim_add3W_ripple cw hx hy hz l r σ hl hr hfit _ _ HM

end FlockSound.Uni.Walk
