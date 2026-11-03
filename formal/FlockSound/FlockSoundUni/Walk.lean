-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The circuit is `formal/Lv42`'s (leanerVM `mumbai`
-- f0393df4's `Blake2sCircuit`, MIT OR Apache-2.0); the walk is `formal/UniStatement`'s (`UniStatement/Rec.lean`).
import FlockSoundUni.WalkCode

/-!
# The TowerWalk terminal's walk computes the BLAKE2s R1CS's products

π1-rec3's verifier (`Slices::TowerWalk`) checks Flock's lincheck terminal against `walked_terminal`, which walks the
BLAKE2s circuit once (`blake2s_row_values`, `crates/leanvm_flock_gas/src/flock.rs:318-388`) to get `A0 w` and `B0 w`.
**`rowValues_spec`** proves that the official transcription `UniStatement.Flock.blake2sRowValues` computes exactly
these: for every row `j < 2^14`,

  `(blake2sRowValues cw).1[j] = Σ_i A[j][i] cw[i]`,  `(blake2sRowValues cw).2[j] = Σ_i B[j][i] cw[i]`,

`A`, `B` the matrices of `Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs` (the R1CS of Lv42's `blake2sCircuit`,
row then column, as `flockMatrixStack` reads them). Nothing is evaluated: the proof is a simulation of the circuit's
builder (`Blake2sCircuit.compressW`) by the walk, gadget by gadget.

* **Forms and their evaluation** (`lev`): a builder form `L` (a bitset over the block) evaluates at the column
  weights to `Σ_{j ∈ L} cw[j]`; XOR is the sum (characteristic two), `var(pos)` is `cw[pos]` (`lev_xor`, `lev_var`).
  A walk word follows a builder word when each bit is the evaluation of the form (`WRel`): XOR, rotation, input
  slots and literals preserve it (`wrel_xor`, `wrel_rotr`, `wrel_slots`, `wrel_lit`).
* **The simulation relation** (`Grow`): the builder records `k` gates at `next, …, next + k − 1` and the walk writes,
  at those rows, the evaluations of the gates' two forms, every other row unchanged. It composes (`Grow.trans`).
* **The gadgets**: the walk's ripple adder follows `addW` (`sim_addW`, bit by bit against `addCarries`), its
  three-operand adder `add3W` (`sim_add3W`: the majority layer against `majorities`, the ripple against
  `rippleCarries`), the mixing step `gW` (`sim_gate`, 184 rows), a round `roundW` (`sim_round`, 1472 rows), the
  rounds (`sim_rounds`), the initial working vector (`srel_initState`).
* **The rows** (`rowModel_spec`): the input rows (`inputs_spec`), the gates' rows (from the simulation), the output
  rows (`outStep_fold`, `wrel_outWord`) and the constant row are the circuit's `rowOf` (`rowOf_gate`, `rowOf_out`,
  `rowOf_none`, via the gate list `gates_toList` and `List.lookup`).

**How the proofs avoid evaluating anything.** The walk's arrays have `2^14` entries and its loops thousands of steps,
so every definitional check must stay structural: `lev` is irreducible (else a failed match evaluates
`Finset.univ` over `Fin 16384`); results of the walk and of the builder are named through `∃ x, x = …` equations
rather than unfolded; facts about named stages are stated about the names and proven by rewriting the goal (never a
hypothesis holding a fold); arithmetic about builder positions is closed (`ring`, `fit_le`) when the context holds
large terms; and index side-goals get explicit bounds. (Each of these was found the hard way: the alternative times
out by unrolling a loop.)

**Decision (recorded):** the coordinator split the TowerWalk lemma; the algebra from these rows to `PendingHolds`
(`walkLemma_of_rows : RowsSpec → WalkLemma`) is on `lean-rec3-sound` (`FlockSoundUni/WalkAlg.lean`), so this module
stops at `rowValues_spec`, stated so that `fun cw hcw j ↦ rowValues_spec cw hcw j : RowsSpec`.

**Rust vs Lv42.** The proof is a line-by-line check that the walk matches Lv42's circuit: gate base 1280, stride
184 (`add3` at `+0`, `add` at `+61`, `add3` at `+92`, `add` at `+153`), majority rows `(x_i + z_i, y_i + z_i)`,
ripple rows for bits `1 … 30` at `base + 31 + i − 1`, adder rows `(x_i + c, y_i + c)` for bits `0 … 30`, the
rotations 16, 12, 8, 7, the lanes and the message schedule (`glanes_eq`, `sigma_zip`), the IV (`iv_getD`), the input
rows `0 … 255`, `640 … 1279`, the output rows `(out bit, w_512)` at `256 + 32 w + i`, the constant row at 512 and zero
rows elsewhere. No mismatch: had there been one, `rowValues_spec` would be false.
-/

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

/-- `sim_addW` at a named base and named results. -/
theorem sim_addW' (cw : Array E) {x y : Word bm} {xw yw : Array E} (hx : WRel cw xw x) (hy : WRel cw yw y)
    (l r : Array E) (σ : BuildState bm) (hl : l.size = 2 ^ bm) (hr : r.size = 2 ^ bm) {cb : ℕ}
    (hcb : σ.next = cb) (hfit : cb + 31 ≤ 2 ^ bm) (w : Array E × Array E × WalkWord)
    (hw : w = walkAdd cw l r xw yw cb) (b : Word bm × BuildState bm) (hb : b = (addW x y).run σ) :
    Grow cw l r σ w.1 w.2.1 b.2 31 ∧ WRel cw w.2.2 b.1 := by
  rw [hw, hb, ← hcb]
  exact sim_addW cw hx hy l r σ hl hr (by omega)

/-- `sim_add3W` at a named base and named results. -/
theorem sim_add3W' (cw : Array E) {x y z : Word bm} {xw yw zw : Array E} (hx : WRel cw xw x)
    (hy : WRel cw yw y) (hz : WRel cw zw z) (l r : Array E) (σ : BuildState bm) (hl : l.size = 2 ^ bm)
    (hr : r.size = 2 ^ bm) {cb : ℕ} (hcb : σ.next = cb) (hfit : cb + 61 ≤ 2 ^ bm)
    (w : Array E × Array E × WalkWord) (hw : w = walkAdd3 cw l r xw yw zw cb) (b : Word bm × BuildState bm)
    (hb : b = (add3W x y z).run σ) :
    Grow cw l r σ w.1 w.2.1 b.2 61 ∧ WRel cw w.2.2 b.1 := by
  rw [hw, hb, ← hcb]
  exact sim_add3W cw hx hy hz l r σ hl hr (by omega)

/-! ## The mixing step, a round, the rounds -/

/-- **The working vectors correspond**: sixteen walk words, each the evaluation of the builder's word. -/
def SRel (cw : Array E) (st : Array WalkWord) (v : Vector (Word bm) 16) : Prop :=
  st.size = 16 ∧ ∀ j : Fin 16, WRel cw (st.getD j #[]) v[j]

theorem SRel.set {cw : Array E} {st : Array WalkWord} {v : Vector (Word bm) 16} (hv : SRel cw st v)
    (j : Fin 16) {w : WalkWord} {x : Word bm} (hw : WRel cw w x) : SRel cw (st.set! j w) (v.set j x) := by
  refine ⟨by rw [size_set!, hv.1], fun k ↦ ?_⟩
  rw [getD_set!]
  by_cases h : (j : ℕ) = k
  · rw [if_pos ⟨h, by rw [hv.1]; exact j.isLt⟩]
    have e : (v.set j x)[k] = x := by simp [Fin.getElem_fin, Vector.getElem_set, h]
    rw [e]
    exact hw
  · rw [if_neg (fun h' ↦ h h'.1)]
    have e : (v.set j x)[k] = v[k] := by simp [Fin.getElem_fin, Vector.getElem_set, h]
    rw [e]
    exact hv.2 k

/-- The message words. -/
def msgV : Vector (Word bm) 16 := Vector.ofFn fun w ↦ Blake2sCircuit.msgW w

theorem wrel_msg (cw : Array E) (ix : Fin 16) : WRel cw (walkSlots cw (640 + 32 * (ix : ℕ))) msgV[ix] := by
  rw [msgV, Fin.getElem_fin, Vector.getElem_ofFn]
  exact wrel_slots cw (by have := ix.isLt; rw [two_pow_bm]; omega)

/-- A mixing step's walk, its base, lanes and message words as parameters (`gateStep` reads them from the round). -/
def gateRes (cw : Array E) (gb la lb lc ld : ℕ) (mx my : WalkWord) (st : Array E × Array E × Array WalkWord) :
    Array E × Array E × Array WalkWord :=
  let a := st.2.2.getD la #[]
  let b := st.2.2.getD lb #[]
  let c := st.2.2.getD lc #[]
  let d := st.2.2.getD ld #[]
  let r1 := walkAdd3 cw st.1 st.2.1 a b mx gb
  let d1 := walkRotr (walkXor d r1.2.2) 16
  let r2 := walkAdd cw r1.1 r1.2.1 c d1 (gb + 61)
  let b1 := walkRotr (walkXor b r2.2.2) 12
  let r3 := walkAdd3 cw r2.1 r2.2.1 r1.2.2 b1 my (gb + 92)
  let d2 := walkRotr (walkXor d1 r3.2.2) 8
  let r4 := walkAdd cw r3.1 r3.2.1 r2.2.2 d2 (gb + 153)
  let b2 := walkRotr (walkXor b1 r4.2.2) 7
  (r4.1, r4.2.1, (((st.2.2.set! la r3.2.2).set! lb b2).set! lc r4.2.2).set! ld d2)

theorem gateStep_eq (cw : Array E) (sigma : List ℕ) (ri : ℕ) (st : Array E × Array E × Array WalkWord)
    (lg : List ℕ × ℕ) :
    gateStep cw sigma ri st lg =
      gateRes cw (1280 + 184 * (ri * 8 + lg.2)) (lg.1.getD 0 0) (lg.1.getD 1 0) (lg.1.getD 2 0) (lg.1.getD 3 0)
        (walkSlots cw (640 + 32 * sigma.getD (2 * lg.2) 0)) (walkSlots cw (640 + 32 * sigma.getD (2 * lg.2 + 1) 0))
        st := rfl

/-- **A mixing step**: the walk's 184 rows from `next` are the gates `gW` records, and the working vectors still
correspond. -/
theorem sim_gate_core (cw : Array E) (w : Array E × Array E × Array WalkWord) (σ : BuildState bm)
    (hl : w.1.size = 2 ^ bm) (hr : w.2.1.size = 2 ^ bm) (hfit : σ.next + 184 ≤ 2 ^ bm) (v : Vector (Word bm) 16)
    (hv : SRel cw w.2.2 v) (a b c d : Fin 16) {mx my : Word bm} {mxw myw : Array E} (hmx : WRel cw mxw mx)
    (hmy : WRel cw myw my) :
    Grow cw w.1 w.2.1 σ (gateRes cw σ.next a b c d mxw myw w).1 (gateRes cw σ.next a b c d mxw myw w).2.1
        ((Blake2sCircuit.gW v a b c d mx my).run σ).2 184 ∧
      SRel cw (gateRes cw σ.next a b c d mxw myw w).2.2 ((Blake2sCircuit.gW v a b c d mx my).run σ).1 := by
  obtain ⟨w1, hw1⟩ : ∃ q, q = walkAdd3 cw w.1 w.2.1 (w.2.2.getD a #[]) (w.2.2.getD b #[]) mxw σ.next :=
    ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ p : Word bm × BuildState bm, p = (add3W v[a] v[b] mx).run σ := ⟨(add3W v[a] v[b] mx).run σ, rfl⟩
  have H1 := sim_add3W' cw (hv.2 a) (hv.2 b) hmx w.1 w.2.1 σ hl hr rfl (by omega) w1 hw1 b1 hb1
  obtain ⟨w2, hw2⟩ : ∃ q, q = walkAdd cw w1.1 w1.2.1 (w.2.2.getD c #[])
      (walkRotr (walkXor (w.2.2.getD d #[]) w1.2.2) 16) (σ.next + 61) := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ p : Word bm × BuildState bm, p = (addW v[c] (rotrW (xorW v[d] b1.1) 16)).run b1.2 := ⟨(addW v[c] (rotrW (xorW v[d] b1.1) 16)).run b1.2, rfl⟩
  have H2 := sim_addW' cw (hv.2 c) (wrel_rotr (wrel_xor (hv.2 d) H1.2) 16) w1.1 w1.2.1 b1.2
    (by rw [H1.1.lsize, hl]) (by rw [H1.1.rsize, hr]) H1.1.next (by omega) w2 hw2 b2 hb2
  obtain ⟨w3, hw3⟩ : ∃ q, q = walkAdd3 cw w2.1 w2.2.1 w1.2.2 (walkRotr (walkXor (w.2.2.getD b #[]) w2.2.2) 12)
      myw (σ.next + 92) := ⟨_, rfl⟩
  obtain ⟨b3, hb3⟩ : ∃ p : Word bm × BuildState bm, p = (add3W b1.1 (rotrW (xorW v[b] b2.1) 12) my).run b2.2 := ⟨(add3W b1.1 (rotrW (xorW v[b] b2.1) 12) my).run b2.2, rfl⟩
  have H3 := sim_add3W' cw H1.2 (wrel_rotr (wrel_xor (hv.2 b) H2.2) 12) hmy w2.1 w2.2.1 b2.2
    (by rw [H2.1.lsize, H1.1.lsize, hl]) (by rw [H2.1.rsize, H1.1.rsize, hr])
    (by rw [H2.1.next, H1.1.next]) (by omega) w3 hw3 b3 hb3
  obtain ⟨w4, hw4⟩ : ∃ q, q = walkAdd cw w3.1 w3.2.1 w2.2.2
      (walkRotr (walkXor (walkRotr (walkXor (w.2.2.getD d #[]) w1.2.2) 16) w3.2.2) 8) (σ.next + 153) := ⟨_, rfl⟩
  obtain ⟨b4, hb4⟩ : ∃ p : Word bm × BuildState bm, p = (addW b2.1 (rotrW (xorW (rotrW (xorW v[d] b1.1) 16) b3.1) 8)).run b3.2 := ⟨(addW b2.1 (rotrW (xorW (rotrW (xorW v[d] b1.1) 16) b3.1) 8)).run b3.2, rfl⟩
  have H4 := sim_addW' cw H2.2 (wrel_rotr (wrel_xor (wrel_rotr (wrel_xor (hv.2 d) H1.2) 16) H3.2) 8)
    w3.1 w3.2.1 b3.2 (by rw [H3.1.lsize, H2.1.lsize, H1.1.lsize, hl]) (by rw [H3.1.rsize, H2.1.rsize, H1.1.rsize, hr])
    (by rw [H3.1.next, H2.1.next, H1.1.next]) (by omega) w4 hw4 b4 hb4
  have hgate : gateRes cw σ.next a b c d mxw myw w =
      (w4.1, w4.2.1, (((w.2.2.set! a w3.2.2).set! b
        (walkRotr (walkXor (walkRotr (walkXor (w.2.2.getD b #[]) w2.2.2) 12) w4.2.2) 7)).set! c w4.2.2).set! d
        (walkRotr (walkXor (walkRotr (walkXor (w.2.2.getD d #[]) w1.2.2) 16) w3.2.2) 8)) := by
    subst hw4 hw3 hw2 hw1
    rfl
  have hrun : (Blake2sCircuit.gW v a b c d mx my).run σ =
      ((((v.set a b3.1).set b (rotrW (xorW (rotrW (xorW v[b] b2.1) 12) b4.1) 7)).set c b4.1).set d
        (rotrW (xorW (rotrW (xorW v[d] b1.1) 16) b3.1) 8), b4.2) := by
    rw [hb4, hb3, hb2, hb1]
    simp only [Blake2sCircuit.gW, StateT.run_bind, StateT.run_pure]
    rfl
  rw [hgate, hrun]
  refine ⟨((H1.1.trans H2.1).trans (H3.1.trans H4.1)).cast (by omega : 61 + 31 + (61 + 31) = 184), ?_⟩
  exact (((hv.set a H3.2).set b (wrel_rotr (wrel_xor (wrel_rotr (wrel_xor (hv.2 b) H2.2) 12) H4.2) 7)).set c
    H4.2).set d (wrel_rotr (wrel_xor (wrel_rotr (wrel_xor (hv.2 d) H1.2) 16) H3.2) 8)

/-- **`gateStep` follows `gW`**, its lanes and message indices read from the round. -/
theorem sim_gate (cw : Array E) (sigma : List ℕ) (ri g : ℕ) (lanes : List ℕ) (a b c d ix iy : Fin 16)
    (hla : lanes.getD 0 0 = a) (hlb : lanes.getD 1 0 = b) (hlc : lanes.getD 2 0 = c) (hld : lanes.getD 3 0 = d)
    (hix : sigma.getD (2 * g) 0 = ix) (hiy : sigma.getD (2 * g + 1) 0 = iy)
    (w : Array E × Array E × Array WalkWord) (σ : BuildState bm) (hσ : σ.next = 1280 + 184 * (ri * 8 + g))
    (hl : w.1.size = 2 ^ bm) (hr : w.2.1.size = 2 ^ bm) (hfit : σ.next + 184 ≤ 2 ^ bm)
    (v : Vector (Word bm) 16) (hv : SRel cw w.2.2 v) (w' : Array E × Array E × Array WalkWord)
    (hw' : w' = gateStep cw sigma ri w (lanes, g)) (b' : Vector (Word bm) 16 × BuildState bm)
    (hb' : b' = (Blake2sCircuit.gW v a b c d msgV[ix] msgV[iy]).run σ) :
    Grow cw w.1 w.2.1 σ w'.1 w'.2.1 b'.2 184 ∧ SRel cw w'.2.2 b'.1 := by
  have e : gateStep cw sigma ri w (lanes, g) = gateRes cw σ.next a b c d
      (walkSlots cw (640 + 32 * (ix : ℕ))) (walkSlots cw (640 + 32 * (iy : ℕ))) w := by
    rw [gateStep_eq]
    dsimp only
    rw [hla, hlb, hlc, hld, hix, hiy, ← hσ]
  rw [hw', hb', e]
  exact sim_gate_core cw w σ hl hr hfit v hv a b c d (wrel_msg cw ix) (wrel_msg cw iy)

theorem glanes_eq : blake2sGLanes.zip (List.range blake2sGLanes.length) =
    [([0, 4, 8, 12], 0), ([1, 5, 9, 13], 1), ([2, 6, 10, 14], 2), ([3, 7, 11, 15], 3),
      ([0, 5, 10, 15], 4), ([1, 6, 11, 12], 5), ([2, 7, 8, 13], 6), ([3, 4, 9, 14], 7)] := rfl

/-- **The simulation so far**, from the walk state `w0` and the builder state `σ0`, `n` gates recorded. -/
structure GInv (cw : Array E) (w0 : Array E × Array E × Array WalkWord) (σ0 : BuildState bm) (n : ℕ)
    (w : Array E × Array E × Array WalkWord) (b : Vector (Word bm) 16 × BuildState bm) : Prop where
  grow : Grow cw w0.1 w0.2.1 σ0 w.1 w.2.1 b.2 n
  srel : SRel cw w.2.2 b.1
  lsize : w.1.size = 2 ^ bm
  rsize : w.2.1.size = 2 ^ bm

theorem GInv.cast {cw : Array E} {w0 w : Array E × Array E × Array WalkWord} {σ0 : BuildState bm} {n n' : ℕ}
    {b : Vector (Word bm) 16 × BuildState bm} (H : GInv cw w0 σ0 n w b) (h : n = n') : GInv cw w0 σ0 n' w b :=
  h ▸ H

theorem GInv.start (cw : Array E) (w : Array E × Array E × Array WalkWord) (σ : BuildState bm)
    (v : Vector (Word bm) 16) (hv : SRel cw w.2.2 v) (hl : w.1.size = 2 ^ bm) (hr : w.2.1.size = 2 ^ bm) :
    GInv cw w σ 0 w (v, σ) :=
  ⟨Grow.refl _ _ _ _, hv, hl, hr⟩

/-- `GInv.start` with the walk state given by its components (so that no projection meets a closed term). -/
theorem GInv.start' (cw l r : Array E) (st : Array WalkWord) (σ : BuildState bm) (v : Vector (Word bm) 16)
    (hv : SRel cw st v) (hl : l.size = 2 ^ bm) (hr : r.size = 2 ^ bm) :
    GInv cw (l, r, st) σ 0 (l, r, st) (v, σ) :=
  ⟨Grow.refl _ _ _ _, hv, hl, hr⟩

/-- One more mixing step (gate `g` of round `ri`), the invariant carried; the arithmetic on `σ0.next + n`. -/
theorem GInv.step {cw : Array E} {w0 : Array E × Array E × Array WalkWord} {σ0 : BuildState bm} {n : ℕ}
    {w : Array E × Array E × Array WalkWord} {b : Vector (Word bm) 16 × BuildState bm}
    (H : GInv cw w0 σ0 n w b) (sigma : List ℕ) (ri g : ℕ) (lanes : List ℕ) (la lb lc ld ix iy : Fin 16)
    (hla : lanes.getD 0 0 = la) (hlb : lanes.getD 1 0 = lb) (hlc : lanes.getD 2 0 = lc) (hld : lanes.getD 3 0 = ld)
    (hix : sigma.getD (2 * g) 0 = ix) (hiy : sigma.getD (2 * g + 1) 0 = iy)
    (hσ : σ0.next + n = 1280 + 184 * (ri * 8 + g)) (hfit : σ0.next + n + 184 ≤ 2 ^ bm)
    (w' : Array E × Array E × Array WalkWord) (hw' : w' = gateStep cw sigma ri w (lanes, g))
    (b' : Vector (Word bm) 16 × BuildState bm)
    (hb' : b' = (Blake2sCircuit.gW b.1 la lb lc ld msgV[ix] msgV[iy]).run b.2) :
    GInv cw w0 σ0 (n + 184) w' b' := by
  have hn := H.grow.next
  have G := sim_gate cw sigma ri g lanes la lb lc ld ix iy hla hlb hlc hld hix hiy w b.2 (by omega) H.lsize H.rsize
    (by omega) b.1 H.srel w' hw' b' hb'
  exact ⟨H.grow.trans G.1, G.2, G.1.lsize.trans H.lsize, G.1.rsize.trans H.rsize⟩

theorem fit_le {a b c d : ℕ} (h : a + d ≤ b) (hc : c ≤ d) : a + c ≤ b := le_trans (Nat.add_le_add_left hc a) h

/-- A round's message indices, as the walk reads them. -/
def rowList (s : Vector (Fin 16) 16) : List ℕ := s.toList.map Fin.val

theorem rowList_getD (s : Vector (Fin 16) 16) (j : ℕ) (h : j < 16) : (rowList s).getD j 0 = (s[j]'h : ℕ) := by
  simp [rowList, List.getD_eq_getElem?_getD, h]

/-- **A round**: the walk's round follows `roundW`, 1472 more rows. -/
theorem sim_round (cw : Array E) (s : Vector (Fin 16) 16) (ri : ℕ) {w0 w : Array E × Array E × Array WalkWord}
    {σ0 : BuildState bm} {n : ℕ} {b : Vector (Word bm) 16 × BuildState bm} (H : GInv cw w0 σ0 n w b)
    (hσ : σ0.next + n = 1280 + 1472 * ri) (hfit : σ0.next + n + 1472 ≤ 2 ^ bm) :
    GInv cw w0 σ0 (n + 1472) (roundStep cw w (rowList s, ri)) ((Blake2sCircuit.roundW b.1 msgV s).run b.2) := by
  have hs : ∀ j (h : j < 16), (rowList s).getD j 0 = (s[j]'h : ℕ) := rowList_getD s
  have A0 : σ0.next + (n) = 1280 + 184 * (ri * 8 + 0) := by
    rw [show σ0.next + (n) = σ0.next + n + 184 * 0 by ring, hσ]; ring
  have F0 : σ0.next + (n) + 184 ≤ 2 ^ bm := by
    rw [show σ0.next + (n) + 184 = σ0.next + n + 184 * 1 by ring]; exact fit_le hfit (by norm_num)
  have A1 : σ0.next + (n + 184) = 1280 + 184 * (ri * 8 + 1) := by
    rw [show σ0.next + (n + 184) = σ0.next + n + 184 * 1 by ring, hσ]; ring
  have F1 : σ0.next + (n + 184) + 184 ≤ 2 ^ bm := by
    rw [show σ0.next + (n + 184) + 184 = σ0.next + n + 184 * 2 by ring]; exact fit_le hfit (by norm_num)
  have A2 : σ0.next + (n + 184 + 184) = 1280 + 184 * (ri * 8 + 2) := by
    rw [show σ0.next + (n + 184 + 184) = σ0.next + n + 184 * 2 by ring, hσ]; ring
  have F2 : σ0.next + (n + 184 + 184) + 184 ≤ 2 ^ bm := by
    rw [show σ0.next + (n + 184 + 184) + 184 = σ0.next + n + 184 * 3 by ring]; exact fit_le hfit (by norm_num)
  have A3 : σ0.next + (n + 184 + 184 + 184) = 1280 + 184 * (ri * 8 + 3) := by
    rw [show σ0.next + (n + 184 + 184 + 184) = σ0.next + n + 184 * 3 by ring, hσ]; ring
  have F3 : σ0.next + (n + 184 + 184 + 184) + 184 ≤ 2 ^ bm := by
    rw [show σ0.next + (n + 184 + 184 + 184) + 184 = σ0.next + n + 184 * 4 by ring]; exact fit_le hfit (by norm_num)
  have A4 : σ0.next + (n + 184 + 184 + 184 + 184) = 1280 + 184 * (ri * 8 + 4) := by
    rw [show σ0.next + (n + 184 + 184 + 184 + 184) = σ0.next + n + 184 * 4 by ring, hσ]; ring
  have F4 : σ0.next + (n + 184 + 184 + 184 + 184) + 184 ≤ 2 ^ bm := by
    rw [show σ0.next + (n + 184 + 184 + 184 + 184) + 184 = σ0.next + n + 184 * 5 by ring]; exact fit_le hfit (by norm_num)
  have A5 : σ0.next + (n + 184 + 184 + 184 + 184 + 184) = 1280 + 184 * (ri * 8 + 5) := by
    rw [show σ0.next + (n + 184 + 184 + 184 + 184 + 184) = σ0.next + n + 184 * 5 by ring, hσ]; ring
  have F5 : σ0.next + (n + 184 + 184 + 184 + 184 + 184) + 184 ≤ 2 ^ bm := by
    rw [show σ0.next + (n + 184 + 184 + 184 + 184 + 184) + 184 = σ0.next + n + 184 * 6 by ring]; exact fit_le hfit (by norm_num)
  have A6 : σ0.next + (n + 184 + 184 + 184 + 184 + 184 + 184) = 1280 + 184 * (ri * 8 + 6) := by
    rw [show σ0.next + (n + 184 + 184 + 184 + 184 + 184 + 184) = σ0.next + n + 184 * 6 by ring, hσ]; ring
  have F6 : σ0.next + (n + 184 + 184 + 184 + 184 + 184 + 184) + 184 ≤ 2 ^ bm := by
    rw [show σ0.next + (n + 184 + 184 + 184 + 184 + 184 + 184) + 184 = σ0.next + n + 184 * 7 by ring]; exact fit_le hfit (by norm_num)
  have A7 : σ0.next + (n + 184 + 184 + 184 + 184 + 184 + 184 + 184) = 1280 + 184 * (ri * 8 + 7) := by
    rw [show σ0.next + (n + 184 + 184 + 184 + 184 + 184 + 184 + 184) = σ0.next + n + 184 * 7 by ring, hσ]; ring
  have F7 : σ0.next + (n + 184 + 184 + 184 + 184 + 184 + 184 + 184) + 184 ≤ 2 ^ bm := by
    rw [show σ0.next + (n + 184 + 184 + 184 + 184 + 184 + 184 + 184) + 184 = σ0.next + n + 184 * 8 by ring]; exact fit_le hfit (by norm_num)
  obtain ⟨w1, hw1⟩ : ∃ q, q = gateStep cw (rowList s) ri w ([0, 4, 8, 12], 0) := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ p : Vector (Word bm) 16 × BuildState bm, p = (Blake2sCircuit.gW b.1 0 4 8 12 (msgV[s[0]'(by decide)]'(Fin.isLt _)) (msgV[s[1]'(by decide)]'(Fin.isLt _))).run b.2 := ⟨(Blake2sCircuit.gW b.1 0 4 8 12 (msgV[s[0]'(by decide)]'(Fin.isLt _)) (msgV[s[1]'(by decide)]'(Fin.isLt _))).run b.2, rfl⟩
  have R1 := H.step (rowList s) ri 0 [0, 4, 8, 12] 0 4 8 12 (s[0]'(by decide)) (s[1]'(by decide)) rfl rfl rfl rfl
    (hs (0) (by decide)) (hs (1) (by decide)) A0 F0 w1 hw1 b1 hb1
  obtain ⟨w2, hw2⟩ : ∃ q, q = gateStep cw (rowList s) ri w1 ([1, 5, 9, 13], 1) := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ p : Vector (Word bm) 16 × BuildState bm, p = (Blake2sCircuit.gW b1.1 1 5 9 13 (msgV[s[2]'(by decide)]'(Fin.isLt _)) (msgV[s[3]'(by decide)]'(Fin.isLt _))).run b1.2 := ⟨(Blake2sCircuit.gW b1.1 1 5 9 13 (msgV[s[2]'(by decide)]'(Fin.isLt _)) (msgV[s[3]'(by decide)]'(Fin.isLt _))).run b1.2, rfl⟩
  have R2 := R1.step (rowList s) ri 1 [1, 5, 9, 13] 1 5 9 13 (s[2]'(by decide)) (s[3]'(by decide)) rfl rfl rfl rfl
    (hs (2) (by decide)) (hs (3) (by decide)) A1 F1 w2 hw2 b2 hb2
  obtain ⟨w3, hw3⟩ : ∃ q, q = gateStep cw (rowList s) ri w2 ([2, 6, 10, 14], 2) := ⟨_, rfl⟩
  obtain ⟨b3, hb3⟩ : ∃ p : Vector (Word bm) 16 × BuildState bm, p = (Blake2sCircuit.gW b2.1 2 6 10 14 (msgV[s[4]'(by decide)]'(Fin.isLt _)) (msgV[s[5]'(by decide)]'(Fin.isLt _))).run b2.2 := ⟨(Blake2sCircuit.gW b2.1 2 6 10 14 (msgV[s[4]'(by decide)]'(Fin.isLt _)) (msgV[s[5]'(by decide)]'(Fin.isLt _))).run b2.2, rfl⟩
  have R3 := R2.step (rowList s) ri 2 [2, 6, 10, 14] 2 6 10 14 (s[4]'(by decide)) (s[5]'(by decide)) rfl rfl rfl rfl
    (hs (4) (by decide)) (hs (5) (by decide)) A2 F2 w3 hw3 b3 hb3
  obtain ⟨w4, hw4⟩ : ∃ q, q = gateStep cw (rowList s) ri w3 ([3, 7, 11, 15], 3) := ⟨_, rfl⟩
  obtain ⟨b4, hb4⟩ : ∃ p : Vector (Word bm) 16 × BuildState bm, p = (Blake2sCircuit.gW b3.1 3 7 11 15 (msgV[s[6]'(by decide)]'(Fin.isLt _)) (msgV[s[7]'(by decide)]'(Fin.isLt _))).run b3.2 := ⟨(Blake2sCircuit.gW b3.1 3 7 11 15 (msgV[s[6]'(by decide)]'(Fin.isLt _)) (msgV[s[7]'(by decide)]'(Fin.isLt _))).run b3.2, rfl⟩
  have R4 := R3.step (rowList s) ri 3 [3, 7, 11, 15] 3 7 11 15 (s[6]'(by decide)) (s[7]'(by decide)) rfl rfl rfl rfl
    (hs (6) (by decide)) (hs (7) (by decide)) A3 F3 w4 hw4 b4 hb4
  obtain ⟨w5, hw5⟩ : ∃ q, q = gateStep cw (rowList s) ri w4 ([0, 5, 10, 15], 4) := ⟨_, rfl⟩
  obtain ⟨b5, hb5⟩ : ∃ p : Vector (Word bm) 16 × BuildState bm, p = (Blake2sCircuit.gW b4.1 0 5 10 15 (msgV[s[8]'(by decide)]'(Fin.isLt _)) (msgV[s[9]'(by decide)]'(Fin.isLt _))).run b4.2 := ⟨(Blake2sCircuit.gW b4.1 0 5 10 15 (msgV[s[8]'(by decide)]'(Fin.isLt _)) (msgV[s[9]'(by decide)]'(Fin.isLt _))).run b4.2, rfl⟩
  have R5 := R4.step (rowList s) ri 4 [0, 5, 10, 15] 0 5 10 15 (s[8]'(by decide)) (s[9]'(by decide)) rfl rfl rfl rfl
    (hs (8) (by decide)) (hs (9) (by decide)) A4 F4 w5 hw5 b5 hb5
  obtain ⟨w6, hw6⟩ : ∃ q, q = gateStep cw (rowList s) ri w5 ([1, 6, 11, 12], 5) := ⟨_, rfl⟩
  obtain ⟨b6, hb6⟩ : ∃ p : Vector (Word bm) 16 × BuildState bm, p = (Blake2sCircuit.gW b5.1 1 6 11 12 (msgV[s[10]'(by decide)]'(Fin.isLt _)) (msgV[s[11]'(by decide)]'(Fin.isLt _))).run b5.2 := ⟨(Blake2sCircuit.gW b5.1 1 6 11 12 (msgV[s[10]'(by decide)]'(Fin.isLt _)) (msgV[s[11]'(by decide)]'(Fin.isLt _))).run b5.2, rfl⟩
  have R6 := R5.step (rowList s) ri 5 [1, 6, 11, 12] 1 6 11 12 (s[10]'(by decide)) (s[11]'(by decide)) rfl rfl rfl rfl
    (hs (10) (by decide)) (hs (11) (by decide)) A5 F5 w6 hw6 b6 hb6
  obtain ⟨w7, hw7⟩ : ∃ q, q = gateStep cw (rowList s) ri w6 ([2, 7, 8, 13], 6) := ⟨_, rfl⟩
  obtain ⟨b7, hb7⟩ : ∃ p : Vector (Word bm) 16 × BuildState bm, p = (Blake2sCircuit.gW b6.1 2 7 8 13 (msgV[s[12]'(by decide)]'(Fin.isLt _)) (msgV[s[13]'(by decide)]'(Fin.isLt _))).run b6.2 := ⟨(Blake2sCircuit.gW b6.1 2 7 8 13 (msgV[s[12]'(by decide)]'(Fin.isLt _)) (msgV[s[13]'(by decide)]'(Fin.isLt _))).run b6.2, rfl⟩
  have R7 := R6.step (rowList s) ri 6 [2, 7, 8, 13] 2 7 8 13 (s[12]'(by decide)) (s[13]'(by decide)) rfl rfl rfl rfl
    (hs (12) (by decide)) (hs (13) (by decide)) A6 F6 w7 hw7 b7 hb7
  obtain ⟨w8, hw8⟩ : ∃ q, q = gateStep cw (rowList s) ri w7 ([3, 4, 9, 14], 7) := ⟨_, rfl⟩
  obtain ⟨b8, hb8⟩ : ∃ p : Vector (Word bm) 16 × BuildState bm, p = (Blake2sCircuit.gW b7.1 3 4 9 14 (msgV[s[14]'(by decide)]'(Fin.isLt _)) (msgV[s[15]'(by decide)]'(Fin.isLt _))).run b7.2 := ⟨(Blake2sCircuit.gW b7.1 3 4 9 14 (msgV[s[14]'(by decide)]'(Fin.isLt _)) (msgV[s[15]'(by decide)]'(Fin.isLt _))).run b7.2, rfl⟩
  have R8 := R7.step (rowList s) ri 7 [3, 4, 9, 14] 3 4 9 14 (s[14]'(by decide)) (s[15]'(by decide)) rfl rfl rfl rfl
    (hs (14) (by decide)) (hs (15) (by decide)) A7 F7 w8 hw8 b8 hb8
  have hwalk : roundStep cw w (rowList s, ri) = w8 := by
    rw [hw8, hw7, hw6, hw5, hw4, hw3, hw2, hw1, roundStep, glanes_eq]
    simp only [List.foldl_cons, List.foldl_nil, Prod.mk.eta]
  have hrun : (Blake2sCircuit.roundW b.1 msgV s).run b.2 = b8 := by
    rw [hb8, hb7, hb6, hb5, hb4, hb3, hb2, hb1]
    simp only [Blake2sCircuit.roundW, StateT.run_bind]
    rfl
  rw [hwalk, hrun]
  exact R8.cast (by ring)

theorem run_foldlM_cons {α : Type} (f : α → Vector (Fin 16) 16 → Builder bm α) (s : Vector (Fin 16) 16)
    (L : List (Vector (Fin 16) 16)) (v : α) (σ : BuildState bm) :
    ((s :: L).foldlM f v).run σ = (L.foldlM f ((f v s).run σ).1).run ((f v s).run σ).2 := by
  rw [List.foldlM_cons, StateT.run_bind]
  rfl

/-- **The rounds**: the walk's rounds follow `roundW`'s fold, 1472 rows each. -/
theorem sim_rounds (cw : Array E) (w0 : Array E × Array E × Array WalkWord) (σ0 : BuildState bm) :
    ∀ (L : List (Vector (Fin 16) 16)) (ri n : ℕ) (w : Array E × Array E × Array WalkWord)
      (b : Vector (Word bm) 16 × BuildState bm), GInv cw w0 σ0 n w b →
      σ0.next + n = 1280 + 1472 * ri → σ0.next + n + 1472 * L.length ≤ 2 ^ bm →
      GInv cw w0 σ0 (n + 1472 * L.length) (((L.map rowList).zip (List.range' ri L.length)).foldl (roundStep cw) w)
        ((L.foldlM (fun v s ↦ Blake2sCircuit.roundW v msgV s) b.1).run b.2)
  | [], _, n, w, b, H, _, _ => H.cast (by simp)
  | s :: L, ri, n, w, b, H, hσ, hfit => by
    rw [List.map_cons, List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons,
      run_foldlM_cons]
    rw [List.length_cons] at hfit
    have R := sim_round cw s ri H hσ (fit_le hfit (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
    exact (sim_rounds cw w0 σ0 L (ri + 1) (n + 1472) _ _ R
      (by rw [show σ0.next + (n + 1472) = σ0.next + n + 1472 by ring, hσ]; ring)
      (by rw [show σ0.next + (n + 1472) + 1472 * L.length = σ0.next + n + 1472 * (L.length + 1) by ring]
          exact hfit)).cast (by ring)

/-! ## Folds of writes -/

theorem getD_foldl_set {α : Type} (g : ℕ → ℕ) (f : ℕ → α) (off : ℕ) (hg : ∀ w, g w = off + w) (d : α) :
    ∀ (n : ℕ) (s0 : Array α), off + n ≤ s0.size →
      ((List.range' 0 n).foldl (fun s w ↦ s.set! (g w) (f w)) s0).size = s0.size ∧
      ∀ j, ((List.range' 0 n).foldl (fun s w ↦ s.set! (g w) (f w)) s0).getD j d =
        if off ≤ j ∧ j < off + n then f (j - off) else s0.getD j d
  | 0, s0, _ => ⟨rfl, fun j ↦ by rw [if_neg (show ¬(off ≤ j ∧ j < off + 0) by omega)]; rfl⟩
  | n + 1, s0, h => by
    obtain ⟨hs, hv⟩ := getD_foldl_set g f off hg d n s0 (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.one_mul, Nat.zero_add]
    refine ⟨by rw [size_set!, hs], fun j ↦ ?_⟩
    rw [getD_set!, hv, hs, hg]
    split_ifs <;> first | (exfalso; omega) | rfl | (congr 1; omega)

/-! ## The initial working vector -/

theorem iv_getD (k : ℕ) (h : k < 8) : blake2sIv.getD k 0 = (Lv42.Parameters.iv[k]'h).toNat := by
  interval_cases k <;> rfl

theorem initState_getD (cw : Array E) :
    (initState cw).size = 16 ∧ ∀ j, j < 16 → (initState cw).getD j #[] =
      if j < 8 then walkSlots cw (32 * (j - 0)) else if j < 12 then walkLiteral cw (blake2sIv.getD (j - 8) 0)
      else walkXor (walkLiteral cw (blake2sIv.getD (4 + (j - 12)) 0)) (walkSlots cw (1152 + 32 * (j - 12))) := by
  have h3 : [1152, 1184, 1216, 1248].zip (List.range 4) = (List.range' 0 4).map (fun w ↦ (1152 + 32 * w, w)) :=
    rfl
  obtain ⟨s1, hs1⟩ : ∃ q, q = (List.range' 0 8).foldl (fun s w ↦ s.set! w (walkSlots cw (32 * w)))
      (Array.replicate 16 (Array.replicate 32 (0 : E))) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ q, q = (List.range' 0 4).foldl
      (fun s w ↦ s.set! (8 + w) (walkLiteral cw (blake2sIv.getD w 0))) s1 := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ q, q = (List.range' 0 4).foldl (fun s w ↦ s.set! (12 + w)
      (walkXor (walkLiteral cw (blake2sIv.getD (4 + w) 0)) (walkSlots cw (1152 + 32 * w)))) s2 := ⟨_, rfl⟩
  have e : initState cw = s3 := by
    rw [hs3, hs2, hs1]
    unfold initState
    dsimp only
    rw [h3, List.foldl_map]
  have H1 := getD_foldl_set (fun w ↦ w) (fun w ↦ walkSlots cw (32 * w)) 0 (fun w ↦ (Nat.zero_add w).symm)
    (#[] : Array E) 8 (Array.replicate 16 (Array.replicate 32 (0 : E))) (by simp)
  rw [← hs1] at H1
  have H2 := getD_foldl_set (fun w ↦ 8 + w) (fun w ↦ walkLiteral cw (blake2sIv.getD w 0)) 8 (fun w ↦ rfl)
    (#[] : Array E) 4 s1 (by rw [H1.1]; simp)
  rw [← hs2] at H2
  have H3 := getD_foldl_set (fun w ↦ 12 + w)
    (fun w ↦ walkXor (walkLiteral cw (blake2sIv.getD (4 + w) 0)) (walkSlots cw (1152 + 32 * w))) 12 (fun w ↦ rfl)
    (#[] : Array E) 4 s2 (by rw [H2.1, H1.1]; simp)
  rw [← hs3] at H3
  rw [e]
  refine ⟨by rw [H3.1, H2.1, H1.1]; simp, fun j hj ↦ ?_⟩
  rw [H3.2, H2.2, H1.2, getD_replicate]
  split_ifs <;> first | (exfalso; omega) | rfl

/-- **The initial working vector**: the walk's is the evaluation of the builder's `initW`. -/
theorem srel_initState (cw : Array E) : SRel cw (initState cw) Blake2sCircuit.initW := by
  obtain ⟨hsize, hget⟩ := initState_getD cw
  refine ⟨hsize, fun j ↦ ?_⟩
  have hj := j.isLt
  rw [hget j hj]
  simp only [Blake2sCircuit.initW, Fin.getElem_fin, Vector.getElem_ofFn]
  by_cases h8 : (j : ℕ) < 8
  · simp only [h8, ↓reduceIte]
    rw [Nat.sub_zero]
    exact wrel_slots cw (by rw [two_pow_bm]; omega)
  · by_cases h12 : (j : ℕ) < 12
    · simp only [h8, h12, ↓reduceIte]
      exact wrel_lit cw _ (iv_getD _ (by omega))
    · simp only [h8, h12, ↓reduceIte]
      rw [show 4 + ((j : ℕ) - 12) = (j : ℕ) - 8 by omega]
      exact wrel_xor (wrel_lit cw _ (iv_getD _ (by omega))) (wrel_slots cw (by rw [two_pow_bm]; omega))

/-! ## The input rows -/

theorem inputRow_fold (cw : Array E) (s : ℕ) : ∀ (n : ℕ) (b : Array E × Array E), s + n ≤ b.1.size →
    s + n ≤ b.2.size →
    ((List.range' s n).foldl (inputRow cw) b).1.size = b.1.size ∧
    ((List.range' s n).foldl (inputRow cw) b).2.size = b.2.size ∧
    ∀ j, ((List.range' s n).foldl (inputRow cw) b).1.getD j 0 =
        (if s ≤ j ∧ j < s + n then cw.getD j 0 else b.1.getD j 0) ∧
      ((List.range' s n).foldl (inputRow cw) b).2.getD j 0 =
        (if s ≤ j ∧ j < s + n then cw.getD constantColumn 0 else b.2.getD j 0)
  | 0, b, _, _ => ⟨rfl, rfl, fun j ↦ ⟨by rw [if_neg (show ¬(s ≤ j ∧ j < s + 0) by omega)]; rfl,
      by rw [if_neg (show ¬(s ≤ j ∧ j < s + 0) by omega)]; rfl⟩⟩
  | n + 1, b, h1, h2 => by
    obtain ⟨hs1, hs2, hv⟩ := inputRow_fold cw s n b (by omega) (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.one_mul]
    refine ⟨by rw [inputRow, size_set!, hs1], by rw [inputRow, size_set!, hs2], fun j ↦ ?_⟩
    rw [inputRow]
    dsimp only
    rw [getD_set!, getD_set!, (hv j).1, (hv j).2, hs1, hs2]
    constructor <;> split_ifs <;> first | (exfalso; omega) | rfl | (congr 1; omega)

/-- **The input rows**: `(w_j, w_512)` at the inputs `0 … 255`, `640 … 1279`, zero elsewhere. -/
theorem inputs_spec (cw : Array E) :
    ([(0, 256), (640, 512), (1152, 128)].foldl (inputRows cw)
        (Array.replicate (2 ^ blake2sR1csLogSize) (0 : E), Array.replicate (2 ^ blake2sR1csLogSize) (0 : E))).1.size =
        2 ^ bm ∧
    ([(0, 256), (640, 512), (1152, 128)].foldl (inputRows cw)
        (Array.replicate (2 ^ blake2sR1csLogSize) (0 : E), Array.replicate (2 ^ blake2sR1csLogSize) (0 : E))).2.size =
        2 ^ bm ∧
    ∀ j, ([(0, 256), (640, 512), (1152, 128)].foldl (inputRows cw)
        (Array.replicate (2 ^ blake2sR1csLogSize) (0 : E), Array.replicate (2 ^ blake2sR1csLogSize) (0 : E))).1.getD j 0 =
        (if j < 256 ∨ (640 ≤ j ∧ j < 1280) then cw.getD j 0 else 0) ∧
      ([(0, 256), (640, 512), (1152, 128)].foldl (inputRows cw)
        (Array.replicate (2 ^ blake2sR1csLogSize) (0 : E), Array.replicate (2 ^ blake2sR1csLogSize) (0 : E))).2.getD j 0 =
        (if j < 256 ∨ (640 ≤ j ∧ j < 1280) then cw.getD constantColumn 0 else 0) := by
  have hsz : (2 : ℕ) ^ blake2sR1csLogSize = 2 ^ bm := rfl
  simp only [List.foldl_cons, List.foldl_nil, inputRows, Prod.mk.eta]
  obtain ⟨a1, ha1⟩ : ∃ q, q = (List.range' 0 256).foldl (inputRow cw)
      (Array.replicate (2 ^ blake2sR1csLogSize) (0 : E), Array.replicate (2 ^ blake2sR1csLogSize) (0 : E)) :=
    ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ q, q = (List.range' 640 512).foldl (inputRow cw) a1 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ q, q = (List.range' 1152 128).foldl (inputRow cw) a2 := ⟨_, rfl⟩
  rw [← ha1, ← ha2, ← ha3]
  have I1 := inputRow_fold cw 0 256 (Array.replicate (2 ^ blake2sR1csLogSize) (0 : E),
    Array.replicate (2 ^ blake2sR1csLogSize) (0 : E)) (by simp [hsz, two_pow_bm]) (by simp [hsz, two_pow_bm])
  rw [← ha1] at I1
  have I2 := inputRow_fold cw 640 512 a1 (by rw [I1.1]; simp [hsz, two_pow_bm])
    (by rw [I1.2.1]; simp [hsz, two_pow_bm])
  rw [← ha2] at I2
  have I3 := inputRow_fold cw 1152 128 a2 (by rw [I2.1, I1.1]; simp [hsz, two_pow_bm])
    (by rw [I2.2.1, I1.2.1]; simp [hsz, two_pow_bm])
  rw [← ha3] at I3
  refine ⟨by rw [I3.1, I2.1, I1.1]; simp [hsz], by rw [I3.2.1, I2.2.1, I1.2.1]; simp [hsz], fun j ↦ ?_⟩
  rw [(I3.2.2 j).1, (I3.2.2 j).2, (I2.2.2 j).1, (I2.2.2 j).2, (I1.2.2 j).1, (I1.2.2 j).2]
  simp only [getD_replicate]
  constructor <;> split_ifs <;> first | (exfalso; omega) | rfl

/-! ## The output rows -/

theorem outBit_fold (cw out : Array E) (word : ℕ) : ∀ (n : ℕ) (b : Array E × Array E),
    256 + 32 * word + n ≤ b.1.size → 256 + 32 * word + n ≤ b.2.size →
    ((List.range' 0 n).foldl (outBit cw out word) b).1.size = b.1.size ∧
    ((List.range' 0 n).foldl (outBit cw out word) b).2.size = b.2.size ∧
    ∀ j, ((List.range' 0 n).foldl (outBit cw out word) b).1.getD j 0 =
        (if 256 + 32 * word ≤ j ∧ j < 256 + 32 * word + n then out.getD (j - (256 + 32 * word)) 0
          else b.1.getD j 0) ∧
      ((List.range' 0 n).foldl (outBit cw out word) b).2.getD j 0 =
        (if 256 + 32 * word ≤ j ∧ j < 256 + 32 * word + n then cw.getD constantColumn 0 else b.2.getD j 0)
  | 0, b, _, _ => ⟨rfl, rfl, fun j ↦
      ⟨by rw [if_neg (show ¬(256 + 32 * word ≤ j ∧ j < 256 + 32 * word + 0) by omega)]; rfl,
        by rw [if_neg (show ¬(256 + 32 * word ≤ j ∧ j < 256 + 32 * word + 0) by omega)]; rfl⟩⟩
  | n + 1, b, h1, h2 => by
    obtain ⟨hs1, hs2, hv⟩ := outBit_fold cw out word n b (by omega) (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.one_mul, Nat.zero_add]
    refine ⟨by rw [outBit, size_set!, hs1], by rw [outBit, size_set!, hs2], fun j ↦ ?_⟩
    rw [outBit]
    dsimp only
    rw [getD_set!, getD_set!, (hv j).1, (hv j).2, hs1, hs2]
    constructor <;> split_ifs <;> first | (exfalso; omega) | rfl | (congr 1; omega)

theorem outStep_fold (cw : Array E) (state : Array WalkWord) : ∀ (W : ℕ) (b : Array E × Array E),
    256 + 32 * W ≤ b.1.size → 256 + 32 * W ≤ b.2.size →
    ((List.range' 0 W).foldl (outStep cw state) b).1.size = b.1.size ∧
    ((List.range' 0 W).foldl (outStep cw state) b).2.size = b.2.size ∧
    ∀ j, ((List.range' 0 W).foldl (outStep cw state) b).1.getD j 0 =
        (if 256 ≤ j ∧ j < 256 + 32 * W then (outWord cw state ((j - 256) / 32)).getD ((j - 256) % 32) 0
          else b.1.getD j 0) ∧
      ((List.range' 0 W).foldl (outStep cw state) b).2.getD j 0 =
        (if 256 ≤ j ∧ j < 256 + 32 * W then cw.getD constantColumn 0 else b.2.getD j 0)
  | 0, b, _, _ => ⟨rfl, rfl, fun j ↦
      ⟨by rw [if_neg (show ¬(256 ≤ j ∧ j < 256 + 32 * 0) by omega)]; rfl,
        by rw [if_neg (show ¬(256 ≤ j ∧ j < 256 + 32 * 0) by omega)]; rfl⟩⟩
  | W + 1, b, h1, h2 => by
    obtain ⟨hs1, hs2, hv⟩ := outStep_fold cw state W b (by omega) (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.one_mul, Nat.zero_add, outStep, Prod.mk.eta]
    have O := outBit_fold cw (outWord cw state W) W 32 ((List.range' 0 W).foldl (outStep cw state) b)
      (by rw [hs1]; omega) (by rw [hs2]; omega)
    refine ⟨by rw [O.1, hs1], by rw [O.2.1, hs2], fun j ↦ ?_⟩
    rw [(O.2.2 j).1, (O.2.2 j).2, (hv j).1, (hv j).2]
    clear O hv hs1 hs2 h1 h2
    constructor <;> split_ifs <;> first | (exfalso; omega) |
      (rw [show (j - 256) / 32 = W by omega, show (j - 256) % 32 = j - (256 + 32 * W) by omega]) | rfl

/-! ## The circuit's rows -/

section Lookup

variable {β : Type}

theorem lookup_eq_none_of {l : List (ProductCircuit.Pos bm × β)} {k : ProductCircuit.Pos bm}
    (h : ∀ p ∈ l, p.1 ≠ k) : l.lookup k = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', b'⟩ := p
    have hk : (k == k') = false := beq_eq_false_iff_ne.mpr (Ne.symm (h _ (List.mem_cons.mpr (Or.inl rfl))))
    simp only [List.lookup, hk]
    exact ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq)

theorem mem_of_lookup_eq_some {l : List (ProductCircuit.Pos bm × β)} {k : ProductCircuit.Pos bm} {b : β}
    (h : l.lookup k = some b) : (k, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p l ih =>
    obtain ⟨k', b'⟩ := p
    by_cases hk : k = k'
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons.mpr (Or.inl rfl)
    · have hk' : (k == k') = false := beq_eq_false_iff_ne.mpr hk
      simp only [List.lookup, hk'] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookup_isSome_of_mem {l : List (ProductCircuit.Pos bm × β)} {k : ProductCircuit.Pos bm} {b : β}
    (h : (k, b) ∈ l) : ∃ b', l.lookup k = some b' := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k', b''⟩ := p
    by_cases hk : k = k'
    · subst hk
      exact ⟨b'', by simp only [List.lookup, beq_self_eq_true]⟩
    · have hk' : (k == k') = false := beq_eq_false_iff_ne.mpr hk
      simp only [List.lookup, hk']
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd (congrArg Prod.fst h') hk
      · exact ih h'

theorem lookup_append_of_none {l1 l2 : List (ProductCircuit.Pos bm × β)} {k : ProductCircuit.Pos bm}
    (h : l1.lookup k = none) : (l1 ++ l2).lookup k = l2.lookup k := by
  induction l1 with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', b'⟩ := p
    by_cases hk : k = k'
    · subst hk
      simp [List.lookup] at h
    · have hk' : (k == k') = false := beq_eq_false_iff_ne.mpr hk
      simp only [List.lookup, hk'] at h
      simp only [List.cons_append, List.lookup, hk']
      exact ih h

end Lookup

theorem rowOf_of_lookup_some (c : ProductCircuit bm) (k : ProductCircuit.Pos bm) (g : Gate bm)
    (h : c.gates.toList.lookup k = some g) : c.rowOf k = g := by
  unfold ProductCircuit.rowOf
  rw [h]

theorem rowOf_of_lookup_none (c : ProductCircuit bm) (k : ProductCircuit.Pos bm)
    (h : c.gates.toList.lookup k = none) :
    c.rowOf k = if k = c.cpos then ⟨Form.var c.cpos, Form.var c.cpos⟩
      else if c.inputs.getLsbD k then ⟨Form.var k, Form.var c.cpos⟩ else ⟨0, 0⟩ := by
  unfold ProductCircuit.rowOf
  rw [h]

theorem mem_outRows' {outs : Vector (Word bm) 8} {kg : ProductCircuit.Pos bm × Gate bm}
    (h : kg ∈ Blake2sCircuit.outRows outs) :
    ∃ (w : Fin 8) (i : Fin 32),
      kg = (pos (256 + 32 * w.val + i.val), ⟨outs[w][i], Form.var Lv42.Parameters.Flock.constPos⟩) := by
  unfold Blake2sCircuit.outRows at h
  simp only [List.mem_flatMap, List.mem_finRange, List.mem_map, true_and] at h
  obtain ⟨w, i, rfl⟩ := h
  exact ⟨w, i, rfl⟩

theorem outRows_pos {outs : Vector (Word bm) 8} {kg : ProductCircuit.Pos bm × Gate bm}
    (h : kg ∈ Blake2sCircuit.outRows outs) : 256 ≤ (kg.1 : ℕ) ∧ (kg.1 : ℕ) < 512 := by
  obtain ⟨w, i, rfl⟩ := mem_outRows' h
  have := w.isLt
  have := i.isLt
  dsimp only
  rw [pos_val (by rw [two_pow_bm]; omega)]
  omega

theorem mem_outRows_of (outs : Vector (Word bm) 8) (w : Fin 8) (i : Fin 32) :
    (pos (256 + 32 * w.val + i.val),
      (⟨outs[w][i], Form.var Lv42.Parameters.Flock.constPos⟩ : Gate bm)) ∈ Blake2sCircuit.outRows outs :=
  List.mem_flatMap.mpr ⟨w, List.mem_finRange w, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩

/-- The compression's output words, from the rounds' final working vector. -/
def outsOf (V : Vector (Word bm) 16) : Vector (Word bm) 8 :=
  Vector.ofFn fun w : Fin 8 ↦ xorW (xorW V[w] V[w.val + 8]) (Blake2sCircuit.cvW w)

/-- The builder's run of the ten rounds from `1280`, as `compressW` writes it. -/
def roundsRun : Vector (Word bm) 16 × BuildState bm :=
  (Lv42.Parameters.sigma.foldlM (fun v s ↦ Blake2sCircuit.roundW v (Vector.ofFn fun w ↦ Blake2sCircuit.msgW w) s)
    Blake2sCircuit.initW).run ⟨Blake2sCircuit.gateBase, #[]⟩

/-- `roundsRun` as the list fold `sim_rounds` follows. -/
theorem roundsRun_toList : roundsRun =
    (Lv42.Parameters.sigma.toList.foldlM (fun v s ↦ Blake2sCircuit.roundW v msgV s) Blake2sCircuit.initW).run
      ⟨Blake2sCircuit.gateBase, #[]⟩ := by
  rw [roundsRun, ← Vector.foldlM_toList, msgV]

theorem compressW_run :
    Blake2sCircuit.compressW.run ⟨Blake2sCircuit.gateBase, #[]⟩ = (outsOf roundsRun.1, roundsRun.2) := by
  simp only [Blake2sCircuit.compressW, StateT.run_bind, StateT.run_pure]
  rfl

theorem gates_toList : Blake2sCircuit.blake2sCircuit.gates.toList =
    roundsRun.2.gates.toList ++ Blake2sCircuit.outRows (outsOf roundsRun.1) := by
  rw [Blake2sCircuit.blake2sCircuit_gates, compressW_run]
  simp

theorem sigma_zip : blake2sSigma.zip (List.range blake2sSigma.length) =
    (Lv42.Parameters.sigma.toList.map rowList).zip (List.range' 0 Lv42.Parameters.sigma.toList.length) := rfl

theorem wrel_outWord (cw : Array E) {st : Array WalkWord} {V : Vector (Word bm) 16} (h : SRel cw st V)
    (w : Fin 8) : WRel cw (outWord cw st w) (outsOf V)[w] := by
  rw [outsOf, Fin.getElem_fin, Vector.getElem_ofFn]
  have hw := w.isLt
  exact wrel_xor (wrel_xor (h.2 ⟨w, by omega⟩) (h.2 ⟨w + 8, by omega⟩)) (wrel_slots cw (by rw [two_pow_bm]; omega))

/-- `A`, `B` of the BLAKE2s R1CS (`blake2sFlockSpec.r1cs`, as `flockMatrixStack` reads them) are the rows' forms. -/
theorem r1csA_eq (j i : Fin (2 ^ 14)) :
    Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A j i = (Blake2sCircuit.blake2sCircuit.rowOf j).a.getLsbD i :=
  rfl

theorem r1csB_eq (j i : Fin (2 ^ 14)) :
    Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B j i = (Blake2sCircuit.blake2sCircuit.rowOf j).b.getLsbD i :=
  rfl

/-- `lev` as the sum over `Fin (2^14)`. -/
theorem lev_eq_sum (cw : Array E) (L : Form bm) :
    lev cw L = ∑ i : Fin (2 ^ 14), (if L.getLsbD i then cw.getD i 0 else 0) := by
  unfold lev
  rfl

theorem lev_rowA (cw : Array E) (j : Fin (2 ^ 14)) :
    lev cw (Blake2sCircuit.blake2sCircuit.rowOf j).a =
      ∑ i : Fin (2 ^ 14), (if Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A j i then cw.getD i 0 else 0) := by
  rw [lev_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [r1csA_eq]

theorem lev_rowB (cw : Array E) (j : Fin (2 ^ 14)) :
    lev cw (Blake2sCircuit.blake2sCircuit.rowOf j).b =
      ∑ i : Fin (2 ^ 14), (if Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B j i then cw.getD i 0 else 0) := by
  rw [lev_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [r1csB_eq]

/-- **A gate's row**: at a gate position, `rowOf` is a gate the rounds recorded at that position. -/
theorem rowOf_gate (k : ProductCircuit.Pos bm) (hC : 1280 ≤ (k : ℕ) ∧ (k : ℕ) < 16000)
    (hpos : roundsRun.2.gates.toList.map (fun g ↦ (g.1 : ℕ)) = List.range' 1280 14720) :
    ∃ g', (k, g') ∈ roundsRun.2.gates.toList ∧ Blake2sCircuit.blake2sCircuit.rowOf k = g' := by
  obtain ⟨g, hg, hgk⟩ : ∃ g ∈ roundsRun.2.gates.toList, (g.1 : ℕ) = k := by
    have hm : (k : ℕ) ∈ (roundsRun.2.gates.toList).map (fun g ↦ (g.1 : ℕ)) := by
      rw [hpos, List.mem_range'_1]
      omega
    simpa using hm
  have hgk' : g.1 = k := Fin.ext hgk
  obtain ⟨g', hg'⟩ := lookup_isSome_of_mem (l := Blake2sCircuit.blake2sCircuit.gates.toList) (k := k) (b := g.2)
    (by rw [gates_toList, ← hgk']; exact List.mem_append_left _ hg)
  have hmem := mem_of_lookup_eq_some hg'
  rw [gates_toList] at hmem
  rcases List.mem_append.mp hmem with hm | hm
  · exact ⟨g', hm, rowOf_of_lookup_some _ _ _ hg'⟩
  · have := outRows_pos hm
    dsimp only at this
    omega

/-- **An output row**: at `256 + 32 w + i`, `rowOf` is `(out_w bit i, 1)`. -/
theorem rowOf_out (k : ProductCircuit.Pos bm) (hB : 256 ≤ (k : ℕ) ∧ (k : ℕ) < 512)
    (hnewpos : ∀ g ∈ roundsRun.2.gates.toList, 1280 ≤ (g.1 : ℕ)) :
    ∃ (w : Fin 8) (i : Fin 32), (w : ℕ) = ((k : ℕ) - 256) / 32 ∧ (i : ℕ) = ((k : ℕ) - 256) % 32 ∧
      Blake2sCircuit.blake2sCircuit.rowOf k =
        ⟨(outsOf roundsRun.1)[w][i], Form.var Lv42.Parameters.Flock.constPos⟩ := by
  have hk := k.isLt
  have h2 := two_pow_bm
  have hwlt : ((k : ℕ) - 256) / 32 < 8 := by omega
  have hilt : ((k : ℕ) - 256) % 32 < 32 := by omega
  obtain ⟨w, hw⟩ : ∃ w : Fin 8, (w : ℕ) = ((k : ℕ) - 256) / 32 := ⟨⟨_, hwlt⟩, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin 32, (i : ℕ) = ((k : ℕ) - 256) % 32 := ⟨⟨_, hilt⟩, rfl⟩
  refine ⟨w, i, hw, hi, ?_⟩
  have e : (pos (256 + 32 * w.val + i.val) : ProductCircuit.Pos bm) = k := by
    apply Fin.ext
    rw [pos_val (by omega)]
    omega
  have hmem : (k, (⟨((outsOf roundsRun.1)[w]'w.isLt)[i]'i.isLt, Form.var Lv42.Parameters.Flock.constPos⟩ :
      Gate bm)) ∈ Blake2sCircuit.blake2sCircuit.gates.toList := by
    rw [gates_toList]
    refine List.mem_append_right _ ?_
    have := mem_outRows_of (outsOf roundsRun.1) w i
    rw [e] at this
    exact this
  obtain ⟨g', hg'⟩ := lookup_isSome_of_mem hmem
  have hmem' := mem_of_lookup_eq_some hg'
  rw [gates_toList] at hmem'
  rw [rowOf_of_lookup_some _ _ _ hg']
  rcases List.mem_append.mp hmem' with hm | hm
  · have := hnewpos _ hm
    dsimp only at this
    omega
  · obtain ⟨w', i', he⟩ := mem_outRows' hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨he1, he2⟩ := he
    have hw' := w'.isLt
    have hi' := i'.isLt
    have hv : (k : ℕ) = 256 + 32 * w'.val + i'.val := by
      rw [he1, pos_val (by omega)]
    have hww : w' = w := Fin.ext (by omega)
    have hii : i' = i := Fin.ext (by omega)
    rw [he2, hww, hii]

/-- **Neither a gate's nor an output row**: `rowOf` is the constant's row, an input's, or zero. -/
theorem rowOf_none (k : ProductCircuit.Pos bm) (hC : ¬(1280 ≤ (k : ℕ) ∧ (k : ℕ) < 16000))
    (hB : ¬(256 ≤ (k : ℕ) ∧ (k : ℕ) < 512))
    (hnewpos : ∀ g ∈ roundsRun.2.gates.toList, 1280 ≤ (g.1 : ℕ) ∧ (g.1 : ℕ) < 16000) :
    Blake2sCircuit.blake2sCircuit.rowOf k =
      if k = Lv42.Parameters.Flock.constPos then
        ⟨Form.var Lv42.Parameters.Flock.constPos, Form.var Lv42.Parameters.Flock.constPos⟩
      else if (k : ℕ) < 256 ∨ (640 ≤ (k : ℕ) ∧ (k : ℕ) < 1280) then
        ⟨Form.var k, Form.var Lv42.Parameters.Flock.constPos⟩
      else ⟨0, 0⟩ := by
  have hnone : Blake2sCircuit.blake2sCircuit.gates.toList.lookup k = none := by
    rw [gates_toList, lookup_append_of_none (lookup_eq_none_of fun p hp hpk ↦ by
      have := hnewpos p hp
      rw [hpk] at this
      omega)]
    exact lookup_eq_none_of fun p hp hpk ↦ by
      have := outRows_pos hp
      rw [hpk] at this
      omega
  rw [rowOf_of_lookup_none _ _ hnone, Blake2sCircuit.blake2sCircuit_cpos, Blake2sCircuit.blake2sCircuit_inputs,
    Blake2sCircuit.getLsbD_inputs]
  simp only [decide_eq_true_eq]

/-- **The walk's rows are the circuit's**: row `k` of `rowModel cw` (the walk) holds the linear evaluations of
`rowOf blake2sCircuit k`'s two forms. -/
theorem rowModel_spec (cw : Array E) (k : ProductCircuit.Pos bm) :
    (rowModel cw).1.getD k 0 = lev cw (Blake2sCircuit.blake2sCircuit.rowOf k).a ∧
      (rowModel cw).2.getD k 0 = lev cw (Blake2sCircuit.blake2sCircuit.rowOf k).b := by
  have hk : (k : ℕ) < 16384 := k.isLt
  have hgb : Blake2sCircuit.gateBase = 1280 := rfl
  -- the walk's stages, named
  obtain ⟨st1, hst1⟩ : ∃ q, q = [(0, 256), (640, 512), (1152, 128)].foldl (inputRows cw)
      (Array.replicate (2 ^ blake2sR1csLogSize) (0 : E), Array.replicate (2 ^ blake2sR1csLogSize) (0 : E)) :=
    ⟨_, rfl⟩
  obtain ⟨st2, hst2⟩ : ∃ q, q = (blake2sSigma.zip (List.range blake2sSigma.length)).foldl (roundStep cw)
      (st1.1, st1.2, initState cw) := ⟨_, rfl⟩
  obtain ⟨st3, hst3⟩ : ∃ q, q = (List.range' 0 8).foldl (outStep cw st2.2.2) (st2.1, st2.2.1) := ⟨_, rfl⟩
  have hrm : rowModel cw = (st3.1.set! constantColumn (cw.getD constantColumn 0),
      st3.2.set! constantColumn (cw.getD constantColumn 0)) := by
    rw [hst3, hst2, hst1]
    rfl
  obtain ⟨I1s, I2s, Iv⟩ : st1.1.size = 2 ^ bm ∧ st1.2.size = 2 ^ bm ∧
      ∀ j, st1.1.getD j 0 = (if j < 256 ∨ (640 ≤ j ∧ j < 1280) then cw.getD j 0 else 0) ∧
        st1.2.getD j 0 = (if j < 256 ∨ (640 ≤ j ∧ j < 1280) then cw.getD constantColumn 0 else 0) := by
    rw [hst1]
    exact inputs_spec cw
  -- the rounds
  have H0 := GInv.start' cw st1.1 st1.2 (initState cw) ⟨Blake2sCircuit.gateBase, #[]⟩ Blake2sCircuit.initW
    (srel_initState cw) I1s I2s
  have R0 := sim_rounds cw _ _ Lv42.Parameters.sigma.toList 0 0 _ _ H0 rfl (by simp [two_pow_bm, hgb])
  dsimp only at R0
  rw [Vector.length_toList] at R0
  have R : GInv cw (st1.1, st1.2, initState cw) ⟨Blake2sCircuit.gateBase, #[]⟩ 14720 st2 roundsRun := by
    rw [hst2, sigma_zip, roundsRun_toList]
    exact R0.cast (by norm_num)
  obtain ⟨new, hnew, hpos, hval⟩ := R.grow.gates
  have hnew' : roundsRun.2.gates.toList = new := by rw [hnew]; rfl
  rw [← hnew'] at hpos hval
  dsimp only at hpos
  have hnewpos : ∀ g ∈ roundsRun.2.gates.toList, 1280 ≤ (g.1 : ℕ) ∧ (g.1 : ℕ) < 16000 := fun g hg ↦ by
    have hm := List.mem_map_of_mem (f := fun g : ProductCircuit.Pos bm × Gate bm ↦ (g.1 : ℕ)) hg
    rw [hpos, List.mem_range'_1] at hm
    omega
  -- the output rows
  obtain ⟨O1s, O2s, Ov⟩ : st3.1.size = st2.1.size ∧ st3.2.size = st2.2.1.size ∧
      ∀ j, st3.1.getD j 0 = (if 256 ≤ j ∧ j < 256 + 32 * 8 then
          (outWord cw st2.2.2 ((j - 256) / 32)).getD ((j - 256) % 32) 0 else st2.1.getD j 0) ∧
        st3.2.getD j 0 = (if 256 ≤ j ∧ j < 256 + 32 * 8 then cw.getD constantColumn 0 else st2.2.1.getD j 0) := by
    rw [hst3]
    exact outStep_fold cw st2.2.2 8 (st2.1, st2.2.1) (by rw [R.lsize, two_pow_bm]; omega)
      (by rw [R.rsize, two_pow_bm]; omega)
  rw [hrm]
  dsimp only
  rw [getD_set!, getD_set!, O1s, O2s, R.lsize, R.rsize, (Ov k).1, (Ov k).2,
    show (constantColumn : ℕ) = 512 from rfl]
  have h2 := two_pow_bm
  by_cases hC : 1280 ≤ (k : ℕ) ∧ (k : ℕ) < 16000
  · -- a gate's row
    obtain ⟨g', hm, hrow⟩ := rowOf_gate k hC (by rw [hpos])
    obtain ⟨hva, hvb⟩ := hval _ hm
    have n1 : ¬(512 = (k : ℕ) ∧ 512 < 2 ^ bm) := by omega
    have n2 : ¬(256 ≤ (k : ℕ) ∧ (k : ℕ) < 256 + 32 * 8) := by omega
    refine ⟨?_, ?_⟩
    · rw [hrow, if_neg n1, if_neg n2]
      exact hva
    · rw [hrow, if_neg n1, if_neg n2]
      exact hvb
  by_cases hB : 256 ≤ (k : ℕ) ∧ (k : ℕ) < 512
  · -- an output row
    obtain ⟨w, i, hw, hi, hrow⟩ := rowOf_out k hB (fun g hg ↦ (hnewpos g hg).1)
    have n1 : ¬(512 = (k : ℕ) ∧ 512 < 2 ^ bm) := by omega
    have p2 : 256 ≤ (k : ℕ) ∧ (k : ℕ) < 256 + 32 * 8 := by omega
    refine ⟨?_, ?_⟩
    · rw [hrow, if_neg n1, if_pos p2, ← hw, ← hi]
      exact wrel_outWord cw R.srel w i i.isLt
    · rw [hrow, if_neg n1, if_pos p2]
      dsimp only
      rw [lev_var, constPos_val]
  -- the constant, an input, or zero
  have hrow := rowOf_none k hC hB hnewpos
  by_cases h512 : (k : ℕ) = 512
  · have hcp : k = Lv42.Parameters.Flock.constPos := Fin.ext (by rw [h512, constPos_val])
    have p1 : 512 = (k : ℕ) ∧ 512 < 2 ^ bm := by omega
    refine ⟨?_, ?_⟩
    · rw [hrow, if_pos hcp, if_pos p1]
      dsimp only
      rw [lev_var, constPos_val]
    · rw [hrow, if_pos hcp, if_pos p1]
      dsimp only
      rw [lev_var, constPos_val]
  have hcp : k ≠ Lv42.Parameters.Flock.constPos := fun h ↦ h512 (by rw [h, constPos_val])
  have hfr := R.grow.frame k (by dsimp only; omega)
  dsimp only at hfr
  have n1 : ¬(512 = (k : ℕ) ∧ 512 < 2 ^ bm) := by omega
  have n2 : ¬(256 ≤ (k : ℕ) ∧ (k : ℕ) < 256 + 32 * 8) := by omega
  by_cases hin : (k : ℕ) < 256 ∨ (640 ≤ (k : ℕ) ∧ (k : ℕ) < 1280)
  · refine ⟨?_, ?_⟩
    · rw [hrow, if_neg hcp, if_pos hin, if_neg n1, if_neg n2, hfr.1, (Iv k).1, if_pos hin]
      dsimp only
      rw [lev_var]
    · rw [hrow, if_neg hcp, if_pos hin, if_neg n1, if_neg n2, hfr.2, (Iv k).2, if_pos hin]
      dsimp only
      rw [lev_var, constPos_val, show (constantColumn : ℕ) = 512 from rfl]
  · refine ⟨?_, ?_⟩
    · rw [hrow, if_neg hcp, if_neg hin, if_neg n1, if_neg n2, hfr.1, (Iv k).1, if_neg hin]
      dsimp only
      rw [lev_zero]
    · rw [hrow, if_neg hcp, if_neg hin, if_neg n1, if_neg n2, hfr.2, (Iv k).2, if_neg hin]
      dsimp only
      rw [lev_zero]

end FlockSound.Uni.Walk

namespace FlockSound.Uni

open UniStatement UniStatement.Flock LeanVM.Parameters

/-- **The walk computes the matrices' products** (`blake2s_row_values` is `A0 w`, `B0 w`): for every row `j`, the
walk's left value is `Σ_i A[j][i] w_i` and its right value `Σ_i B[j][i] w_i`, `A`, `B` the BLAKE2s R1CS's matrices
(row, column) as `flockMatrixStack` reads them. The size hypothesis is not needed (the walk reads `getD`). -/
theorem rowValues_spec (cw : Array E) (hcw : cw.size = 2 ^ 14) (j : Fin (2 ^ 14)) :
    (Flock.blake2sRowValues cw).1.getD j 0 =
        ∑ i : Fin (2 ^ 14), (if Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A j i then cw.getD i 0 else 0) ∧
      (Flock.blake2sRowValues cw).2.getD j 0 =
        ∑ i : Fin (2 ^ 14), (if Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B j i then cw.getD i 0 else 0) := by
  have _ := hcw
  have H := Walk.rowModel_spec cw j
  rw [Walk.blake2sRowValues_eq]
  exact ⟨H.1.trans (Walk.lev_rowA cw j), H.2.trans (Walk.lev_rowB cw j)⟩

end FlockSound.Uni

/-- info: 'FlockSound.Uni.rowValues_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.rowValues_spec

/-- info: 'FlockSound.Uni.Walk.rowModel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.Walk.rowModel_spec

/-- info: 'FlockSound.Uni.Walk.blake2sRowValues_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.Walk.blake2sRowValues_eq
