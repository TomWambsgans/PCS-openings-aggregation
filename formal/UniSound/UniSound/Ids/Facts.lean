-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Bridges
import UniSound.Ids.Cantor

/-!
# The small facts of the verifier's definitions, proved

The `Prop`s of `UniSound.Ids.Bridges`' last section:

* `eqKernelLagrange` (`EqKernelLagrange`): `eqKernel`'s entry `s` is `Π_j (r_j if bit j of s else
  1 + r_j)` (`eqKernel_getD`), which is CompPoly's `lagrangeBasis` in characteristic two;
* `gpowInK` (`GpowInK`): `epow x n = x ^ n` (`epow_eq`), and `gen = ofK (K.ofLane 2)`, so
  `g^n = ofK (K.ofLane 2 ^ n)`;
* `tablesFacts` (`TablesFacts`): structurally, by the `Flushes` builders (each adds one pull and one
  push, of at most sixteen forms) and the forms' coefficients (built from `g^e`, the separators and
  constants by sums and products, all in `K`); nothing of `E` is evaluated;
* `zActZero` (`ZActZero`): `Z_act(ω_k)` is a product of factors, the bit `r`'s vanishing exactly on a
  full table, bit `b`'s exactly on its coset `k >>> b = 2^(r−b) − 2` (`coset_iff`: the rows
  `[2^r − 2^(b+1), 2^r − 2^b)`, where `log₂(2^r − k − 1) = b`), which is `isActive`.
-/

namespace UniSound.Ids.Facts

open LeanVM.Parameters UniStatement Finset

/-! ## `eqKernel` is the fingerprint's weights -/

theorem eqKernel_snoc (l : List E) (r : E) :
    eqKernel (l ++ [r]) = (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
  simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem size_eqKernel (l : List E) : (eqKernel l).size = 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l r ih =>
    rw [eqKernel_snoc, Array.size_append, Array.size_map, Array.size_map, ih, List.length_append,
      List.length_singleton, pow_succ, mul_two]

/-- **`eqKernel`'s entry `x`**: `Π_j (r_j if bit j of x else 1 + r_j)`, the first coordinate the lowest
bit. -/
theorem eqKernel_getElem (l : List E) (x : ℕ) (hx : x < (eqKernel l).size) :
    (eqKernel l)[x] =
      ∏ j ∈ range l.length, (if x.testBit j then l.getD j 0 else 1 + l.getD j 0) := by
  induction l using List.reverseRecOn generalizing x with
  | nil =>
    have : x = 0 := by simpa [eqKernel] using hx
    subst this
    rfl
  | append_singleton l r ih =>
    have hlen := size_eqKernel l
    have hgetD : ∀ j < l.length, (l ++ [r]).getD j 0 = l.getD j 0 := fun j hj ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hlast : (l ++ [r]).getD l.length 0 = r := by simp [List.getD_eq_getElem?_getD]
    simp only [eqKernel_snoc]
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
    by_cases hlo : x < 2 ^ l.length
    · rw [Array.getElem_append_left (by simp [hlen, hlo]), Array.getElem_map,
        ih x (by rw [hlen]; exact hlo), Nat.testBit_lt_two_pow hlo, hlast]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by rw [hgetD j (Finset.mem_range.mp hj)]
    · have hx' : x < 2 ^ l.length + 2 ^ l.length := by
        simp only [eqKernel_snoc, Array.size_append, Array.size_map, hlen] at hx
        omega
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ l.length + y := ⟨x - 2 ^ l.length, by omega⟩
      have hy : y < 2 ^ l.length := by omega
      rw [Array.getElem_append_right (by simp [hlen]), Array.getElem_map]
      simp only [Array.size_map, hlen, Nat.add_sub_cancel_left]
      rw [ih y (by rw [hlen]; exact hy), Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy, hlast]
      simp only [Bool.not_false, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by
        rw [hgetD j (Finset.mem_range.mp hj), Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hj)]

theorem eqKernel_getD (l : List E) (x : ℕ) (hx : x < 2 ^ l.length) :
    (eqKernel l).getD x 0 =
      ∏ j ∈ range l.length, (if x.testBit j then l.getD j 0 else 1 + l.getD j 0) := by
  have hx' : x < (eqKernel l).size := by rw [size_eqKernel]; exact hx
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx', Option.getD_some,
    eqKernel_getElem l x hx']

theorem alphasOf_length (ch : List E) : (alphasOf ch).length = 4 := by simp [alphasOf]

theorem alphasOf_getD (ch : List E) {j : ℕ} (hj : j < 4) : (alphasOf ch).getD j 0 = ch.getD j 0 := by
  rw [alphasOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

end UniSound.Ids.Facts

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Facts

/-- **`eqKernel` is the fingerprint's weights** (`EqKernelLagrange`). -/
theorem eqKernelLagrange : EqKernelLagrange := by
  intro ch s
  rw [eqKernel_getD _ _ (by rw [alphasOf_length]; exact s.isLt), alphasOf_length,
    LeanVM.Protocol.fingerprintWeights, Vector.get_eq_getElem, CompPoly.CMlPolynomialEval.lagrangeBasis,
    Vector.getElem_ofFn,
    ← Fin.prod_univ_eq_prod_range (fun j ↦ if s.val.testBit j then (alphasOf ch).getD j 0
      else 1 + (alphasOf ch).getD j 0)]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [BitVec.getLsb_eq_getElem, BitVec.getElem_ofFin, Fin.getElem_fin, Vector.getElem_ofFn,
    CharTwo.sub_eq_add, alphasOf_getD ch j.isLt]

end UniSound.Ids

namespace UniSound.Ids.Facts

open LeanVM.Parameters UniStatement Finset

/-! ## `g^n` is in `K` -/

/-- **Square and multiply** computes the power, given fuel for the exponent's bits. -/
theorem epowAux_eq : ∀ (fuel : ℕ) (base out : E) (n : ℕ), n < 2 ^ fuel →
    epowAux fuel base out n = out * base ^ n
  | 0, base, out, n, hn => by
    have : n = 0 := by simpa using hn
    subst this
    simp [epowAux]
  | fuel + 1, base, out, n, hn => by
    have hn' : n / 2 < 2 ^ fuel := by rw [pow_succ] at hn; omega
    unfold epowAux
    split_ifs with h0 h1
    · subst h0
      simp
    · rw [epowAux_eq fuel _ _ _ hn']
      conv_rhs => rw [← Nat.div_add_mod n 2, h1]
      ring
    · rw [epowAux_eq fuel _ _ _ hn']
      have h1' : n % 2 = 0 := by omega
      conv_rhs => rw [← Nat.div_add_mod n 2, h1']
      ring

theorem epow_eq (x : E) (n : ℕ) : epow x n = x ^ n := by
  rw [epow, epowAux_eq _ _ _ _ Nat.lt_log2_self, one_mul]

theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

theorem eK_eq (c : UInt64) : eK c = ofK (K.ofLane c) := by
  rw [eK, eNew, ofK_eq_ofLimbs, show K.ofLane 0 = 0 from rfl]

theorem gen_eq : gen = ofK (K.ofLane 2) := eK_eq 2

theorem gpow_eq (n : ℕ) : UniStatement.gpow n = ofK (K.ofLane 2 ^ n) := by
  rw [UniStatement.gpow, epow_eq, gen_eq, ofK_pow]

theorem toK_ofK (a : K) : toK (ofK a) = a := by
  simp [toK, limb_ofK]

/-- **An element of `K`** (in `E`). -/
def InK (x : E) : Prop := ∃ a : K, x = ofK a

theorem InK.ofK_toK {x : E} (h : InK x) : ofK (toK x) = x := by
  obtain ⟨a, rfl⟩ := h
  rw [toK_ofK]

theorem inK_ofK (a : K) : InK (ofK a) := ⟨a, rfl⟩

theorem InK.add {x z : E} (hx : InK x) (hz : InK z) : InK (x + z) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hz
  exact ⟨a + b, (UniSound.Ids.ofK_add a b).symm⟩

theorem InK.mul {x z : E} (hx : InK x) (hz : InK z) : InK (x * z) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hz
  exact ⟨a * b, (UniSound.Ids.ofK_mul a b).symm⟩

theorem inK_zero : InK 0 := ⟨0, UniSound.Ids.ofK_zero.symm⟩

theorem inK_one : InK 1 := ⟨1, UniSound.Ids.ofK_one.symm⟩

theorem inK_gpow (n : ℕ) : InK (UniStatement.gpow n) := ⟨_, gpow_eq n⟩

theorem inK_eK (c : UInt64) : InK (eK c) := ⟨_, eK_eq c⟩

end UniSound.Ids.Facts

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Facts

/-- **`g^n` is in `K`** (`GpowInK`). -/
theorem gpowInK : GpowInK := fun n ↦ (inK_gpow n).ofK_toK

end UniSound.Ids

namespace UniSound.Ids.Facts

open LeanVM.Parameters UniStatement

/-! ## The tables' flushes -/

/-- A form whose coefficients are in `K`. -/
def FormK (f : Form) : Prop := ∀ mc ∈ f, InK mc.2

/-- Forms all in `K`. -/
def AllK (l : List Form) : Prop := ∀ f ∈ l, FormK f

/-- A tuple of at most sixteen forms in `K`. -/
def TupK (tup : List Form) : Prop := tup.length ≤ 16 ∧ AllK tup

/-- **Flushes as `TablesFacts` wants them**: as many pulls as pushes, each tuple a `TupK`. -/
def Good (fl : Flushes) : Prop :=
  fl.pull.length = fl.push.length ∧ ∀ tup ∈ fl.pull ++ fl.push, TupK tup

theorem allK_nil : AllK [] := fun _ h ↦ absurd h List.not_mem_nil

theorem AllK.cons {f : Form} {l : List Form} (hf : FormK f) (hl : AllK l) : AllK (f :: l) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | h
  · exact hf
  · exact hl g h

theorem AllK.append {l l' : List Form} (hl : AllK l) (hl' : AllK l') : AllK (l ++ l') := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact hl g h
  · exact hl' g h

theorem allK_map {α : Type} (l : List α) {φ : α → Form} (h : ∀ a, FormK (φ a)) : AllK (l.map φ) := by
  intro g hg
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hg
  exact h a

theorem formK_term (mono : List ℕ) {c : E} (hc : InK c) : FormK (Form.term mono c) := by
  intro mc hmc
  rw [Form.term, List.mem_singleton] at hmc
  subst hmc
  exact hc

theorem formK_constant {c : E} (hc : InK c) : FormK (constant c) := formK_term [] hc

theorem formK_col (index exponent : ℕ) : FormK (col index exponent) :=
  formK_term [index] (inK_gpow exponent)

theorem formK_prod (a b exponent : ℕ) : FormK (UniStatement.prod a b exponent) :=
  formK_term [min a b, max a b] (inK_gpow exponent)

theorem FormK.addAt {mono : List ℕ} {c : E} (hc : InK c) : ∀ {f : Form}, FormK f → FormK (f.addAt mono c)
  | [], _ => by
    intro mc hmc
    simp only [Form.addAt, List.mem_singleton] at hmc
    subst hmc
    exact hc
  | (k, v) :: rest, hf => by
    have hv : InK v := hf (k, v) List.mem_cons_self
    have hrest : FormK rest := fun mc h ↦ hf mc (List.mem_cons_of_mem _ h)
    simp only [Form.addAt]
    split_ifs
    · intro mc hmc
      rcases List.mem_cons.mp hmc with rfl | h
      · exact hv.add hc
      · exact hrest mc h
    · intro mc hmc
      rcases List.mem_cons.mp hmc with rfl | h
      · exact hc
      · exact hf mc h
    · intro mc hmc
      rcases List.mem_cons.mp hmc with rfl | h
      · exact hv
      · exact FormK.addAt hc hrest mc h

theorem FormK.addScaled {w : E} (hw : InK w) : ∀ {f other : Form}, FormK f → FormK other →
    FormK (f.addScaled other w)
  | _, [], hf, _ => hf
  | f, (mono, c) :: rest, hf, ho => by
    have hc : InK c := ho (mono, c) List.mem_cons_self
    have hrest : FormK rest := fun mc h ↦ ho mc (List.mem_cons_of_mem _ h)
    rw [Form.addScaled, List.foldl_cons]
    exact FormK.addScaled hw (hf.addAt (hw.mul hc)) hrest

theorem FormK.add {f other : Form} (hf : FormK f) (ho : FormK other) : FormK (f.add other) :=
  FormK.addScaled inK_one hf ho

theorem formK_sum : ∀ {forms : List Form} {acc : Form}, FormK acc → AllK forms →
    FormK (forms.foldl Form.add acc)
  | [], _, hacc, _ => hacc
  | x :: rest, _, hacc, hf => by
    rw [List.foldl_cons]
    exact formK_sum (hacc.add (hf x List.mem_cons_self)) fun h hh ↦ hf h (List.mem_cons_of_mem _ hh)

theorem formK_Form_sum {forms : List Form} (hf : AllK forms) : FormK (Form.sum forms) :=
  formK_sum (fun _ h ↦ absurd h List.not_mem_nil) hf

theorem good_empty : Good ⟨[], []⟩ := ⟨rfl, fun _ h ↦ absurd h List.not_mem_nil⟩

theorem Good.pair {f : Flushes} {push pull : List Form} (hf : Good f) (hpush : TupK push)
    (hpull : TupK pull) : Good (f.pair push pull) := by
  refine ⟨by simp [Flushes.pair, hf.1], ?_⟩
  intro tup htup
  simp only [Flushes.pair, List.mem_append, List.mem_singleton] at htup
  rcases htup with (h | rfl) | (h | rfl)
  · exact hf.2 tup (List.mem_append_left _ h)
  · exact hpull
  · exact hf.2 tup (List.mem_append_right _ h)
  · exact hpush

theorem Good.stateDerived {f : Flushes} (hf : Good f) (pc fp : ℕ) {npc nfp : Form} (hn : FormK npc)
    (hnf : FormK nfp) : Good (f.stateDerived pc fp npc nfp) :=
  hf.pair ⟨by simp, (((allK_nil.cons hnf).cons hn).cons (formK_constant inK_one))⟩
    ⟨by simp, (((allK_nil.cons (formK_col fp 0)).cons (formK_col pc 0)).cons (formK_constant inK_one))⟩

theorem Good.stateStep {f : Flushes} (hf : Good f) (pc fp : ℕ) : Good (f.stateStep pc fp) :=
  hf.stateDerived pc fp (formK_col pc 1) (formK_col fp 0)

theorem Good.counted {f : Flushes} {pre suffix : List Form} (hf : Good f) (count : ℕ)
    (hlen : pre.length + suffix.length ≤ 15) (hpre : AllK pre) (hsuf : AllK suffix) :
    Good (f.counted pre count suffix) := by
  unfold Flushes.counted
  exact hf.pair ⟨by simp; omega, (hpre.append (allK_nil.cons (formK_col count 1))).append hsuf⟩
    ⟨by simp; omega, (hpre.append (allK_nil.cons (formK_col count 0))).append hsuf⟩

theorem Good.bytecode {f : Flushes} (hf : Good f) (pc count opcode : ℕ) {operands : List Form}
    (hlen : operands.length ≤ 12) (hop : AllK operands) : Good (f.bytecode pc count opcode operands) :=
  hf.counted count (by simp; omega)
    ((allK_nil.cons (formK_col pc 0)).cons (formK_constant (inK_eK 4)))
    ((allK_nil.cons (formK_constant (inK_gpow opcode))).append hop)

theorem Good.memory {f : Flushes} (hf : Good f) {address : Form} (ha : FormK address) (count : ℕ)
    {values : List Form} (hlen : values.length ≤ 13) (hv : AllK values) :
    Good (f.memory address count values) :=
  hf.counted count (by simp; omega) ((allK_nil.cons ha).cons (formK_constant (inK_eK 2))) hv

theorem Good.memoryCols {f : Flushes} (hf : Good f) {address : Form} (ha : FormK address)
    (count : ℕ) (columns : List ℕ) : Good (f.memoryCols address count columns) := by
  unfold Flushes.memoryCols
  refine hf.memory ha count (by simp) (allK_map _ fun limb ↦ ?_)
  split
  · exact formK_col _ 0
  · exact formK_constant inK_zero

theorem good_foldl {α : Type} (step : Flushes → α → Flushes) (h : ∀ f a, Good f → Good (step f a)) :
    ∀ (l : List α) {init : Flushes}, Good init → Good (l.foldl step init)
  | [], _, hi => hi
  | a :: l, _, hi => by
    rw [List.foldl_cons]
    exact good_foldl step h l (h _ a hi)

/-- Closes the `AllK`/`FormK` goals of the tables' literal tuples. -/
macro "formk" : tactic => `(tactic| repeat' first
  | exact allK_nil
  | exact formK_col _ _
  | exact formK_prod _ _ _
  | exact formK_constant inK_zero
  | exact formK_constant inK_one
  | apply formK_Form_sum
  | apply FormK.add
  | apply AllK.cons
  | apply AllK.append)

theorem good_arith (opcode : ℕ) (multiply : Bool) : Good (flushesArith opcode multiply) := by
  unfold flushesArith
  dsimp only
  refine ((((good_empty.stateStep _ _).bytecode _ _ _ (by simp) (by formk)).memoryCols
    (formK_prod _ _ 0) _ _).memoryCols (formK_prod _ _ 0) _ _).memory (formK_prod _ _ 0) _ ?_ ?_
  · cases multiply <;> simp
  · cases multiply
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact allK_map _ fun _ ↦ (formK_col _ 0).add (formK_col _ 0)
    · simp only [↓reduceIte]
      exact allK_map _ fun lane ↦ formK_Form_sum (allK_map lane fun ⟨_, _⟩ ↦ formK_prod _ _ 0)

theorem good_set : Good flushesSet := by
  unfold flushesSet
  dsimp only
  exact ((good_empty.stateStep _ _).bytecode _ _ _ (by simp) (by formk)).memoryCols
    (formK_prod _ _ 0) _ _

theorem good_deref : Good flushesDeref := by
  unfold flushesDeref
  dsimp only
  exact ((((good_empty.stateStep _ _).bytecode _ _ _ (by simp) (by formk)).memoryCols
    (formK_prod _ _ 0) _ _).memory (formK_prod _ _ 0) _ (by simp) (by formk)).memoryCols
    (formK_prod _ _ 0) _ _

theorem good_jump : Good flushesJump := by
  unfold flushesJump
  dsimp only
  exact (((((good_empty.stateDerived _ _ (by formk) (by formk)).bytecode _ _ _ (by simp)
    (by formk)).memoryCols (formK_prod _ _ 0) _ _).memoryCols (formK_prod _ _ 0) _ _).memoryCols
    (formK_prod _ _ 0) _ _)

theorem good_blake2s : Good flushesBlake2s := by
  unfold flushesBlake2s
  dsimp only
  refine good_foldl _ (fun f x hf ↦ ?_) _
    ((good_empty.stateStep _ _).bytecode _ _ _ (by simp) (allK_map _ fun _ ↦ formK_col _ 0))
  obtain ⟨_, _, _⟩ := x
  exact hf.memoryCols (formK_prod _ _ _) _ _

end UniSound.Ids.Facts

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Facts

/-- **The tables' flushes** (`TablesFacts`): as many pulls as pushes, tuples of at most `16` forms,
every coefficient in `K`. -/
theorem tablesFacts : TablesFacts := by
  have key : ∀ tab ∈ tables, Good tab.flushes := by
    intro tab htab
    simp only [tables, List.mem_cons, List.not_mem_nil, or_false] at htab
    rcases htab with rfl | rfl | rfl | rfl | rfl | rfl
    · exact good_arith _ _
    · exact good_arith _ _
    · exact good_set
    · exact good_deref
    · exact good_jump
    · exact good_blake2s
  intro tab htab
  obtain ⟨hlen, htup⟩ := key tab htab
  exact ⟨hlen, fun tup h ↦ ⟨(htup tup h).1, fun f hf mc hmc ↦ ((htup tup h).2 f hf mc hmc).ofK_toK⟩⟩

end UniSound.Ids

namespace UniSound.Ids.Facts

open LeanVM.Parameters UniStatement Polynomial

/-! ## The fixed cosets -/

theorem eK_zero' : eK (UInt64.ofNat 0) = 0 := by
  rw [eK_eq, show K.ofLane (UInt64.ofNat 0) = 0 by decide, UniSound.Ids.ofK_zero]

theorem eK_one' : eK (UInt64.ofNat 1) = 1 := by
  rw [eK_eq, show K.ofLane (UInt64.ofNat 1) = 1 by decide, UniSound.Ids.ofK_one]

/-- **A count's bit** (`Scalar::bits(j, 1)`) is the scalar `0` or `1`. -/
theorem intBits_one (n j : ℕ) : intBits n j 1 = bitE n j := by
  unfold intBits bitE
  rw [show min 1 64 = 1 from rfl, pow_one, Nat.testBit_eq_decide_div_mod_eq,
    ← Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (n >>> j) with h | h
  · rw [h, eK_zero']
    simp
  · rw [h, eK_one']
    simp

theorem foldl_mul_eq {M : Type} [CommMonoid M] (q : ℕ → M) : ∀ (l : List ℕ) (init : M),
    l.foldl (fun p b ↦ p * q b) init = init * (l.map q).prod
  | [], init => by simp
  | a :: l, init => by
    rw [List.foldl_cons, foldl_mul_eq q l, List.map_cons, List.prod_cons, mul_assoc]

/-- **`Z_act` at a point**, factor by factor. -/
theorem eval_zActP (bits : List E) (r : ℕ) (x : E) :
    (zActP bits r).eval x = (1 + bits.getD r 0 * ((digitP r).eval x + 1)) *
      ((List.range r).map fun b ↦
        1 + bits.getD b 0 * ((digitP b).eval x + (cosetOffset r b + 1))).prod := by
  unfold zActP
  rw [foldl_mul_eq (fun b ↦ 1 + C (bits.getD b 0) * (digitP b + C (cosetOffset r b + 1))),
    Polynomial.eval_mul, eval_list_prod, List.map_map]
  simp only [Function.comp_def, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C]

theorem bits_getD (count r : ℕ) {j : ℕ} (hj : j < r + 1) :
    ((List.range (r + 1)).map fun j ↦ intBits count j 1).getD j 0 = bitE count j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some, intBits_one]

theorem pointE_add (h : BetaCantor) {i j : ℕ} (hi : i < 2 ^ 24) (hj : j < 2 ^ 24) :
    pointE i + pointE j = pointE (i ^^^ j) := by
  rw [pointE_eq_omega h hi, pointE_eq_omega h hj, pointE_eq_omega h (Nat.xor_lt_two_pow hi hj),
    Heap.omega_xor]

theorem pointE_eq_zero_iff (h : BetaCantor) {i : ℕ} (hi : i < 2 ^ 24) : pointE i = 0 ↔ i = 0 := by
  constructor
  · intro h0
    by_contra hne
    exact Heap.omega_ne_zero (cantorE h) (Nat.pos_of_ne_zero hne) hi
      (by rw [← pointE_eq_omega h hi]; exact h0)
  · rintro rfl
    exact pointE_zero

theorem one_add_one : (1 : E) + 1 = 0 := CharTwo.add_self_eq_zero 1

/-- A coset's factor: `1 + c (ω_x + ω_y + 1)` vanishes iff `c = 1` and `x = y`. -/
theorem factor_eq_zero_iff (h : BetaCantor) (c : Bool) {x y : ℕ} (hx : x < 2 ^ 24) (hy : y < 2 ^ 24) :
    1 + (if c then 1 else 0) * (pointE x + (pointE y + 1)) = 0 ↔ c = true ∧ x = y := by
  cases c
  · simp
  · simp only [ite_true, one_mul, true_and]
    rw [show (1 : E) + (pointE x + (pointE y + 1)) = pointE x + pointE y by
      linear_combination one_add_one, pointE_add h hx hy, pointE_eq_zero_iff h (Nat.xor_lt_two_pow hx hy),
      Nat.xor_eq_zero_iff]

/-- **Bit `b`'s coset**: `k >>> b = 2^(r−b) − 2` iff `k ∈ [2^r − 2^(b+1), 2^r − 2^b)`, i.e. the gap
`2^r − k` is at least `2` and `log₂(2^r − k − 1) = b`. -/
theorem coset_iff {r b k : ℕ} (hk : k < 2 ^ r) (hb : b < r) :
    k >>> b = 2 ^ (r - b) - 2 ↔ 2 ≤ 2 ^ r - k ∧ Nat.log2 (2 ^ r - k - 1) = b := by
  have hP : 0 < 2 ^ b := Nat.two_pow_pos b
  have hN : 2 ^ (r - b) * 2 ^ b = 2 ^ r := by rw [← pow_add]; congr 1; omega
  have hq : 2 ≤ 2 ^ (r - b) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ r - b by omega)
    simpa using this
  have h1 : (2 ^ (r - b) - 2) * 2 ^ b = 2 ^ r - 2 * 2 ^ b := by rw [Nat.sub_mul, hN]
  have h2 : (2 ^ (r - b) - 2 + 1) * 2 ^ b = 2 ^ r - 2 ^ b := by
    rw [show 2 ^ (r - b) - 2 + 1 = 2 ^ (r - b) - 1 by omega, Nat.sub_mul, hN, one_mul]
  have h3 : 2 * 2 ^ b ≤ 2 ^ r := by rw [← hN]; exact Nat.mul_le_mul_right _ hq
  have h2P : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ, mul_comm]
  have hdiv : k / 2 ^ b = 2 ^ (r - b) - 2 ↔ 2 ^ r - 2 * 2 ^ b ≤ k ∧ k < 2 ^ r - 2 ^ b := by
    rw [le_antisymm_iff, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hP, Nat.le_div_iff_mul_le hP, h1,
      Nat.succ_eq_add_one, h2]
    exact and_comm
  rw [Nat.shiftRight_eq_div_pow, hdiv]
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨by omega, ?_⟩
    rw [Nat.log2_eq_iff (by omega), h2P]
    omega
  · rintro ⟨hg, hl⟩
    rw [Nat.log2_eq_iff (by omega), h2P] at hl
    omega

/-- `Z_act(ω_k)` vanishes iff the table is full or `k` is in a set bit's coset. -/
theorem zAct_eval_eq_zero_iff (h : BetaCantor) {count r k : ℕ} (hr : r < 24) (hc : count ≤ 2 ^ r)
    (hk : k < 2 ^ r) :
    (zActP ((List.range (r + 1)).map fun j ↦ intBits count j 1) r).eval (pointE k) = 0 ↔
      count = 2 ^ r ∨ ∃ b, b < r ∧ count.testBit b = true ∧ k >>> b = 2 ^ (r - b) - 2 := by
  have hr24 : 2 ^ r ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hr.le
  have hk24 : k < 2 ^ 24 := lt_of_lt_of_le hk hr24
  rw [eval_zActP, mul_eq_zero, List.prod_eq_zero_iff, List.mem_map]
  refine or_congr ?_ (exists_congr fun b ↦ ?_)
  · rw [bits_getD count r (Nat.lt_succ_self r), eval_digitP_pointE h r hk24,
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hk, pointE_zero, zero_add, mul_one]
    unfold bitE
    by_cases hfull : count = 2 ^ r
    · rw [hfull, Nat.testBit_two_pow_self]
      simp [one_add_one]
    · have hlt : count < 2 ^ r := lt_of_le_of_ne hc hfull
      rw [Nat.testBit_lt_two_pow hlt]
      simp [hfull]
  · rw [List.mem_range]
    constructor
    · rintro ⟨hb, h0⟩
      have hkb : k >>> b < 2 ^ 24 :=
        lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hk24
      have hm : 2 ^ (r - b) - 2 < 2 ^ 24 :=
        lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by norm_num))
          ((Nat.pow_le_pow_right (by norm_num) (Nat.sub_le r b)).trans hr24)
      rw [bits_getD count r (by omega), eval_digitP_pointE h b hk24, cosetOffset] at h0
      exact ⟨hb, (factor_eq_zero_iff h _ hkb hm).1 h0⟩
    · rintro ⟨hb, hbit, hkb'⟩
      have hkb : k >>> b < 2 ^ 24 :=
        lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hk24
      have hm : 2 ^ (r - b) - 2 < 2 ^ 24 :=
        lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by norm_num))
          ((Nat.pow_le_pow_right (by norm_num) (Nat.sub_le r b)).trans hr24)
      refine ⟨hb, ?_⟩
      rw [bits_getD count r (by omega), eval_digitP_pointE h b hk24, cosetOffset]
      exact (factor_eq_zero_iff h _ hkb hm).2 ⟨hbit, hkb'⟩

/-- `isActive` is the set bits' cosets (or every row of a full table). -/
theorem isActive_iff {count r k : ℕ} (hk : k < 2 ^ r) :
    isActive k count r = true ↔
      count = 2 ^ r ∨ ∃ b, b < r ∧ count.testBit b = true ∧ k >>> b = 2 ^ (r - b) - 2 := by
  unfold isActive
  by_cases hfull : count = 2 ^ r
  · simp [hfull]
  · rw [ite_eq_right hfull, or_iff_right hfull]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h2, hbit⟩
      have hb : Nat.log2 (2 ^ r - k - 1) < r := (Nat.log2_lt (by omega)).2 (by omega)
      exact ⟨_, hb, hbit, (coset_iff hk hb).2 ⟨h2, rfl⟩⟩
    · rintro ⟨b, hb, hbit, hkb⟩
      obtain ⟨h2, hlog⟩ := (coset_iff hk hb).1 hkb
      exact ⟨h2, hlog ▸ hbit⟩

end UniSound.Ids.Facts

namespace UniSound.Ids

open Facts

/-- **The fixed cosets** (`ZActZero`, F1b): `Z_act(ω_k)` vanishes exactly on the active rows. -/
theorem zActZero : ZActZero := fun h _ _ _ hr hc hk ↦
  (zAct_eval_eq_zero_iff h hr hc hk).trans (isActive_iff hk).symm

end UniSound.Ids

/-! ## Axioms -/

/-- info: 'UniSound.Ids.eqKernelLagrange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.eqKernelLagrange

/-- info: 'UniSound.Ids.gpowInK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.gpowInK

/-- info: 'UniSound.Ids.tablesFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.tablesFacts

/-- info: 'UniSound.Ids.zActZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.zActZero
