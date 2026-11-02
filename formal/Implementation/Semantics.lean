-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Program
import Implementation.Field
import QuotientSecurity.Cantor

/-!
# What each node computes

The interpreter's values (`values`) read as elements of a field `F` whose limbs are `F192`'s
(`IsF192`): `val k` is the element node `k`'s value stands for. Node by node (`val_add`,
`val_mul`, `val_frob`, `val_const`): an `add` node is the sum of its operands, a `mul` node their
product, a `frob` node `x^(2^64)`, a `const` node its constant. Then the operations of
`Program.lean` (`look` and the folds `record.rs` does) have the same meaning (`add_spec`,
`mul_spec`, `frob_spec`, `cnst_spec`), and so do its blocks: the `w` chain (`wChain_spec`), the
folds and maps, the inversion by the norm (`inverse_spec`: `x⁻¹`, from `card_eq`), the batch
inversion (`prefixes_spec`, `backInv_spec`) and the cells (`cell_spec`).

Statements about a program `p : Option α` are `Spec p Q`: whatever `p` gives meets `Q`.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open Program Emitted QuotientSecurity

/-! ## The values, node by node -/

section Fold

variable (f : Array Nat → Node → Nat)

/-- The interpreter's fold, from any start. -/
def go (acc : Array Nat) (l : List Node) : Array Nat := l.foldl (fun v n => v.push (f v n)) acc

theorem go_cons (acc : Array Nat) (n : Node) (l : List Node) :
    go f acc (n :: l) = go f (acc.push (f acc n)) l := rfl

theorem go_append (acc : Array Nat) (l₁ l₂ : List Node) :
    go f acc (l₁ ++ l₂) = go f (go f acc l₁) l₂ := by
  simp [go, List.foldl_append]

theorem go_size : ∀ (l : List Node) (acc : Array Nat), (go f acc l).size = acc.size + l.length
  | [], acc => by simp [go]
  | n :: l, acc => by rw [go_cons, go_size l, Array.size_push]; simp; omega

theorem go_getD_lt : ∀ (l : List Node) (acc : Array Nat) (j : Nat), j < acc.size →
    (go f acc l).getD j 0 = acc.getD j 0
  | [], _, _, _ => rfl
  | n :: l, acc, j, hj => by
    rw [go_cons, go_getD_lt l _ j (by rw [Array.size_push]; omega)]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, show j ≠ acc.size by omega]

theorem go_getD (l : List Node) (k : Nat) (hk : k < l.length) :
    (go f #[] l).getD k 0 = f (go f #[] (l.take k)) l[k] := by
  have e : l = l.take k ++ (l[k] :: l.drop (k + 1)) := by simp
  have hs : (go f #[] (l.take k)).size = k := by rw [go_size]; simp; omega
  conv_lhs => rw [e, go_append, go_cons]
  rw [go_getD_lt f _ _ _ (by rw [Array.size_push]; omega)]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.getElem_push, hs]

theorem go_getD_prefix (l : List Node) (k j : Nat) (hj : j < k) (hk : k ≤ l.length) :
    (go f #[] (l.take k)).getD j 0 = (go f #[] l).getD j 0 := by
  have e : l = l.take k ++ l.drop k := by simp
  conv_rhs => rw [e, go_append]
  rw [go_getD_lt f (l.drop k) _ _ (by rw [go_size]; simp; omega)]

end Fold

/-- The operands of a node. -/
def operands : Node → List Nat
  | .add a b => [a, b]
  | .mul a b => [a, b]
  | .frob a => [a]
  | .low a => [a]
  | .hash st xs => st :: xs
  | _ => []

/-- **Every node reads only nodes before it.** -/
theorem nodes_wf : ∀ k < nodes.length, ∀ a ∈ operands (nodes.getD k default), a < k := by
  decide +kernel

theorem getD_of_getElem? {k : Nat} {n : Node} (h : nodes[k]? = some n) : nodes.getD k default = n := by
  simp [List.getD_eq_getElem?_getD, h]

section Values

variable (H : List UInt8 → Vector UInt8 32) (idx cd : List UInt8)

theorem values_eq : values H idx cd = go (step H idx cd) #[] nodes := rfl

/-- A node's value is the interpreter's step on the values before it. -/
theorem values_getD {k : Nat} {n : Node} (h : nodes[k]? = some n) :
    (values H idx cd).getD k 0 = step H idx cd (go (step H idx cd) #[] (nodes.take k)) n := by
  obtain ⟨hk, e⟩ := List.getElem?_eq_some_iff.mp h
  rw [values_eq, go_getD _ _ _ hk, e]

theorem prefix_getD {k a : Nat} {n : Node} (h : nodes[k]? = some n) (ha : a ∈ operands n) :
    (go (step H idx cd) #[] (nodes.take k)).getD a 0 = (values H idx cd).getD a 0 := by
  obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.mp h
  have hwf := nodes_wf k hk a (by rw [getD_of_getElem? h]; exact ha)
  exact go_getD_prefix _ _ _ _ hwf hk.le

theorem values_add {k a b : Nat} (h : nodes[k]? = some (.add a b)) :
    (values H idx cd).getD k 0 = (values H idx cd).getD a 0 ^^^ (values H idx cd).getD b 0 := by
  rw [values_getD H idx cd h]
  simp only [step]
  rw [prefix_getD H idx cd h (by simp [operands]), prefix_getD H idx cd h (by simp [operands])]

theorem values_mul {k a b : Nat} (h : nodes[k]? = some (.mul a b)) :
    (values H idx cd).getD k 0 = mulE ((values H idx cd).getD a 0) ((values H idx cd).getD b 0) := by
  rw [values_getD H idx cd h]
  simp only [step]
  rw [prefix_getD H idx cd h (by simp [operands]), prefix_getD H idx cd h (by simp [operands])]

theorem values_frob {k a : Nat} (h : nodes[k]? = some (.frob a)) :
    (values H idx cd).getD k 0 = frobE ((values H idx cd).getD a 0) := by
  rw [values_getD H idx cd h]
  simp only [step]
  rw [prefix_getD H idx cd h (by simp [operands])]

theorem values_const {k c : Nat} (h : nodes[k]? = some (.const c)) :
    (values H idx cd).getD k 0 = c := by
  rw [values_getD H idx cd h]
  rfl

theorem values_low {k a : Nat} (h : nodes[k]? = some (.low a)) :
    (values H idx cd).getD k 0 = (values H idx cd).getD a 0 % B192 := by
  rw [values_getD H idx cd h]
  simp only [step]
  rw [prefix_getD H idx cd h (by simp [operands])]

theorem values_hash {k st : Nat} {xs : List Nat} (h : nodes[k]? = some (.hash st xs)) :
    (values H idx cd).getD k 0 = beNat (H (beBytes 32 ((values H idx cd).getD st 0) ++
      xs.flatMap fun x => beBytes 32 ((values H idx cd).getD x 0))).toList := by
  rw [values_getD H idx cd h]
  simp only [step]
  have e : (xs.flatMap fun x => beBytes 32 ((go (step H idx cd) #[] (nodes.take k)).getD x 0)) =
      xs.flatMap fun x => beBytes 32 ((values H idx cd).getD x 0) :=
    List.flatMap_congr fun x hx => by rw [prefix_getD H idx cd h (by simp [operands, hx])]
  rw [prefix_getD H idx cd h (by simp [operands]), e]

theorem values_seed {k : Nat} (h : nodes[k]? = some .seed) :
    (values H idx cd).getD k 0 = beNat (H (bytesOf name ++ idx ++ (cd.drop 4).take 64)).toList := by
  rw [values_getD H idx cd h]
  rfl

theorem values_statement {k j : Nat} (h : nodes[k]? = some (.statement j)) :
    (values H idx cd).getD k 0 = half (cdWord cd (4 + 32 * (j / 2))) j := by
  rw [values_getD H idx cd h]
  rfl

theorem values_root {k j : Nat} (h : nodes[k]? = some (.root j)) :
    (values H idx cd).getD k 0 = half (cdWord cd (4 + 64 + 32 * (j / 2))) j := by
  rw [values_getD H idx cd h]
  rfl

theorem values_input {k i : Nat} (h : nodes[k]? = some (.input i)) :
    (values H idx cd).getD k 0 = cdWord cd (4 + 128 + 24 * i) >>> 64 := by
  rw [values_getD H idx cd h]
  rfl

end Values

/-! ## In the field -/

variable {F : Type} [Field F] [CharP F 2] {limbs : F ≃ QuotientRpm.Limbs}
variable (limbs) (H : List UInt8 → Vector UInt8 32) (idx cd : List UInt8)

/-- **The element node `k` stands for.** -/
def val (k : Nat) : F := elem limbs ((values H idx cd).getD k 0)

variable {limbs H idx cd}

/-- The Frobenius is `x^(2^64)` on numbers (`elem_frobE`, `Field.lean`). -/
def FrobOK (limbs : F ≃ QuotientRpm.Limbs) : Prop := ∀ x, elem limbs (frobE x) = elem limbs x ^ 2 ^ 64

variable (hF : IsF192 limbs)
include hF

theorem val_add {k a b : Nat} (h : nodes[k]? = some (.add a b)) :
    val limbs H idx cd k = val limbs H idx cd a + val limbs H idx cd b := by
  simp only [val, values_add H idx cd h, elem_xor hF]

theorem val_mul {k a b : Nat} (h : nodes[k]? = some (.mul a b)) :
    val limbs H idx cd k = val limbs H idx cd a * val limbs H idx cd b := by
  simp only [val, values_mul H idx cd h, elem_mulE hF]

theorem val_const {k c : Nat} (h : nodes[k]? = some (.const c)) : val limbs H idx cd k = elem limbs c := by
  simp only [val, values_const H idx cd h]

omit hF in
theorem val_frob (hfr : FrobOK limbs) {k a : Nat} (h : nodes[k]? = some (.frob a)) :
    val limbs H idx cd k = val limbs H idx cd a ^ 2 ^ 64 := by
  simp only [val, values_frob H idx cd h]
  exact hfr _

/-! ## The operations of `Program.lean` -/

omit hF in
theorem findFrom_spec {n : Node} : ∀ {l : List Node} {i k : Nat}, findFrom n l i = some k →
    i ≤ k ∧ l[k - i]? = some n
  | [], _, _, h => by simp [findFrom] at h
  | m :: l, i, k, h => by
    unfold findFrom at h
    split_ifs at h with hm
    · cases h; simp [hm]
    · obtain ⟨h1, h2⟩ := findFrom_spec h
      refine ⟨by omega, ?_⟩
      rw [show k - i = (k - (i + 1)) + 1 by omega]
      simpa using h2

omit hF in
theorem look_spec {n : Node} {k : Nat} (h : look n = some k) : nodes[k]? = some n := by
  simpa using (findFrom_spec h).2

omit hF in
theorem constAt_spec {a c : Nat} (h : constAt a = some c) : nodes[a]? = some (.const c) := by
  unfold constAt at h
  split at h
  · rename_i e; cases h; exact e
  · cases h

/-- What a program gives meets `Q`. -/
def Spec {α : Type} (p : Option α) (Q : α → Prop) : Prop := ∀ a, p = some a → Q a

omit hF in
theorem Spec.bind {α β : Type} {p : Option α} {f : α → Option β} {Q : β → Prop}
    (h : Spec p fun a => Spec (f a) Q) : Spec (p >>= f) Q := by
  intro b hb
  cases p with
  | none => cases hb
  | some a => exact h a rfl b hb

omit hF in
theorem Spec.pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Spec (Pure.pure a : Option α) Q := by
  intro b hb; cases hb; exact h

omit hF in
theorem Spec.weaken {α : Type} {p : Option α} {P Q : α → Prop} (h : Spec p P) (hPQ : ∀ a, P a → Q a) :
    Spec p Q := fun a ha => hPQ a (h a ha)

omit hF in
theorem Spec.some {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Spec (some a) Q := by
  intro b hb; cases hb; exact h

theorem cnst_spec (c : Nat) : Spec (cnst c) fun k => val limbs H idx cd k = elem limbs c :=
  fun _ h => val_const hF (look_spec h)

theorem constAt_val {a c : Nat} (h : constAt a = some c) : val limbs H idx cd a = elem limbs c :=
  val_const hF (constAt_spec h)

theorem add_spec (a b : Nat) :
    Spec (Program.add a b) fun k => val limbs H idx cd k = val limbs H idx cd a + val limbs H idx cd b := by
  intro k h
  unfold Program.add at h
  rcases hx : constAt a with _ | x <;> rcases hy : constAt b with _ | y <;>
    simp only [hx, hy, reduceCtorEq, ite_false, Option.some.injEq] at h
  · split_ifs at h with hab
    · subst hab; rw [cnst_spec hF _ k h, elem_zero hF, CharTwo.add_self_eq_zero]
    · rw [val_add hF (look_spec h)]
      rcases le_total a b with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]
      · rw [min_eq_right hle, max_eq_left hle, add_comm]
  · split_ifs at h with hy0 hab
    · cases h; rw [constAt_val hF hy, hy0, elem_zero hF, add_zero]
    · subst hab; rw [cnst_spec hF _ k h, elem_zero hF, CharTwo.add_self_eq_zero]
    · rw [val_add hF (look_spec h)]
      rcases le_total a b with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]
      · rw [min_eq_right hle, max_eq_left hle, add_comm]
  · split_ifs at h with hx0 hab
    · cases h; rw [constAt_val hF hx, hx0, elem_zero hF, zero_add]
    · subst hab; rw [cnst_spec hF _ k h, elem_zero hF, CharTwo.add_self_eq_zero]
    · rw [val_add hF (look_spec h)]
      rcases le_total a b with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]
      · rw [min_eq_right hle, max_eq_left hle, add_comm]
  · rw [cnst_spec hF _ k h, constAt_val hF hx, constAt_val hF hy, elem_xor hF]

theorem mul_spec (a b : Nat) :
    Spec (Program.mul a b) fun k => val limbs H idx cd k = val limbs H idx cd a * val limbs H idx cd b := by
  intro k h
  unfold Program.mul at h
  have hlook : look (.mul (min a b) (max a b)) = some k →
      val limbs H idx cd k = val limbs H idx cd a * val limbs H idx cd b := fun h => by
    rw [val_mul hF (look_spec h)]
    rcases le_total a b with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle, mul_comm]
  rcases hx : constAt a with _ | x <;> rcases hy : constAt b with _ | y <;>
    simp only [hx, hy, reduceCtorEq, ite_false, false_or, or_false, Option.some.injEq] at h
  · exact hlook h
  · split_ifs at h with hy0 hy1
    · rw [cnst_spec hF _ k h, constAt_val hF hy, hy0, elem_zero hF, mul_zero]
    · cases h; rw [constAt_val hF hy, hy1, elem_one hF, mul_one]
    · exact hlook h
  · split_ifs at h with hx0 hx1
    · rw [cnst_spec hF _ k h, constAt_val hF hx, hx0, elem_zero hF, zero_mul]
    · cases h; rw [constAt_val hF hx, hx1, elem_one hF, one_mul]
    · exact hlook h
  · rw [cnst_spec hF _ k h, constAt_val hF hx, constAt_val hF hy, elem_mulE hF]

theorem frob_spec (hfr : FrobOK limbs) (a : Nat) :
    Spec (Program.frob a) fun k => val limbs H idx cd k = val limbs H idx cd a ^ 2 ^ 64 := by
  intro k h
  unfold Program.frob at h
  split at h
  · rename_i x hx
    rw [cnst_spec hF _ k h, constAt_val hF hx, hfr]
  · exact val_frob hfr (look_spec h)

end Implementation
