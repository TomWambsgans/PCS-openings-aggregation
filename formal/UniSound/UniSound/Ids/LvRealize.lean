-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The rows' lemmas (`walk`, the cosets,
-- `activePositions`) are this repository's `formal/UniComplete/UniComplete/DomainPositions.lean` (branch
-- `lean-uni-complete`, e7de70d), copied here as that library is not on this branch.
import UniSound.Ids.Bridges
import Lv42.Protocol.LeanIsa.Read
import Lv42.Protocol.LeanIsa.Bus
import Heap.LeanIsa

/-!
# The heap read off `C1` realizes Lv42's bus (`LvRealizes`)

`lvRealizes`: for a deployment `D`, wherever the copies hold (`CopiesOf`), the heap the verifier reads off
`C1` (`hdOf`) realizes the bus of `C1`'s Lv42 stack (`Heap.Realizes`, `lv42Stack`): its push and its pull
tuples are permutations of `(D.inst rows).tuples q side`. The pieces:

1. **The forms are Lv42's flushes** (`uni_tuples_eq`, `tables_tuples`): on every row `r : ℕ → K`, table
   `j`'s tuples of `UniStatement.tables` (`tupleK` of its push or pull forms) are, in order, Lv42's flushes
   of opcode table `j` of that side (`Component.toM3` of its Clean component) evaluated at the row. By
   reflection: both sides are read as polynomials in a normal form (`SP`, `spNorm`; the forms' `E`
   coefficients by `toK`, Clean's expressions by `exprSP`), the twelve normal forms are equal by
   `decide +kernel` (`sides_eq`), and the normal form keeps the value (`spEval_spNorm`). Every tuple has at
   most `16` forms (`tables_length_le`).
2. **The rows** (`map_rowPosition`, `activePositions_perm`): `rowPosition count h` maps Lv42's executed rows
   `[0, count)` onto the active rows, a permutation of `{y < 2^h : isActive y count h}`.
3. **The values** (`row_eq`): Lv42's row `x` of opcode table `j` is `C1`'s row `rowPosition x`
   (`LvReadBack`), on `BLAKE2S`'s limb columns by the copies (`CopiesOf`; Lv42's slots are
   `UniStatement.qflockSlot`'s, `slots_eq`).
4. **The boundary** (`memSeed_eq`, …): the memory's and the bytecode's pairs and the state boundary are Lv42's
   six boundary blocks; the setup's address is `g^x` and its bytecode slots are `tupleSlot` (`BasisValueInv`).
5. **The heap** (`heap_keys`): `HeapLayout.new`'s blocks are the memory's, the bytecode's, the six tables'
   and unused ones; assembled as `Heap.LeanIsa.realizes`.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement

namespace LvR

/-! ## Polynomials in a normal form -/

/-- A polynomial in the row's variables: monomials (lists of variables) with `K` coefficients. -/
abbrev SP := List (List ℕ × K)

/-- A monomial's value at a row. -/
def monoVal (r : ℕ → K) (m : List ℕ) : K := (m.map r).prod

/-- A polynomial's value at a row. -/
def spEval (r : ℕ → K) (p : SP) : K := (p.map fun mc ↦ mc.2 * monoVal r mc.1).sum

@[simp] theorem spEval_nil (r : ℕ → K) : spEval r [] = 0 := rfl

@[simp] theorem spEval_cons (r : ℕ → K) (a : List ℕ × K) (p : SP) :
    spEval r (a :: p) = a.2 * monoVal r a.1 + spEval r p := by
  simp [spEval]

theorem spEval_append (r : ℕ → K) (p q : SP) : spEval r (p ++ q) = spEval r p + spEval r q := by
  simp [spEval]

theorem monoVal_append (r : ℕ → K) (a b : List ℕ) : monoVal r (a ++ b) = monoVal r a * monoVal r b := by
  simp [monoVal]

/-- A monomial's variables, sorted (insertion sort: the kernel reduces it). -/
def sortMono (m : List ℕ) : List ℕ := m.insertionSort (· ≤ ·)

theorem monoVal_sortMono (r : ℕ → K) (m : List ℕ) : monoVal r (sortMono m) = monoVal r m :=
  ((List.perm_insertionSort _ m).map r).prod_eq

/-- Add `c · m` to a polynomial sorted by `monoLt`, merging a monomial it has. -/
def spIns (m : List ℕ) (c : K) : SP → SP
  | [] => [(m, c)]
  | (k, v) :: rest =>
    if k = m then (k, v + c) :: rest
    else if monoLt m k then (m, c) :: (k, v) :: rest
    else (k, v) :: spIns m c rest

theorem spEval_spIns (r : ℕ → K) (m : List ℕ) (c : K) (p : SP) :
    spEval r (spIns m c p) = c * monoVal r m + spEval r p := by
  induction p with
  | nil => simp [spIns]
  | cons a p ih =>
    obtain ⟨k, v⟩ := a
    simp only [spIns]
    split_ifs with h1 h2
    · subst h1
      simp only [spEval_cons]
      ring
    · simp only [spEval_cons]
    · simp only [spEval_cons, ih]
      ring

/-- **The normal form**: monomials sorted and merged, zero coefficients dropped. -/
def spNorm (p : SP) : SP :=
  (p.foldr (fun mc acc ↦ spIns (sortMono mc.1) mc.2 acc) []).filter fun mc ↦ decide (mc.2 ≠ 0)

theorem spEval_foldr (r : ℕ → K) (p : SP) :
    spEval r (p.foldr (fun mc acc ↦ spIns (sortMono mc.1) mc.2 acc) []) = spEval r p := by
  induction p with
  | nil => rfl
  | cons a p ih => rw [List.foldr_cons, spEval_spIns, ih, monoVal_sortMono, spEval_cons]

theorem spEval_filter (r : ℕ → K) (p : SP) :
    spEval r (p.filter fun mc ↦ decide (mc.2 ≠ 0)) = spEval r p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    by_cases h : a.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih, spEval_cons, h, zero_mul, zero_add]
    · rw [List.filter_cons_of_pos (by simp [h]), spEval_cons, spEval_cons, ih]

/-- **The normal form keeps the value.** -/
theorem spEval_spNorm (r : ℕ → K) (p : SP) : spEval r (spNorm p) = spEval r p := by
  rw [spNorm, spEval_filter, spEval_foldr]

/-- The product of two polynomials. -/
def spMul (p q : SP) : SP := p.flatMap fun a ↦ q.map fun b ↦ (a.1 ++ b.1, a.2 * b.2)

theorem spEval_map_mul (r : ℕ → K) (a : List ℕ × K) (q : SP) :
    spEval r (q.map fun b ↦ (a.1 ++ b.1, a.2 * b.2)) = a.2 * monoVal r a.1 * spEval r q := by
  induction q with
  | nil => simp
  | cons b q ih =>
    rw [List.map_cons, spEval_cons, spEval_cons, ih, monoVal_append]
    ring

theorem spEval_spMul (r : ℕ → K) (p q : SP) : spEval r (spMul p q) = spEval r p * spEval r q := by
  induction p with
  | nil => simp [spMul]
  | cons a p ih =>
    rw [spMul, List.flatMap_cons, spEval_append, spEval_map_mul, ← spMul, ih, spEval_cons]
    ring

/-! ## Clean's expressions and the verifier's forms as polynomials -/

/-- A Clean expression on a row of `n` cells as a polynomial (a variable past the row is `0`, as Clean
reads a missing cell). -/
def exprSP (n : ℕ) : Expression K → SP
  | .var v => if v.index < n then [([v.index], 1)] else []
  | .const c => [([], c)]
  | .add x y => exprSP n x ++ exprSP n y
  | .mul x y => spMul (exprSP n x) (exprSP n y)

/-- **An expression's value on a row is its polynomial's.** -/
theorem eval_exprSP (n : ℕ) (R : ℕ → K) (data : ProverData K) (e : Expression K) :
    e.eval (Environment.fromArray (Array.ofFn fun i : Fin n ↦ R i.val) data) = spEval R (exprSP n e) := by
  induction e with
  | var v =>
    simp only [Expression.eval, exprSP]
    split_ifs with h
    · simp [h, monoVal]
    · simp [h]
  | const c => simp [Expression.eval, exprSP, monoVal]
  | add x y hx hy => simp only [Expression.eval, exprSP, spEval_append, hx, hy]
  | mul x y hx hy => simp only [Expression.eval, exprSP, spEval_spMul, hx, hy]

/-- A form as a polynomial: its coefficients read in `K` (`toK`), a monomial of more than two variables
`0` (as `formK` reads it). -/
def formSP (f : Form) : SP := f.map fun mc ↦ (mc.1, if mc.1.length ≤ 2 then toK mc.2 else 0)

/-- **A form's value on a row is its polynomial's.** -/
theorem formK_eq (f : Form) (R : ℕ → K) : formK f R = spEval R (formSP f) := by
  simp only [formK, formSP, spEval, List.map_map]
  congr 1
  refine List.map_congr_left fun mc _ ↦ ?_
  obtain ⟨m, c⟩ := mc
  match m with
  | [] => simp [monoVal]
  | [i] => simp [monoVal]
  | [i, j] => simp only [Function.comp_apply, monoVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil]; simp; ring
  | _ :: _ :: _ :: _ => simp

/-! ## Tuples -/

/-- No prover data (a flush's polynomials read none). -/
def noData : ProverData K := fun _ _ ↦ #[]

/-- Sixteen polynomials' values at a row. -/
def tupleOfSP (R : ℕ → K) (l : List SP) : Vector K 16 := Vector.ofFn fun s ↦ spEval R (l.getD s.val [])

/-- A tuple of forms as sixteen polynomials. -/
def tupSP (tup : List Form) : List SP := (List.range 16).map fun s ↦ formSP (tup.getD s [])

/-- An interaction of a Clean component as sixteen polynomials: its separator, its message, zeros. -/
def aiSP (n : ℕ) (ai : AbstractInteraction K) : List SP :=
  (List.range 16).map fun k ↦
    if k = 0 then [([], Lv42.Arithmetization.channelSep ai.channel)]
    else match ai.msg.toArray[k - 1]? with
      | some e => exprSP n e
      | none => []

theorem getD_map_range (g : ℕ → SP) (s : ℕ) (hs : s < 16) :
    (((List.range 16).map g).map spNorm).getD s [] = spNorm (g s) := by
  rw [List.getD_eq_getElem _ _ (by simp [hs])]
  simp

/-- **`tupleK` is its polynomials' values.** -/
theorem tupleK_eq (tup : List Form) (R : ℕ → K) : tupleK tup R = tupleOfSP R ((tupSP tup).map spNorm) := by
  apply Vector.ext
  intro s hs
  simp only [tupleK, tupleOfSP, tupSP, Vector.getElem_ofFn]
  rw [getD_map_range _ s hs, spEval_spNorm, formK_eq]

/-- **A flush's polynomials evaluate to its polynomials' values.** -/
theorem flushPolys_eval_eq (n : ℕ) (ai : AbstractInteraction K) (R : ℕ → K) :
    (LeanVM.Protocol.flushPolys Lv42.Arithmetization.channelSep n ai).map
        (·.eval fun i : Fin n ↦ R i.val) = tupleOfSP R ((aiSP n ai).map spNorm) := by
  apply Vector.ext
  intro k hk
  simp only [LeanVM.Protocol.flushPolys, Vector.getElem_map, Vector.getElem_ofFn, tupleOfSP, aiSP]
  rw [getD_map_range _ k hk, spEval_spNorm]
  split_ifs with h0
  · simp [CPoly.CMvPolynomial.eval_C, monoVal]
  · cases hm : ai.msg.toArray[k - 1]? with
    | none => simp [CPoly.CMvPolynomial.eval_zero]
    | some e =>
      simp only [Option.map_some, Option.getD_some]
      rw [Expression.eval_toCMvPolynomial _ noData, eval_exprSP]

/-! ## The six tables: the forms are Lv42's flushes -/

/-- Table `j`'s forms of one side, as normal forms. -/
def uniSide (j : ℕ) (push : Bool) : List (List SP) :=
  ((if push then (tables.getD j default).flushes.push else (tables.getD j default).flushes.pull).map
    tupSP).map (·.map spNorm)

/-- Lv42's opcode table `j`'s interactions of one side. -/
def lvInteractions (j : Fin 6) (push : Bool) : List (AbstractInteraction K) :=
  (Lv42.Protocol.LeanIsa.opcodeComponent j).rowOperations.interactions.filter fun ai ↦
    decide (Lv42.Arithmetization.channelDir ai.channel =
      if push then Lv42.Arithmetization.Direction.push else .pull)

/-- Lv42's opcode table `j`'s flushes of one side, as normal forms. -/
def lvSide (j : Fin 6) (push : Bool) : List (List SP) :=
  ((lvInteractions j push).map (aiSP (Lv42.Protocol.LeanIsa.opcodeComponent j).width)).map (·.map spNorm)

set_option maxRecDepth 100000 in
/-- **The normal forms are equal**, table by table, side by side, in order. -/
theorem sides_eq : ∀ j : Fin 6, ∀ push : Bool, uniSide j push = lvSide j push := by
  decide +kernel

/-- **The forms are Lv42's flushes**, on every row, in order. -/
theorem uni_tuples_eq (j : Fin 6) (push : Bool) (R : ℕ → K) :
    ((if push then (tables.getD j default).flushes.push else (tables.getD j default).flushes.pull).map
        fun tup ↦ tupleK tup R) =
      (lvInteractions j push).map fun ai ↦
        (LeanVM.Protocol.flushPolys Lv42.Arithmetization.channelSep
          (Lv42.Protocol.LeanIsa.opcodeComponent j).width ai).map
            (·.eval fun i : Fin (Lv42.Protocol.LeanIsa.opcodeComponent j).width ↦ R i.val) := by
  have h := congrArg (List.map (tupleOfSP R)) (sides_eq j push)
  simp only [uniSide, lvSide, List.map_map] at h
  simp only [tupleK_eq, flushPolys_eval_eq]
  exact h

set_option maxRecDepth 100000 in
/-- **Every tuple has at most sixteen forms.** -/
theorem tables_length_le : ∀ j : Fin 6, ∀ tup ∈ (tables.getD j default).flushes.push ++
    (tables.getD j default).flushes.pull, tup.length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Every coefficient of the forms lies in `K`** (its `y` and `y²` limbs are zero), and every monomial has
at most two variables. -/
theorem tables_coeffs_decide : ∀ j : Fin 6, ∀ tup ∈ (tables.getD j default).flushes.push ++
    (tables.getD j default).flushes.pull, ∀ f ∈ tup, ∀ mc ∈ f, IsInK mc.2 ∧ mc.1.length ≤ 2 := by
  decide +kernel

/-- **Every coefficient of the forms is `ofK` of its `K` reading** (`toK`), and every monomial has at most
two variables. -/
theorem tables_coeffs (j : Fin 6) : ∀ tup ∈ (tables.getD j default).flushes.push ++
    (tables.getD j default).flushes.pull, ∀ f ∈ tup, ∀ mc ∈ f, mc.2 = ofK (toK mc.2) ∧ mc.1.length ≤ 2 := by
  intro tup htup f hf mc hmc
  obtain ⟨hK, hl⟩ := tables_coeffs_decide j tup htup f hf mc hmc
  refine ⟨?_, hl⟩
  rw [toK, ofK_eq_ofLimbs, ofLimbs_of_isInK hK]


/-! ## The rows: `rowPosition` maps the executed rows onto the active ones -/

theorem ite_pos_of {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_neg_of {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem two_pow_succ' (b : ℕ) : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ, mul_comm]

theorem coset_top {r b : ℕ} (hb : b < r) : 2 ^ r - 2 ^ (b + 1) + 2 ^ b = 2 ^ r - 2 ^ b := by
  have h1 : 2 ^ (b + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hb
  have := two_pow_succ' b
  omega

theorem coset_iff_log2 {r b i : ℕ} (hb : b < r) (hi : i < 2 ^ r) :
    (2 ^ r - 2 ^ (b + 1) ≤ i ∧ i < 2 ^ r - 2 ^ b) ↔ (2 ≤ 2 ^ r - i ∧ Nat.log2 (2 ^ r - i - 1) = b) := by
  have h1 : 2 ^ (b + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hb
  have h2 := two_pow_succ' b
  have hp : 0 < 2 ^ b := Nat.two_pow_pos b
  constructor
  · rintro ⟨hlo, hhi⟩
    have hne : 2 ^ r - i - 1 ≠ 0 := by omega
    refine ⟨by omega, (Nat.log2_eq_iff hne).mpr ⟨by omega, by omega⟩⟩
  · rintro ⟨hg, hl⟩
    have hne : 2 ^ r - i - 1 ≠ 0 := by omega
    have := (Nat.log2_eq_iff hne).mp hl
    omega

theorem log2_gap_lt {r i : ℕ} (hi : i < 2 ^ r) (hg : 2 ≤ 2 ^ r - i) : Nat.log2 (2 ^ r - i - 1) < r :=
  (Nat.log2_lt (by omega)).mpr (by omega)

theorem isActive_iff_exists {i count r : ℕ} (hi : i < 2 ^ r) (hfull : count ≠ 2 ^ r) :
    isActive i count r = true ↔
      ∃ b < r, count.testBit b = true ∧ 2 ^ r - 2 ^ (b + 1) ≤ i ∧ i < 2 ^ r - 2 ^ b := by
  unfold isActive
  rw [ite_neg_of hfull]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hg, hbit⟩
    exact ⟨_, log2_gap_lt hi hg, hbit, (coset_iff_log2 (log2_gap_lt hi hg) hi).mpr ⟨hg, rfl⟩⟩
  · rintro ⟨b, hb, hbit, hmem⟩
    obtain ⟨hg, hl⟩ := (coset_iff_log2 hb hi).mp hmem
    exact ⟨hg, hl ▸ hbit⟩

theorem coset_disjoint {r b b' j : ℕ} (hb : b < r) (hb' : b' < r) (hne : b ≠ b')
    (h : 2 ^ r - 2 ^ (b + 1) ≤ j ∧ j < 2 ^ r - 2 ^ (b + 1) + 2 ^ b)
    (h' : 2 ^ r - 2 ^ (b' + 1) ≤ j ∧ j < 2 ^ r - 2 ^ (b' + 1) + 2 ^ b') : False := by
  wlog hlt : b < b' generalizing b b'
  · exact this hb' hb (Ne.symm hne) h' h (by omega)
  have h1 : 2 ^ (b + 1) ≤ 2 ^ b' := Nat.pow_le_pow_right (by norm_num) hlt
  have h2 : 2 ^ (b' + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hb'
  have e1 := two_pow_succ' b
  have e2 := two_pow_succ' b'
  omega

theorem sum_bits_true (n r : ℕ) :
    ((List.range r).map fun b ↦ if n.testBit b = true then 2 ^ b else 0).sum = n % 2 ^ r := by
  induction r with
  | zero => simp [Nat.mod_one]
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_singleton, List.sum_singleton,
      Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ r) with h | h <;> simp [h]

/-- The cosets of the bits `b ∈ bs` of `count` equal to `v`, in order. -/
def cosets (count r : ℕ) (v : Bool) (bs : List ℕ) : List ℕ :=
  bs.flatMap fun b ↦ if count.testBit b = v then List.range' (2 ^ r - 2 ^ (b + 1)) (2 ^ b) else []

theorem cosets_cons (count r : ℕ) (v : Bool) (b : ℕ) (bs : List ℕ) :
    cosets count r v (b :: bs) =
      (if count.testBit b = v then List.range' (2 ^ r - 2 ^ (b + 1)) (2 ^ b) else []) ++
        cosets count r v bs := rfl

theorem mem_coset_ite {c : Prop} [Decidable c] {s n j : ℕ} :
    j ∈ (if c then List.range' s n else []) ↔ c ∧ s ≤ j ∧ j < s + n := by
  split_ifs with h
  · rw [List.mem_range'_1]
    exact ⟨fun h' ↦ ⟨h, h'⟩, fun h' ↦ h'.2⟩
  · simp [h]

theorem mem_cosets {count r : ℕ} {v : Bool} {bs : List ℕ} {j : ℕ} :
    j ∈ cosets count r v bs ↔
      ∃ b ∈ bs, count.testBit b = v ∧ 2 ^ r - 2 ^ (b + 1) ≤ j ∧ j < 2 ^ r - 2 ^ (b + 1) + 2 ^ b := by
  unfold cosets
  rw [List.mem_flatMap]
  exact exists_congr fun b ↦ and_congr_right fun _ ↦ mem_coset_ite

theorem length_cosets (count r : ℕ) (v : Bool) (bs : List ℕ) :
    (cosets count r v bs).length = (bs.map fun b ↦ if count.testBit b = v then 2 ^ b else 0).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [cosets_cons, List.length_append, ih, List.map_cons, List.sum_cons]
    split_ifs <;> simp

theorem lt_of_mem_cosets {count r : ℕ} {v : Bool} {bs : List ℕ} (hbs : ∀ b ∈ bs, b < r) {j : ℕ}
    (hj : j ∈ cosets count r v bs) : j < 2 ^ r - 1 := by
  obtain ⟨b, hb, _, _, hhi⟩ := mem_cosets.mp hj
  rw [coset_top (hbs b hb)] at hhi
  have := Nat.two_pow_pos b
  omega

theorem nodup_cosets {count r : ℕ} {v : Bool} {bs : List ℕ} (hnd : bs.Nodup) (hbs : ∀ b ∈ bs, b < r) :
    (cosets count r v bs).Nodup := by
  unfold cosets
  rw [List.nodup_flatMap]
  refine ⟨fun b _ ↦ ?_, hnd.imp_of_mem fun {a b} ha hb hab ↦ ?_⟩
  · split_ifs
    · exact List.nodup_range'
    · exact List.nodup_nil
  · intro j h1 h2
    obtain ⟨-, h1⟩ := mem_coset_ite.mp h1
    obtain ⟨-, h2⟩ := mem_coset_ite.mp h2
    exact coset_disjoint (hbs a ha) (hbs b hb) hab h1 h2

theorem range_reverse_lt (r : ℕ) : ∀ b ∈ (List.range r).reverse, b < r := by
  intro b hb
  simpa using hb

theorem range_reverse_nodup (r : ℕ) : (List.range r).reverse.Nodup :=
  List.nodup_reverse.mpr List.nodup_range

theorem activePositions_of_ne {count r : ℕ} (h : count ≠ 2 ^ r) :
    activePositions count r = cosets count r true (List.range r).reverse := by
  unfold activePositions
  rw [ite_neg_of h]
  rfl

theorem activePositions_full (r : ℕ) : activePositions (2 ^ r) r = List.range (2 ^ r) := by
  unfold activePositions
  rw [ite_pos_of rfl]

/-- `isActive` is membership in `activePositions`, for `i < 2^r`. -/
theorem mem_activePositions_iff {i count r : ℕ} (hi : i < 2 ^ r) :
    i ∈ activePositions count r ↔ isActive i count r = true := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [activePositions_full, List.mem_range]
    simp [isActive, hi]
  · rw [activePositions_of_ne hf, mem_cosets, isActive_iff_exists hi hf]
    simp only [List.mem_reverse, List.mem_range]
    refine exists_congr fun b ↦ ?_
    constructor
    · rintro ⟨hb, hbit, hlo, hhi⟩
      exact ⟨hb, hbit, hlo, by rw [← coset_top hb]; exact hhi⟩
    · rintro ⟨hb, hbit, hlo, hhi⟩
      exact ⟨hb, hbit, hlo, by rw [coset_top hb]; exact hhi⟩

theorem lt_of_mem_activePositions {count r j : ℕ} (hj : j ∈ activePositions count r) : j < 2 ^ r := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [activePositions_full, List.mem_range] at hj
    exact hj
  · rw [activePositions_of_ne hf] at hj
    have := lt_of_mem_cosets (range_reverse_lt r) hj
    omega

theorem activePositions_length {count r : ℕ} (hc : count ≤ 2 ^ r) :
    (activePositions count r).length = count := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [activePositions_full, List.length_range]
  · rw [activePositions_of_ne hf, length_cosets, List.map_reverse, List.sum_reverse, sum_bits_true,
      Nat.mod_eq_of_lt (lt_of_le_of_ne hc hf)]

theorem activePositions_nodup (count r : ℕ) : (activePositions count r).Nodup := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [activePositions_full]
    exact List.nodup_range
  · rw [activePositions_of_ne hf]
    exact nodup_cosets (range_reverse_nodup r) (range_reverse_lt r)

/-- `rowPosition`'s loop as a recursion over the bits `r − 1, …, 0`. -/
def walk (count r : ℕ) (v : Bool) : List ℕ → ℕ → Option ℕ × ℕ
  | [], y => (none, y)
  | b :: bs, y =>
    if count.testBit b = v then
      if y < 2 ^ b then (some (2 ^ r - 2 ^ (b + 1) + y), y) else walk count r v bs (y - 2 ^ b)
    else walk count r v bs y

theorem walk_fst (count r : ℕ) (v : Bool) (bs : List ℕ) (y : ℕ) :
    (walk count r v bs y).1 = (cosets count r v bs)[y]? := by
  induction bs generalizing y with
  | nil => rfl
  | cons b bs ih =>
    rw [walk, cosets_cons]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left (by rw [List.length_range']; exact h2), List.getElem?_range' h2,
        one_mul]
    · rw [ih, List.getElem?_append_right (by rw [List.length_range']; omega), List.length_range']
    · rw [ih, List.nil_append]

theorem forIn_walk (count r : ℕ) (v : Bool) (F : ℕ → Option ℕ × ℕ → Id (ForInStep (Option ℕ × ℕ)))
    (hF : ∀ i s, F i s = if (count.testBit (r - 1 - i) == v) = true then
        (if s.2 < 2 ^ (r - 1 - i) then pure (ForInStep.done (some (2 ^ r - 2 ^ (r - 1 - i + 1) + s.2), s.2))
          else pure (ForInStep.yield (none, s.2 - 2 ^ (r - 1 - i))))
        else pure (ForInStep.yield (none, s.2)))
    (L : List ℕ) (y : ℕ) :
    forIn L ((none : Option ℕ), y) F = (walk count r v (L.map fun i ↦ r - 1 - i) y : Id (Option ℕ × ℕ)) := by
  induction L generalizing y with
  | nil => rfl
  | cons i L ih =>
    rw [List.forIn_cons, hF, List.map_cons, walk]
    simp only [beq_iff_eq]
    split_ifs with h1 h2
    · rfl
    · exact ih _
    · exact ih _

theorem range'_map_reverse (r : ℕ) : (List.range' 0 r).map (fun i ↦ r - 1 - i) = (List.range r).reverse := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range', List.getElem_reverse, List.getElem_range,
      List.length_range]
    omega

theorem rowPosition_of_ne {count r : ℕ} (hf : count ≠ 2 ^ r) (x : ℕ) :
    rowPosition count r x =
      ((cosets count r (decide (x < count)) (List.range r).reverse)[if x < count then x else x - count]?).getD
        (2 ^ r - 1) := by
  unfold rowPosition
  simp only [Id.run, ite_neg_of hf]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_walk count r (decide (x < count)) _ (fun _ _ ↦ rfl)]
  have hsize : (Std.Legacy.Range.mk 0 r 1 (by omega)).size = r := by
    simp [Std.Legacy.Range.size]
  have hL := range'_map_reverse r
  have hw := walk_fst count r (decide (x < count)) (List.range r).reverse
    (if decide (x < count) = true then x else x - count)
  simp only [decide_eq_true_eq] at hw ⊢
  rw [hsize, hL, ← hw]
  rcases walk count r (decide (x < count)) (List.range r).reverse (if x < count then x else x - count) with
    ⟨_ | v, y'⟩ <;> rfl

theorem rowPosition_full (r x : ℕ) : rowPosition (2 ^ r) r x = x := by
  unfold rowPosition
  simp only [Id.run]
  rfl

/-- **An executed row's position**: entry `x` of `activePositions`. -/
theorem rowPosition_of_lt {count r x : ℕ} (hc : count ≤ 2 ^ r) (hx : x < count) :
    rowPosition count r x = (activePositions count r)[x]'(by rw [activePositions_length hc]; exact hx) := by
  by_cases hf : count = 2 ^ r
  · subst hf
    simp only [rowPosition_full, activePositions_full, List.getElem_range]
  · rw [rowPosition_of_ne hf, ite_pos_of hx, decide_eq_true hx, ← activePositions_of_ne hf,
      List.getElem?_eq_getElem (by rw [activePositions_length hc]; exact hx), Option.getD_some]

/-- **`rowPosition` lists the active rows**, in order. -/
theorem map_rowPosition {count r : ℕ} (hc : count ≤ 2 ^ r) :
    (List.range count).map (rowPosition count r) = activePositions count r := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, activePositions_length hc]
  · intro x h1 h2
    rw [List.getElem_map, List.getElem_range, rowPosition_of_lt hc (by simpa using h1)]

/-- **The active rows are `isActive`'s.** -/
theorem activePositions_perm (count r : ℕ) :
    (activePositions count r).Perm ((List.range (2 ^ r)).filter fun y ↦ isActive y count r) := by
  refine (List.perm_ext_iff_of_nodup (activePositions_nodup count r)
    (List.nodup_range.filter _)).mpr fun y ↦ ?_
  rw [List.mem_filter, List.mem_range]
  constructor
  · intro h
    exact ⟨lt_of_mem_activePositions h, (mem_activePositions_iff (lt_of_mem_activePositions h)).mp h⟩
  · rintro ⟨h1, h2⟩
    exact (mem_activePositions_iff h1).mpr h2

/-- An executed row's position is a row of the table. -/
theorem rowPosition_lt_of_lt {count r x : ℕ} (hc : count ≤ 2 ^ r) (hx : x < count) :
    rowPosition count r x < 2 ^ r := by
  rw [rowPosition_of_lt hc hx]
  exact lt_of_mem_activePositions (List.getElem_mem _)

/-! ## Lv42's flushes on a row -/

open Lv42.Protocol Lv42.Protocol.LeanIsa

theorem decide_sideOf (d : Lv42.Arithmetization.Direction) (side : Side) :
    decide (sideOf d = side) = decide (d = if decide (side = .push) then .push else .pull) := by
  cases d <;> cases side <;> rfl

theorem dite_pos_of {α : Sort*} {c : Prop} [Decidable c] {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := by
  simp [h]

theorem map_filter_map {α β γ : Type*} (l : List α) (f : α → β) (p : β → Bool) (g : β → γ)
    (q : α → Bool) (h : ∀ a, p (f a) = q a) (g' : α → γ) (hg : ∀ a, g (f a) = g' a) :
    ((l.map f).filter p).map g = (l.filter q).map g' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons, h a]
    split_ifs
    · rw [List.map_cons, List.map_cons, hg a, ih]
    · exact ih

/-- Lv42's opcode table `j`'s flushes: its interactions, each on its channel's side. -/
theorem flushes_opIdx (j : Fin 6) :
    flushes (opIdx j) = ((opcodeComponent j).rowOperations.interactions.map fun i ↦
      (Lv42.Arithmetization.channelDir i.channel,
        LeanVM.Protocol.flushPolys Lv42.Arithmetization.channelSep (opcodeComponent j).width i)).map
          fun f ↦ (sideOf f.1, f.2) := rfl

/-- Lv42's flushes of opcode table `j` of a side, on a row, are its interactions' of that side. -/
theorem inst_flushes_eq (j : Fin 6) (side : Side) (row : Fin (width (opIdx j)) → K) :
    ((flushes (opIdx j)).filter fun f ↦ decide (f.1 = side)).map (fun f ↦ f.2.map (·.eval row)) =
      (lvInteractions j (decide (side = .push))).map fun ai ↦
        (LeanVM.Protocol.flushPolys Lv42.Arithmetization.channelSep (opcodeComponent j).width ai).map
          (·.eval row) := by
  rw [flushes_opIdx, List.map_map]
  exact map_filter_map _ _
    (fun f : Side × Vector (CPoly.CMvPolynomial (opcodeComponent j).width K) 16 ↦ decide (f.1 = side)) _ _
    (fun ai ↦ decide_sideOf _ side) _ fun _ ↦ rfl

/-- **A row's flushes are its forms' tuples**: where Lv42's row `x` of opcode table `j` is the row `R`,
its tuples of a side are the forms' of that side at `R`, in order. -/
theorem rowTuples_eq (F : FlockSpec) (prog : Lv42.Semantics.Program) (s : Sizes)
    (q : LeanVM.Protocol.Column (leanIsaInstance F prog s).μ) (j : Fin 6) (side : Side) (x : ℕ)
    (hx : x < 2 ^ (leanIsaInstance F prog s).τ (opIdx j)) (R : ℕ → K)
    (hrow : (leanIsaInstance F prog s).row q (opIdx j) ⟨x, hx⟩ = fun i ↦ R i.val) :
    Heap.rowTuples (leanIsaInstance F prog s) q (opIdx j) side x =
      (if side = .push then (tables.getD j default).flushes.push
        else (tables.getD j default).flushes.pull).map fun tup ↦ tupleK tup R := by
  simp only [Heap.rowTuples, dite_pos_of hx, Heap.flushTuple, hrow]
  refine (inst_flushes_eq j side _).trans ?_
  cases side
  · exact (uni_tuples_eq j true R).symm
  · exact (uni_tuples_eq j false R).symm

/-! ## The values: Lv42's rows are `C1`'s -/

theorem layoutOf_c1 (S : UniStatement.Shape) : layoutOf S .c1 = c1Layout S := rfl

theorem layoutOf_setup (S : UniStatement.Shape) : layoutOf S .setup = setupLayout S := rfl

set_option maxRecDepth 10000 in
/-- **Lv42's slots are the verifier's**: limb `k` (column `9 + k`) is `q_flock`'s slot `slots k`. -/
theorem slots_eq : ∀ k : Fin 18,
    qflockSlot (blake2sColumns.getD (9 + k.val) "") = some (Blake2sFlock.slots k).val := by
  decide

/-- A column of one limb, read at a row of its block. -/
theorem c1Block_getD {L : StackLayout} {col : Column} {v off : ℕ} (h : L.limbs col = [(0, v, off)])
    (stack : ℕ → K) {i : ℕ} (hi : i < 2 ^ v) : (c1Block L stack col).getD i 0 = stack (off + i) := by
  simp [c1Block, h, hi]

section Rows

variable (D : Deployment) (rows : List ℕ) (c : Stk)

/-- **Lv42's executed row `x` of opcode table `j` is `C1`'s row `rowPosition x`**: by `LvReadBack` on the
committed columns, by the copies on `BLAKE2S`'s limbs. -/
theorem row_eq (hRB : LvReadBack D) (hC1 : C1Limbs D.shape)
    (hcp : ∀ x < 2 ^ D.shape.heights.getD opBlake2s 0, ∀ col slot,
      qflockSlot (blake2sColumns.getD col "") = some slot →
        c1Val D c (.table opBlake2s col) (D.shape.heights.getD opBlake2s 0) x = c (qfOff D + slot + 256 * x))
    (j : Fin 6) (x : Fin (2 ^ (D.inst rows).τ (opIdx j))) (hx : x.val < rows.getD j 0)
    (hcount : rows.getD j 0 ≤ 2 ^ D.shape.heights.getD j 0) :
    (D.inst rows).row (lv42Stack D.prog (D.sizes rows) D.shape c) (opIdx j) x =
      fun i ↦ c1Row D c j (rowPosition (rows.getD j 0) (D.shape.heights.getD j 0) x.val) i.val := by
  funext i
  by_cases hl : IsLimb ⟨opIdx j, i⟩
  · obtain ⟨hj, h9, h27⟩ := hl
    have hj5 : j = 5 := by
      have := congrArg Fin.val hj
      simp only [opIdx] at this
      exact Fin.ext (by omega)
    subst hj5
    change 9 ≤ i.val at h9
    change i.val < 27 at h27
    set k : Fin 18 := ⟨i.val - 9, by omega⟩ with hk
    have hik : i.val = 9 + k.val := by simp only [hk]; omega
    have hb : 9 + k.val < width (opIdx 5) := by rw [width_blake2s]; have := k.isLt; omega
    have key : ∀ i' : Fin (width (opIdx 5)), i'.val = 9 + k.val →
        (D.inst rows).row (lv42Stack D.prog (D.sizes rows) D.shape c) (opIdx 5) x i' =
          ((D.inst rows).column (lv42Stack D.prog (D.sizes rows) D.shape c) (limbCol k)).values.get x := by
      intro i' h
      have : i' = ⟨9 + k.val, hb⟩ := Fin.ext h
      subst this
      rfl
    rw [key i hik]
    have hlimb := column_limb Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows)
      (lv42Stack D.prog (D.sizes rows) D.shape c) k x
    have hfl := column_committed Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows)
      (lv42Stack D.prog (D.sizes rows) D.shape c) flockCol not_isLimb_flockCol
        (LeanVM.Protocol.cubeIndex (Blake2sFlock.blake2sFlockSpec.slot k) x)
    have e : ((D.inst rows).column (lv42Stack D.prog (D.sizes rows) D.shape c) (limbCol k)).values.get x =
        ((D.inst rows).column (lv42Stack D.prog (D.sizes rows) D.shape c) flockCol).values.get
          (LeanVM.Protocol.cubeIndex (Blake2sFlock.blake2sFlockSpec.slot k) x) := by
      rw [hlimb, hfl]
      rfl
    refine e.trans ((hRB rows c flockCol not_isLimb_flockCol _).trans ?_)
    show (Vector.ofFn fun x ↦ (c1Block (c1Layout D.shape) c .qflock).getD
        (x.val % 256 + 256 * rowPosition ((D.sizes rows).rows 5) (D.shape.heights.getD 5 0) (x.val / 256))
          0).get _ = _
    refine (Vector.get_ofFn _ _).trans ?_
    obtain ⟨off, hoff⟩ := hC1.2.2.2.2
    rw [layoutOf_c1] at hoff
    have hslot := (Blake2sFlock.slots k).isLt
    have hval : (LeanVM.Protocol.cubeIndex (k := 8) (Blake2sFlock.blake2sFlockSpec.slot k) x).val =
        (Blake2sFlock.slots k).val + 256 * x.val := by
      rw [LeanVM.Protocol.cubeIndex_val]
      rfl
    have hmod : (LeanVM.Protocol.cubeIndex (k := 8) (Blake2sFlock.blake2sFlockSpec.slot k) x).val % 256 =
        (Blake2sFlock.slots k).val := by
      rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hslot]
    have hdiv : (LeanVM.Protocol.cubeIndex (k := 8) (Blake2sFlock.blake2sFlockSpec.slot k) x).val / 256 = x.val := by
      rw [hval, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hslot, zero_add]
    show (c1Block (c1Layout D.shape) c .qflock).getD
        ((LeanVM.Protocol.cubeIndex (k := 8) (Blake2sFlock.blake2sFlockSpec.slot k) x).val % 256 +
          256 * rowPosition ((D.sizes rows).rows 5) (D.shape.heights.getD 5 0)
            ((LeanVM.Protocol.cubeIndex (k := 8) (Blake2sFlock.blake2sFlockSpec.slot k) x).val / 256)) 0 = _
    rw [hmod, hdiv]
    have hy : rowPosition (rows.getD 5 0) (D.shape.heights.getD 5 0) x.val < 2 ^ D.shape.heights.getD 5 0 :=
      rowPosition_lt_of_lt hcount hx
    have hidx : (Blake2sFlock.slots k).val + 256 * rowPosition (rows.getD 5 0) (D.shape.heights.getD 5 0) x.val <
        2 ^ (D.shape.heights.getD opBlake2s 0 + 8) := by
      rw [pow_add]
      show _ < 2 ^ D.shape.heights.getD 5 0 * 256
      nlinarith
    rw [show (D.sizes rows).rows 5 = rows.getD 5 0 from rfl, c1Block_getD hoff c hidx]
    have hc := hcp _ hy i.val (Blake2sFlock.slots k).val (by rw [hik]; exact slots_eq k)
    have hq : qfOff D = off := by simp [qfOff, hoff]
    show _ = c1Val D c (.table opBlake2s i.val) (D.shape.heights.getD opBlake2s 0)
      (rowPosition (rows.getD 5 0) (D.shape.heights.getD 5 0) x.val)
    rw [hc, hq, add_assoc]
  · have h := hRB rows c ⟨opIdx j, i⟩ hl x
    refine h.trans ?_
    show (Vector.ofFn fun x ↦ basisValue (c1Block (c1Layout D.shape) c (.table j.val i.val))
      (D.shape.heights.getD j.val 0)
        (rowPosition ((D.sizes rows).rows j) (D.shape.heights.getD j.val 0) x.val)).get x = _
    rw [Vector.get_ofFn]
    rfl

theorem flatMap_ite_filter {α β : Type*} (l : List α) (p : α → Bool) (g : α → List β) :
    (l.flatMap fun x ↦ if p x then g x else []) = (l.filter p).flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- **A table's block holds Lv42's executed rows' flushes**, on one side. -/
theorem table_side_perm (hRB : LvReadBack D) (hC1 : C1Limbs D.shape)
    (hcp : ∀ x < 2 ^ D.shape.heights.getD opBlake2s 0, ∀ col slot,
      qflockSlot (blake2sColumns.getD col "") = some slot →
        c1Val D c (.table opBlake2s col) (D.shape.heights.getD opBlake2s 0) x = c (qfOff D + slot + 256 * x))
    (j : Fin 6) (r : ℕ) (hr : r = D.shape.heights.getD j 0) (hcount : rows.getD j 0 ≤ 2 ^ r)
    (side : Side) :
    ((List.range (2 ^ r)).flatMap fun x ↦ if isActive x (rows.getD j 0) r then
      (if side = .push then (tables.getD j default).flushes.push
        else (tables.getD j default).flushes.pull).map (fun tup ↦ tupleK tup (c1Row D c j x)) else []).Perm
      (Heap.tableTuples (D.inst rows) (lv42Stack D.prog (D.sizes rows) D.shape c) (opIdx j) side) := by
  subst hr
  rw [flatMap_ite_filter]
  refine ((activePositions_perm _ _).symm.flatMap_right _).trans ?_
  rw [← map_rowPosition hcount, List.flatMap_map]
  refine List.Perm.trans (List.Perm.of_eq (List.flatMap_congr fun x hx ↦ ?_))
    (Heap.rows_perm_tableTuples (D.inst rows) (lv42Stack D.prog (D.sizes rows) D.shape c) (opIdx j) side)
  have hxc : x < rows.getD j 0 := List.mem_range.mp hx
  have hx' : x < 2 ^ (D.inst rows).τ (opIdx j) :=
    lt_of_lt_of_le hxc ((D.inst rows).rows_le (opIdx j))
  exact (rowTuples_eq _ _ _ _ j side x hx' _ (row_eq D rows c hRB hC1 hcp j ⟨x, hx'⟩ hxc hcount)).symm

/-- A table's block's pushes. -/
theorem tableBlock_pushes (hRB : LvReadBack D) (hC1 : C1Limbs D.shape)
    (hcp : ∀ x < 2 ^ D.shape.heights.getD opBlake2s 0, ∀ col slot,
      qflockSlot (blake2sColumns.getD col "") = some slot →
        c1Val D c (.table opBlake2s col) (D.shape.heights.getD opBlake2s 0) x = c (qfOff D + slot + 256 * x))
    (j : Fin 6) (b : Block) (hr : b.r = D.shape.heights.getD j 0) (hcount : rows.getD j 0 ≤ 2 ^ b.r) :
    (tableBlockK D c rows b j).pushes.Perm
      (Heap.tableTuples (D.inst rows) (lv42Stack D.prog (D.sizes rows) D.shape c) (opIdx j) .push) :=
  table_side_perm D rows c hRB hC1 hcp j b.r hr hcount .push

/-- A table's block's pulls. -/
theorem tableBlock_pulls (hRB : LvReadBack D) (hC1 : C1Limbs D.shape)
    (hcp : ∀ x < 2 ^ D.shape.heights.getD opBlake2s 0, ∀ col slot,
      qflockSlot (blake2sColumns.getD col "") = some slot →
        c1Val D c (.table opBlake2s col) (D.shape.heights.getD opBlake2s 0) x = c (qfOff D + slot + 256 * x))
    (j : Fin 6) (b : Block) (hr : b.r = D.shape.heights.getD j 0) (hcount : rows.getD j 0 ≤ 2 ^ b.r) :
    (tableBlockK D c rows b j).pulls.Perm
      (Heap.tableTuples (D.inst rows) (lv42Stack D.prog (D.sizes rows) D.shape c) (opIdx j) .pull) :=
  table_side_perm D rows c hRB hC1 hcp j b.r hr hcount .pull

end Rows

/-! ## The heap's blocks -/

theorem forIn_inv {β : Type} (P : β → Prop) (L : List ℕ) (init : β) (F : ℕ → β → Id (ForInStep β))
    (hF : ∀ i b, P b → P (F i b).value) (h0 : P init) : P (forIn L init F) := by
  induction L generalizing init with
  | nil => exact h0
  | cons i L ih =>
    rw [List.forIn_cons]
    have := hF i init h0
    cases h : F i init with
    | done b => simp only [h, ForInStep.value] at this ⊢; exact this
    | yield b => simp only [h, ForInStep.value] at this ⊢; exact ih b this

theorem unusedBlocks_unused (base offset : ℕ) : ∀ b ∈ unusedBlocks base offset, b.leaves = .unused := by
  unfold unusedBlocks
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  intro b hb
  refine forIn_inv (fun s : Array Block × ℕ ↦ ∀ b ∈ s.1.toList, b.leaves = .unused) _ (#[], offset) _ ?_
    (by simp) b hb
  intro i s hs
  split_ifs with h
  · intro b hb
    simp only [ForInStep.value, bind, pure, Array.toList_push, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hs b hb
    · rfl
  · exact hs

/-- A block's key: its leaves and its variables. -/
def blockKey (b : Block) : Leaves × ℕ := (b.leaves, b.r)

theorem foldl_keys {β : Type} (f : Array Block × β → Leaves × ℕ → Array Block × β)
    (hf : ∀ acc p, (f acc p).1.toList.map blockKey = acc.1.toList.map blockKey ++ [p]) :
    ∀ (l : List (Leaves × ℕ)) (acc : Array Block × β),
      (l.foldl f acc).1.toList.map blockKey = acc.1.toList.map blockKey ++ l
  | [], acc => by simp
  | p :: l, acc => by rw [List.foldl_cons, foldl_keys f hf l, hf, List.append_assoc]; rfl

/-- **The heap's blocks** (`HeapLayout.new`): the memory's, the bytecode's, the tables', and unused ones
(read through any `F` that reads nothing off an unused block). -/
theorem heap_flatMap {α : Type} (S : UniStatement.Shape) (F : Leaves × ℕ → List α)
    (hF : ∀ r, F (.unused, r) = []) :
    ((S.heap.blocks.map blockKey).flatMap F).Perm
      (([(Leaves.memory, S.logMemory), (Leaves.bytecode, S.logBytecode)] ++
        (List.range S.heights.length).map fun t ↦ (Leaves.table t, S.heights.getD t 0)).flatMap F) := by
  unfold Shape.heap HeapLayout.new
  simp only []
  rw [List.map_append, List.flatMap_append, foldl_keys]
  · have hU : ∀ base off, (List.map blockKey (unusedBlocks base off)).flatMap F = [] := by
      intro base off
      refine List.flatMap_eq_nil_iff.mpr fun k hk ↦ ?_
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hk
      have := unusedBlocks_unused _ _ u hu
      simp only [blockKey, this, hF]
    rw [hU, List.append_nil]
    simp only [List.map_nil, List.nil_append]
    exact (List.mergeSort_perm _ _).flatMap_right _
  · intro acc p
    simp [blockKey]

/-! ## The setup -/

theorem setupLayout_eq (S : UniStatement.Shape) :
    setupLayout S = StackLayout.new [(.bytecodeTuple, S.logBytecode + 4, false), (.address, S.logMemory, false)] :=
  rfl

theorem setupLayout_blocks (S : UniStatement.Shape) : (setupLayout S).blocks =
    if S.logMemory ≤ S.logBytecode + 4 then
      [(.bytecodeTuple, 0, S.logBytecode + 4, 0), (.address, 0, S.logMemory, 2 ^ (S.logBytecode + 4))]
    else [(.address, 0, S.logMemory, 0), (.bytecodeTuple, 0, S.logBytecode + 4, 2 ^ S.logMemory)] := by
  rw [setupLayout_eq]
  unfold StackLayout.new
  simp only [List.flatMap_cons, List.flatMap_nil, Bool.false_eq_true, ite_false, List.range_one,
    List.map_cons, List.map_nil, List.singleton_append, List.append_nil]
  rw [List.mergeSort]
  split_ifs with h
  · simp [List.MergeSort.Internal.splitInTwo, h]
  · simp [List.MergeSort.Internal.splitInTwo, h]

theorem setupLayout_vars (S : UniStatement.Shape) : (setupLayout S).vars =
    max (log2Ceil (max (2 ^ (S.logBytecode + 4) + 2 ^ S.logMemory) 2)) 15 := by
  rw [setupLayout_eq]
  unfold StackLayout.new
  simp only [List.flatMap_cons, List.flatMap_nil, Bool.false_eq_true, ite_false, List.range_one,
    List.map_cons, List.map_nil, List.singleton_append, List.append_nil]
  rw [List.mergeSort]
  by_cases h : S.logMemory ≤ S.logBytecode + 4
  · simp [List.MergeSort.Internal.splitInTwo, h]
  · simp [List.MergeSort.Internal.splitInTwo, h, Nat.add_comm]

theorem setupStk_eq (D : Deployment) (w : ℕ) (tOff aOff : ℕ)
    (ht : (setupLayout D.shape).limbs .bytecodeTuple = [(0, D.shape.logBytecode + 4, tOff)])
    (ha : (setupLayout D.shape).limbs .address = [(0, D.shape.logMemory, aOff)])
    (hw : w < 2 ^ (setupLayout D.shape).vars) :
    setupStk D w = if tOff ≤ w ∧ w < tOff + 2 ^ (D.shape.logBytecode + 4) then
        ((Array.ofFn (n := 16) fun s ↦ bCoefficients D.prog.logSize
          (Array.ofFn (n := 2 ^ D.prog.logSize) fun i ↦ tupleSlot D.prog i s.val)).getD ((w - tOff) % 16)
            #[]).getD ((w - tOff) / 16) 0
      else if aOff ≤ w ∧ w < aOff + 2 ^ D.shape.logMemory then
        (bCoefficients D.shape.logMemory (Array.ofFn (n := 2 ^ D.shape.logMemory) fun i ↦
          LeanVM.Parameters.gpow i.val)).getD (w - aOff) 0
      else 0 := by
  simp only [setupStk, setupStack, ht, ha, List.headD_cons]
  simp [Array.getD_eq_getD_getElem?, hw]

theorem le_two_pow_log2Ceil (n : ℕ) : n ≤ 2 ^ log2Ceil n := by
  unfold log2Ceil
  split_ifs with h
  · simpa using h
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-- **The setup's two blocks**: one limb each, disjoint, inside the stack. -/
theorem setup_facts (S : UniStatement.Shape) : ∃ tOff aOff,
    (setupLayout S).limbs .bytecodeTuple = [(0, S.logBytecode + 4, tOff)] ∧
    (setupLayout S).limbs .address = [(0, S.logMemory, aOff)] ∧
    (tOff + 2 ^ (S.logBytecode + 4) ≤ aOff ∨ aOff + 2 ^ S.logMemory ≤ tOff) ∧
    tOff + 2 ^ (S.logBytecode + 4) ≤ 2 ^ (setupLayout S).vars ∧
    aOff + 2 ^ S.logMemory ≤ 2 ^ (setupLayout S).vars := by
  have hv : 2 ^ (S.logBytecode + 4) + 2 ^ S.logMemory ≤ 2 ^ (setupLayout S).vars := by
    rw [setupLayout_vars]
    calc _ ≤ max (2 ^ (S.logBytecode + 4) + 2 ^ S.logMemory) 2 := le_max_left _ _
      _ ≤ 2 ^ log2Ceil (max (2 ^ (S.logBytecode + 4) + 2 ^ S.logMemory) 2) := le_two_pow_log2Ceil _
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h1 := Nat.two_pow_pos S.logMemory
  have h2 := Nat.two_pow_pos (S.logBytecode + 4)
  by_cases h : S.logMemory ≤ S.logBytecode + 4
  · refine ⟨0, 2 ^ (S.logBytecode + 4), ?_, ?_, Or.inl (by omega), by omega, by omega⟩ <;>
      simp [StackLayout.limbs, setupLayout_blocks, h]
  · refine ⟨2 ^ S.logMemory, 0, ?_, ?_, Or.inr (by omega), by omega, by omega⟩ <;>
      simp [StackLayout.limbs, setupLayout_blocks, h]

theorem foldl_size {β : Type} (l : List β) (f : Array K → β → Array K) (hf : ∀ a b, (f a b).size = a.size) :
    ∀ v : Array K, (l.foldl f v).size = v.size := by
  induction l with
  | nil => intro v; rfl
  | cons b l ih => intro v; rw [List.foldl_cons, ih, hf]

theorem bCoefficients_size (r : ℕ) (v : Array K) : (bCoefficients r v).size = v.size := by
  unfold bCoefficients subsetSums PcsQuotient.Domain.coefficients
  rw [foldl_size _ _ (fun a _ ↦ Array.size_ofFn), foldl_size _ _ (fun a _ ↦ by
    simp [PcsQuotient.Domain.stage])]

/-- **The setup's address column is `g^x`** (`BasisValueInv`). -/
theorem suVal_address (D : Deployment) (hBV : BasisValueInv) (hlm : D.shape.logMemory ≤ 24) (x : ℕ)
    (hx : x < 2 ^ D.shape.logMemory) : suVal D .address D.shape.logMemory x = LeanVM.Parameters.gpow x := by
  obtain ⟨tOff, aOff, ht, ha, hdis, htv, hav⟩ := setup_facts D.shape
  have hblock : c1Block (setupLayout D.shape) (setupStk D) .address = bCoefficients D.shape.logMemory
      (Array.ofFn (n := 2 ^ D.shape.logMemory) fun i ↦ LeanVM.Parameters.gpow i.val) := by
    simp only [c1Block, ha]
    apply Array.ext
    · simp [bCoefficients_size]
    · intro i h1 h2
      simp only [Array.getElem_ofFn]
      rw [Array.size_ofFn] at h1
      rw [setupStk_eq D _ tOff aOff ht ha (by omega), ite_neg_of (by omega), ite_pos_of (by omega)]
      simp [Array.getD_eq_getD_getElem?, h2]
  rw [suVal, hblock, hBV _ hlm _ (by simp) x hx]
  simp [Array.getD_eq_getD_getElem?, hx]

/-- **The setup's bytecode slot `s` is `tupleSlot`** (`BasisValueInv`). -/
theorem slotVal_eq (D : Deployment) (hBV : BasisValueInv) (hlb : D.shape.logBytecode ≤ 24) (s : ℕ)
    (hs : s < 16) (x : Fin (2 ^ D.prog.logSize)) : slotVal D s x.val = tupleSlot D.prog x s := by
  obtain ⟨tOff, aOff, ht, ha, hdis, htv, hav⟩ := setup_facts D.shape
  have hlbe := D.logBytecode_eq
  have hoff : tupleOff D = tOff := by simp [tupleOff, ht]
  have harr : (Array.ofFn (n := 2 ^ D.shape.logBytecode) fun k ↦ setupStk D (tupleOff D + s + 16 * k.val)) =
      bCoefficients D.prog.logSize (Array.ofFn (n := 2 ^ D.prog.logSize) fun i ↦ tupleSlot D.prog i s) := by
    apply Array.ext
    · simp [bCoefficients_size, hlbe]
    · intro k h1 h2
      simp only [Array.getElem_ofFn]
      rw [Array.size_ofFn] at h1
      have hk16 : s + 16 * k < 2 ^ (D.shape.logBytecode + 4) := by
        rw [pow_add]; norm_num; omega
      rw [hoff, setupStk_eq D _ tOff aOff ht ha (by omega), ite_pos_of (by omega)]
      have e1 : (tOff + s + 16 * k - tOff) % 16 = s := by omega
      have e2 : (tOff + s + 16 * k - tOff) / 16 = k := by omega
      rw [e1, e2]
      simp [Array.getD_eq_getD_getElem?, hs, h2]
  rw [slotVal, harr, hlbe, hBV _ (hlbe ▸ hlb) _ (by simp) x.val x.isLt]
  simp [Array.getD_eq_getD_getElem?]

/-! ## Powers of the generator -/

theorem epowAux_eq : ∀ (fuel : ℕ) (base out : E) (n : ℕ), n < 2 ^ fuel →
    epowAux fuel base out n = out * base ^ n
  | 0, base, out, n, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [epowAux]
  | fuel + 1, base, out, n, h => by
    unfold epowAux
    split_ifs with h0 h1
    · subst h0; simp
    · rw [epowAux_eq fuel _ _ _ (by rw [pow_succ] at h; omega)]
      conv_rhs => rw [← Nat.div_add_mod n 2, h1, pow_add, pow_mul]
      ring
    · rw [epowAux_eq fuel _ _ _ (by rw [pow_succ] at h; omega)]
      have : n % 2 = 0 := by omega
      conv_rhs => rw [← Nat.div_add_mod n 2, this, add_zero, pow_mul]
      ring

theorem epow_eq (x : E) (n : ℕ) : epow x n = x ^ n := by
  rw [epow, epowAux_eq _ _ _ _ Nat.lt_log2_self, one_mul]

theorem gen_eq : gen = ofK LeanVM.Parameters.g := by
  rw [gen, eK, eNew, ofK_eq_ofLimbs]
  congr 1

/-- **`gpow i = ofK (g^i)`**: the verifier's powers of its generator lie in `K`. -/
theorem gpow_eq_ofK (n : ℕ) : UniStatement.gpow n = ofK (LeanVM.Parameters.gpow n) := by
  rw [UniStatement.gpow, epow_eq, gen_eq]
  exact (map_pow (algebraMap K E) _ _).symm

theorem toK_ofK (a : K) : toK (ofK a) = a := by
  simp [toK]

theorem toK_gpow (n : ℕ) : toK (UniStatement.gpow n) = LeanVM.Parameters.gpow n := by
  rw [gpow_eq_ofK, toK_ofK]

/-! ## The boundary: the memory's and the bytecode's pairs, the state boundary -/

theorem toK_sepMem : toK sepMem = LeanVM.Parameters.gpow 1 := by
  rw [sepMem, gen_eq, toK_ofK]
  exact (pow_one _).symm

theorem ofBits_four : K.ofBits 4 = LeanVM.Parameters.gpow 2 := by decide +kernel

section Boundary

variable (D : Deployment) (rows : List ℕ) (c : Stk)

theorem cell_mem (hRB : LvReadBack D) (i : Fin 4) (x : Fin (2 ^ (D.sizes rows).logMem)) :
    cell Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows) (lv42Stack D.prog (D.sizes rows) D.shape c)
      (memCol i) x = c1Val D c (.memory i.val) D.shape.logMemory x.val :=
  (hRB rows c (memCol i) (by simp [IsLimb, memCol, opIdx]) x).trans (Vector.get_ofFn _ _)

theorem cell_bfcnt (hRB : LvReadBack D) (x : Fin (2 ^ D.prog.logSize)) :
    cell Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows) (lv42Stack D.prog (D.sizes rows) D.shape c)
      bfcntCol x = c1Val D c .bytecodeFinal D.shape.logBytecode x.val := by
  refine (hRB rows c bfcntCol (by simp [IsLimb, bfcntCol, opIdx]) x).trans ((Vector.get_ofFn _ _).trans ?_)
  rw [D.logBytecode_eq]
  rfl

/-- **The memory's tuple of cell `x`** is Lv42's memory boundary tuple. -/
theorem memTupleK_eq (hRB : LvReadBack D) (hBV : BasisValueInv) (hlm : D.shape.logMemory ≤ 24) (cnt : K)
    (x : Fin (2 ^ (D.sizes rows).logMem)) :
    memTupleK D c cnt x.val = tupleOf (LeanVM.Parameters.gpow 1)
      (#[LeanVM.Parameters.gpow x.val, cnt] ++ (memLimbs Blake2sFlock.blake2sFlockSpec (D.sizes rows)
        (lv42Stack D.prog (D.sizes rows) D.shape c) x).toArray) := by
  have hsu := suVal_address D hBV hlm x.val x.isLt
  apply Vector.ext
  intro k hk
  simp only [memTupleK, tupleOf, Vector.getElem_ofFn, memLimbs, cell_mem D rows c hRB]
  interval_cases k <;> simp [hsu, toK_sepMem]

/-- **The bytecode's tuple of instruction `i`** is Lv42's bytecode boundary tuple. -/
theorem bcTupleK_eq (hBV : BasisValueInv) (hlb : D.shape.logBytecode ≤ 24) (cnt : K)
    (i : Fin (2 ^ D.prog.logSize)) :
    bcTupleK D cnt i.val = tupleOf (LeanVM.Parameters.gpow 2)
      (#[LeanVM.Parameters.gpow i.val, cnt] ++ (entryList i).toArray) := by
  apply Vector.ext
  intro k hk
  simp only [bcTupleK, tupleOf, Vector.getElem_ofFn, slotVal_eq D hBV hlb k hk i, tupleSlot, entryList]
  interval_cases k <;> simp [ofBits_four]

theorem initK_eq : initK = tupleOf (LeanVM.Parameters.gpow 0) #[1, 1] := by
  apply Vector.ext
  intro k hk
  simp only [initK, tupleOf, Vector.getElem_ofFn]
  interval_cases k <;> simp

theorem finK_eq : finK D = tupleOf (LeanVM.Parameters.gpow 0) #[D.prog.finalPc, 1] := by
  apply Vector.ext
  intro k hk
  simp only [finK, tupleOf, Vector.getElem_ofFn]
  interval_cases k <;> simp [toK_gpow, Lv42.Semantics.Program.finalPc, D.logBytecode_eq]

end Boundary

/-! ## The heap realizes Lv42's bus -/

/-- A leaf block's tuples of one side. -/
def lbSide (b : Heap.LeafBlock (Vector K 16)) : Side → List (Vector K 16)
  | .push => b.pushes
  | .pull => b.pulls

theorem blockK_key (D : Deployment) (c : Stk) (rows : List ℕ) (b : Block) :
    blockK D c rows b = blockK D c rows ⟨b.leaves, b.r, 0⟩ := by
  obtain ⟨l, r, p⟩ := b
  cases l <;> rfl

theorem blockK_unused (D : Deployment) (c : Stk) (rows : List ℕ) (r : ℕ) (side : Side) :
    lbSide (blockK D c rows ⟨.unused, r, 0⟩) side = [] := by
  cases side
  · exact Heap.LeafBlock.pushes_unused r
  · exact Heap.LeafBlock.pulls_unused r

theorem map_range_eq_finRange {α : Type*} (n : ℕ) (f : ℕ → α) (g : Fin n → α)
    (h : ∀ x : Fin n, f x.val = g x) : (List.range n).map f = (List.finRange n).map g := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left fun x _ ↦ h x

theorem perm_shuffle {α : Type*} (a b t f : List α) : (a ++ b ++ t ++ f).Perm (t ++ (f ++ a ++ b)) := by
  have := List.perm_append_comm (l₁ := a ++ b) (l₂ := t ++ f)
  simpa only [List.append_assoc] using this

theorem le_sum_of_mem' {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · rw [List.sum_cons]
      exact (ih h).trans (Nat.le_add_left _ _)

/-- **The heap's blocks, side by side**: the memory's, the bytecode's, the six tables'. -/
theorem blocks_side (D : Deployment) (c : Stk) (rows : List ℕ) (side : Side) :
    ((D.shape.heap.blocks.map (blockK D c rows)).flatMap (lbSide · side)).Perm
      (lbSide (blockK D c rows ⟨.memory, D.shape.logMemory, 0⟩) side ++
        lbSide (blockK D c rows ⟨.bytecode, D.shape.logBytecode, 0⟩) side ++
          (List.range 6).flatMap fun t ↦ lbSide (blockK D c rows ⟨.table t, D.shape.heights.getD t 0, 0⟩) side) := by
  have h := heap_flatMap D.shape (fun k ↦ lbSide (blockK D c rows ⟨k.1, k.2, 0⟩) side)
    (fun r ↦ blockK_unused D c rows r side)
  rw [List.flatMap_map] at h
  rw [List.flatMap_map]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map,
    D.valid.1] at h
  refine List.Perm.trans (List.Perm.of_eq ?_) h
  exact List.flatMap_congr fun b _ ↦ by rw [blockK_key]; rfl

/-- The memory and bytecode blocks' heights fit `BasisValueInv`'s. -/
theorem heights_le (D : Deployment) (hHG : HeapGood D.shape) :
    D.shape.logMemory ≤ 24 ∧ D.shape.logBytecode ≤ 24 := by
  obtain ⟨_, hh, hsum, -⟩ := hHG
  have hk := heap_flatMap D.shape (fun k : Leaves × ℕ ↦ if k.1 = .unused then [] else [2 ^ k.2])
    (fun r ↦ by simp)
  have hmem : ∀ k ∈ [(Leaves.memory, D.shape.logMemory), (Leaves.bytecode, D.shape.logBytecode)],
      2 ^ k.2 ≤ 2 ^ (D.shape.heap.h - 1) := by
    intro k hk'
    have hin : 2 ^ k.2 ∈ (D.shape.heap.blocks.map blockKey).flatMap
        (fun k : Leaves × ℕ ↦ if k.1 = .unused then [] else [2 ^ k.2]) := by
      refine hk.symm.subset (List.mem_flatMap.mpr ⟨k, List.mem_append_left _ hk', ?_⟩)
      rcases List.mem_cons.mp hk' with rfl | hk'
      · simp
      · rw [List.mem_singleton] at hk'
        subst hk'
        simp
    obtain ⟨k', hk'', hin'⟩ := List.mem_flatMap.mp hin
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk''
    rw [← hsum]
    have : 2 ^ k.2 = 2 ^ b.r := by
      by_cases hu : b.leaves = .unused
      · simp [blockKey, hu] at hin'
      · simpa [blockKey, hu] using hin'
    rw [this]
    exact le_sum_of_mem' (List.mem_map.mpr ⟨b, hb, rfl⟩)
  have h1 := hmem _ (List.mem_cons_self ..)
  have h2 := hmem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  simp only at *
  omega

open Lv42.Protocol.Blake2sFlock in
/-- **The heap read off `C1` realizes Lv42's bus** wherever the copies hold (`LvRealizes`). -/
theorem realizes (D : Deployment) (hRB : LvReadBack D) (hBV : BasisValueInv) (hC1 : C1Limbs D.shape)
    (hHG : HeapGood D.shape) : LvRealizes D := by
  intro s c hcp
  obtain ⟨⟨-, hfit⟩, hcopy⟩ := hcp
  obtain ⟨hlm, hlb⟩ := heights_le D hHG
  set rows := s.2 with hrows
  set q := lv42Stack D.prog (D.sizes rows) D.shape c with hq
  have htab : ∀ side : Side, ((List.range 6).flatMap fun t ↦
      lbSide (blockK D c rows ⟨.table t, D.shape.heights.getD t 0, 0⟩) side).Perm
        ((List.finRange 6).flatMap fun j ↦ Heap.tableTuples (D.inst rows) q (opIdx j) side) := by
    intro side
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    refine List.Perm.flatMap_left _ fun j _ ↦ ?_
    cases side
    · exact tableBlock_pushes D rows c hRB hC1 hcopy j ⟨.table j.val, _, 0⟩ rfl (hfit j j.isLt)
    · exact tableBlock_pulls D rows c hRB hC1 hcopy j ⟨.table j.val, _, 0⟩ rfl (hfit j j.isLt)
  have hrange : List.range (2 ^ D.shape.logBytecode) = List.range (2 ^ D.prog.logSize) := by
    rw [D.logBytecode_eq]
  constructor
  · -- push
    have hmem : lbSide (blockK D c rows ⟨.memory, D.shape.logMemory, 0⟩) .push =
        (List.finRange (2 ^ (D.sizes rows).logMem)).map fun x ↦ tupleOf (LeanVM.Parameters.gpow 1)
          (#[LeanVM.Parameters.gpow x.val, 1] ++ (memLimbs blake2sFlockSpec (D.sizes rows) q x).toArray) := by
      refine (Heap.LeafBlock.pushes_pair _ _ _).trans ?_
      exact map_range_eq_finRange _ _ _ fun x ↦ memTupleK_eq D rows c hRB hBV hlm 1 x
    have hbc : lbSide (blockK D c rows ⟨.bytecode, D.shape.logBytecode, 0⟩) .push =
        (List.finRange (2 ^ D.prog.logSize)).map fun i ↦ tupleOf (LeanVM.Parameters.gpow 2)
          (#[LeanVM.Parameters.gpow i.val, 1] ++ (entryList i).toArray) := by
      refine (Heap.LeafBlock.pushes_pair _ _ _).trans ?_
      rw [hrange]
      exact map_range_eq_finRange _ _ _ fun i ↦ bcTupleK_eq D hBV hlb 1 i
    have hb := blocks_side D c rows .push
    rw [hmem, hbc] at hb
    show ((D.shape.heap.blocks.map (blockK D c rows)).flatMap (lbSide · .push) ++ [initK]).Perm
      ((D.inst rows).flushTuples q .push ++ (D.inst rows).boundaryTuples q .push)
    rw [Heap.LeanIsa.flushTuples_eq_opcode, boundaryTuples_push, initK_eq]
    refine (hb.append_right _).trans ?_
    refine (((htab .push).append_left _).append_right _).trans ?_
    exact perm_shuffle _ _ _ _
  · -- pull
    have hmem : lbSide (blockK D c rows ⟨.memory, D.shape.logMemory, 0⟩) .pull =
        (List.finRange (2 ^ (D.sizes rows).logMem)).map fun x ↦ tupleOf (LeanVM.Parameters.gpow 1)
          (#[LeanVM.Parameters.gpow x.val, cell blake2sFlockSpec D.prog (D.sizes rows) q (memCol 3) x] ++
            (memLimbs blake2sFlockSpec (D.sizes rows) q x).toArray) := by
      refine (Heap.LeafBlock.pulls_pair _ _ _).trans ?_
      refine map_range_eq_finRange _ _ _ fun x ↦ ?_
      rw [cell_mem D rows c hRB 3 x]
      exact memTupleK_eq D rows c hRB hBV hlm _ x
    have hbc : lbSide (blockK D c rows ⟨.bytecode, D.shape.logBytecode, 0⟩) .pull =
        (List.finRange (2 ^ D.prog.logSize)).map fun i ↦ tupleOf (LeanVM.Parameters.gpow 2)
          (#[LeanVM.Parameters.gpow i.val, cell blake2sFlockSpec D.prog (D.sizes rows) q bfcntCol i] ++
            (entryList i).toArray) := by
      refine (Heap.LeafBlock.pulls_pair _ _ _).trans ?_
      rw [hrange]
      refine map_range_eq_finRange _ _ _ fun i ↦ ?_
      rw [cell_bfcnt D rows c hRB i]
      exact bcTupleK_eq D hBV hlb _ i
    have hb := blocks_side D c rows .pull
    rw [hmem, hbc] at hb
    show ((D.shape.heap.blocks.map (blockK D c rows)).flatMap (lbSide · .pull) ++ [finK D]).Perm
      ((D.inst rows).flushTuples q .pull ++ (D.inst rows).boundaryTuples q .pull)
    rw [Heap.LeanIsa.flushTuples_eq_opcode, boundaryTuples_pull, finK_eq]
    refine (hb.append_right _).trans ?_
    refine (((htab .pull).append_left _).append_right _).trans ?_
    exact perm_shuffle _ _ _ _

end LvR

/-- **The heap read off `C1` realizes Lv42's bus** wherever the copies hold (`LvRealizes`): from Lv42's
columns of `C1`'s Lv42 stack being `lv42Column`'s (`LvReadBack`), the setup's basis-`B` coefficients being its
values' (`BasisValueInv`), `C1`'s `q_flock` one limb (`C1Limbs`) and the heap's blocks fitting the leaves
(`HeapGood`: the memory's and the bytecode's heights at most `24`). -/
theorem lvRealizes (D : Deployment) (hRB : LvReadBack D) (hBV : BasisValueInv) (hC1 : C1Limbs D.shape)
    (hHG : HeapGood D.shape) : LvRealizes D :=
  LvR.realizes D hRB hBV hC1 hHG

end UniSound.Ids

/-- info: 'UniSound.Ids.lvRealizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.lvRealizes

/-- info: 'UniSound.Ids.LvR.uni_tuples_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.LvR.uni_tuples_eq

/-- info: 'UniSound.Ids.LvR.rowTuples_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.LvR.rowTuples_eq

/-- info: 'UniSound.Ids.LvR.tables_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.LvR.tables_length_le

/-- info: 'UniSound.Ids.LvR.tables_coeffs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.LvR.tables_coeffs

/-- info: 'UniSound.Ids.LvR.map_rowPosition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.LvR.map_rowPosition

/-- info: 'UniSound.Ids.LvR.activePositions_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.LvR.activePositions_perm

/-- info: 'UniSound.Ids.LvR.row_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.LvR.row_eq

/-- info: 'UniSound.Ids.LvR.slots_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms UniSound.Ids.LvR.slots_eq
