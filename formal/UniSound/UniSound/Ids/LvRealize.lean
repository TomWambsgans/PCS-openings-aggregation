-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The rows' lemmas (`walk`, the cosets,
-- `activePositions`) are this repository's `formal/UniComplete/UniComplete/DomainPositions.lean` (branch
-- `lean-uni-complete`, e7de70d), copied here as that library is not on this branch.
import UniSound.Ids.Bridges

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

end LvR

end UniSound.Ids
