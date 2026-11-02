-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.Openings

/-!
# The simulator's tables, computed

The joint simulator opens, for each secret table, a public table with the verifier's claimed values
(`hsimT`). The classical choice of such a table is replaced here by **a computable Gaussian
elimination**, with the classical choice's guarantee: **the built table has the claimed values
whenever some table has them** (`claims_build`), so the joint model's claims `cl` stay the built
table's and the honest table's claims give `hT` (`Main.lean`).

**The elimination** (`Elim`, generic). Each entry `e` of the stack has a **column** `col e`: the
coordinates over `K` (`rep.coords`; for `F192` the limbs) of the `m` claims' weights at `e`, `r = 3m`
of them (`colOf`); the claimed values have the **target** `tgtOf val`. The **scan** (`scan`) takes the
entries in a fixed order (`entryAt k`, `k < N`), reduces each column by the rows found so far
(`reduce`: one subtraction per row) and, if what is left is not zero, keeps it as a new row,
normalized at its first nonzero coordinate (`insertE`); **it stops once every coordinate is a
pivot**. The solution (`solveElim`) is the target reduced by the rows, the entries recorded on the
way: a table (`sparse`) zero but at the at most `r` rows' entries.

* `solveElim_spec`: **whenever the target is a combination of the scanned entries' columns, the
  solution's columns sum to it**: the rows are in echelon form (`WF`); a combination of them zero at
  every pivot is zero (`eq_zero_of_mem_span`); every scanned column is a combination of the rows, or
  every coordinate is a pivot (`scan_spec`);
* **`claims_build`**: for claims that weigh nothing of the randomness (`WeightsFit`) and a scan
  that reaches every entry, **if some table has the claimed values, the built table has them**.

**The deployed tables** (`Tables`). The claims' weights and values are compiled (`pointWc`, `valWc`,
`pointQc`, `valsQc`: the verifier's formulas, the public polynomials evaluated by `Polynomial.eval`;
equal to `pointW`, `valsW`, `pointQ`, `valsQ`). The scan takes first a few **candidates**, then every
entry, lane by lane (`enumL`). The candidates are chosen so that the scan stops on them at almost
every challenge; correctness does not depend on them (`claims_build` asks only that every entry be
reached), and their rank, sketched here, is not proved in this file: for the witness claim the
overflow lane's entries `256 .. 260, 264`, where the weight is `R·eq(ρ, ·)·eq(ρ², ·)·eq(u₂, ·)·eq(u₃, ·)`
(`R` never zero), whose columns span `K³` when `ρ ∉ K`, or when `ρ ≠ 1` and the row of `t` is not in
`K`; for the quotient table the entry `2^22 - 1` of the lanes of blocks `3, 67, 131` (the sum claim
weighs `g·(1, Y, Y²)` there) and the first entries of the overflow lane's pieces `1, 17, 33, 5, 21, 37`
(the quotient claim weighs `R(1+z)(1+ρ)g·(1, Y, Y²)` on the first three, `Rz(1+ρ)g·(1, Y, Y²)` on the
others, the sum claim nothing), whose columns span `K⁶` when `ρ ≠ 1`. **`claims_simTW`**,
**`claims_simTQ`**: the claims of `simTW rep Y c v`, `simTQ rep P₀ stmt Y c v` are the verifier's
values `valsW c v`, `valsQ P₀ stmt Y c v` whenever some table's are.

**Cost** (field operations; `m ≤ 2` claims, `r = 3m ≤ 6` equations; a stack of `L = 40` or `63`
lanes of `2^ℓ = 2^19` or `2^22` entries, `H = 33` or `167` held pieces, points of `n = 25` or `30`
coordinates). A column is `m` evaluations of a claim's weight at an entry (`Layout.claimW`:
`O(6L + nH)`, about `4·10^3` operations) and `r` coordinates; inserting it is at most `r` reduction
steps of `O(r)` operations (each reduced vector computed once, `mat`); the solution `O(r²)`. **A scan
of `k` entries costs `O(k·(4·10^3·m + r²))`**. It stops after the first entries whose columns span
`K^r` (after the `6` or `9` candidates at the challenges above), and **after at most
`N = #candidates + L·2^ℓ` entries in any case** (`6 + 40·2^19`, `9 + 63·2^22`: `scan`'s fuel). The
table lists at most `2^r - 1` weighted entries (at most `r` distinct ones, the rows' entries); an
entry is read by one pass over that list. Nothing here is
`noncomputable` (`Test/Builder.lean` runs it on `F192`).
-/

open Finset Module QuotientSecurity QuotientSecurity.Hiding
open QuotientZk.Joint

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

namespace Builder

/-! ## Sparse tables -/

section Sparse

variable {K E ι Y : Type} [Field K] [Field E] [Algebra K E] [DecidableEq ι] [DecidableEq Y]

/-- **A sparse table**: listed entries and values (a repeated entry adds), zero elsewhere. -/
def sparse (es : List ((ι × Y) × K)) : ι → Y → K :=
  fun l y => (es.map fun p => if p.1 = (l, y) then p.2 else 0).sum

/-- What a weight gives a sparse table. -/
def sparseVal (w : ι → Y → E) (es : List ((ι × Y) × K)) : E :=
  (es.map fun p => p.2 • w p.1.1 p.1.2).sum

variable [Fintype ι] [Fintype Y]

theorem sparse_cons (p : (ι × Y) × K) (es : List ((ι × Y) × K)) :
    sparse (p :: es) = (fun l y => if p.1 = (l, y) then p.2 else 0) + sparse es := by
  funext l y
  simp [sparse]

/-- **The claims of a sparse table**, for claims that weigh nothing of the randomness: each is
what its weight gives the list. -/
theorem claimsMap_stackD_sparse (L : GadgetLayout ι Y) {m : ℕ} (Wc : Fin m → ι → Y → E)
    (hW : ∀ j l y, L.randPos l y → Wc j l y = 0) (es : List ((ι × Y) × K)) (j : Fin m) :
    HiddenLayout.claimsMap Wc (L.stackD (sparse es)) j = sparseVal (Wc j) es := by
  induction es with
  | nil =>
    have h0 : sparse ([] : List ((ι × Y) × K)) = 0 := by funext l y; simp [sparse]
    rw [h0, map_zero, map_zero]
    simp [sparseVal]
  | cons p es ih =>
    rw [sparse_cons, map_add, map_add, Pi.add_apply, ih]
    simp only [sparseVal, List.map_cons, List.sum_cons]
    congr 1
    show ∑ l, ∑ y, Wc j l y * algebraMap K E
        (if L.randPos l y then 0 else (if p.1 = (l, y) then p.2 else 0)) = p.2 • Wc j p.1.1 p.1.2
    rw [Finset.sum_eq_single p.1.1, Finset.sum_eq_single p.1.2]
    · by_cases hp : L.randPos p.1.1 p.1.2
      · rw [hW j _ _ hp]
        simp
      · simp only [hp, ↓reduceIte, Prod.mk.eta]
        rw [Algebra.smul_def, mul_comm]
    · intro y _ hy
      have : p.1 ≠ (p.1.1, y) := fun h => hy (congrArg Prod.snd h).symm
      simp [this]
    · simp
    · intro l _ hl
      refine Finset.sum_eq_zero fun y _ => ?_
      have : p.1 ≠ (l, y) := fun h => hl (congrArg Prod.fst h).symm
      simp [this]
    · simp

/-- Claims that fit the layout (`WeightsFit`) weigh nothing of the randomness. -/
theorem weight_randPos (L : GadgetLayout ι Y) {m : ℕ} {Wc : Fin m → ι → Y → E}
    (hW : L.WeightsFit Wc) : ∀ j l y, L.randPos l y → Wc j l y = 0 := by
  rintro j l y (hf | hg | hr | ⟨rfl, hh⟩)
  · exact hW.first j l y hf
  · exact hW.gadget j l y hg
  · exact hW.rand j l y hr
  · exact hW.off_held j y hh

end Sparse

/-! ## Gaussian elimination -/

section Elim

variable {K α : Type} [Field K] [DecidableEq K] {r : ℕ}

/-- **A row of the echelon basis**: its pivot, its vector, the weighted entries it combines. -/
structure Row (K α : Type) (r : ℕ) where
  piv : Fin r
  vec : Fin r → K
  comb : List (α × K)

/-- What weighted entries give through the columns `col`. -/
def comboVal (col : α → Fin r → K) (x : List (α × K)) : Fin r → K :=
  (x.map fun p => p.2 • col p.1).sum

/-- Weighted entries, scaled. -/
def scaleL (a : K) (x : List (α × K)) : List (α × K) := x.map fun p => (p.1, a * p.2)

/-- **A vector, computed once**: its coordinates in an array (`mat v = v`), so that a chain of
reductions does not recompute its predecessors. -/
def mat (v : Fin r → K) : Fin r → K :=
  let a := Array.ofFn v
  fun i => a.getD i 0

@[simp] theorem mat_eq (v : Fin r → K) : mat v = v := by
  funext i
  simp [mat, Array.getD, Array.size_ofFn]

/-- **One reduction step**: clear the vector's coordinate at the row's pivot, recording the row's
entries. -/
def step (vx : (Fin r → K) × List (α × K)) (row : Row K α r) : (Fin r → K) × List (α × K) :=
  let c := vx.1 row.piv
  (mat (vx.1 - c • row.vec), vx.2 ++ scaleL (-c) row.comb)

theorem step_eq (vx : (Fin r → K) × List (α × K)) (row : Row K α r) :
    step vx row = (vx.1 - vx.1 row.piv • row.vec, vx.2 ++ scaleL (-vx.1 row.piv) row.comb) := by
  simp [step]

/-- **Reduction** by the rows, in order. -/
def reduce (B : List (Row K α r)) (vx : (Fin r → K) × List (α × K)) :
    (Fin r → K) × List (α × K) :=
  B.foldl step vx

/-- The first nonzero coordinate. -/
def firstNZ (v : Fin r → K) : Option (Fin r) := (List.finRange r).find? fun i => v i ≠ 0

/-- **Insert an entry**: its column reduced; unless zero, a new row at its first nonzero coordinate,
normalized there. -/
def insertE (col : α → Fin r → K) (B : List (Row K α r)) (e : α) : List (Row K α r) :=
  let vx := reduce B (col e, [(e, 1)])
  match firstNZ vx.1 with
  | none => B
  | some p => B ++ [⟨p, mat ((vx.1 p)⁻¹ • vx.1), scaleL (vx.1 p)⁻¹ vx.2⟩]

/-- **The scan**: `n` entries from the `k`-th, stopping once every coordinate is a pivot. -/
def scan (col : α → Fin r → K) (entryAt : ℕ → α) : ℕ → ℕ → List (Row K α r) → List (Row K α r)
  | 0, _, B => B
  | n + 1, k, B =>
    if B.length = r then B else scan col entryAt n (k + 1) (insertE col B (entryAt k))

/-- **The solution** for the target `t`: `t` reduced by the rows of the scan of the first `N`
entries; the entries recorded, negated. -/
def solveElim (col : α → Fin r → K) (entryAt : ℕ → α) (N : ℕ) (t : Fin r → K) : List (α × K) :=
  scaleL (-1) (reduce (scan col entryAt N 0 []) (t, [])).2

/-! ### Correctness -/

variable (col : α → Fin r → K)

theorem comboVal_nil : comboVal col ([] : List (α × K)) = 0 := by simp [comboVal]

theorem comboVal_append (x y : List (α × K)) :
    comboVal col (x ++ y) = comboVal col x + comboVal col y := by
  simp [comboVal]

theorem comboVal_scaleL (a : K) (x : List (α × K)) :
    comboVal col (scaleL a x) = a • comboVal col x := by
  induction x with
  | nil => simp [comboVal, scaleL]
  | cons p x ih =>
    simp only [comboVal, scaleL, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, smul_add, mul_smul]

/-- **Echelon form**: each row's vector is its entries' combination and is one at its pivot, and
the later rows are zero there. -/
def WF : List (Row K α r) → Prop
  | [] => True
  | row :: B => comboVal col row.comb = row.vec ∧ row.vec row.piv = 1 ∧
      (∀ row' ∈ B, row'.vec row.piv = 0) ∧ WF B

/-- The rows' vectors. -/
def vecs (B : List (Row K α r)) : Set (Fin r → K) := {w | ∃ row ∈ B, row.vec = w}

variable {col}

theorem WF.one : ∀ {B : List (Row K α r)}, WF col B → ∀ row ∈ B, row.vec row.piv = 1
  | [], _, _, h => by simp at h
  | _ :: _, h, _, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.2.1
    · exact WF.one h.2.2.2 _ hm

theorem WF.append : ∀ {B : List (Row K α r)} (n : Row K α r), WF col B →
    (∀ row ∈ B, n.vec row.piv = 0) → comboVal col n.comb = n.vec → n.vec n.piv = 1 →
    WF col (B ++ [n])
  | [], n, _, _, h1, h2 => ⟨h1, h2, by simp, trivial⟩
  | row :: B, n, h, hz, h1, h2 => by
    refine ⟨h.1, h.2.1, fun row' hm => ?_, WF.append n h.2.2.2
      (fun row' hm => hz row' (List.mem_cons_of_mem _ hm)) h1 h2⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact h.2.2.1 row' hm
    · rw [List.mem_singleton.mp hm]
      exact hz row List.mem_cons_self

theorem reduce_cons (row : Row K α r) (B : List (Row K α r)) (vx : (Fin r → K) × List (α × K)) :
    reduce (row :: B) vx = reduce B (step vx row) := rfl

/-- **Reduction keeps the vector less its recorded combination.** -/
theorem reduce_inv : ∀ {B : List (Row K α r)}, WF col B → ∀ vx : (Fin r → K) × List (α × K),
    (reduce B vx).1 - comboVal col (reduce B vx).2 = vx.1 - comboVal col vx.2
  | [], _, _ => rfl
  | row :: B, h, vx => by
    rw [reduce_cons, reduce_inv h.2.2.2]
    simp only [step_eq, comboVal_append, comboVal_scaleL, h.1]
    rw [neg_smul]
    abel

/-- Reduction keeps a coordinate where every row is zero. -/
theorem reduce_zero_of : ∀ {B : List (Row K α r)} {q : Fin r}, (∀ row ∈ B, row.vec q = 0) →
    ∀ vx : (Fin r → K) × List (α × K), vx.1 q = 0 → (reduce B vx).1 q = 0
  | [], _, _, _, h => h
  | row :: B, q, hB, vx, h => by
    rw [reduce_cons]
    refine reduce_zero_of (fun row' hm => hB row' (List.mem_cons_of_mem _ hm)) _ ?_
    simp [step_eq, h, hB row List.mem_cons_self]

/-- **The reduced vector is zero at every pivot.** -/
theorem reduce_piv : ∀ {B : List (Row K α r)}, WF col B → ∀ vx : (Fin r → K) × List (α × K),
    ∀ row ∈ B, (reduce B vx).1 row.piv = 0
  | [], _, _, _, h => by simp at h
  | row₀ :: B, h, vx, row, hm => by
    rw [reduce_cons]
    rcases List.mem_cons.mp hm with rfl | hm
    · refine reduce_zero_of h.2.2.1 _ ?_
      simp [step_eq, h.2.1]
    · exact reduce_piv h.2.2.2 _ row hm

/-- The reduction subtracts a combination of the rows. -/
theorem reduce_sub_mem : ∀ (B : List (Row K α r)) (vx : (Fin r → K) × List (α × K)),
    (reduce B vx).1 - vx.1 ∈ Submodule.span K (vecs B)
  | [], vx => by simp [reduce]
  | row :: B, vx => by
    rw [reduce_cons]
    have h1 := reduce_sub_mem B (step vx row)
    have hmono : Submodule.span K (vecs B) ≤ Submodule.span K (vecs (row :: B)) :=
      Submodule.span_mono fun w ⟨row', hm, hw⟩ => ⟨row', List.mem_cons_of_mem _ hm, hw⟩
    have h2 : (step vx row).1 - vx.1 ∈ Submodule.span K (vecs (row :: B)) := by
      simp only [step_eq, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨row, List.mem_cons_self, rfl⟩))
    have := Submodule.add_mem _ (hmono h1) h2
    rwa [sub_add_sub_cancel] at this

/-- **A combination of the rows that is zero at every pivot is zero.** -/
theorem eq_zero_of_mem_span : ∀ {B : List (Row K α r)}, WF col B → ∀ {w : Fin r → K},
    w ∈ Submodule.span K (vecs B) → (∀ row ∈ B, w row.piv = 0) → w = 0
  | [], _, w, hw, _ => by
    have : vecs ([] : List (Row K α r)) = ∅ := by ext; simp [vecs]
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hw
    exact hw
  | row :: B, h, w, hw, hz => by
    have hv : vecs (row :: B) = insert row.vec (vecs B) := by
      ext u
      simp [vecs, eq_comm]
    rw [hv, Submodule.mem_span_insert] at hw
    obtain ⟨a, z, hzm, rfl⟩ := hw
    have hzp : z row.piv = 0 := by
      have hle : Submodule.span K (vecs B) ≤ LinearMap.ker (LinearMap.proj (R := K)
          (φ := fun _ : Fin r => K) row.piv) :=
        Submodule.span_le.mpr fun u ⟨row', hm, hu⟩ => by
          rw [← hu]
          exact h.2.2.1 row' hm
      exact hle hzm
    have ha : a = 0 := by
      have := hz row List.mem_cons_self
      simpa [h.2.1, hzp] using this
    subst ha
    rw [zero_smul, zero_add] at hz ⊢
    exact eq_zero_of_mem_span h.2.2.2 hzm fun row' hm => hz row' (List.mem_cons_of_mem _ hm)

theorem piv_nodup : ∀ {B : List (Row K α r)}, WF col B → (B.map Row.piv).Nodup
  | [], _ => List.nodup_nil
  | row :: B, h => by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, piv_nodup h.2.2.2⟩
    obtain ⟨row', hm', he⟩ := List.mem_map.mp hm
    have h1 := WF.one h.2.2.2 row' hm'
    rw [he, h.2.2.1 row' hm'] at h1
    exact zero_ne_one h1

/-- **The residual is zero** when the rows span the target or every coordinate is a pivot. -/
theorem reduce_eq_zero {B : List (Row K α r)} (h : WF col B) {t : Fin r → K}
    (ht : B.length = r ∨ t ∈ Submodule.span K (vecs B)) (x : List (α × K)) :
    (reduce B (t, x)).1 = 0 := by
  rcases ht with hl | ht
  · funext q
    have hall : ∀ q : Fin r, ∃ row ∈ B, row.piv = q := by
      intro q
      have hc : ((B.map Row.piv).toFinset).card = r := by
        rw [List.toFinset_card_of_nodup (piv_nodup h), List.length_map, hl]
      have hu := Finset.eq_univ_of_card _ (hc.trans (Fintype.card_fin r).symm)
      have : q ∈ (B.map Row.piv).toFinset := hu ▸ Finset.mem_univ q
      simpa using this
    obtain ⟨row, hm, rfl⟩ := hall q
    exact reduce_piv h _ row hm
  · refine eq_zero_of_mem_span h ?_ (reduce_piv h _)
    have := Submodule.add_mem _ (reduce_sub_mem B (t, x)) ht
    rwa [sub_add_cancel] at this

/-- **Insertion keeps the echelon form.** -/
theorem WF.insertE {B : List (Row K α r)} (h : WF col B) (e : α) : WF col (insertE col B e) := by
  have hinv : comboVal col (reduce B (col e, [(e, 1)])).2 = (reduce B (col e, [(e, 1)])).1 := by
    have := reduce_inv h (col e, [(e, 1)])
    simp only [comboVal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      one_smul, sub_self] at this
    exact (sub_eq_zero.mp this).symm
  rcases hp : firstNZ (reduce B (col e, [(e, 1)])).1 with _ | p
  · simp only [Builder.insertE, hp]
    exact h
  · simp only [Builder.insertE, hp]
    have hne : (reduce B (col e, [(e, 1)])).1 p ≠ 0 := by
      have := List.find?_some hp
      simpa using this
    refine WF.append _ h (fun row hm => ?_) ?_ ?_
    · simp [reduce_piv h _ row hm]
    · simp only [comboVal_scaleL, hinv, mat_eq]
    · simp [inv_mul_cancel₀ hne]

/-- **After insertion, the entry's column is a combination of the rows**, and so is every
combination of the earlier rows. -/
theorem insertE_span (B : List (Row K α r)) (e : α) :
    Submodule.span K (vecs B) ≤ Submodule.span K (vecs (insertE col B e)) ∧
      col e ∈ Submodule.span K (vecs (insertE col B e)) := by
  have hsub : col e - (reduce B (col e, [(e, 1)])).1 ∈ Submodule.span K (vecs B) := by
    have := Submodule.neg_mem _ (reduce_sub_mem B (col e, [(e, 1)]))
    rwa [neg_sub] at this
  rcases hp : firstNZ (reduce B (col e, [(e, 1)])).1 with _ | p
  · simp only [Builder.insertE, hp]
    have h0 : (reduce B (col e, [(e, 1)])).1 = 0 := by
      funext i
      have := List.find?_eq_none.mp hp i (List.mem_finRange i)
      simpa using this
    refine ⟨le_rfl, ?_⟩
    simpa [h0] using hsub
  · simp only [Builder.insertE, hp]
    set v := (reduce B (col e, [(e, 1)])).1
    have hne : v p ≠ 0 := by
      have := List.find?_some hp
      simpa using this
    have hmono : Submodule.span K (vecs B) ≤ Submodule.span K
        (vecs (B ++ [⟨p, mat ((v p)⁻¹ • v), scaleL (v p)⁻¹ (reduce B (col e, [(e, 1)])).2⟩])) :=
      Submodule.span_mono fun w ⟨row, hm, hw⟩ => ⟨row, List.mem_append_left _ hm, hw⟩
    refine ⟨hmono, ?_⟩
    have hv : v ∈ Submodule.span K
        (vecs (B ++ [⟨p, mat ((v p)⁻¹ • v), scaleL (v p)⁻¹ (reduce B (col e, [(e, 1)])).2⟩])) := by
      have hrow := Submodule.smul_mem _ (v p) (Submodule.subset_span (R := K)
        (s := vecs (B ++ [⟨p, mat ((v p)⁻¹ • v), scaleL (v p)⁻¹ (reduce B (col e, [(e, 1)])).2⟩]))
        ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩)
      have hvv : v p • mat ((v p)⁻¹ • v) = v := by
        rw [mat_eq, smul_smul, mul_inv_cancel₀ hne, one_smul]
      rwa [hvv] at hrow
    have := Submodule.add_mem _ (hmono hsub) hv
    rwa [sub_add_cancel] at this

/-- **The scan's invariant**: echelon rows, and every scanned column a combination of them unless
every coordinate is a pivot. -/
theorem scan_spec (entryAt : ℕ → α) : ∀ (n k : ℕ) (B : List (Row K α r)), WF col B →
    (B.length = r ∨ ∀ i < k, col (entryAt i) ∈ Submodule.span K (vecs B)) →
    WF col (scan col entryAt n k B) ∧ ((scan col entryAt n k B).length = r ∨
      ∀ i < k + n, col (entryAt i) ∈ Submodule.span K (vecs (scan col entryAt n k B)))
  | 0, k, B, h, hs => ⟨h, hs⟩
  | n + 1, k, B, h, hs => by
    unfold scan
    split
    · rename_i hl
      exact ⟨h, Or.inl hl⟩
    · rename_i hl
      have hall := hs.resolve_left hl
      obtain ⟨hmono, he⟩ := insertE_span (col := col) B (entryAt k)
      have := scan_spec entryAt n (k + 1) (insertE col B (entryAt k)) (h.insertE _)
        (Or.inr fun i hi => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact hmono (hall i hi)
          · exact he)
      rwa [show k + 1 + n = k + (n + 1) by omega] at this

/-- **The solution meets the target** whenever the target is a combination of the columns of
entries the scan reaches. -/
theorem solveElim_spec (entryAt : ℕ → α) (N : ℕ) (t : Fin r → K) (U : Set α)
    (hU : ∀ e ∈ U, ∃ i < N, entryAt i = e) (ht : t ∈ Submodule.span K (col '' U)) :
    comboVal col (solveElim col entryAt N t) = t := by
  obtain ⟨hWF, hs⟩ := scan_spec (col := col) entryAt N 0 [] trivial
    (Or.inr fun i hi => absurd hi (Nat.not_lt_zero i))
  have hres : (reduce (scan col entryAt N 0 []) (t, [])).1 = 0 := by
    refine reduce_eq_zero hWF (hs.imp_right fun hall => ?_) []
    refine (Submodule.span_le.mpr ?_) ht
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨i, hi, rfl⟩ := hU e he
    exact hall i (by omega)
  have hinv := reduce_inv hWF (t, [])
  rw [hres, comboVal_nil, zero_sub, sub_zero] at hinv
  rw [solveElim, comboVal_scaleL, neg_one_smul]
  exact hinv

end Elim

/-! ## Tables meeting claims -/

section Claims

variable {K E ι Y : Type} [Field K] [DecidableEq K] [Field E] [Algebra K E]
  [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]

/-- **The columns**: claim `j`'s weight at the entry, its coordinate `k`, at `(j, k)`. -/
def colOf (co : E → Fin 3 → K) {m : ℕ} (Wc : Fin m → ι → Y → E) (e : ι × Y) :
    Fin (m * 3) → K :=
  let ws := Array.ofFn fun j : Fin m => co (Wc j e.1 e.2)
  fun i => (ws.getD (finProdFinEquiv.symm i).1 0) (finProdFinEquiv.symm i).2

theorem colOf_eq (co : E → Fin 3 → K) {m : ℕ} (Wc : Fin m → ι → Y → E) (e : ι × Y) :
    colOf co Wc e = fun i => co (Wc (finProdFinEquiv.symm i).1 e.1 e.2) (finProdFinEquiv.symm i).2 := by
  funext i
  have hi : (i : ℕ) / 3 < m := (Nat.div_lt_iff_lt_mul (by norm_num)).mpr i.isLt
  simp only [colOf]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat, hi, ↓reduceDIte, Option.getD_some]
  rfl

/-- **The target**: the claimed values' coordinates. -/
def tgtOf (co : E → Fin 3 → K) {m : ℕ} (val : Fin m → E) : Fin (m * 3) → K :=
  fun i => co (val (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

/-- **The table built for the claimed values `val`**, by the scan of `entryAt k`, `k < N`. -/
def build (co : E → Fin 3 → K) {m : ℕ} (Wc : Fin m → ι → Y → E) (entryAt : ℕ → ι × Y) (N : ℕ)
    (val : Fin m → E) : ι → Y → K :=
  sparse (solveElim (colOf co Wc) entryAt N (tgtOf co val))

theorem co_sparseVal (co : E ≃ₗ[K] (Fin 3 → K)) {m : ℕ} (Wc : Fin m → ι → Y → E) (j : Fin m)
    (k : Fin 3) (x : List ((ι × Y) × K)) :
    co (sparseVal (Wc j) x) k = comboVal (colOf co Wc) x (finProdFinEquiv (j, k)) := by
  induction x with
  | nil => simp [sparseVal, comboVal]
  | cons p x ih =>
    simp only [sparseVal, comboVal, List.map_cons, List.sum_cons] at ih ⊢
    rw [map_add, Pi.add_apply, ih, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    simp [colOf_eq]

/-- **The built table has the claimed values whenever some table has them**, for claims that
weigh nothing of the randomness and a scan that reaches every entry. -/
theorem claims_build (co : E ≃ₗ[K] (Fin 3 → K)) (L : GadgetLayout ι Y) {m : ℕ}
    (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc) (entryAt : ℕ → ι × Y) (N : ℕ)
    (hcov : ∀ e, ∃ i < N, entryAt i = e) (val : Fin m → E) {d : ι → Y → K}
    (hd : HiddenLayout.claimsMap Wc (L.stackD d) = val) :
    HiddenLayout.claimsMap Wc (L.stackD (build co Wc entryAt N val)) = val := by
  have hspan : tgtOf co val ∈ Submodule.span K (colOf co Wc '' Set.univ) := by
    have he : tgtOf co val = ∑ e : ι × Y, L.stackD d e.1 e.2 • colOf co Wc e := by
      funext i
      rw [Finset.sum_apply, Fintype.sum_prod_type, tgtOf, ← hd]
      show co (∑ l, ∑ y, Wc _ l y * algebraMap K E (L.stackD d l y)) _ = _
      simp only [map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colOf_eq]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun y _ => ?_
      rw [mul_comm, ← Algebra.smul_def, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [he]
    exact Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨e, Set.mem_univ _, rfl⟩)
  have hsol := solveElim_spec entryAt N (tgtOf co val) Set.univ (fun e _ => hcov e) hspan
  funext j
  rw [build, claimsMap_stackD_sparse L Wc (weight_randPos L hW)]
  refine co.injective (funext fun k => ?_)
  rw [co_sparseVal, hsol]
  simp [tgtOf]

end Claims

/-! ## The verifier's points and values, compiled -/

section Points

open Polynomial

variable {E : Type} [Field E] [DecidableEq E] [CharP E 2]

/-- `claimPoint`, compiled. -/
def claimPointC (first m : ℕ) (t : E) : Fin m → E :=
  fun k => sq^[(k : ℕ) + first] t / (1 + sq^[(k : ℕ) + first] t)

theorem claimPointC_eq (first m : ℕ) (t : E) : claimPointC first m t = claimPoint first m t := rfl

/-- `claimScale`, compiled. -/
def claimScaleC (first m : ℕ) (t : E) : E := ∏ k : Fin m, (1 + sq^[(k : ℕ) + first] t)

theorem claimScaleC_eq (first m : ℕ) (t : E) : claimScaleC first m t = claimScale first m t := rfl

theorem ofFn_snoc' {α : Type} {n : ℕ} (f : Fin n → α) (a : α) :
    List.ofFn (Fin.snoc f a : Fin (n + 1) → α) = List.ofFn f ++ [a] := by
  rw [List.ofFn_succ', List.concat_eq_append, Fin.snoc_last]
  congr 2
  funext i
  exact Fin.snoc_castSucc (α := fun _ => α) a f i

/-- **The witness claim's point** (`pointW`), compiled (as a list: `ρ, ρ², u_2, …, u_24`). -/
def pointWc (c : DChal E) : List E :=
  c.1.2 :: c.1.2 ^ 2 :: List.ofFn (claimPointC 2 (22 + 1) c.1.1.2)

theorem pointWc_eq (c : DChal E) : pointWc c = pointW c := by
  unfold pointWc pointW
  rw [List.ofFn_succ, List.ofFn_succ]
  rfl

/-- **The witness claim's value** (`valsW`), compiled. -/
def valWc (c : DChal E) (v : Vals E) : E :=
  (∑ j, Params.opening c.1.2 j * v.1 j) / claimScaleC 2 (22 + 1) c.1.1.2

theorem valsW_eq (c : DChal E) (v : Vals E) : valsW c v = fun _ => valWc c v := rfl

/-- The digit basis at a point (`digit`): `1, x, x² + x, x³ + x²`. -/
def digitAt (j : Fin 4) (x : E) : E := ![1, x, x ^ 2 + x, (x ^ 2 + x) * x] j

theorem eval_digit (j : Fin 4) (x : E) : (digit j : E[X]).eval x = digitAt j x := by
  fin_cases j <;> simp [digit, digitAt]

/-- `Params.cellAt`, compiled. -/
def cellAtC (θ : E) (a : Fin 4 → E) (t : E) (c : Fin 4) : E :=
  ∑ j, digitAt j (t + shift θ c) * a j

theorem cellAtC_eq (P : Params E) (a : Fin 4 → E) (t : E) (c : Fin 4) :
    cellAtC P.θ a t c = P.cellAt a t c := by
  simp only [cellAtC, Params.cellAt, eval_digit]

/-- `Params.claimDen`, compiled (the polynomials evaluated by `Polynomial.eval`). -/
def claimDenC (P : Params E) (α β t : E) (a : Fin 4 → E) (s : E) : E :=
  (α + cellAtC P.θ a t 0 + β * t) * (α + cellAtC P.θ a t 0 + β * s) + P.vCells.eval t

theorem claimDenC_eq (P : Params E) (α β t : E) (a : Fin 4 → E) (s : E) :
    claimDenC P α β t a s = P.claimDen α β t a s := by
  simp only [claimDenC, Params.claimDen, cellAtC_eq]

/-- `Params.claimValue`, compiled. -/
def claimValueC (P : Params E) (α β γ t ρ : E) (a : Fin 4 → E) (s : E) : E :=
  ((1 + ρ) * ((α + cellAtC P.θ a t 0 + β * t) + (α + cellAtC P.θ a t 0 + β * s)
        + (P.pub γ).eval t * cellAtC P.θ a t 0
          * ((α + cellAtC P.θ a t 0 + β * t) * (α + cellAtC P.θ a t 0 + β * s))) * P.vRows.eval t
      + ρ * ((α + cellAtC P.θ a t 0 + β * t) * (α + cellAtC P.θ a t 0 + β * s))
        * gate (cellAtC P.θ a t 0) (cellAtC P.θ a t 1) (cellAtC P.θ a t 2) (cellAtC P.θ a t 3))
    / (claimDenC P α β t a s * P.vRows.eval t)

theorem claimValueC_eq (P : Params E) (α β γ t ρ : E) (a : Fin 4 → E) (s : E) :
    claimValueC P α β γ t ρ a s = P.claimValue α β γ t ρ a s := by
  simp only [claimValueC, Params.claimValue, cellAtC_eq, claimDenC_eq]

/-- **The quotient claim's point** (`pointQ`), compiled. -/
def pointQc (P₀ : Params E) (Y : E) (c : DChal E) (v : Vals E) : List E :=
  List.ofFn (claimPointC 0 (22 + 2 + 1 + 1) c.1.1.2) ++
    [P₀.vCells.eval c.1.1.2 / claimDenC P₀ c.1.1.1.1 c.1.1.1.2.1 c.1.1.2 v.1 v.2, c.1.2,
      Y / (1 + Y), Y ^ 2 / (1 + Y ^ 2)]

theorem pointQc_eq (P₀ : Params E) (Y : E) (c : DChal E) (v : Vals E) :
    pointQc P₀ Y c v = pointQ P₀ Y c v := by
  unfold pointQc pointQ
  rw [ofFn_snoc', ofFn_snoc', ofFn_snoc', ofFn_snoc', claimDenC_eq, claimPointC_eq]
  simp

/-- The sum claim's point (`pointS`), compiled: `1` on the cells' `24` digits, four zeros, then
`Y/(1+Y)`, `Y²/(1+Y²)`. -/
def pointSc (Y : E) : List E :=
  List.replicate (22 + 2) 1 ++ [0, 0, 0, 0, Y / (1 + Y), Y ^ 2 / (1 + Y ^ 2)]

theorem pointSc_eq (Y : E) : pointSc Y = pointS Y := by
  unfold pointSc pointS sumPoint
  rw [ofFn_snoc', ofFn_snoc', ofFn_snoc', ofFn_snoc', ofFn_snoc', ofFn_snoc', List.ofFn_const]
  simp

/-- **The quotient table's claimed values** (`valsQ`), compiled. -/
def valsQc (P₀ : Params E) (stmt : Fin P₀.words → E) (Y : E) (c : DChal E) (v : Vals E) :
    Fin 2 → E :=
  ![claimValueC P₀ c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2 v.1 v.2 /
      ((1 + Y) * (1 + Y ^ 2)) / claimScaleC 0 (22 + 2 + 1 + 1) c.1.1.2,
    P₀.target stmt c.1.1.1.2.2 / ((1 + Y) * (1 + Y ^ 2))]

theorem valsQc_eq (P₀ : Params E) (stmt : Fin P₀.words → E) (Y : E) (c : DChal E) (v : Vals E) :
    valsQc P₀ stmt Y c v = valsQ P₀ stmt Y c v := by
  simp only [valsQc, valsQ, claimValueC_eq, claimScaleC_eq]

end Points

end Builder

open Builder

/-! ## The simulator's tables -/

section Tables

variable {K E : Type} [Field K] [DecidableEq K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2]

/-- **Every entry of a layout's stack**, lane by lane: `k ↦ (k / 2^ℓ mod L, k mod 2^ℓ)`. -/
def enumL (L : QuotientSecurity.Hiding.Deployed.Layout) (h : L.OK) (k : ℕ) :
    Fin L.lanes.length × Fin (2 ^ L.logLane) :=
  (⟨k / 2 ^ L.logLane % L.lanes.length, Nat.mod_lt _ (by have := h.lanes_ge; omega)⟩,
    ⟨k % 2 ^ L.logLane, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)

/-- **The scan's order**: the candidates, then every entry. -/
def entryAt {α : Type} (cands : List α) (enum : ℕ → α) (k : ℕ) : α :=
  match cands[k]? with
  | some e => e
  | none => enum (k - cands.length)

/-- The scan reaches every entry. -/
theorem entryAt_cover (L : QuotientSecurity.Hiding.Deployed.Layout) (h : L.OK)
    (cands : List (Fin L.lanes.length × Fin (2 ^ L.logLane))) {N : ℕ}
    (hN : cands.length + L.lanes.length * 2 ^ L.logLane ≤ N)
    (e : Fin L.lanes.length × Fin (2 ^ L.logLane)) :
    ∃ i < N, entryAt cands (enumL L h) i = e := by
  have h1 := e.1.isLt
  have h2 := e.2.isLt
  have hp : 0 < 2 ^ L.logLane := Nat.two_pow_pos _
  refine ⟨cands.length + ((e.1 : ℕ) * 2 ^ L.logLane + e.2), ?_, ?_⟩
  · have : (e.1 : ℕ) * 2 ^ L.logLane + e.2 < L.lanes.length * 2 ^ L.logLane :=
      calc (e.1 : ℕ) * 2 ^ L.logLane + e.2 < (e.1 : ℕ) * 2 ^ L.logLane + 2 ^ L.logLane := by omega
        _ = ((e.1 : ℕ) + 1) * 2 ^ L.logLane := by ring
        _ ≤ L.lanes.length * 2 ^ L.logLane := Nat.mul_le_mul_right _ h1
    omega
  · have hn : cands[cands.length + ((e.1 : ℕ) * 2 ^ L.logLane + e.2)]? = none :=
      List.getElem?_eq_none (by omega)
    simp only [entryAt, hn, Nat.add_sub_cancel_left, enumL]
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show ((e.1 : ℕ) * 2 ^ L.logLane + e.2) / 2 ^ L.logLane % L.lanes.length = e.1
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h2, zero_add,
        Nat.mod_eq_of_lt h1]
    · show ((e.1 : ℕ) * 2 ^ L.logLane + e.2) % 2 ^ L.logLane = e.2
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]

/-- Entry `y` of the overflow lane `32` of the witness stack. -/
def eW (y : ℕ) (hy : y < 2 ^ 19 := by norm_num) : ιW × YW :=
  (⟨32, by rw [lanes_W]; norm_num⟩, ⟨y, by rw [logLane_W]; exact hy⟩)

/-- Lane `l` and entry `y` of the quotient stack. -/
def eQ (l y : ℕ) (hl : l < 63 := by norm_num) (hy : y < 2 ^ 22 := by norm_num) : ιQ × YQ :=
  (⟨l, by rw [lanes_Q]; exact hl⟩, ⟨y, by rw [logLane_Q]; exact hy⟩)

/-- **The witness table's candidates**: entries `256 .. 260, 264` of the overflow lane. -/
def candsW : List (ιW × YW) := [eW 256, eW 257, eW 258, eW 259, eW 260, eW 264]

/-- **The quotient table's candidates**: entry `2^22 - 1` of the lanes `3, 19, 43` (blocks `3, 67,
131`), the first entries of the overflow lane's pieces `1, 17, 33, 5, 21, 37`. -/
def candsQ : List (ιQ × YQ) :=
  [eQ 3 (2 ^ 22 - 1), eQ 19 (2 ^ 22 - 1), eQ 43 (2 ^ 22 - 1), eQ 32 256, eQ 32 (256 * 17),
    eQ 32 (256 * 33), eQ 32 (256 * 5), eQ 32 (256 * 21), eQ 32 (256 * 37)]

/-- The witness claim's weight (`openW`'s), compiled. -/
def wW (c : DChal E) : Fin 1 → ιW → YW → E :=
  let p := pointWc c
  Lw.claimW fun _ : Fin 1 => p

/-- The quotient table's claims' weights (`openQ`'s), compiled. -/
def wQ (P₀ : Params E) (Y : E) (c : DChal E) (v : Vals E) : Fin 2 → ιQ → YQ → E :=
  let p := pointQc P₀ Y c v
  let s := pointSc Y
  Lq.claimW ![p, s]

/-- **The simulator's witness table**: the elimination over the candidates, then every entry, for
the verifier's claimed value. -/
def simTW (rep : Rep K E) (_Y : E) (c : DChal E) (v : Vals E) : ιW → YW → K :=
  build rep.coords (wW c) (entryAt candsW (enumL Lw okW)) (candsW.length + 40 * 2 ^ 19)
    (fun _ => valWc c v)

/-- **The simulator's quotient table**: likewise, for the two claimed values. -/
def simTQ (rep : Rep K E) (P₀ : Params E) (stmt : Fin P₀.words → E) (Y : E) (c : DChal E)
    (v : Vals E) : ιQ → YQ → K :=
  build rep.coords (wQ P₀ Y c v) (entryAt candsQ (enumL Lq okQ)) (candsQ.length + 63 * 2 ^ 22)
    (valsQc P₀ stmt Y c v)

/-- **The simulator's witness table has the verifier's claimed value whenever some table has
it.** -/
theorem claims_simTW {rep : Rep K E} {Y : E} {c : DChal E} {v : Vals E} {d : ιW → YW → K}
    (hd : (openW rep Y).claims (c, v) d = valsW c v) :
    (openW rep Y).claims (c, v) (simTW rep Y c v) = valsW c v :=
  claims_build rep.coords (Lw.toGadget okW) (wW c)
    (QuotientSecurity.Hiding.Deployed.Layout.weightsFit two_eq_zero_E okW _) _ _
    (entryAt_cover Lw okW candsW (le_of_eq (by
      have : Lw.lanes.length * 2 ^ Lw.logLane = 40 * 2 ^ 19 := by rw [lanes_W, logLane_W]
      rw [this]))) _ hd

/-- **The simulator's quotient table has the verifier's claimed values whenever some table has
them.** -/
theorem claims_simTQ {rep : Rep K E} {P₀ : Params E} {stmt : Fin P₀.words → E} {Y : E}
    {c : DChal E} {v : Vals E} {d : ιQ → YQ → K}
    (hd : (openQ rep P₀ Y).claims (c, v) d = valsQ P₀ stmt Y c v) :
    (openQ rep P₀ Y).claims (c, v) (simTQ rep P₀ stmt Y c v) = valsQ P₀ stmt Y c v := by
  have hW : (openQ rep P₀ Y).Wc (c, v) = wQ P₀ Y c v := by
    show Lq.claimW ![pointQ P₀ Y c v, pointS Y] = Lq.claimW ![pointQc P₀ Y c v, pointSc Y]
    rw [pointQc_eq, pointSc_eq]
  have hd' : HiddenLayout.claimsMap (wQ P₀ Y c v) ((Lq.toGadget okQ).stackD d) =
      valsQc P₀ stmt Y c v := by
    rw [← hW, valsQc_eq]
    exact hd
  rw [← valsQc_eq]
  show HiddenLayout.claimsMap ((openQ rep P₀ Y).Wc (c, v))
    ((Lq.toGadget okQ).stackD (simTQ rep P₀ stmt Y c v)) = valsQc P₀ stmt Y c v
  rw [hW]
  exact claims_build rep.coords (Lq.toGadget okQ) (wQ P₀ Y c v)
    (QuotientSecurity.Hiding.Deployed.Layout.weightsFit two_eq_zero_E okQ _) _ _
    (entryAt_cover Lq okQ candsQ (le_of_eq (by
      have : Lq.lanes.length * 2 ^ Lq.logLane = 63 * 2 ^ 22 := by rw [lanes_Q, logLane_Q]
      rw [this]))) _ hd'

end Tables

end QuotientZk.Instance

/-! ## Axioms -/

/--
info: 'QuotientZk.Instance.Builder.solveElim_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.Instance.Builder.solveElim_spec

/--
info: 'QuotientZk.Instance.claims_simTW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.Instance.claims_simTW

/--
info: 'QuotientZk.Instance.claims_simTQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.Instance.claims_simTQ
