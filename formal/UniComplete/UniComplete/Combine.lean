-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Claims
import UniComplete.Prover

/-!
# Combining true relations with the powers of `ρ` gives a true weighted claim (milestone 4)

`combine rels c ρ` (`UniStatement.combine`, `Relations::combine`) merges the relations on the commitment `c` into
one weighted claim: relation `i`'s terms at coefficient `ρ^i ·`, merged by (column, point index, twist), each point
once; then each point index is **renumbered** to the longest point having that point as a prefix. Its meaning on a
stack (`Combined.Holds`) is the pairing of its weight (`denseWeight`) with the stack.

1. **`denseWeight` is linear** (`denseWeight_getD_eq_sum`, `dotK_denseWeight`): a claim's weight is, word by word,
   the sum over its terms of each term's one-term weight (`denseWeight (termClaim (termAt claim e))`, the term at
   the claim's `points[p]`); a one-term weight is linear in its coefficient (`denseWeight_termClaim_getD_mul`,
   `termEval_mul`, `termEval_add`); `dotK` is the sum of its products (`dotK_eq_sum`), so the pairing of a claim
   is the sum of its terms' values.
2. **`combine_holds`**: if every relation of `rels` on `c` holds on `c`'s stack, and every term of those
   relations **reads its own point** (`ReadsOwnPoint`), the combined claim holds. `combine_holds_of_relations`
   states it with `Relation.Holds` for relations whose terms are all on `c`.
3. **The verifier's relations** (`atTOf`): `AtTWellFormed` (the condition of 2 for every commitment, and every
   relation on one commitment), and `atT_combined_hold`: under it, the combined claims the prover hands the batch
   hold whenever the relations do.

## Decisions and findings

* **What "reads its own point" must be.** `denseWeight` reads a term at its claim point: an ordinary column
  (every column but `q_flock`'s slots) reads the point's first `vars` coordinates, zero-padded, on each block of
  `vars` variables; so renumbering it to a longer point having its own as a prefix reads the same coordinates
  **iff its point has at least `vars` coordinates** for every block of its column (a shorter point is read
  zero-padded at its own length, and at the longer point's coordinates after the renumbering). This is the
  condition for ordinary columns: `∀ b ∈ layout.limbs column, b.2.1 ≤ point.length` (it is weaker than the
  point having exactly the column's number of variables, which the verifier's points have).
* **Finding: `q_flock`'s slots read their point whole.** `denseWeight`'s slot `j` writes `eqKernel point` at the
  words `j + 256 u` for all of `point`'s `2^|point|` indices, as the verifier's `weightAt` (`row = bits(j) ++
  point`, of `rowLen = 8 + |point|` coordinates); neither truncates the point to `q_flock`'s variables minus 8.
  So a slot term renumbered to a strictly longer point (its point `y(t)`, of `h_B` coordinates, a prefix of
  another point on `C1`) reads the longer point's extra coordinates, and the combined claim's weight is no
  longer the sum of the relations' weights. The Rust prover's `dense_weight` truncates the slot point to
  `vars − 8` (`claim.points[p][..len]`) but the Rust verifier's `weight_at` (`row_from`, over the whole point)
  does not, so there the prover and the verifier would disagree. For slot terms, the condition is therefore
  **maximality**: no point among the commitment's relations' points strictly extends the slot's point
  (`∀ q ∈ others, point <+: q → q = point`). For the verifier's relations this is a condition on the
  challenges, not a fact: the slot point `y(t)` must not be a prefix of `w(t).take r` for a table (or the
  memory, or the bytecode) of more than `h_B` variables, nor of Flock's point on `q_flock`
  (`AtTSlotsMaximal`); it fails only where a coordinate equation in `t` holds (a small set of `t`, not bounded
  here). Truncating the slot point to `vars − 8` in `weightAt` and `denseWeight` (as the Rust prover does) would
  make the condition the ordinary one (`vars − 8 ≤ |y|`), which the verifier's slots satisfy.
* **Proof structure.** `denseWeight` is a fold of additions (`addAt`): every step adds a fixed array (`AddsTo`)
  whatever the array it is applied to, so the fold adds their sum. `combine` is mirrored by `combineTerm`,
  `combineRel`, `combineEnd` (`combine_eq`, by `rfl`); its first fold is followed with the *final* points array
  `PF` (every intermediate points array is a prefix of it, `combineTerms_mono`), so a term's index `p` reads
  `PF[p] = t.point`; the merged terms' values add up (`sum_mergeTerm`, for any functional additive in the
  coefficient); `longestOf` gives the longest extension and is idempotent (`longestOf_spec`,
  `longestOf_longestOf`), so the renumbered point is `PF[longestOf PF p]` (`getD_renumber`).
-/

namespace UniComplete

open UniStatement LeanVM.Parameters

/-! ### Sums -/

theorem foldl_add_eq_sum {α : Type} (f : α → E) : ∀ (l : List α) (a : E),
    l.foldl (fun acc u ↦ acc + f u) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_eq_sum f l, List.map_cons, List.sum_cons, add_assoc]

/-- **`dotK` is the sum of its products** (so linear in the weight). -/
theorem dotK_eq_sum (w : Array E) (s : Array K) :
    dotK w s = ((List.range w.size).map fun u ↦ w.getD u 0 * ofK (s.getD u 0)).sum := by
  unfold dotK
  rw [foldl_add_eq_sum, zero_add]

theorem sum_map_comm {α β : Type} (L : List α) (M : List β) (f : α → β → E) :
    (M.map fun b ↦ (L.map fun a ↦ f a b).sum).sum = (L.map fun a ↦ (M.map fun b ↦ f a b).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, List.sum_map_add, ih]

theorem getD_replicate_zero (N u : ℕ) : (Array.replicate N (0 : E)).getD u 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem toArray_getD {α : Type} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp

/-! ### Additive steps on weight arrays -/

/-- **`g` adds `Δ`** to every array of `N` words: it keeps the size and adds `Δ u` at every word `u`. -/
def AddsTo (N : ℕ) (g : Array E → Array E) (Δ : ℕ → E) : Prop :=
  ∀ W : Array E, W.size = N → (g W).size = N ∧ ∀ u, (g W).getD u 0 = W.getD u 0 + Δ u

theorem addsTo_addAt (N i : ℕ) (x : E) :
    AddsTo N (fun W ↦ addAt W i x) (fun u ↦ if u = i ∧ i < N then x else 0) := by
  intro W hW
  subst hW
  refine ⟨by simp [addAt], fun u ↦ ?_⟩
  simp only [addAt, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hu : i = u
  · subst hu
    by_cases hN : i < W.size
    · simp [hN]
    · simp [hN]
  · have hu' : ¬u = i := fun h ↦ hu h.symm
    simp [hu, hu']

theorem addsTo_foldl {α : Type} (N : ℕ) (f : Array E → α → Array E) (Δ : α → ℕ → E)
    (h : ∀ a, AddsTo N (fun W ↦ f W a) (Δ a)) (L : List α) :
    AddsTo N (fun W ↦ L.foldl f W) (fun u ↦ (L.map fun a ↦ Δ a u).sum) := by
  induction L with
  | nil => intro W hW; exact ⟨hW, fun u ↦ by simp⟩
  | cons a L ih =>
    intro W hW
    obtain ⟨h1, h2⟩ := h a W hW
    obtain ⟨h3, h4⟩ := ih (f W a) h1
    refine ⟨h3, fun u ↦ ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [h4, h2, add_assoc]


/-! ### One term's step of `denseWeight` -/

/-- `q_flock`'s slot `j` on one block `b = (limb, vars, offset)`: `eq` of the whole point at the words
`offset + j + 256 u`. -/
def slotBlock (point : List E) (j : ℕ) (coefficient : E) (W : Array E) (b : ℕ × ℕ × ℕ) : Array E :=
  (List.range (eqKernel point).size).foldl (fun W u ↦
    addAt W (b.2.2 + j + 256 * u) (limbScale coefficient b.1 * (eqKernel point).getD u 0)) W

/-- `q_flock`'s slot `j` (`denseWeight`'s first branch), on `q_flock`'s blocks. -/
def slotFold (layout : StackLayout) (point : List E) (j : ℕ) (coefficient : E) (W : Array E) : Array E :=
  (layout.limbs .qflock).foldl (slotBlock point j coefficient) W

/-- A term's value at an entry `e` of its `eq` table: `Φ(e)` for the ring-switch term, `e^(2^twist)` else. -/
def twistValue (ringMap : Option (List E)) (twist : ℕ) (e : E) : E :=
  if twist = ringTwist then
    (match ringMap with
      | some map => Flock.towerRingMap e map
      | none => 0)
  else sqn e twist

/-- The `eq` table an ordinary column reads on a block of `vars` variables: of the point's first `vars`
coordinates, zero-padded. -/
def blockEq (point : List E) (vars : ℕ) : Array E := eqKernel ((point ++ List.replicate vars 0).take vars)

/-- An ordinary column on one block `b = (limb, vars, offset)`. -/
def genericBlock (ringMap : Option (List E)) (point : List E) (twist : ℕ) (coefficient : E) (W : Array E)
    (b : ℕ × ℕ × ℕ) : Array E :=
  (List.range (2 ^ b.2.1)).foldl (fun W u ↦
    addAt W (b.2.2 + u) (limbScale coefficient b.1 * twistValue ringMap twist ((blockEq point b.2.1).getD u 0))) W

/-- An ordinary column (`denseWeight`'s second branch), on its blocks. -/
def genericFold (layout : StackLayout) (ringMap : Option (List E)) (point : List E) (column : Column)
    (twist : ℕ) (coefficient : E) (W : Array E) : Array E :=
  (layout.limbs column).foldl (genericBlock ringMap point twist coefficient) W

/-- **One term's step** of `denseWeight`, at its point. -/
def termStep (layout : StackLayout) (ringMap : Option (List E)) (point : List E) (column : Column)
    (twist : ℕ) (coefficient : E) (W : Array E) : Array E :=
  match column with
  | .qflockSlot j => slotFold layout point j coefficient W
  | _ => genericFold layout ringMap point column twist coefficient W

/-- `denseWeight` is the fold of its terms' steps. -/
theorem denseWeight_eq_foldl (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) :
    denseWeight claim layout ringMap = claim.terms.foldl (fun W e ↦
      termStep layout ringMap (claim.points.toArray.getD e.2.1 []) e.1 e.2.2.1 e.2.2.2 W)
      (Array.replicate (2 ^ layout.vars) 0) := rfl

/-- A term as the claim reads it: its column, the claim's point at its index, its twist and coefficient. -/
def termAt (claim : Combined) (e : Column × ℕ × ℕ × E) : Term :=
  ⟨e.1, claim.points.getD e.2.1 [], e.2.2.1, e.2.2.2⟩

/-- A one-term claim's weight is its term's step on zeros. -/
theorem denseWeight_termClaim (t : Term) (layout : StackLayout) (ringMap : Option (List E)) :
    denseWeight (termClaim t) layout ringMap =
      termStep layout ringMap t.point t.column t.twist t.coefficient (Array.replicate (2 ^ layout.vars) 0) :=
  rfl

/-! ### What a step adds -/

/-- What `slotBlock` adds at word `x` from index `u`. -/
def slotWordDelta (N : ℕ) (point : List E) (j : ℕ) (coefficient : E) (b : ℕ × ℕ × ℕ) (u x : ℕ) : E :=
  if x = b.2.2 + j + 256 * u ∧ b.2.2 + j + 256 * u < N then
    limbScale coefficient b.1 * (eqKernel point).getD u 0 else 0

def slotBlockDelta (N : ℕ) (point : List E) (j : ℕ) (coefficient : E) (b : ℕ × ℕ × ℕ) (x : ℕ) : E :=
  ((List.range (eqKernel point).size).map fun u ↦ slotWordDelta N point j coefficient b u x).sum

def slotDelta (N : ℕ) (layout : StackLayout) (point : List E) (j : ℕ) (coefficient : E) (x : ℕ) : E :=
  ((layout.limbs .qflock).map fun b ↦ slotBlockDelta N point j coefficient b x).sum

/-- What `genericBlock` adds at word `x` from index `u`. -/
def genericWordDelta (N : ℕ) (ringMap : Option (List E)) (point : List E) (twist : ℕ) (coefficient : E)
    (b : ℕ × ℕ × ℕ) (u x : ℕ) : E :=
  if x = b.2.2 + u ∧ b.2.2 + u < N then
    limbScale coefficient b.1 * twistValue ringMap twist ((blockEq point b.2.1).getD u 0) else 0

def genericBlockDelta (N : ℕ) (ringMap : Option (List E)) (point : List E) (twist : ℕ) (coefficient : E)
    (b : ℕ × ℕ × ℕ) (x : ℕ) : E :=
  ((List.range (2 ^ b.2.1)).map fun u ↦ genericWordDelta N ringMap point twist coefficient b u x).sum

def genericDelta (N : ℕ) (layout : StackLayout) (ringMap : Option (List E)) (point : List E) (column : Column)
    (twist : ℕ) (coefficient : E) (x : ℕ) : E :=
  ((layout.limbs column).map fun b ↦ genericBlockDelta N ringMap point twist coefficient b x).sum

/-- **What one term's step adds**, word by word. -/
def termDelta (N : ℕ) (layout : StackLayout) (ringMap : Option (List E)) (point : List E) (column : Column)
    (twist : ℕ) (coefficient : E) : ℕ → E :=
  match column with
  | .qflockSlot j => slotDelta N layout point j coefficient
  | _ => genericDelta N layout ringMap point column twist coefficient

theorem slotBlock_addsTo (N : ℕ) (point : List E) (j : ℕ) (coefficient : E) (b : ℕ × ℕ × ℕ) :
    AddsTo N (fun W ↦ slotBlock point j coefficient W b) (slotBlockDelta N point j coefficient b) :=
  addsTo_foldl N (fun W u ↦
      addAt W (b.2.2 + j + 256 * u) (limbScale coefficient b.1 * (eqKernel point).getD u 0))
    (slotWordDelta N point j coefficient b)
    (fun u ↦ addsTo_addAt N (b.2.2 + j + 256 * u) (limbScale coefficient b.1 * (eqKernel point).getD u 0))
    (List.range (eqKernel point).size)

theorem slotFold_addsTo (N : ℕ) (layout : StackLayout) (point : List E) (j : ℕ) (coefficient : E) :
    AddsTo N (slotFold layout point j coefficient) (slotDelta N layout point j coefficient) :=
  addsTo_foldl N (slotBlock point j coefficient) (slotBlockDelta N point j coefficient)
    (slotBlock_addsTo N point j coefficient) (layout.limbs .qflock)

theorem genericBlock_addsTo (N : ℕ) (ringMap : Option (List E)) (point : List E) (twist : ℕ) (coefficient : E)
    (b : ℕ × ℕ × ℕ) :
    AddsTo N (fun W ↦ genericBlock ringMap point twist coefficient W b)
      (genericBlockDelta N ringMap point twist coefficient b) :=
  addsTo_foldl N (fun W u ↦
      addAt W (b.2.2 + u) (limbScale coefficient b.1 * twistValue ringMap twist ((blockEq point b.2.1).getD u 0)))
    (genericWordDelta N ringMap point twist coefficient b)
    (fun u ↦ addsTo_addAt N (b.2.2 + u)
      (limbScale coefficient b.1 * twistValue ringMap twist ((blockEq point b.2.1).getD u 0)))
    (List.range (2 ^ b.2.1))

theorem genericFold_addsTo (N : ℕ) (layout : StackLayout) (ringMap : Option (List E)) (point : List E)
    (column : Column) (twist : ℕ) (coefficient : E) :
    AddsTo N (genericFold layout ringMap point column twist coefficient)
      (genericDelta N layout ringMap point column twist coefficient) :=
  addsTo_foldl N (genericBlock ringMap point twist coefficient) (genericBlockDelta N ringMap point twist coefficient)
    (genericBlock_addsTo N ringMap point twist coefficient) (layout.limbs column)

/-- On a column other than a slot, the step is the ordinary one. -/
theorem termStep_generic {column : Column} (hs : ∀ j, column ≠ .qflockSlot j) (layout : StackLayout)
    (ringMap : Option (List E)) (point : List E) (twist : ℕ) (coefficient : E) :
    termStep layout ringMap point column twist coefficient =
      genericFold layout ringMap point column twist coefficient := by
  cases column <;> first | rfl | exact absurd rfl (hs _)

theorem termDelta_generic {column : Column} (hs : ∀ j, column ≠ .qflockSlot j) (N : ℕ) (layout : StackLayout)
    (ringMap : Option (List E)) (point : List E) (twist : ℕ) (coefficient : E) :
    termDelta N layout ringMap point column twist coefficient =
      genericDelta N layout ringMap point column twist coefficient := by
  cases column <;> first | rfl | exact absurd rfl (hs _)

theorem termStep_addsTo (N : ℕ) (layout : StackLayout) (ringMap : Option (List E)) (point : List E)
    (column : Column) (twist : ℕ) (coefficient : E) :
    AddsTo N (termStep layout ringMap point column twist coefficient)
      (termDelta N layout ringMap point column twist coefficient) := by
  by_cases hs : ∃ j, column = .qflockSlot j
  · obtain ⟨j, rfl⟩ := hs
    exact slotFold_addsTo N layout point j coefficient
  · have hs' : ∀ j, column ≠ .qflockSlot j := fun j h ↦ hs ⟨j, h⟩
    rw [termStep_generic hs', termDelta_generic hs']
    exact genericFold_addsTo N layout ringMap point column twist coefficient

/-! ### Linearity in the coefficient -/

theorem limbScale_mul (c a : E) (limb : ℕ) : limbScale (c * a) limb = c * limbScale a limb := by
  unfold limbScale
  split_ifs <;> ring

theorem slotDelta_mul (N : ℕ) (layout : StackLayout) (point : List E) (j : ℕ) (c a : E) (x : ℕ) :
    slotDelta N layout point j (c * a) x = c * slotDelta N layout point j a x := by
  unfold slotDelta slotBlockDelta slotWordDelta
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun b _ ↦ ?_)
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun u _ ↦ ?_)
  split_ifs <;> simp [limbScale_mul, mul_assoc]

theorem genericDelta_mul (N : ℕ) (layout : StackLayout) (ringMap : Option (List E)) (point : List E)
    (column : Column) (twist : ℕ) (c a : E) (x : ℕ) :
    genericDelta N layout ringMap point column twist (c * a) x =
      c * genericDelta N layout ringMap point column twist a x := by
  unfold genericDelta genericBlockDelta genericWordDelta
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun b _ ↦ ?_)
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun u _ ↦ ?_)
  split_ifs <;> simp [limbScale_mul, mul_assoc]

theorem termDelta_mul (N : ℕ) (layout : StackLayout) (ringMap : Option (List E)) (point : List E)
    (column : Column) (twist : ℕ) (c a : E) (x : ℕ) :
    termDelta N layout ringMap point column twist (c * a) x =
      c * termDelta N layout ringMap point column twist a x := by
  by_cases hs : ∃ j, column = .qflockSlot j
  · obtain ⟨j, rfl⟩ := hs
    exact slotDelta_mul N layout point j c a x
  · have hs' : ∀ j, column ≠ .qflockSlot j := fun j h ↦ hs ⟨j, h⟩
    rw [termDelta_generic hs', termDelta_generic hs']
    exact genericDelta_mul N layout ringMap point column twist c a x

/-! ### `denseWeight` is linear -/

theorem denseWeight_addsTo (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) :
    AddsTo (2 ^ layout.vars) (fun W ↦ claim.terms.foldl (fun W e ↦
      termStep layout ringMap (claim.points.toArray.getD e.2.1 []) e.1 e.2.2.1 e.2.2.2 W) W)
      (fun u ↦ (claim.terms.map fun e ↦ termDelta (2 ^ layout.vars) layout ringMap
        (claim.points.toArray.getD e.2.1 []) e.1 e.2.2.1 e.2.2.2 u).sum) :=
  addsTo_foldl (2 ^ layout.vars) (fun W e ↦
      termStep layout ringMap (claim.points.toArray.getD e.2.1 []) e.1 e.2.2.1 e.2.2.2 W)
    (fun e ↦ termDelta (2 ^ layout.vars) layout ringMap (claim.points.toArray.getD e.2.1 []) e.1 e.2.2.1 e.2.2.2)
    (fun e ↦ termStep_addsTo (2 ^ layout.vars) layout ringMap (claim.points.toArray.getD e.2.1 []) e.1 e.2.2.1
      e.2.2.2) claim.terms

theorem size_denseWeight (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) :
    (denseWeight claim layout ringMap).size = 2 ^ layout.vars := by
  rw [denseWeight_eq_foldl]
  exact (denseWeight_addsTo claim layout ringMap _ Array.size_replicate).1

/-- A claim's weight, word by word, is what its terms' steps add. -/
theorem denseWeight_getD_eq_delta (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) (u : ℕ) :
    (denseWeight claim layout ringMap).getD u 0 = (claim.terms.map fun e ↦
      termDelta (2 ^ layout.vars) layout ringMap (claim.points.getD e.2.1 []) e.1 e.2.2.1 e.2.2.2 u).sum := by
  rw [denseWeight_eq_foldl, (denseWeight_addsTo claim layout ringMap _ Array.size_replicate).2 u,
    getD_replicate_zero, zero_add]
  simp only [toArray_getD]

/-- A one-term weight, word by word, is what its step adds. -/
theorem denseWeight_termClaim_getD (t : Term) (layout : StackLayout) (ringMap : Option (List E)) (u : ℕ) :
    (denseWeight (termClaim t) layout ringMap).getD u 0 =
      termDelta (2 ^ layout.vars) layout ringMap t.point t.column t.twist t.coefficient u := by
  rw [denseWeight_termClaim, ((termStep_addsTo (2 ^ layout.vars) layout ringMap t.point t.column t.twist
    t.coefficient) _ Array.size_replicate).2 u, getD_replicate_zero, zero_add]

/-- **`denseWeight` is linear**: a claim's weight, word by word, is the sum over its terms of each term's
one-term weight, the term at the claim's point `points[p]`. -/
theorem denseWeight_getD_eq_sum (claim : Combined) (layout : StackLayout) (ringMap : Option (List E))
    (u : ℕ) :
    (denseWeight claim layout ringMap).getD u 0 =
      (claim.terms.map fun e ↦ (denseWeight (termClaim (termAt claim e)) layout ringMap).getD u 0).sum := by
  rw [denseWeight_getD_eq_delta]
  refine congrArg List.sum (List.map_congr_left fun e _ ↦ ?_)
  rw [denseWeight_termClaim_getD]
  rfl

/-- **A one-term weight is linear in its coefficient**, word by word. -/
theorem denseWeight_termClaim_getD_mul (layout : StackLayout) (ringMap : Option (List E)) (column : Column)
    (point : List E) (twist : ℕ) (c a : E) (u : ℕ) :
    (denseWeight (termClaim ⟨column, point, twist, c * a⟩) layout ringMap).getD u 0 =
      c * (denseWeight (termClaim ⟨column, point, twist, a⟩) layout ringMap).getD u 0 := by
  rw [denseWeight_termClaim_getD, denseWeight_termClaim_getD]
  exact termDelta_mul _ layout ringMap point column twist c a u

/-- A term's value is the pairing of what its step adds with the stack. -/
theorem termEval_eq (layout : StackLayout) (stack : Array K) (ringMap : Option (List E)) (t : Term) :
    termEval layout stack ringMap t = ((List.range (2 ^ layout.vars)).map fun u ↦
      termDelta (2 ^ layout.vars) layout ringMap t.point t.column t.twist t.coefficient u *
        ofK (stack.getD u 0)).sum := by
  unfold termEval
  rw [dotK_eq_sum, size_denseWeight]
  refine congrArg List.sum (List.map_congr_left fun u _ ↦ ?_)
  rw [denseWeight_termClaim_getD]

/-- **A claim's pairing is the sum of its terms' values.** -/
theorem dotK_denseWeight (claim : Combined) (layout : StackLayout) (stack : Array K)
    (ringMap : Option (List E)) :
    dotK (denseWeight claim layout ringMap) stack =
      (claim.terms.map fun e ↦ termEval layout stack ringMap (termAt claim e)).sum := by
  rw [dotK_eq_sum, size_denseWeight]
  have hw : ∀ u, (denseWeight claim layout ringMap).getD u 0 * ofK (stack.getD u 0) =
      (claim.terms.map fun e ↦ termDelta (2 ^ layout.vars) layout ringMap (claim.points.getD e.2.1 []) e.1
        e.2.2.1 e.2.2.2 u * ofK (stack.getD u 0)).sum := by
    intro u
    rw [denseWeight_getD_eq_delta, List.sum_map_mul_right]
  rw [List.map_congr_left fun u _ ↦ hw u, sum_map_comm]
  refine congrArg List.sum (List.map_congr_left fun e _ ↦ ?_)
  rw [termEval_eq]
  rfl

/-- **A term's value is linear in its coefficient.** -/
theorem termEval_mul (layout : StackLayout) (stack : Array K) (ringMap : Option (List E)) (column : Column)
    (point : List E) (twist : ℕ) (c a : E) :
    termEval layout stack ringMap ⟨column, point, twist, c * a⟩ =
      c * termEval layout stack ringMap ⟨column, point, twist, a⟩ := by
  rw [termEval_eq, termEval_eq, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun u _ ↦ ?_)
  rw [termDelta_mul, mul_assoc]

theorem termEval_add (layout : StackLayout) (stack : Array K) (ringMap : Option (List E)) (column : Column)
    (point : List E) (twist : ℕ) (a b : E) :
    termEval layout stack ringMap ⟨column, point, twist, a + b⟩ =
      termEval layout stack ringMap ⟨column, point, twist, a⟩ +
        termEval layout stack ringMap ⟨column, point, twist, b⟩ := by
  have h (c : E) : termEval layout stack ringMap ⟨column, point, twist, c⟩ =
      c * termEval layout stack ringMap ⟨column, point, twist, 1⟩ := by
    rw [← termEval_mul, mul_one]
  rw [h (a + b), h a, h b, add_mul]

/-! ### A term read at a longer point -/

/-- **A term reads its own point** among the points `others` of its commitment's relations (what `combine`'s
renumbering needs of it): an ordinary column's blocks have at most as many variables as the point has
coordinates, so a longer point having it as a prefix is read at the same coordinates; a slot of `q_flock`, which
`denseWeight` (and `weightAt`) read whole, has no strictly longer point among `others` having it as a prefix. -/
def ReadsOwnPoint (layout : StackLayout) (others : List (List E)) (column : Column) (point : List E) : Prop :=
  match column with
  | .qflockSlot _ => ∀ q ∈ others, point <+: q → q = point
  | column => ∀ b ∈ layout.limbs column, b.2.1 ≤ point.length

theorem readsOwnPoint_generic {column : Column} (hs : ∀ j, column ≠ .qflockSlot j) {layout : StackLayout}
    {others : List (List E)} {point : List E} :
    ReadsOwnPoint layout others column point ↔ ∀ b ∈ layout.limbs column, b.2.1 ≤ point.length := by
  cases column <;> first | exact Iff.rfl | exact absurd rfl (hs _)

theorem readsOwnPoint_mono {layout : StackLayout} {others others' : List (List E)}
    (hsub : ∀ q ∈ others', q ∈ others) {column : Column} {point : List E}
    (h : ReadsOwnPoint layout others column point) : ReadsOwnPoint layout others' column point := by
  by_cases hs : ∃ j, column = .qflockSlot j
  · obtain ⟨j, rfl⟩ := hs
    exact fun q hq hpq ↦ h q (hsub q hq) hpq
  · have hs' : ∀ j, column ≠ .qflockSlot j := fun j h ↦ hs ⟨j, h⟩
    exact (readsOwnPoint_generic hs').2 ((readsOwnPoint_generic hs').1 h)

theorem blockEq_extend {P Q : List E} {vars : ℕ} (hPQ : P <+: Q) (hv : vars ≤ P.length) :
    blockEq Q vars = blockEq P vars := by
  unfold blockEq
  obtain ⟨R, rfl⟩ := hPQ
  rw [List.append_assoc, List.take_append_of_le_length hv, List.take_append_of_le_length hv]

theorem genericFold_extend {layout : StackLayout} {ringMap : Option (List E)} {P Q : List E} {column : Column}
    {twist : ℕ} {coefficient : E} (hcov : ∀ b ∈ layout.limbs column, b.2.1 ≤ P.length) (hPQ : P <+: Q) :
    genericFold layout ringMap Q column twist coefficient = genericFold layout ringMap P column twist coefficient := by
  funext W
  unfold genericFold
  apply List.foldl_ext
  intro W b hb
  unfold genericBlock
  rw [blockEq_extend hPQ (hcov b hb)]

/-- **A term reads its own point at a longer one** having it as a prefix, among `others`. -/
theorem termEval_extend (layout : StackLayout) (stack : Array K) (ringMap : Option (List E))
    {others : List (List E)} {column : Column} {P Q : List E} (twist : ℕ) (a : E)
    (hwf : ReadsOwnPoint layout others column P) (hPQ : P <+: Q) (hQ : Q ∈ others) :
    termEval layout stack ringMap ⟨column, Q, twist, a⟩ = termEval layout stack ringMap ⟨column, P, twist, a⟩ := by
  by_cases hs : ∃ j, column = .qflockSlot j
  · obtain ⟨j, rfl⟩ := hs
    rw [hwf Q hQ hPQ]
  · have hs' : ∀ j, column ≠ .qflockSlot j := fun j h ↦ hs ⟨j, h⟩
    unfold termEval
    rw [denseWeight_termClaim, denseWeight_termClaim]
    dsimp only
    rw [termStep_generic hs', termStep_generic hs', genericFold_extend ((readsOwnPoint_generic hs').1 hwf) hPQ]

/-! ### Merging terms -/

theorem sum_map_modify {α : Type} (F : α → E) (f : α → α) (δ : E) :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length), F (f l[i]) = F l[i] + δ →
      ((l.modify i f).map F).sum = (l.map F).sum + δ
  | [], _, hi, _ => absurd hi (by simp)
  | a :: l, 0, _, h => by
    rw [List.modify_zero_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    rw [List.getElem_cons_zero] at h
    rw [h, add_right_comm]
  | a :: l, i + 1, hi, h => by
    rw [List.modify_succ_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      sum_map_modify F f δ l i (by simpa using hi) (by simpa using h), add_assoc]

/-- **Merging a term adds its value**, for a functional additive in the coefficient. -/
theorem sum_mergeTerm (F : Column × ℕ × ℕ × E → E)
    (hF : ∀ c p k a b, F (c, p, k, a + b) = F (c, p, k, a) + F (c, p, k, b))
    (terms : Array (Column × ℕ × ℕ × E)) (column : Column) (p twist : ℕ) (coefficient : E) :
    ((mergeTerm terms column p twist coefficient).toList.map F).sum =
      (terms.toList.map F).sum + F (column, p, twist, coefficient) := by
  unfold mergeTerm
  split
  · next i hi =>
    rw [Array.findIdx?_eq_some_iff_getElem] at hi
    obtain ⟨hlt, hpred, -⟩ := hi
    rw [Array.toList_modify]
    refine sum_map_modify F _ _ terms.toList i (by simpa using hlt) ?_
    rw [Array.getElem_toList]
    generalize terms[i] = x at hpred ⊢
    obtain ⟨c', q', k', v⟩ := x
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpred
    exact hF _ _ _ _ _
  · rw [Array.toList_push, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

/-- **Merging a list of terms renumbered by `ren` adds their values.** -/
theorem sum_mergeFold (F : Column × ℕ × ℕ × E → E)
    (hF : ∀ c p k a b, F (c, p, k, a + b) = F (c, p, k, a) + F (c, p, k, b)) (ren : ℕ → ℕ) :
    ∀ (L : List (Column × ℕ × ℕ × E)) (acc : Array (Column × ℕ × ℕ × E)),
      ((L.foldl (fun acc e ↦ mergeTerm acc e.1 (ren e.2.1) e.2.2.1 e.2.2.2) acc).toList.map F).sum =
        (acc.toList.map F).sum + (L.map fun e ↦ F (e.1, ren e.2.1, e.2.2.1, e.2.2.2)).sum
  | [], acc => by simp
  | e :: L, acc => by
    rw [List.foldl_cons, sum_mergeFold F hF ren L, sum_mergeTerm F hF, List.map_cons, List.sum_cons, add_assoc]

/-! ### The longest extension -/

/-- `longestOf`'s step. -/
def longestStep (points : Array (List E)) (pp : List E) (best q : ℕ) : ℕ :=
  let pq := points.getD q []
  if pq.length ≥ pp.length ∧ pq.take pp.length == pp ∧ pq.length > (points.getD best []).length then q
  else best

/-- `if_pos` (which this Mathlib deprecates). -/
theorem iteT {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]

/-- `if_neg` (which this Mathlib deprecates). -/
theorem iteF {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by simp [h]

theorem longestOf_eq (points : Array (List E)) (p : ℕ) :
    longestOf points p = (List.range points.size).foldl (longestStep points (points.getD p [])) p := rfl

theorem prefix_iff_cond {pp pq : List E} :
    (pq.length ≥ pp.length ∧ (pq.take pp.length == pp) = true) ↔ pp <+: pq := by
  rw [beq_iff_eq]
  constructor
  · rintro ⟨-, h⟩
    rw [← h]
    exact List.take_prefix _ _
  · intro h
    exact ⟨h.length_le, (List.prefix_iff_eq_take.mp h).symm⟩

theorem longestStep_spec (points : Array (List E)) (pp : List E) (best q : ℕ) (hb : best < points.size)
    (hq : q < points.size) (hpb : pp <+: points.getD best []) :
    longestStep points pp best q < points.size ∧ pp <+: points.getD (longestStep points pp best q) [] ∧
      (points.getD best []).length ≤ (points.getD (longestStep points pp best q) []).length ∧
      (pp <+: points.getD q [] →
        (points.getD q []).length ≤ (points.getD (longestStep points pp best q) []).length) := by
  unfold longestStep
  dsimp only
  by_cases h : (points.getD q []).length ≥ pp.length ∧ (points.getD q []).take pp.length == pp ∧
    (points.getD q []).length > (points.getD best []).length
  · rw [iteT h]
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨hq, prefix_iff_cond.mp ⟨h1, h2⟩, le_of_lt h3, fun _ ↦ le_refl _⟩
  · rw [iteF h]
    refine ⟨hb, hpb, le_refl _, fun hpq ↦ ?_⟩
    have := prefix_iff_cond.mpr hpq
    by_contra hlt
    exact h ⟨this.1, this.2, not_le.mp hlt⟩

theorem longestFold_spec (points : Array (List E)) (pp : List E) :
    ∀ (L : List ℕ) (best : ℕ), (∀ q ∈ L, q < points.size) → best < points.size → pp <+: points.getD best [] →
      L.foldl (longestStep points pp) best < points.size ∧
      pp <+: points.getD (L.foldl (longestStep points pp) best) [] ∧
      (points.getD best []).length ≤ (points.getD (L.foldl (longestStep points pp) best) []).length ∧
      ∀ q ∈ L, pp <+: points.getD q [] →
        (points.getD q []).length ≤ (points.getD (L.foldl (longestStep points pp) best) []).length
  | [], _, _, hb, hpb => ⟨hb, hpb, le_refl _, fun _ hq ↦ absurd hq (by simp)⟩
  | q :: L, best, hL, hb, hpb => by
    obtain ⟨h1, h2, h3, h4⟩ := longestStep_spec points pp best q hb (hL q (by simp)) hpb
    obtain ⟨i1, i2, i3, i4⟩ := longestFold_spec points pp L _ (fun q' hq' ↦ hL q' (by simp [hq'])) h1 h2
    refine ⟨i1, i2, h3.trans i3, fun q' hq' hpq' ↦ ?_⟩
    rcases List.mem_cons.mp hq' with rfl | hq'
    · exact (h4 hpq').trans i3
    · exact i4 q' hq' hpq'

/-- **`longestOf` is the longest extension**: a point of the array, having point `p` as a prefix, at least as
long as every point having `p` as a prefix. -/
theorem longestOf_spec (points : Array (List E)) {p : ℕ} (hp : p < points.size) :
    longestOf points p < points.size ∧ points.getD p [] <+: points.getD (longestOf points p) [] ∧
      ∀ q < points.size, points.getD p [] <+: points.getD q [] →
        (points.getD q []).length ≤ (points.getD (longestOf points p) []).length := by
  rw [longestOf_eq]
  obtain ⟨h1, h2, -, h4⟩ := longestFold_spec points (points.getD p []) (List.range points.size) p
    (fun q hq ↦ List.mem_range.mp hq) hp (List.prefix_refl _)
  exact ⟨h1, h2, fun q hq hpq ↦ h4 q (List.mem_range.mpr hq) hpq⟩

theorem foldl_fixed {f : ℕ → ℕ → ℕ} {b : ℕ} : ∀ (L : List ℕ), (∀ q ∈ L, f b q = b) → L.foldl f b = b
  | [], _ => rfl
  | q :: L, h => by
    rw [List.foldl_cons, h q (by simp)]
    exact foldl_fixed L (fun q' hq' ↦ h q' (by simp [hq']))

/-- **`longestOf` is idempotent**: the longest extension is its own. -/
theorem longestOf_longestOf (points : Array (List E)) {p : ℕ} (hp : p < points.size) :
    longestOf points (longestOf points p) = longestOf points p := by
  obtain ⟨-, hpre, hmax⟩ := longestOf_spec points hp
  rw [longestOf_eq points (longestOf points p)]
  refine foldl_fixed _ fun q hq ↦ ?_
  unfold longestStep
  dsimp only
  by_cases h : (points.getD q []).length ≥ (points.getD (longestOf points p) []).length ∧
    (points.getD q []).take (points.getD (longestOf points p) []).length ==
      points.getD (longestOf points p) [] ∧
    (points.getD q []).length > (points.getD (longestOf points p) []).length
  · exfalso
    obtain ⟨h1, h2, h3⟩ := h
    have hpq := prefix_iff_cond.mp ⟨h1, h2⟩
    have := hmax q (List.mem_range.mp hq) (hpre.trans hpq)
    omega
  · rw [iteF h]

/-! ### The renumbering -/

/-- `combine`'s `longest`. -/
def longestList (points : Array (List E)) : List ℕ := (List.range points.size).map (longestOf points)

/-- `combine`'s `kept`: the points that are their own longest extension. -/
def keptOf (points : Array (List E)) : List ℕ :=
  (List.range points.size).filter fun p ↦ (longestList points).getD p p == p

/-- `combine`'s `renumber`. -/
def renumberOf (points : Array (List E)) (p : ℕ) : ℕ := (keptOf points).idxOf ((longestList points).getD p p)

theorem longestList_getD (points : Array (List E)) {p : ℕ} (hp : p < points.size) :
    (longestList points).getD p p = longestOf points p := by
  unfold longestList
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp, Option.map_some, Option.getD_some]

/-- **A renumbered point is the longest extension.** -/
theorem getD_renumber (points : Array (List E)) {p : ℕ} (hp : p < points.size) :
    ((keptOf points).map (points.getD · [])).getD (renumberOf points p) [] =
      points.getD (longestOf points p) [] := by
  obtain ⟨hlt, -, -⟩ := longestOf_spec points hp
  have hmem : longestOf points p ∈ keptOf points := by
    simp only [keptOf, List.mem_filter, List.mem_range]
    rw [longestList_getD points hlt, longestOf_longestOf points hp]
    exact ⟨hlt, beq_self_eq_true _⟩
  unfold renumberOf
  rw [longestList_getD points hp]
  have hi := List.idxOf_lt_length_of_mem hmem
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    Option.getD_some, List.getElem_idxOf hi]

/-! ### `combine`, step by step -/

/-- `combine`'s inner step: one term of a relation, at the relation's scale. -/
def combineTerm (scale : E) (acc : Array (List E) × Array (Column × ℕ × ℕ × E)) (t : Term) :
    Array (List E) × Array (Column × ℕ × ℕ × E) :=
  let (points, terms) := acc
  let (points, p) := match points.findIdx? (· == t.point) with
    | some p => (points, p)
    | none => (points.push t.point, points.size)
  (points, mergeTerm terms t.column p t.twist (scale * t.coefficient))

/-- `combine`'s outer step: one relation. -/
def combineRel (rho : E) (acc : Array (List E) × Array (Column × ℕ × ℕ × E) × E × E) (relation : Relation) :
    Array (List E) × Array (Column × ℕ × ℕ × E) × E × E :=
  let (points, terms, value, scale) := acc
  let value := value + scale * relation.value
  let (points, terms) := relation.terms.foldl (combineTerm scale) (points, terms)
  (points, terms, value, scale * rho)

/-- `combine`'s end: the kept points, the terms renumbered and merged. -/
def combineEnd (points : Array (List E)) (terms : Array (Column × ℕ × ℕ × E)) (value : E) (n : ℕ) : Combined :=
  ⟨(keptOf points).map (points.getD · []),
    (terms.foldl (fun acc e ↦ mergeTerm acc e.1 (renumberOf points e.2.1) e.2.2.1 e.2.2.2) #[]).toList, value, n⟩

theorem combine_eq (relations : List Relation) (c : Commitment) (rho : E) :
    combine relations c rho =
      if (relations.filter (·.commitment == c)).isEmpty then none else
        some (combineEnd ((relations.filter (·.commitment == c)).foldl (combineRel rho) (#[], #[], 0, 1)).1
          ((relations.filter (·.commitment == c)).foldl (combineRel rho) (#[], #[], 0, 1)).2.1
          ((relations.filter (·.commitment == c)).foldl (combineRel rho) (#[], #[], 0, 1)).2.2.1
          (relations.filter (·.commitment == c)).length) := rfl

theorem combineRel_eq (rho : E) (acc : Array (List E) × Array (Column × ℕ × ℕ × E) × E × E)
    (relation : Relation) :
    combineRel rho acc relation =
      ((relation.terms.foldl (combineTerm acc.2.2.2) (acc.1, acc.2.1)).1,
        (relation.terms.foldl (combineTerm acc.2.2.2) (acc.1, acc.2.1)).2,
        acc.2.2.1 + acc.2.2.2 * relation.value, acc.2.2.2 * rho) := rfl

theorem combineTerm_spec (scale : E) (acc : Array (List E) × Array (Column × ℕ × ℕ × E)) (t : Term) :
    ∃ p, acc.1.toList <+: (combineTerm scale acc t).1.toList ∧
      (∀ q ∈ (combineTerm scale acc t).1.toList, q ∈ acc.1.toList ∨ q = t.point) ∧
      p < (combineTerm scale acc t).1.size ∧ (combineTerm scale acc t).1.getD p [] = t.point ∧
      (combineTerm scale acc t).2 = mergeTerm acc.2 t.column p t.twist (scale * t.coefficient) := by
  obtain ⟨points, terms⟩ := acc
  rcases hp : points.findIdx? (· == t.point) with _ | p
  · have h : combineTerm scale (points, terms) t =
        (points.push t.point, mergeTerm terms t.column points.size t.twist (scale * t.coefficient)) := by
      simp only [combineTerm, hp]
    rw [h]
    refine ⟨points.size, ?_, ?_, ?_, ?_, rfl⟩
    · rw [Array.toList_push]
      exact List.prefix_append _ _
    · intro q hq
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hq
      exact hq
    · simp
    · simp
  · have h : combineTerm scale (points, terms) t =
        (points, mergeTerm terms t.column p t.twist (scale * t.coefficient)) := by
      simp only [combineTerm, hp]
    rw [h]
    rw [Array.findIdx?_eq_some_iff_getElem] at hp
    obtain ⟨hlt, hpt, -⟩ := hp
    refine ⟨p, List.prefix_refl _, fun q hq ↦ Or.inl hq, hlt, ?_, rfl⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
    exact beq_iff_eq.mp hpt

theorem getD_of_prefix {A B : Array (List E)} (h : A.toList <+: B.toList) {p : ℕ} (hp : p < A.size) :
    p < B.size ∧ B.getD p [] = A.getD p [] := by
  obtain ⟨R, hR⟩ := h
  have hB : B.size = A.size + R.length := by
    rw [← Array.length_toList, ← hR, List.length_append, Array.length_toList]
  refine ⟨by omega, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← Array.getElem?_toList, ← hR, List.getElem?_append_left (by simpa using hp)]

theorem getD_mem_toList {A : Array (List E)} {p : ℕ} (hp : p < A.size) : A.getD p [] ∈ A.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp, Option.getD_some]
  exact Array.getElem_mem_toList hp

theorem combineTerms_mono (scale : E) :
    ∀ (L : List Term) (acc : Array (List E) × Array (Column × ℕ × ℕ × E)),
      acc.1.toList <+: (L.foldl (combineTerm scale) acc).1.toList
  | [], _ => List.prefix_refl _
  | t :: L, acc => by
    obtain ⟨_, h, -⟩ := combineTerm_spec scale acc t
    exact h.trans (combineTerms_mono scale L _)

theorem combineTerms_mem (scale : E) :
    ∀ (L : List Term) (acc : Array (List E) × Array (Column × ℕ × ℕ × E)),
      ∀ q ∈ (L.foldl (combineTerm scale) acc).1.toList, q ∈ acc.1.toList ∨ q ∈ L.map (·.point)
  | [], _, _, hq => Or.inl hq
  | t :: L, acc, q, hq => by
    obtain ⟨_, -, hmem, -⟩ := combineTerm_spec scale acc t
    rcases combineTerms_mem scale L _ q hq with h | h
    · rcases hmem q h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp [h'])
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **A relation's terms add their values** to `combine`'s terms, at the final points `PF`. -/
theorem combineTerms_sum (PF : Array (List E)) (G : Column × ℕ × ℕ × E → E)
    (hG : ∀ c p k a b, G (c, p, k, a + b) = G (c, p, k, a) + G (c, p, k, b)) (scale : E) (val : Term → E) :
    ∀ (L : List Term) (acc : Array (List E) × Array (Column × ℕ × ℕ × E)),
      (L.foldl (combineTerm scale) acc).1.toList <+: PF.toList →
      (∀ t ∈ L, ∀ p < PF.size, PF.getD p [] = t.point → G (t.column, p, t.twist, scale * t.coefficient) = val t) →
      ((L.foldl (combineTerm scale) acc).2.toList.map G).sum = (acc.2.toList.map G).sum + (L.map val).sum
  | [], _, _, _ => by simp
  | t :: L, acc, hpre, hval => by
    obtain ⟨p, -, -, hp, hpt, hterms⟩ := combineTerm_spec scale acc t
    have hpre' := (combineTerms_mono scale L (combineTerm scale acc t)).trans hpre
    obtain ⟨hpPF, hget⟩ := getD_of_prefix hpre' hp
    have ih := combineTerms_sum PF G hG scale val L (combineTerm scale acc t) hpre
      (fun t' ht' ↦ hval t' (List.mem_cons_of_mem _ ht'))
    rw [List.foldl_cons, ih, hterms, sum_mergeTerm G hG, hval t (by simp) p hpPF (hget.trans hpt),
      List.map_cons, List.sum_cons, add_assoc]

theorem combineRels_mono (rho : E) :
    ∀ (L : List Relation) (acc : Array (List E) × Array (Column × ℕ × ℕ × E) × E × E),
      acc.1.toList <+: (L.foldl (combineRel rho) acc).1.toList
  | [], _ => List.prefix_refl _
  | r :: L, acc => by
    have h : acc.1.toList <+: (combineRel rho acc r).1.toList := by
      rw [combineRel_eq]
      exact combineTerms_mono acc.2.2.2 r.terms (acc.1, acc.2.1)
    exact h.trans (combineRels_mono rho L _)

theorem combineRels_mem (rho : E) :
    ∀ (L : List Relation) (acc : Array (List E) × Array (Column × ℕ × ℕ × E) × E × E),
      ∀ q ∈ (L.foldl (combineRel rho) acc).1.toList,
        q ∈ acc.1.toList ∨ q ∈ L.flatMap fun r ↦ r.terms.map (·.point)
  | [], _, _, hq => Or.inl hq
  | r :: L, acc, q, hq => by
    rcases combineRels_mem rho L _ q hq with h | h
    · rw [combineRel_eq] at h
      rcases combineTerms_mem acc.2.2.2 r.terms (acc.1, acc.2.1) q h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_flatMap.mpr ⟨r, by simp, h'⟩)
    · rw [List.flatMap_cons]
      exact Or.inr (List.mem_append_right _ h)

/-- **The relations' values add up** to `combine`'s value, at the final points `PF`: if every relation holds
and every term's value at its index is its own, the terms' values are the value. -/
theorem combineRels_value (PF : Array (List E)) (G : Column × ℕ × ℕ × E → E)
    (hG : ∀ c p k a b, G (c, p, k, a + b) = G (c, p, k, a) + G (c, p, k, b)) (rho : E)
    (layout : StackLayout) (stack : Array K) (ringMap : Option (List E)) :
    ∀ (L : List Relation) (acc : Array (List E) × Array (Column × ℕ × ℕ × E) × E × E),
      (L.foldl (combineRel rho) acc).1.toList <+: PF.toList →
      (∀ r ∈ L, (r.terms.map (termEval layout stack ringMap)).sum = r.value) →
      (∀ r ∈ L, ∀ t ∈ r.terms, ∀ p < PF.size, PF.getD p [] = t.point → ∀ a,
        G (t.column, p, t.twist, a) = termEval layout stack ringMap ⟨t.column, t.point, t.twist, a⟩) →
      (acc.2.1.toList.map G).sum = acc.2.2.1 →
      ((L.foldl (combineRel rho) acc).2.1.toList.map G).sum = (L.foldl (combineRel rho) acc).2.2.1
  | [], _, _, _, _, h => h
  | r :: L, acc, hpre, hholds, hterm, hacc => by
    refine combineRels_value PF G hG rho layout stack ringMap L (combineRel rho acc r) hpre
      (fun r' h' ↦ hholds r' (List.mem_cons_of_mem _ h')) (fun r' h' ↦ hterm r' (List.mem_cons_of_mem _ h')) ?_
    have hpre' : (r.terms.foldl (combineTerm acc.2.2.2) (acc.1, acc.2.1)).1.toList <+: PF.toList := by
      have := (combineRels_mono rho L (combineRel rho acc r)).trans hpre
      rwa [combineRel_eq] at this
    rw [combineRel_eq]
    dsimp only
    rw [combineTerms_sum PF G hG acc.2.2.2 (fun t ↦ acc.2.2.2 * termEval layout stack ringMap t) r.terms
      (acc.1, acc.2.1) hpre' ?_]
    · dsimp only
      rw [hacc, List.sum_map_mul_left, hholds r (by simp)]
    · intro t ht p hp hpt
      rw [hterm r (by simp) t ht p hp hpt, termEval_mul]

/-! ### Combining true relations -/

/-- The points of the relations on `c`, every term's (`combine`'s points are these, each once). -/
def pointsOn (rels : List Relation) (c : Commitment) : List (List E) :=
  (rels.filter (·.commitment == c)).flatMap fun r ↦ r.terms.map (·.point)

/-- **Combining true relations with the powers of `ρ` gives a true weighted claim**: if every relation of `rels`
on `c` holds on `c`'s stack and layout (its terms' values, each on `c`'s stack, add up to its value), and every
term of those relations reads its own point among their points (`ReadsOwnPoint`), then the claim
`combine rels c ρ` holds. -/
theorem combine_holds (rels : List Relation) (c : Commitment) (rho : E) (layout : StackLayout)
    (stack : Array K) (ringMap : Option (List E)) (claim : Combined)
    (hholds : ∀ r ∈ rels, r.commitment = c → (r.terms.map (termEval layout stack ringMap)).sum = r.value)
    (hwf : ∀ r ∈ rels, r.commitment = c → ∀ t ∈ r.terms,
      ReadsOwnPoint layout (pointsOn rels c) t.column t.point)
    (h : combine rels c rho = some claim) : Combined.Holds layout stack ringMap claim := by
  rw [combine_eq] at h
  split at h
  · exact absurd h (by simp)
  · have hclaim := Option.some.inj h
    subst hclaim
    have hmem : ∀ r ∈ rels.filter (·.commitment == c), r ∈ rels ∧ r.commitment = c := fun r hr ↦ by
      rw [List.mem_filter, beq_iff_eq] at hr
      exact hr
    set mine := rels.filter (·.commitment == c) with hmine
    set st := mine.foldl (combineRel rho) (#[], #[], 0, 1) with hst
    set PF := st.1 with hPF
    have hPFsub : ∀ q ∈ PF.toList, q ∈ pointsOn rels c := by
      intro q hq
      rcases combineRels_mem rho mine (#[], #[], 0, 1) q hq with h' | h'
      · simp at h'
      · exact h'
    have hF : ∀ (c : Column) (p k : ℕ) (a b : E),
        termEval layout stack ringMap ⟨c, ((keptOf PF).map (PF.getD · [])).getD p [], k, a + b⟩ =
          termEval layout stack ringMap ⟨c, ((keptOf PF).map (PF.getD · [])).getD p [], k, a⟩ +
            termEval layout stack ringMap ⟨c, ((keptOf PF).map (PF.getD · [])).getD p [], k, b⟩ :=
      fun c p k a b ↦ termEval_add layout stack ringMap c _ k a b
    have hterm : ∀ r ∈ mine, ∀ t ∈ r.terms, ∀ p < PF.size, PF.getD p [] = t.point → ∀ a,
        termEval layout stack ringMap ⟨t.column, ((keptOf PF).map (PF.getD · [])).getD (renumberOf PF p) [],
          t.twist, a⟩ = termEval layout stack ringMap ⟨t.column, t.point, t.twist, a⟩ := by
      intro r hr t ht p hp hpt a
      rw [getD_renumber PF hp]
      obtain ⟨hlt, hpre, -⟩ := longestOf_spec PF hp
      rw [hpt] at hpre
      exact termEval_extend layout stack ringMap t.twist a
        (readsOwnPoint_mono hPFsub (hwf r (hmem r hr).1 (hmem r hr).2 t ht)) hpre (getD_mem_toList hlt)
    have hval := combineRels_value PF
      (fun e ↦ termEval layout stack ringMap
        ⟨e.1, ((keptOf PF).map (PF.getD · [])).getD (renumberOf PF e.2.1) [], e.2.2.1, e.2.2.2⟩)
      (fun c p k a b ↦ hF c (renumberOf PF p) k a b) rho layout stack ringMap mine (#[], #[], 0, 1)
      (List.prefix_refl _) (fun r hr ↦ hholds r (hmem r hr).1 (hmem r hr).2) hterm (by simp)
    unfold Combined.Holds
    rw [dotK_denseWeight]
    simp only [combineEnd, termAt]
    rw [← Array.foldl_toList]
    refine (sum_mergeFold (fun e ↦ termEval layout stack ringMap
        ⟨e.1, ((keptOf PF).map (PF.getD · [])).getD e.2.1 [], e.2.2.1, e.2.2.2⟩)
      (fun c p k a b ↦ hF c p k a b) (renumberOf PF) st.2.1.toList #[]).trans ?_
    rw [Array.toList_empty, List.map_nil, List.sum_nil, zero_add]
    exact hval

/-- **`combine_holds` for relations all of whose terms are on `c`**, with `Relation.Holds`. -/
theorem combine_holds_of_relations (rels : List Relation) (c : Commitment) (rho : E)
    (layoutOf : Commitment → StackLayout) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (claim : Combined)
    (hon : ∀ r ∈ rels, r.commitment = c → ∀ t ∈ r.terms, t.column.commitment = c)
    (hholds : ∀ r ∈ rels, r.commitment = c → Relation.Holds layoutOf stackOf ringMap r)
    (hwf : ∀ r ∈ rels, r.commitment = c → ∀ t ∈ r.terms,
      ReadsOwnPoint (layoutOf c) (pointsOn rels c) t.column t.point)
    (h : combine rels c rho = some claim) : Combined.Holds (layoutOf c) (stackOf c) ringMap claim := by
  refine combine_holds rels c rho (layoutOf c) (stackOf c) ringMap claim (fun r hr hc ↦ ?_) hwf h
  rw [← hholds r hr hc]
  refine congrArg List.sum (List.map_congr_left fun t ht ↦ ?_)
  rw [hon r hr hc t ht]

/-! ### The verifier's relations -/

/-- **Every relation the prover states at `t` is on one commitment**: its terms are on its commitment (the
first term's). -/
def AtTOnOne (a : AtT) : Prop := ∀ r ∈ a.relations, ∀ t ∈ r.terms, t.column.commitment = r.commitment

/-- **Every term's point covers its column**: on its commitment's layout (the verifier's `layouts shape
c2Columns`), every block of its column has at most as many variables as its point has coordinates. (A slot of
`q_flock` has no blocks of its own; `q_flock`'s are its.) -/
def AtTCovers (shape : Shape) (a : AtT) : Prop :=
  ∀ r ∈ a.relations, ∀ t ∈ r.terms,
    ∀ b ∈ (layoutIn (layouts shape a.c2Columns) t.column.commitment).limbs t.column, b.2.1 ≤ t.point.length

/-- **`q_flock`'s slot terms' points are maximal on `C1`**: no point of a relation on `C1` strictly extends
one. At `atTOf` the slot terms are BLAKE2S's limb copies at `y(t) = coordinatesAt t (coordinateFunctionals
h_B)` (`h_B` coordinates), and the other points on `C1` are `w(t).take r` for each table's height `r`,
`w(t).take lm`, `w(t).take lb` and Flock's point on `q_flock`; so this asks that `y(t)` is not
`w(t).take h_B` while some table, the memory or the bytecode has more than `h_B` variables, nor the first
`h_B` coordinates of Flock's point: a condition on the challenges `t` (and Flock's), false on a small set of
them (not bounded here). -/
def AtTSlotsMaximal (a : AtT) : Prop :=
  ∀ r ∈ a.relations, ∀ t ∈ r.terms, ∀ j, t.column = .qflockSlot j →
    ∀ q ∈ pointsOn a.relations .c1, t.point <+: q → q = t.point

/-- **The verifier's relations are well-formed for `combine`**, at the layouts `layouts shape a.c2Columns`. -/
def AtTWellFormed (shape : Shape) (a : AtT) : Prop := AtTOnOne a ∧ AtTCovers shape a ∧ AtTSlotsMaximal a

/-- Under `AtTWellFormed`, every relation on `c` has its terms on `c`, and they read their own points. -/
theorem atTWellFormed_readsOwn {shape : Shape} {a : AtT} (hwf : AtTWellFormed shape a) (c : Commitment) :
    (∀ r ∈ a.relations, r.commitment = c → ∀ t ∈ r.terms, t.column.commitment = c) ∧
    ∀ r ∈ a.relations, r.commitment = c → ∀ t ∈ r.terms,
      ReadsOwnPoint (layoutIn (layouts shape a.c2Columns) c) (pointsOn a.relations c) t.column t.point := by
  obtain ⟨hone, hcov, hslot⟩ := hwf
  refine ⟨fun r hr hc t ht ↦ (hone r hr t ht).trans hc, fun r hr hc t ht ↦ ?_⟩
  have htc : t.column.commitment = c := (hone r hr t ht).trans hc
  by_cases hs : ∃ j, t.column = .qflockSlot j
  · obtain ⟨j, hj⟩ := hs
    have hc1 : c = .c1 := by rw [← htc, hj]; rfl
    subst hc1
    rw [hj]
    exact fun q hq hpq ↦ hslot r hr t ht j hj q hq hpq
  · have hs' : ∀ j, t.column ≠ .qflockSlot j := fun j h ↦ hs ⟨j, h⟩
    rw [readsOwnPoint_generic hs']
    intro b hb
    rw [← htc] at hb
    exact hcov r hr t ht b hb

/-- **The combined claims the prover hands the batch hold whenever the relations do** (`proveStreamWith`'s
`combined`, on the layouts `layouts shape a.c2Columns` the batch reads them at), for well-formed relations. -/
theorem atT_combined_hold (shape : Shape) (a : AtT) (stackOf : Commitment → Array K) (rho : E)
    (hwf : AtTWellFormed shape a)
    (hholds : ∀ r ∈ a.relations, Relation.Holds (layoutIn (layouts shape a.c2Columns)) stackOf a.ringMap r) :
    ∀ p ∈ commitments.filterMap (fun c ↦ (combine a.relations c rho).map (c, ·)),
      Combined.Holds (layoutIn (layouts shape a.c2Columns) p.1) (stackOf p.1) a.ringMap p.2 := by
  intro p hp
  obtain ⟨c, -, hc⟩ := List.mem_filterMap.mp hp
  cases h : combine a.relations c rho with
  | none => rw [h] at hc; exact absurd hc (by simp)
  | some claim =>
    rw [h] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨hon, hreads⟩ := atTWellFormed_readsOwn hwf c
    exact combine_holds_of_relations a.relations c rho (layoutIn (layouts shape a.c2Columns)) stackOf a.ringMap
      claim hon (fun r hr _ ↦ hholds r hr) hreads h

end UniComplete

/-- info: 'UniComplete.dotK_denseWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.dotK_denseWeight

/-- info: 'UniComplete.denseWeight_getD_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.denseWeight_getD_eq_sum

/-- info: 'UniComplete.combine_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.combine_holds

/-- info: 'UniComplete.combine_holds_of_relations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.combine_holds_of_relations

/-- info: 'UniComplete.atT_combined_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.atT_combined_hold
