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

end UniComplete

/-- info: 'UniComplete.dotK_denseWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.dotK_denseWeight
