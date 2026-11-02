-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Model

/-!
# The bridges the identity model rests on, stated

Each is a `Prop` about the verifier's definitions (`formal/UniStatement`), Lv42's, or the deployment's
constants; `UniSound.Ids.Build` constructs `BusModel` and `UniIdsRest` from them, and the files named
below prove them (a bridge not yet proved is a hypothesis of the construction, by this name).

* **The batch's algebra** (`Weights.lean`): `weightAt` is linear in its terms (`WeightAtLinear`);
  `combine` is the `ρ`-combination at the merged points (`CombineEq`); a term's weight on the cube
  against a zero-extended stack is its claim on the column's blocks (`TermInner`, `SlotInner`,
  `RingInner`); merging a point into a longer one changes no column's weight but `q_flock`'s slot
  view's (`MergedPrefix`, `MergedSelf`, `TermWExtend`).
* **The tower** (`Tower.lean`): the ring-switch weight in tower order is `Σ_k d_k eq(φ^k(p), r)`
  (`TowerWeight`).
* **The deployment's constants** (`Deployed.lean`): the verifier's basis is Cantor on its first `24`
  vectors (`BetaCantor`), its coordinate functionals invert the Moore matrix at `BLAKE2S`'s height
  (`FunctionalsCorrect`), the stack layouts place each block aligned inside the stack and each `C1` and
  setup column as one limb (`LayoutAligned`, `C1Limbs`, `SetupLimbs`), the heap's blocks fill the
  leaves end to end, aligned (`HeapGood`), the setup's basis-`B` coefficients are its values'
  (`BasisValueInv`).
* **Lv42** (`BusLink.lean`): the constraints on `C1`'s rows give Lv42's `ConstraintsVanish`,
  `CountsNonzero`, `PublicLinesHold` (`LvConstraints`); the heap read off `C1` realizes Lv42's bus where
  the copies hold (`LvRealizes`); Flock's predicate on `q_flock` is Lv42's region's (`LvAux`); the bus
  counts (`LvBusCount`).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset

/-! ## The batch's algebra -/

/-- **`weightAt` is linear in its claim's terms**: the sum of each term's coefficient times the weight
of the term alone at its point. -/
def WeightAtLinear : Prop :=
  ∀ (claim : Combined) (L : StackLayout) (r : List E) (rm : Option (List E)),
    weightAt claim L r rm = (claim.terms.map fun tm ↦
      tm.2.2.2 * weightAt ⟨[claim.points.getD tm.2.1 []], [(tm.1, 0, tm.2.2.1, 1)], 0, 1⟩ L r rm).sum

/-- **`combine` is the `ρ`-combination**: where the commitment has relations, its claim's value is
`Σ_i ρ^i v_i`, and every additive reading `F` of its terms at their points is `Σ_i ρ^i` of the
relations' terms read at their merged points (`mergedPoint`). -/
def CombineEq : Prop :=
  ∀ (rels : List Relation) (c : Commitment) (ρ : E), mine rels c ≠ [] →
    ∃ cb, combine rels c ρ = some cb ∧
      cb.value = ((mine rels c).zipIdx.map fun ri ↦ ρ ^ ri.2 * ri.1.value).sum ∧
      ∀ F : Column → List E → ℕ → E,
        (cb.terms.map fun tm ↦ tm.2.2.2 * F tm.1 (cb.points.getD tm.2.1 []) tm.2.2.1).sum =
          ((mine rels c).zipIdx.map fun ri ↦ ρ ^ ri.2 * (ri.1.terms.map fun tm ↦
            tm.coefficient * F tm.column (mergedPoint (mine rels c) tm.point) tm.twist).sum).sum

/-- **A column's term on the cube** (not `q_flock`'s slot view, untwisted): its weight against the
zero-extended stack is its claim on the column's blocks, each at the selector's aligned block. -/
def TermInner : Prop :=
  ∀ (L : StackLayout) (rm : Option (List E)) (V : ℕ) (C : Stk) (col : Column) (pt : List E),
    (∀ j, col ≠ .qflockSlot j) → (∀ b ∈ L.limbs col, b.2.1 ≤ V) →
      ∑ u ∈ range (2 ^ V), termW L rm V col pt 0 u * stE C L.vars u =
        ((L.limbs col).map fun b ↦ limbScale b.1 *
          ∑ x ∈ range (2 ^ b.2.1), cubeEq pt b.2.1 x * stE C L.vars (blockBase b.2.2 b.2.1 V + x)).sum

/-- **`q_flock`'s slot `j` on the cube**: its claim on `q_flock`'s blocks at `(bits(j), pt)`. -/
def SlotInner : Prop :=
  ∀ (L : StackLayout) (rm : Option (List E)) (V : ℕ) (C : Stk) (j : ℕ) (pt : List E),
    (∀ b ∈ L.limbs .qflock, b.2.1 = 8 + pt.length ∧ b.2.1 ≤ V) →
      ∑ u ∈ range (2 ^ V), termW L rm V (.qflockSlot j) pt 0 u * stE C L.vars u =
        ((L.limbs .qflock).map fun b ↦ limbScale b.1 *
          ∑ x ∈ range (2 ^ b.2.1), cubeEq ((List.range 8).map (bitE j) ++ pt) b.2.1 x *
            stE C L.vars (blockBase b.2.2 b.2.1 V + x)).sum

/-- **The ring-switch term on the cube** (twist `ringTwist`): the tower weight at the cube's points of
each block. -/
def RingInner : Prop :=
  ∀ (L : StackLayout) (map : List E) (V : ℕ) (C : Stk) (pt : List E),
    (∀ b ∈ L.limbs .qflock, b.2.1 ≤ V) →
      ∑ u ∈ range (2 ^ V), termW L (some map) V .qflock pt ringTwist u * stE C L.vars u =
        ((L.limbs .qflock).map fun b ↦ limbScale b.1 *
          ∑ x ∈ range (2 ^ b.2.1), Flock.towerWeightAt (pt.take b.2.1)
            ((bitsE x b.2.1).map (1 + ·)) map * stE C L.vars (blockBase b.2.2 b.2.1 V + x)).sum

/-- **A merged point extends the point** and is a term's point. -/
def MergedPrefix : Prop :=
  ∀ (rels : List Relation) (p : List E), (∃ r ∈ rels, ∃ tm ∈ r.terms, tm.point = p) →
    (mergedPoint rels p).take p.length = p ∧ ∃ r ∈ rels, ∃ tm ∈ r.terms, tm.point = mergedPoint rels p

/-- **A point no longer point extends is not merged.** -/
def MergedSelf : Prop :=
  ∀ (rels : List Relation) (p : List E), (∃ r ∈ rels, ∃ tm ∈ r.terms, tm.point = p) →
    (∀ r ∈ rels, ∀ tm ∈ r.terms, p.length < tm.point.length → tm.point.take p.length ≠ p) →
      mergedPoint rels p = p

/-- **Merging changes no column's weight** but `q_flock`'s slot view's: a column of at most `p.length`
variables reads only `p`'s coordinates of any extension of `p`. -/
def TermWExtend : Prop :=
  ∀ (L : StackLayout) (rm : Option (List E)) (V : ℕ) (col : Column) (p q : List E) (twist u : ℕ),
    (∀ j, col ≠ .qflockSlot j) → (∀ b ∈ L.limbs col, b.2.1 ≤ p.length) → q.take p.length = p →
      termW L rm V col q twist u = termW L rm V col p twist u

/-! ## The tower -/

/-- **The ring-switch weight in tower order** (`ring_tower::weight_at`): `Φ(eq(p, ·))` at `r` is
`Σ_{k<64} d_k Π_n (1 + r_n + p_n^(2^k))`, `d = towerCoefficients map`. -/
def TowerWeight : Prop :=
  ∀ (p r map : List E), p.length = r.length →
    Flock.towerWeightAt p (r.map (1 + ·)) map =
      ∑ k ∈ range 64, (Flock.towerCoefficients map).getD k 0 *
        ∏ n ∈ range p.length, (1 + r.getD n 0 + sqn (p.getD n 0) k)

/-! ## The deployment's constants -/

/-- **The verifier's basis is Cantor** on its first `24` vectors: `β_0 = 1`, `s(β_{k+1}) = β_k`. -/
def BetaCantor : Prop :=
  beta.getD 0 0 = 1 ∧ ∀ k, k + 1 < 24 → sK (beta.getD (k + 1) 0) = beta.getD k 0

/-- **The coordinate functionals at height `r`** (`coordinateFunctionals r`, `r ≤ 24`): `r` rows of `r`,
and `y_l(β_k) = Σ_m a_{l,m} β_k^(2^m) = [l = k]`. -/
def FunctionalsCorrect (r : ℕ) : Prop :=
  (coordinateFunctionals r).size = r ∧
    ∀ l < r, ∀ k < r, ((List.range r).map fun m ↦
      ((coordinateFunctionals r).getD l #[]).getD m 0 * frobK (beta.getD k 0) m).sum =
        if l = k then 1 else 0

/-- **A layout's blocks are aligned inside its stack.** -/
def LayoutAligned (L : StackLayout) : Prop :=
  ∀ b ∈ L.blocks, 2 ^ b.2.2.1 ∣ b.2.2.2 ∧ b.2.2.2 + 2 ^ b.2.2.1 ≤ 2 ^ L.vars

/-- **`C1`'s columns are one limb each**, at their tables' heights (the tables' columns and `z_T`),
the memory's, the bytecode's, `q_flock`'s `h_B + 8`. -/
def C1Limbs (S : Shape) : Prop :=
  (∀ o < 6, ∀ i < (tables.getD o default).width, ∃ off,
      (layoutOf S .c1).limbs (.table o i) = [(0, S.heights.getD o 0, off)]) ∧
    (∀ o < 6, ∃ off, (layoutOf S .c1).limbs (.inverse o) = [(0, S.heights.getD o 0, off)]) ∧
    (∀ k < 4, ∃ off, (layoutOf S .c1).limbs (.memory k) = [(0, S.logMemory, off)]) ∧
    (∃ off, (layoutOf S .c1).limbs .bytecodeFinal = [(0, S.logBytecode, off)]) ∧
    (∃ off, (layoutOf S .c1).limbs .qflock = [(0, S.heights.getD opBlake2s 0 + 8, off)])

/-- **The setup's two columns are one limb each.** -/
def SetupLimbs (S : Shape) : Prop :=
  (∃ off, (layoutOf S .setup).limbs .address = [(0, S.logMemory, off)]) ∧
    ∃ off, (layoutOf S .setup).limbs .bytecodeTuple = [(0, S.logBytecode + 4, off)]

/-- **The heap's blocks** (`HeapLayout.new`): depth at most `24`, laid end to end from the first leaf
`2^(h−1)`, each aligned, filling the leaves; the memory's of `2^lm` leaves, the bytecode's of `2^lb`,
table `t`'s of `2^(h_t)`. -/
def HeapGood (S : Shape) : Prop :=
  1 ≤ S.heap.h ∧ S.heap.h ≤ 24 ∧
    (S.heap.blocks.map fun b ↦ 2 ^ b.r).sum = 2 ^ (S.heap.h - 1) ∧
    (∀ i < S.heap.blocks.length, (S.heap.blocks.getD i default).position =
      2 ^ (S.heap.h - 1) + ((S.heap.blocks.take i).map fun b ↦ 2 ^ b.r).sum) ∧
    (∀ b ∈ S.heap.blocks, 2 ^ b.r ∣ b.position) ∧
    (∀ b ∈ S.heap.blocks, match b.leaves with
      | .memory => b.r = S.logMemory
      | .bytecode => b.r = S.logBytecode
      | .table t => t < 6 ∧ b.r = S.heights.getD t 0
      | .unused => True)

/-- **The setup's basis-`B` coefficients are its values'** (`bCoefficients`, `basisValue`), `r ≤ 24`. -/
def BasisValueInv : Prop :=
  ∀ r ≤ 24, ∀ v : Array K, v.size = 2 ^ r → ∀ x < 2 ^ r, basisValue (bCoefficients r v) r x = v.getD x 0

/-! ## Lv42 -/

/-- **The constraints on `C1`'s rows, pointwise** (what the constraint quotient's identity gives on the
domain): `JUMP`'s two, the counters' inverse, the limb copies, the public lines. -/
structure RowConstraints (D : Deployment) (c : Stk) (s : USt) : Prop where
  jump : ∀ x < 2 ^ D.shape.heights.getD opJump 0,
    c1Val D c (.table opJump (colIdx jumpColumns "b")) (D.shape.heights.getD opJump 0) x +
        c1Val D c (.table opJump (colIdx jumpColumns "v_cond")) (D.shape.heights.getD opJump 0) x *
          c1Val D c (.table opJump (colIdx jumpColumns "w")) (D.shape.heights.getD opJump 0) x = 0 ∧
      c1Val D c (.table opJump (colIdx jumpColumns "v_cond")) (D.shape.heights.getD opJump 0) x *
          (c1Val D c (.table opJump (colIdx jumpColumns "b")) (D.shape.heights.getD opJump 0) x + 1) = 0
  counters : ∀ o < 6, ∀ x < 2 ^ D.shape.heights.getD o 0,
    c1Val D c (.inverse o) (D.shape.heights.getD o 0) x *
      ((tables.getD o default).countColumns.map fun j ↦
        c1Val D c (.table o j) (D.shape.heights.getD o 0) x).prod = 1
  copies : ∀ x < 2 ^ D.shape.heights.getD opBlake2s 0, ∀ col slot,
    qflockSlot (blake2sColumns.getD col "") = some slot →
      c1Val D c (.table opBlake2s col) (D.shape.heights.getD opBlake2s 0) x = c (qfOff D + slot + 256 * x)
  lines : ∀ k < 3,
    c1Val D c (.memory k) D.shape.logMemory 0 = toK ((linesOf (publicWordsOf s.1.toList)).getD k (0, 0)).1 ∧
      c1Val D c (.memory k) D.shape.logMemory 1 = toK ((linesOf (publicWordsOf s.1.toList)).getD k (0, 0)).2

/-- **Lv42's columns of `C1`'s Lv42 stack are `lv42Column`'s**: a committed column read back through
Lv42's layout (`M3Instance.column`) is the column `lv42Stack` stacked (`lv42Column`). -/
def LvReadBack (D : Deployment) : Prop :=
  ∀ (rows : List ℕ) (c : Stk) (col : Lv42.Protocol.LeanIsa.Col), ¬ Lv42.Protocol.LeanIsa.IsLimb col →
    ∀ x : Fin (2 ^ Lv42.Protocol.LeanIsa.kappa D.prog (D.sizes rows) col),
      ((D.inst rows).column (lv42Stack D.prog (D.sizes rows) D.shape c) col).values.get x =
        (lv42Column D.prog (D.sizes rows) D.shape c col).get x

/-- **The constraints on `C1`'s rows are Lv42's** `ConstraintsVanish`, `CountsNonzero`,
`PublicLinesHold` of `C1`'s Lv42 stack (`lv42Stack`, its rows through `rowPosition`). -/
def LvConstraints (D : Deployment) : Prop :=
  ∀ (s : USt) (c : Stk), CountsFit D.shape s.2 → RowConstraints D c s →
    (D.inst s.2).ConstraintsVanish (lv42Stack D.prog (D.sizes s.2) D.shape c) ∧
      (D.inst s.2).CountsNonzero (lv42Stack D.prog (D.sizes s.2) D.shape c) ∧
      (D.inst s.2).PublicLinesHold (publicInputOf s.1.toList) (lv42Stack D.prog (D.sizes s.2) D.shape c)

/-- **The heap read off `C1` realizes Lv42's bus** of `C1`'s Lv42 stack where the copies hold. -/
def LvRealizes (D : Deployment) : Prop :=
  ∀ (s : USt) (c : Stk), CopiesOf D c s →
    Heap.Realizes (I := D.inst s.2) (lv42Stack D.prog (D.sizes s.2) D.shape c) (hdOf D c s)

/-- **Flock's predicate on `C1`'s `q_flock` is Lv42's region's** (`aux`). -/
def LvAux (D : Deployment) : Prop :=
  ∀ (s : USt) (c : Stk), FlockHolds (D.shape.heights.getD opBlake2s 0)
    (qfOf D c (D.shape.heights.getD opBlake2s 0)) →
      (D.inst s.2).aux (lv42Stack D.prog (D.sizes s.2) D.shape c)

/-- **The bus counts** at counts in range: at most `N` tuples a side. -/
def LvBusCount (D : Deployment) (N : ℕ) : Prop :=
  ∀ rows : List ℕ, CountsFit D.shape rows →
    Heap.busCount (D.inst rows) .push ≤ N ∧ Heap.busCount (D.inst rows) .pull ≤ N

end UniSound.Ids
