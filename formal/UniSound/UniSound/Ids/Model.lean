-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The identities are
-- `crates/leanvm_univariate/SPEC.md` §5–§6 and `formal/UniStatement`'s `constraintRelation`,
-- `heapRelations`, `batch`.
import UniSound.Ids.Rels
import UniSound.Mle

/-!
# The identity model's data

What `BusModel` and `UniIdsRest` are made of, for a deployment `D` and Flock's phase `Fl` (the proofs
are elsewhere):

* **the relations' differences** (`diffsOf`): each commitment's relations (`relsOf`, in `combine`'s
  order), each evaluated on its candidate stack the way the batch reads it — a term's weight on the
  batch's cube (`termW`, `weightAt` of the term alone) at the point `combine` merges its point into
  (`mergedPoint`), against the stack zero-extended (`stE`) — plus its value; and the pending matrices'
  sum plus its claim;
* **the batch** (`prodOf`, `targetOf`): `Σ_{k<3} λ^k W_k C_k + λ³ G L` over the batch's `V`
  variables, `W_k` the combined claim's weight (`weightAt`) at the cube's points, and its target
  `Σ_k λ^k v_k + λ³ claim`, as `batch` computes them;
* **the identities as polynomials in `t`** (`polysOf`): the tree, the root, the constraint quotient's
  identity (times `Z_bad`, below), and each heap block's leaf identity, each read off the committed
  columns by `colPoly` (a column's claim at a polynomial point);
* **the heap read off `C1`** (`hdOf`, `Heap.HeapData`): the memory's, the bytecode's and each table's
  blocks (a table's active rows, `isActive`, with their flushes' tuples, `tupleK` of the forms on the
  row's values, `c1Val`), the unused blocks, the state boundary;
* **the constraint vectors** (`cvecOf`): each row's `M_i(ω_x) W_i(ω_x)`, the constraint quotient's
  numerator's terms on the domain.

**Out of range** (a row count above `2^h`, which the verifier's range checks reject), the model is
degenerate: the constraint vectors hold a `1` and the identities a nonzero constant, so the states are
false from round `0` on. Likewise, if Flock's result is not the main line's (a ring end, its point of
`8 + κ` coordinates, its pending rounds within the batch's), the differences are a nonzero constant.

**`Z_bad`.** `combine` merges a point that is a prefix of a longer one into that one (a column reads
only as many of its point's coordinates as it has variables). `q_flock`'s slot view reads its whole
point, `8 + |y|` coordinates (`weightAt`'s `.qflockSlot` case): if `y(t)` were a strict prefix of a
longer `C1` point (`w(t)` cut at `21`, Flock's point), the batch would weigh the copies' slots wrongly.
Every longer `C1` point starts with `t` or with Flock's first coordinate, so this needs
`y_0(t) ∈ {t, p_0}`, the roots of `Z_bad = (y_0 + X)(y_0 + p_0)`; the constraint identity is stated
times `Z_bad`, which costs `2^(h_B)` in its degree and nothing in the polynomial's vanishing.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Polynomial Finset

/-! ## Layouts, challenges, the inputs of the relations -/

/-- A commitment's stack layout at a shape (`layoutsOf`, as `batch` finds it). -/
def layoutOf (S : Shape) (c : Commitment) : StackLayout :=
  (((layoutsOf S).find? (·.1 == c)).map (·.2)).getD default

/-- **The batch's variables**: the longest stack's (`batch`'s `vars`). -/
def batchVars (S : Shape) : ℕ := ((layoutsOf S).map (·.2.vars)).foldl max 0

/-- The tuple weights' point `α`, as the verifier samples it (round `0`'s first four challenges). -/
def alphasOf (ch : List E) : List E := (List.range 4).map fun i ↦ ch.getD i 0

/-- `β`, round `0`'s fifth challenge. -/
def betaOf (ch : List E) : E := ch.getD 4 0

/-- `γ`, round `0`'s sixth challenge. -/
def gammaOf (ch : List E) : E := ch.getD 5 0

/-- Each table's count bits `0..=r` (`countBits`). -/
def countsOf (S : Shape) (rows : List ℕ) : List (List E) :=
  (rows.zip S.heights).map fun p ↦ (List.range (p.2 + 1)).map fun b ↦ intBits p.1 b 1

/-- Flock's result: its point, its end, its pending reduction. -/
abbrev FlockOut := List E × Option Flock.End × Flock.Pending

/-- **The relations' inputs** at a statement, round `0`'s challenges, Flock's result, `t`, the values. -/
def relInput (D : Deployment) (s : USt) (ch : List E) (fl : FlockOut) (t : E) (vals : List E) :
    RelInput :=
  ⟨D.shape, publicWordsOf s.1.toList, countsOf D.shape s.2, alphasOf ch, betaOf ch, gammaOf ch, fl.1,
    fl.2.1, t, vals⟩

/-- **The counts the verifier accepts** (`readCounts`' range checks): six, each at most `2^h`. -/
def CountsFit (S : Shape) (rows : List ℕ) : Prop :=
  rows.length = 6 ∧ ∀ j < 6, rows.getD j 0 ≤ 2 ^ S.heights.getD j 0

/-- **Flock's result is the main line's**: a ring end, a point of `q_flock`'s `8 + κ` coordinates, the
pending reduction's rounds within the batch's `V`. -/
def FlockGood (κ V : ℕ) (fl : FlockOut) : Prop :=
  (∃ map target, fl.2.1 = some (.ring map target)) ∧ fl.1.length = 8 + κ ∧ fl.2.2.rounds ≤ V

/-! ## A relation's difference on a stack -/

/-- **A term's weight at the batch's cube point `u`** (`weightAt` of the term alone, coefficient `1`). -/
def termW (L : StackLayout) (ringMap : Option (List E)) (V : ℕ) (column : Column) (pt : List E)
    (twist : ℕ) (u : ℕ) : E :=
  weightAt ⟨[pt], [(column, 0, twist, 1)], 0, 1⟩ L (bitsE u V) ringMap

/-- **A stack, zero-extended** past its `2^vars` words (the batch's `C_k`). -/
def stE (C : Stk) (vars u : ℕ) : E := if u < 2 ^ vars then ofK (C u) else 0

/-- `combine`'s points: every term's point, each once, in order of first use. -/
def combinePoints (rels : List Relation) : Array (List E) :=
  rels.foldl (fun points r ↦ r.terms.foldl (fun points tm ↦
    match points.findIdx? (· == tm.point) with
    | some _ => points
    | none => points.push tm.point) points) #[]

/-- **The point `combine` reads a term at `p` with**: of the points having `p` as a prefix, the longest
(`longestOf`). -/
def mergedPoint (rels : List Relation) (p : List E) : List E :=
  (combinePoints rels).getD
    (longestOf (combinePoints rels) (((combinePoints rels).findIdx? (· == p)).getD 0)) []

/-- **A relation's difference**: `Σ terms + value`, each term its coefficient times its weight's inner
product with the stack, at its merged point. -/
noncomputable def relDiff (L : StackLayout) (ringMap : Option (List E)) (V : ℕ) (C : Stk)
    (mp : List E → List E) (r : Relation) : E :=
  (r.terms.map fun tm ↦ tm.coefficient *
    ∑ u ∈ range (2 ^ V), termW L ringMap V tm.column (mp tm.point) tm.twist u * stE C L.vars u).sum +
    r.value

/-- The pending matrices' difference: their sum over the batch's cube plus their claim. -/
noncomputable def pendDiff (p : Flock.Pending) (V : ℕ) : E :=
  ∑ u ∈ range (2 ^ V), Pending.Gext p u * Pending.Llift p u + p.claim

section Model

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ)

/-- The relations at a statement, round `0`'s challenges, Flock's transcript, `t` and the values. -/
def relsAt (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) : List Relation :=
  relsOf (relInput D s ch (Fl.prog.out fd []) t vals)

/-- The ring map of Flock's end. -/
def ringMapAt (fd : Done) : Option (List E) :=
  match (Fl.prog.out fd []).2.1 with
  | some (.ring mp _) => some mp
  | _ => none

open Classical in
/-- **The relations' differences** (`UniIdsRest.diffs`): per commitment (`C1`, `C2`, the setup) its
relations' differences, then the pending matrices'. -/
noncomputable def diffsOf (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) : List (List E) :=
  if CountsFit D.shape s.2 ∧ FlockGood κ (batchVars D.shape) (Fl.prog.out fd []) then
    (commitments.map fun c ↦ (mine (relsAt D Fl s ch fd t vals) c).map
      (relDiff (layoutOf D.shape c) (ringMapAt Fl fd) (batchVars D.shape) (stackFor D c1 c2 c)
        (mergedPoint (mine (relsAt D Fl s ch fd t vals) c)))) ++
      [[pendDiff (Fl.prog.out fd []).2.2 (batchVars D.shape)]]
  else [[1]]

/-- The commitment of the batch's `k`-th product. -/
def cm (k : ℕ) : Commitment := commitments.getD k .c1

/-- A commitment's combined claim. -/
def combAt (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (ρ : E) (c : Commitment) :
    Combined :=
  (combine (relsAt D Fl s ch fd t vals) c ρ).getD default

open Classical in
/-- **The batch** (`UniIdsRest.prod`): `Σ_{k<3} λ^k W_k C_k + λ³ G L` over the batch's variables. -/
noncomputable def prodOf (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) (ρ l : E) : ProdSum :=
  if CountsFit D.shape s.2 ∧ FlockGood κ (batchVars D.shape) (Fl.prog.out fd []) then
    { vars := batchVars D.shape
      n := 4
      coef := fun k ↦ l ^ k
      A := fun k u ↦ if k < 3 then
          weightAt (combAt D Fl s ch fd t vals ρ (cm k)) (layoutOf D.shape (cm k))
            (bitsE u (batchVars D.shape)) (ringMapAt Fl fd)
        else Pending.Gext (Fl.prog.out fd []).2.2 u
      B := fun k u ↦ if k < 3 then
          stE (stackFor D c1 c2 (cm k)) (layoutOf D.shape (cm k)).vars u
        else Pending.Llift (Fl.prog.out fd []).2.2 u }
  else { vars := batchVars D.shape, n := 0, coef := fun _ ↦ 0, A := fun _ _ ↦ 0, B := fun _ _ ↦ 0 }

open Classical in
/-- **The batch's target** (`UniIdsRest.target`): `Σ_{k<3} λ^k v_k + λ³ claim`. -/
noncomputable def targetOf (s : USt) (_c1 : Stk) (ch : List E) (fd : Done) (_c2 : Stk) (t : E)
    (vals : List E) (ρ l : E) : E :=
  if CountsFit D.shape s.2 ∧ FlockGood κ (batchVars D.shape) (Fl.prog.out fd []) then
    ∑ k ∈ range 3, l ^ k * (combAt D Fl s ch fd t vals ρ (cm k)).value +
      l ^ 3 * (Fl.prog.out fd []).2.2.claim
  else 1

end Model

/-! ## Columns as polynomials -/

/-- `weightAt`'s limb scale: `1, y, y²`. -/
def limbScale (limb : ℕ) : E := if limb = 0 then 1 else limbBasis.getD limb 0

/-- The aligned block a selector picks: the offset's bits from `v` to `V`. -/
def blockBase (off v V : ℕ) : ℕ := off % 2 ^ V / 2 ^ v * 2 ^ v

/-- **A column's polynomial on a stack**, its claim at the polynomial point `pt`: limb by limb, the
block's words (zero-extended) at the multilinear point `pt`. -/
noncomputable def colPoly (L : StackLayout) (V : ℕ) (C : Stk) (column : Column)
    (pt : ℕ → Polynomial E) : Polynomial E :=
  ((L.limbs column).map fun b ↦
    Polynomial.C (limbScale b.1) * mlP (fun x ↦ stE C L.vars (blockBase b.2.2 b.2.1 V + x)) b.2.1 pt).sum

/-- A form as a polynomial in its columns' polynomials (monomials of degree at most two, as
`linearise` reads them). -/
noncomputable def formP (f : Form) (cols : ℕ → Polynomial E) : Polynomial E :=
  (f.map fun mc ↦ match mc.1 with
    | [] => C mc.2
    | [i] => C mc.2 * cols i
    | [i, j] => C mc.2 * cols i * cols j
    | _ => 0).sum

/-- A tuple's fingerprint without `β`: `Σ_s eq(α, s) τ_s`. -/
noncomputable def tupleP (tuple : List Form) (weights : Array E) (cols : ℕ → Polynomial E) :
    Polynomial E :=
  ((tuple.zip (List.range tuple.length)).map fun p ↦ C (weights.getD p.2 0) * formP p.1 cols).sum

/-- A table's pull product `Π_j (β + fp_j)`. -/
noncomputable def pullP (tab : Table) (weights : Array E) (beta : E) (cols : ℕ → Polynomial E) :
    Polynomial E :=
  ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ C beta + tupleP fl.1 weights cols).prod

/-- A table's push product `Π_j (β + fp'_j)`. -/
noncomputable def pushP (tab : Table) (weights : Array E) (beta : E) (cols : ℕ → Polynomial E) :
    Polynomial E :=
  ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ C beta + tupleP fl.2 weights cols).prod

/-- **`Z_act` as a polynomial** (`activeVanishingFromBits`, F1b). -/
noncomputable def zActP (bits : List E) (r : ℕ) : Polynomial E :=
  (List.range r).foldl (fun prod b ↦
    prod * (1 + C (bits.getD b 0) * (digitP b + C (cosetOffset r b + 1))))
    (1 + C (bits.getD r 0) * (digitP r + 1))

/-- `w_m / w_r = Π_{j=r}^{m−1} (w_j + 1)` (`vanishingRatio`). -/
noncomputable def liftP (r m : ℕ) : Polynomial E :=
  ((List.range' r (m - r)).map fun j ↦ digitP j + 1).prod

/-- The coordinate functional `y_l(X) = Σ_m a_{l,m} X^(2^m)` (`coordinatesAt`). -/
noncomputable def yP (a : Array (Array K)) (l : ℕ) : Polynomial E :=
  ((List.range a.size).map fun m ↦ C (ofK ((a.getD l #[]).getD m 0)) * X ^ (2 ^ m)).sum

section Polys

variable (S : Shape) (c1 c2 setup : Stk)

/-- A `C1` column at the digits. -/
noncomputable def c1P (column : Column) : Polynomial E :=
  colPoly (layoutOf S .c1) (batchVars S) c1 column digitP

/-- A `C2` column at a polynomial point. -/
noncomputable def c2P (column : Column) (pt : ℕ → Polynomial E) : Polynomial E :=
  colPoly (layoutOf S .c2) (batchVars S) c2 column pt

/-- A setup column at a polynomial point. -/
noncomputable def suP (column : Column) (pt : ℕ → Polynomial E) : Polynomial E :=
  colPoly (layoutOf S .setup) (batchVars S) setup column pt

/-- A quotient's polynomial from its chunks: `Q_0 + w_{e_0}(Q_1 + w_{e_1}(Q_2 …))` (`quotientTerms`). -/
noncomputable def quotP (column : ℕ → Column) (sizes : List ℕ) : Polynomial E :=
  ((List.range sizes.length).map fun c ↦
    c2P S c2 (column c) digitP * ((List.range c).map fun c' ↦ digitP (sizes.getD c' 0)).prod).sum

/-- `q_flock`'s slot `j` at `y(X)`: its claim at `(bits(j), y(X))`. -/
noncomputable def slotP (slot : ℕ) : Polynomial E :=
  colPoly (layoutOf S .c1) (batchVars S) c1 .qflock fun l ↦
    if l < 8 then C (bitE slot l) else yP (coordinateFunctionals (S.heights.getD opBlake2s 0)) (l - 8)

/-- The public lines (`constraintRelation`): limb `k`'s cells `0, 1`. -/
def linesOf (pw : List E) : List (E × E) :=
  [(pw.getD 0 0, pw.getD 2 0), (pw.getD 1 0, pw.getD 3 0), (0, 0)]

/-- **The constraints** `(M_i, W_i)` (`constraintRelation`'s, in its order): per table, `JUMP`'s two,
the counters' `z Π c + 1`, `BLAKE2S`'s copies `copy_c + slot(y)`; then the public lines; each `W_i` on
its table's domain, `M_i` its lift to `V_{r_W}`. -/
noncomputable def constraintsP (pw : List E) : List (Polynomial E × Polynomial E) :=
  (tables.flatMap fun tab ↦
    let o := tab.opcode
    let lift := liftP (S.heights.getD o 0) S.constraintVars
    let col (n : String) : Polynomial E := c1P S c1 (.table o (colIdx tab.columns n))
    (if o = opJump then
      [(lift, col "b" + col "v_cond" * col "w"), (lift, col "v_cond" * (col "b" + 1))] else []) ++
    [(lift, c1P S c1 (.inverse o) * (tab.countColumns.map fun c ↦ c1P S c1 (.table o c)).prod + 1)] ++
    (if o = opBlake2s then (List.range tab.width).filterMap fun c ↦
      (qflockSlot (tab.columns.getD c "")).map fun slot ↦ (lift, c1P S c1 (.table o c) + slotP S c1 slot)
     else [])) ++
  ((linesOf pw).zip (List.range 3)).map fun lk ↦
    (liftP 1 S.constraintVars, c1P S c1 (.memory lk.2) + C lk.1.1 + X * C (lk.1.1 + lk.1.2))

/-- **`Z_bad`**: `(y_0 + X)(y_0 + p_0)`, `p_0` Flock's point's first coordinate. -/
noncomputable def zBad (p0 : E) : Polynomial E :=
  (yP (coordinateFunctionals (S.heights.getD opBlake2s 0)) 0 + X) *
    (yP (coordinateFunctionals (S.heights.getD opBlake2s 0)) 0 + C p0)

/-- **The constraint quotient's identity** (step 5), times `Z_bad`:
`Z_bad (Σ_i γ^i M_i W_i + Q_W w_{r_W})`. -/
noncomputable def wP (pw : List E) (gamma p0 : E) : Polynomial E :=
  zBad S p0 * ((((constraintsP S c1 pw).zip (List.range (constraintsP S c1 pw).length)).map
      fun mw ↦ C (gamma ^ mw.2) * mw.1.1 * mw.1.2).sum +
    quotP S c2 Column.constraintQuotient (chunks (S.constraintDegree + 1)) * digitP S.constraintVars)

/-- **The tree's identity** (step 6): `w_1 (T(s(X)) + T(X) T(X + 1)) + w_h (Q_0 + w_h q_1)`. -/
noncomputable def treeP : Polynomial E :=
  digitP 1 * (c2P S c2 .heap (fun l ↦ digitP (l + 1)) +
      c2P S c2 .heap digitP * c2P S c2 .heap (fun l ↦ if l = 0 then digitP 0 + 1 else digitP l)) +
    digitP S.heap.h * (c2P S c2 (.treeQuotient 0) digitP +
      digitP S.heap.h * c2P S c2 (.treeQuotient 1) digitP)

/-- The state boundary's push and pull fingerprints (`heapRelations`' root). -/
def rootInit (weights : Array E) (beta : E) : E :=
  beta + weights.getD 0 0 * sepState + weights.getD 1 0 + weights.getD 2 0

def rootFin (S : Shape) (weights : Array E) (beta : E) : E :=
  beta + weights.getD 0 0 * sepState + weights.getD 1 0 * UniStatement.gpow (2 ^ S.logBytecode - 1) +
    weights.getD 2 0

/-- **The root's identity**: `T(1) fp(init) + fp(fin)`, a constant. -/
noncomputable def rootP (weights : Array E) (beta : E) : Polynomial E :=
  C (rootInit weights beta) * c2P S c2 .heap (fun l ↦ if l = 0 then 1 else 0) + C (rootFin S weights beta)

/-- A heap block's mixed point (SPEC §2's restriction): `w_l + ω_{pos >> l}` below `r`, `ω_{pos >> l}`
above. -/
noncomputable def mixP (b : Block) (l : ℕ) : Polynomial E :=
  if l < b.r then digitP l + C (pointE (b.position >>> l)) else C (pointE (b.position >>> l))

/-- The memory's pull fingerprint as a polynomial. -/
noncomputable def memPullP (weights : Array E) (beta : E) : Polynomial E :=
  C beta + C (weights.getD 0 0 * sepMem) + C (weights.getD 1 0) * suP S setup .address digitP +
    C (weights.getD 2 0) * c1P S c1 (.memory 3) +
    ((List.range 3).map fun k ↦ C (weights.getD (3 + k) 0) * c1P S c1 (.memory k)).sum

/-- The bytecode's pull fingerprint as a polynomial: the setup's 16 slots at `(α, X)`, the final count. -/
noncomputable def bcPullP (alphas : List E) (weights : Array E) (beta : E) : Polynomial E :=
  C beta + suP S setup .bytecodeTuple (fun l ↦ if l < 4 then C (alphas.getD l 0) else digitP (l - 4)) +
    C (weights.getD 2 0) * c1P S c1 .bytecodeFinal

/-- **A heap block's leaf identity** (step 6): a table's times `Z_act`,
`R (P w_r + Z²) + Q w_r Z + P' w_r + Z²`; the memory's and the bytecode's `R P + Q w_r + P'`; an unused
block's `R + 1`. -/
noncomputable def blockP (rows : List ℕ) (alphas : List E) (beta : E) (b : Block) (i : ℕ) :
    Polynomial E :=
  let weights := eqKernel alphas
  let R := c2P S c2 .heap (mixP b)
  let wr := digitP b.r
  let n := 2 ^ b.r
  match b.leaves with
  | .unused => R + 1
  | .memory =>
    R * memPullP S c1 setup weights beta +
      quotP S c2 (Column.leafQuotient i) (chunks (degree (2 * (n - 1)) n + 1)) * wr +
      (memPullP S c1 setup weights beta + C (weights.getD 2 0) * (1 + c1P S c1 (.memory 3)))
  | .bytecode =>
    R * bcPullP S c1 setup alphas weights beta +
      quotP S c2 (Column.leafQuotient i) (chunks (degree (2 * (n - 1)) n + 1)) * wr +
      (bcPullP S c1 setup alphas weights beta + C (weights.getD 2 0) * (1 + c1P S c1 .bytecodeFinal))
  | .table t =>
    let tab := tables.getD t default
    let cols (c : ℕ) : Polynomial E := c1P S c1 (.table tab.opcode c)
    let Z := zActP ((List.range (b.r + 1)).map fun j ↦ intBits (rows.getD t 0) j 1) b.r
    let d := degree (max (tableDegrees tab).1 (tableDegrees tab).2 * (n - 1) + (n - Shape.leastRows b.r)) n
    R * (pullP tab weights beta cols * wr + Z ^ 2) +
      quotP S c2 (Column.leafQuotient i) (chunks (d + 1)) * (wr * Z) +
      pushP tab weights beta cols * wr + Z ^ 2

end Polys

open Classical in
/-- **The identities as polynomials in `t`** (`UniIdsRest.polys`): the tree, the root, the constraint
quotient's (times `Z_bad`), every heap block's leaf identity; a nonzero constant out of range. -/
noncomputable def polysOf (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (s : USt) (c1 : Stk)
    (ch : List E) (fd : Done) (c2 : Stk) : List (Polynomial E) :=
  if CountsFit D.shape s.2 then
    [treeP D.shape c2, rootP D.shape c2 (eqKernel (alphasOf ch)) (betaOf ch),
      wP D.shape c1 c2 (publicWordsOf s.1.toList) (gammaOf ch) ((Fl.prog.out fd []).1.getD 0 0)] ++
    (D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)).map fun bi ↦
      blockP D.shape c1 c2 (stackFor D c1 c2 .setup) s.2 (alphasOf ch) (betaOf ch) bi.1 bi.2
  else [1]

/-! ## The heap read off `C1`, the constraint vectors -/

/-- An element's base limb (`K`'s part). -/
def toK (e : E) : K := e.limb 0

/-- A form at a row of `K` values (its coefficients read in `K`). -/
def formK (f : Form) (row : ℕ → K) : K :=
  (f.map fun mc ↦ match mc.1 with
    | [] => toK mc.2
    | [i] => toK mc.2 * row i
    | [i, j] => toK mc.2 * row i * row j
    | _ => 0).sum

/-- A tuple at a row, as a bus tuple of sixteen coordinates. -/
def tupleK (tuple : List Form) (row : ℕ → K) : Vector K 16 :=
  Vector.ofFn fun s ↦ formK (tuple.getD s.val []) row

section Heap

variable (D : Deployment) (c : Stk)

/-- **A `C1` column's value at row `x`** (basis `B` at `vars` variables), as `lv42Column` reads it. -/
def c1Val (column : Column) (vars x : ℕ) : K := basisValue (c1Block (c1Layout D.shape) c column) vars x

/-- The setup stack, word by word. -/
def setupStk : Stk := fun i ↦ (setupStack D.prog D.shape).getD i 0

/-- A setup column's value at row `x`. -/
def suVal (column : Column) (vars x : ℕ) : K :=
  basisValue (c1Block (setupLayout D.shape) (setupStk D) column) vars x

/-- The setup's bytecode tuples' offset. -/
def tupleOff : ℕ := (((setupLayout D.shape).limbs .bytecodeTuple).headD (0, 0, 0)).2.2

/-- The setup's bytecode slot `s` at instruction `x` (slot `s` of coefficient `k` at word `s + 16 k`). -/
def slotVal (s x : ℕ) : K :=
  basisValue (Array.ofFn (n := 2 ^ D.shape.logBytecode) fun k ↦ setupStk D (tupleOff D + s + 16 * k.val))
    D.shape.logBytecode x

/-- Table `o`'s row `x` of `C1`, as values. -/
def c1Row (o x : ℕ) : ℕ → K := fun i ↦ c1Val D c (.table o i) (D.shape.heights.getD o 0) x

/-- A table's block of leaves on `C1`: its active rows (`isActive`) with their flushes' tuples. -/
def tableBlockK (rows : List ℕ) (b : Block) (o : ℕ) : Heap.LeafBlock (Vector K 16) where
  r := b.r
  push x := if isActive x (rows.getD o 0) b.r then
      (tables.getD o default).flushes.push.map fun tup ↦ tupleK tup (c1Row D c o x) else []
  pull x := if isActive x (rows.getD o 0) b.r then
      (tables.getD o default).flushes.pull.map fun tup ↦ tupleK tup (c1Row D c o x) else []

/-- The memory's tuple of cell `x` with count `cnt`: `(SEP_MEM, g^x, cnt, m_0, m_1, m_2)`. -/
def memTupleK (cnt : K) (x : ℕ) : Vector K 16 :=
  Vector.ofFn fun s ↦
    if s.val = 0 then toK sepMem
    else if s.val = 1 then suVal D .address D.shape.logMemory x
    else if s.val = 2 then cnt
    else if s.val < 6 then c1Val D c (.memory (s.val - 3)) D.shape.logMemory x
    else 0

/-- The bytecode's tuple of instruction `x`: the setup's slots, the count added in slot `2`. -/
def bcTupleK (cnt : K) (x : ℕ) : Vector K 16 :=
  Vector.ofFn fun s ↦ slotVal D s.val x + if s.val = 2 then cnt else 0

/-- **A heap block's leaves read off `C1`.** -/
def blockK (rows : List ℕ) (b : Block) : Heap.LeafBlock (Vector K 16) :=
  match b.leaves with
  | .memory => Heap.LeafBlock.pair b.r (memTupleK D c 1)
      (fun x ↦ memTupleK D c (c1Val D c (.memory 3) D.shape.logMemory x) x)
  | .bytecode => Heap.LeafBlock.pair b.r (bcTupleK D 1)
      (fun x ↦ bcTupleK D (c1Val D c .bytecodeFinal D.shape.logBytecode x) x)
  | .table t => tableBlockK D c rows b t
  | .unused => Heap.LeafBlock.unused b.r

/-- The state boundary's push `(SEP_STATE, 1, 1)`. -/
def initK : Vector K 16 := Vector.ofFn fun s ↦ if s.val < 3 then 1 else 0

/-- The state boundary's pull `(SEP_STATE, g^(2^lb − 1), 1)`. -/
def finK : Vector K 16 :=
  Vector.ofFn fun s ↦ if s.val = 1 then toK (UniStatement.gpow (2 ^ D.shape.logBytecode - 1))
    else if s.val < 3 then 1 else 0

/-- **The heap the verifier reads off `C1`** (`BusModel.hd`). -/
def hdOf (s : USt) : Heap.HeapData :=
  ⟨D.shape.heap.h, D.shape.heap.blocks.map (blockK D c s.2), initK, finK D⟩

open Classical in
/-- **The constraint vectors** (`BusModel.cvec`): row `x`'s `M_i(ω_x) W_i(ω_x)`; a `1` out of range. -/
noncomputable def cvecOf (s : USt) (x : ℕ) : List E :=
  if CountsFit D.shape s.2 then
    (constraintsP D.shape c (publicWordsOf s.1.toList)).map fun mw ↦ (mw.1 * mw.2).eval (pointE x)
  else [1]

/-- `q_flock`'s offset in `C1`. -/
def qfOff : ℕ := (((c1Layout D.shape).limbs .qflock).headD (0, 0, 0)).2.2

/-- **`C1`'s column `q_flock`** (`BusModel.qf`). -/
def qfOf (κ : ℕ) : LeanVM.Protocol.Column (8 + κ) :=
  ⟨Vector.ofFn fun x ↦ c (qfOff D + x.val)⟩

/-- **The limb copies hold** (`BusModel.Copies`): the counts in range, and on every `BLAKE2S` row of
`C1` each limb's copy is `q_flock`'s slot. -/
def CopiesOf (s : USt) : Prop :=
  CountsFit D.shape s.2 ∧
    ∀ x < 2 ^ D.shape.heights.getD opBlake2s 0, ∀ col slot,
      qflockSlot (blake2sColumns.getD col "") = some slot →
        c1Val D c (.table opBlake2s col) (D.shape.heights.getD opBlake2s 0) x =
          c (qfOff D + slot + 256 * x)

end Heap

end UniSound.Ids
