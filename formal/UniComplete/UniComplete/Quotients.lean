-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `crates/leanvm_univariate/src/prover/quotients.rs`
-- (branch `leanvm-univariate-prover2`): the second commitment's quotients (SPEC.md §5.2, §6, §13), here as exact
-- polynomial divisions (the Rust divides on an extension coset and interpolates back).
import UniComplete.Bus

/-!
# The quotients, as exact polynomial divisions

Each quotient is its numerator, a polynomial built from the columns' polynomials, divided by the subspace polynomial
`w_r` of its domain (`divByMonic`, CompPoly's, Mathlib's `/ₘ` behind it):

* **the tree** (`treeQuotient`): `w_1 (T(s(X)) + T(X) T(X + 1)) / w_H`, `T(s(X))` and `T(X + 1)` from `T`'s novel
  coefficients (`X_k(s(x)) = X_{2k}(x)`; `X_k(x + 1) = X_k(x) + X_{k−1}(x)` for odd `k`);
* **a table's leaves** (`tableLeafQuotient`): `((R P + P') Z_pad + (R + 1) Z_act) / w_r` (the verifier checks it
  times `Z_act`), `Z_act`, `Z_pad` the products over the fixed cosets of the count's set and unset bits;
* **the memory's, the bytecode's leaves**: `(R D_fin + D_init) / w_r`;
* **the constraints** (`constraintQuotient`): `Σ_i γ^i M_i (w_{r_W} / w_r) / w_{r_W}`, in the verifier's order of
  powers: per table JUMP's two constraints, the counters `z Π c + 1`, BLAKE2S's copies `copy − ℓ`, then the public
  input's three lines.

A quotient's chunks (`chunksB`): its novel coefficients (`toNovel`) cut at the verifier's sizes (`chunks`), each
chunk in basis `B`.
-/

namespace UniComplete

open UniStatement LeanVM.Parameters

/-! ### Polynomial helpers -/

/-- `Π_{j ∈ [r, m)} (w_j + 1)`, the lift `w_m / w_r`. -/
def liftP (r m : ℕ) : Poly := (List.range' r (m - r)).foldl (fun acc j ↦ acc * (wPoly j + 1)) 1

/-- The vanishing polynomial of a coset factor `(b, a)`: `w_b + ω_a`. -/
def cosetP (b a : ℕ) : Poly := wPoly b + pC (pointE a)

/-- **`Z_act`** of a height-`r` table of `rows` rows (`active_factors`): `w_r` when full, else the product over
the set bits `b < r` of `w_b + ω_{2^(r−b) − 2}`. -/
def zActP (rows r : ℕ) : Poly :=
  if rows = 2 ^ r then wPoly r
  else (List.range r).foldl (fun acc b ↦ if rows.testBit b then acc * cosetP b (2 ^ (r - b) - 2) else acc) 1

/-- **`Z_pad`** (`padding_factors`): `1` when full, else the product over the unset bits `b < r` and the last row
`2^r − 1`. -/
def zPadP (rows r : ℕ) : Poly :=
  if rows = 2 ^ r then 1
  else (List.range r).foldl (fun acc b ↦ if rows.testBit b then acc else acc * cosetP b (2 ^ (r - b) - 2))
    (cosetP 0 (2 ^ r - 1))

/-- The multilinear extension of a table at a point of polynomials (low coordinate first). -/
def mleP (vals : Array Poly) (pt : List Poly) : Poly :=
  (pt.foldl (fun (cur : Array Poly) r ↦ Array.ofFn (n := cur.size / 2) fun i ↦
    let a := cur.getD (2 * i.val) 0
    let b := cur.getD (2 * i.val + 1) 0
    a + r * (a + b)) vals).getD 0 0

/-- `y_l(X) = Σ_m a_{l,m} X^(2^m)`, the coordinate functionals at the variable. -/
def coordinateP (functionals : Array (Array K)) (l : ℕ) : Poly :=
  ((functionals.getD l #[]).toList.zip (List.range (functionals.getD l #[]).size)).foldl
    (fun acc (a, mm) ↦ acc + pC (ofK a) * pX ^ (2 ^ mm)) 0

/-- The polynomial `T(s(X))` from `T`'s `2^h` novel coefficients: `X_k(s(x)) = X_{2k}(x)`. -/
def compSNovel (h : ℕ) (d : Array E) : Array E :=
  Array.ofFn (n := 2 ^ (h + 1)) fun j ↦ if j.val % 2 = 0 then d.getD (j.val / 2) 0 else 0

/-- `T(X + 1)` from `T`'s novel coefficients: coefficient `j` is `d_j + d_{j+1}` for even `j`, `d_j` for odd. -/
def shiftOneNovel (h : ℕ) (d : Array E) : Array E :=
  Array.ofFn (n := 2 ^ h) fun j ↦ if j.val % 2 = 0 then d.getD j.val 0 + d.getD (j.val + 1) 0 else d.getD j.val 0

/-- `CompPoly`'s exact division by a monic polynomial. -/
def divM (p q : Poly) : Poly := CompPoly.CPolynomial.divByMonic p q

/-- The remainder. -/
def modM (p q : Poly) : Poly := CompPoly.CPolynomial.modByMonic p q

/-! ### The quotients -/

/-- The columns' polynomials of table `t`. -/
def tablePolys (tr : Trace) (t : ℕ) : Array Poly :=
  Array.ofFn (n := (tables.getD t default).width) fun c ↦ colPolyK (tr.height t) (tr.column t c)

/-- **The tree's numerator** `w_1 (T(s(X)) + T(X) T(X + 1))`, from `T`'s novel coefficients. -/
def treeNumerator (h : ℕ) (heapNovel : Array E) : Poly :=
  wPoly 1 * (ofNovel (h + 1) (compSNovel h heapNovel) +
    ofNovel h heapNovel * ofNovel h (shiftOneNovel h heapNovel))

/-- **The tree quotient** `N / w_h`. -/
def treeQuotient (h : ℕ) (heapNovel : Array E) : Poly := divM (treeNumerator h heapNovel) (wPoly h)

/-- **A table's leaf numerator** `(R P + P') Z_pad + (R + 1) Z_act`, `R` the heap's block. -/
def tableLeafNumerator (tr : Trace) (weights : Array E) (beta : E) (t : ℕ) (rPoly : Poly) : Poly :=
  let table := tables.getD t default
  let r := tr.height t
  let rows := tr.rows.getD t 0
  let polys := tablePolys tr t
  let col := fun c ↦ polys.getD c 0
  let pull := table.flushes.pull.foldl (fun acc tuple ↦ acc * fpP tuple weights beta col) 1
  let push := table.flushes.push.foldl (fun acc tuple ↦ acc * fpP tuple weights beta col) 1
  (rPoly * pull + push) * zPadP rows r + (rPoly + 1) * zActP rows r

/-- The memory cell's fingerprint at the columns' polynomials. -/
def memoryFpP (weights : Array E) (beta : E) (address count : Poly) (limbs : List Poly) : Poly :=
  (List.range 3).foldl (fun acc k ↦ acc + pC (weights.getD (3 + k) 0) * limbs.getD k 0)
    (pC (beta + weights.getD 0 0 * sepMem) + pC (weights.getD 1 0) * address + pC (weights.getD 2 0) * count)

/-- **The memory's leaf numerator** `R D_fin + D_init`. -/
def memoryLeafNumerator (tr : Trace) (weights : Array E) (beta : E) (rPoly : Poly) : Poly :=
  let lm := tr.shape.logMemory
  let limbs := (List.range 3).map fun k ↦ colPolyK lm (tr.memory.getD k #[])
  let address := colPolyK lm (addressColumn lm)
  let count := colPolyK lm (tr.memory.getD 3 #[])
  rPoly * memoryFpP weights beta address count limbs + memoryFpP weights beta address 1 limbs

/-- The instruction's fingerprint at the slots' polynomials, slot `2` the count. -/
def bytecodeFpP (weights : Array E) (beta : E) (slot : ℕ → Poly) : Poly :=
  (List.range 16).foldl (fun acc s ↦ acc + pC (weights.getD s 0) * slot s) (pC beta)

/-- **The bytecode's leaf numerator** `R D_fin + D_init`. -/
def bytecodeLeafNumerator (tr : Trace) (weights : Array E) (beta : E) (rPoly : Poly) : Poly :=
  let lb := tr.shape.logBytecode
  let slots : Array Poly := Array.ofFn (n := 16) fun s ↦ colPolyK lb (tr.slots.getD s.val #[])
  let count := colPolyK lb tr.bytecodeFinal
  let slot (c : Poly) (s : ℕ) : Poly := if s = 2 then c else slots.getD s 0
  rPoly * bytecodeFpP weights beta (slot count) + bytecodeFpP weights beta (slot 1)

/-- A block's leaf numerator (none for an unused block). -/
def leafNumerator (tr : Trace) (weights : Array E) (beta : E) (block : Block) (rPoly : Poly) : Option Poly :=
  match block.leaves with
  | .unused => none
  | .memory => some (memoryLeafNumerator tr weights beta rPoly)
  | .bytecode => some (bytecodeLeafNumerator tr weights beta rPoly)
  | .table t => some (tableLeafNumerator tr weights beta t rPoly)

/-- **The constraints' numerator** `Σ_i γ^i M_i (w_{r_W} / w_r)`, the powers in the verifier's order
(`constraintRelation`). -/
def constraintNumerator (tr : Trace) (gamma : E) (publicWords : List E) : Poly := Id.run do
  let rW := tr.shape.constraintVars
  let mut acc : Poly := 0
  let mut power : E := 1
  for table in tables do
    let t := table.opcode
    let r := tr.height t
    let lift := liftP r rW
    let polys := tablePolys tr t
    let col := fun (name : String) ↦ polys.getD (colIdx table.columns name) 0
    if t = opJump then
      -- b + v_cond w, v_cond (b + 1)
      acc := acc + pC power * (col "b" + col "v_cond" * col "w") * lift
      power := power * gamma
      acc := acc + pC power * (col "v_cond" * (col "b" + 1)) * lift
      power := power * gamma
    -- z Π c + 1, on every row
    let counters := table.countColumns.foldl (fun p c ↦ p * polys.getD c 0)
      (colPolyK r (inverseColumn tr t))
    acc := acc + pC power * (counters + 1) * lift
    power := power * gamma
    if t = opBlake2s then
      let functionals := coordinateFunctionals r
      let y := (List.range r).map (coordinateP functionals)
      for c in List.range table.width do
        if let some slot := qflockSlot (table.columns.getD c "") then
          let slotValues : Array Poly := Array.ofFn (n := 2 ^ r) fun u ↦
            pC (ofK (tr.qflock.getD (slot + 256 * u.val) 0))
          acc := acc + pC power * (polys.getD c 0 + mleP slotValues y) * lift
          power := power * gamma
  -- the public lines: mem_k + low + X (low + high), lifted by w_{r_W} / w_1
  let lm := tr.shape.logMemory
  let lines : List (E × E) :=
    [(publicWords.getD 0 0, publicWords.getD 2 0), (publicWords.getD 1 0, publicWords.getD 3 0), (0, 0)]
  let lift := liftP 1 rW
  for ((low, high), k) in lines.zip (List.range 3) do
    let mem := colPolyK lm (tr.memory.getD k #[])
    acc := acc + pC power * (mem + pC low + pX * pC (low + high)) * lift
    power := power * gamma
  return acc

/-- **The constraint quotient** `N / w_{r_W}`. -/
def constraintQuotient (tr : Trace) (gamma : E) (publicWords : List E) : Poly :=
  divM (constraintNumerator tr gamma publicWords) (wPoly tr.shape.constraintVars)

/-! ### Chunks -/

/-- **A quotient's chunks in basis `B`** (`Quotient::chunks_b`): its novel coefficients cut at the sizes `2^e`, each
in basis `B`. -/
def chunksB (q : Poly) (sizes : List ℕ) : List (Array E) :=
  let total := (sizes.map (2 ^ ·)).sum
  let novel := toNovel (log2Ceil total) q
  (sizes.foldl (fun (acc : Array (Array E) × ℕ) e ↦
    let chunk : Array E := Array.ofFn (n := 2 ^ e) fun i ↦ novel.getD (acc.2 + i.val) 0
    (acc.1.push (subsetSumsE e chunk), acc.2 + 2 ^ e)) (#[], 0)).1.toList

end UniComplete
