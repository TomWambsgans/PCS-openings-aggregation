-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): `eqEval`, `eqKernel`, `boolPoint` and their lemmas
-- (`Protocol/Whir/Complete/Tables.lean`).
import UniComplete.Claims
import UniComplete.Whir

/-!
# The verifier's `weightAt` is the multilinear extension of the prover's dense weight

`UniStatement.weightAt claim layout r ringMap` (the verifier's `weight_at`) evaluates a combined claim's weight at
the batch's point `r` term by term: `eq` of the (twisted) point on each block of the term's column, times the block's
selector on the coordinates above, the ring-switch term by the map in tower order (`towerWeightAt`), `q_flock`'s
slot `j` by its 8 bits then the point. The prover writes the same weight out over the stack's words
(`UniComplete.denseWeight`). **`weightAt_eq_mle`**: the first is the multilinear extension over `r.length` variables
of the second zero-extended (`mleAt`), at `r`, for `r.length ≥ layout.vars`, on an aligned layout (`Aligned`:
every block of `2^v` words at a multiple of `2^v`, inside the stack; `aligned_new`: `StackLayout.new`'s layouts are),
for a well-formed claim (`WeightWF`):

* a slot term (`qflockSlot j`) is untwisted, `j < 256`, and its point has `v − 8` coordinates for every block of
  `q_flock` (`v` that block's variables);
* a ring-switch term's point has at least `v` coordinates for every block of its column;
* the ring map has at most six stages.

The terms on the cube, as the proof reads them:

* a plain or Frobenius-twisted term: `eq(p, u)^(2^k) = eq(φ^k(p), u)` for `u ∈ {0,1}^v` (`eqEval_boolPoint_pow`),
  and the multilinear extension of `eq(q, ·)` is `eq(q, ·)` (`sum_eqEval_eqEval`); a point shorter than the block
  is zero-padded on both sides (`denseWeight` pads, `rowEq` reads `0` past the point);
* **the ring-switch term**: `towerWeightAt (p.take v) ((1 + r).take v) map` is the multilinear extension of
  `u ↦ towerRingMap (eq(p, u)) map` (`towerWeightAt_eq_sum`). Proof by the stages: after stage `j`, entry `k` of
  `towerWeightAt`'s table (`k` a multiple of `2^j`) is `Σ_u eq(u, r) · T_j(eq(p, u))^(2^k)`, `T_j` the map's first
  `j` stages (`towerT`); stage `j` pairs `k`, `k + 2^j` by `f_j^(2^k)`, which is `T_{j+1} = Φ_j ∘ T_j` raised to
  `2^k` (the Frobenius is additive and multiplicative). No coefficient formula (`towerCoefficients`) is needed;
* a slot term: word `j + 256 u` of `q_flock`'s block is the cube point `bits(j) ++ bits(u)`.

**Findings.** None on the well-formed claims. Outside them the two disagree, each case named by a hypothesis of
`WeightWF`: a slot term with a twist (`denseWeight` ignores it, `weightAt` twists or, at `ringTwist`, drops it); a
slot point whose length is not the block's `v − 8` (`weightAt` reads `8 + |p|` coordinates, `denseWeight` writes
`2^|p|` instances, past the block if longer); a ring-switch point shorter than the block (`towerWeightAt` zips the
point with `1 + r`, stopping at the point's end, where `denseWeight` pads with zeros); a ring map of more than six
stages (`towerRingMap` applies them all, `towerWeightAt` six). The Rust `dense_weight` truncates a slot point to
`v − 8` coordinates (`claim.points[p][..len]`) where the Lean prover reads it whole; the two agree on the slot points
of `v − 8` coordinates, the only ones the verifier's relations state (`y(t)` of `r` coordinates on `q_flock` of
`r + 8` variables) unless `combine` lengthens `y(t)` (when it is a proper prefix of another point of `C1`'s claim).
-/

open LeanVM.Parameters
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.Verifier (eqEval)
open LeanVM.Protocol.Whir.Complete (eqEval_cons eqEval_append eqEval_comm boolPoint_add boolPoint_succ
  length_boolPoint isMultilinearFn_eqEval isMultilinearFn_iff getD_eqKernel length_eqKernel)
open Finset

namespace UniComplete

open UniStatement (Combined StackLayout Column)

/-! ## Characteristic two, powers of two -/

theorem ite_pos {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ite_neg {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem one_add_one_eq_zero_E : (1 : E) + 1 = 0 := CharTwo.add_self_eq_zero 1

theorem add_self_E (x : E) : x + x = 0 := CharTwo.add_self_eq_zero x

/-- `sqn x k = x^(2^k)`. -/
theorem sqn_eq_pow (x : E) : ∀ k, UniStatement.sqn x k = x ^ 2 ^ k
  | 0 => by simp [UniStatement.sqn]
  | k + 1 => by
    rw [UniStatement.sqn, sqn_eq_pow (x * x) k, ← sq, ← pow_mul, pow_succ']

/-- The Frobenius `x ↦ x^(2^k)` is additive. -/
theorem frob_add (x y : E) (k : ℕ) : (x + y) ^ 2 ^ k = x ^ 2 ^ k + y ^ 2 ^ k := add_pow_char_pow x y 2 k

theorem frob_frob (x : E) (a b : ℕ) : (x ^ 2 ^ a) ^ 2 ^ b = x ^ 2 ^ (a + b) := by
  rw [← pow_mul, ← pow_add]

theorem zero_frob (k : ℕ) : (0 : E) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero _ two_ne_zero)

theorem bool_frob (b : Bool) (k : ℕ) : ((if b then 1 else 0 : E)) ^ 2 ^ k = if b then 1 else 0 := by
  cases b <;> simp

/-! ## Folds as sums and products -/

theorem foldl_add_map {α : Type} (f : α → E) : ∀ (l : List α) (a : E),
    l.foldl (fun acc x ↦ acc + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_map f l, List.map_cons, List.sum_cons, add_assoc]

theorem foldl_mul_map {α : Type} (f : α → E) : ∀ (l : List α) (a : E),
    l.foldl (fun acc x ↦ acc * f x) a = a * (l.map f).prod
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_mul_map f l, List.map_cons, List.prod_cons, mul_assoc]

theorem prod_map_range (f : ℕ → E) : ∀ n, ((List.range n).map f).prod = ∏ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.prod_append, prod_map_range f n, prod_range_succ]; simp

theorem sum_map_range (f : ℕ → E) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f n, sum_range_succ]; simp

theorem getD_map_zero (l : List E) (f : E → E) (hf : f 0 = 0) (k : ℕ) :
    (l.map f).getD k 0 = f (l.getD k 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> simp [hf]

theorem arr_getD (a : Array E) (i : ℕ) : a.getD i 0 = a.toList.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-! ## The equality kernel -/

/-- `eqEval` of two points of one length, as a product over the coordinates. -/
theorem eqEval_eq_prod : ∀ (a b : List E), a.length = b.length →
    eqEval a b = ∏ i ∈ range a.length, (1 + a.getD i 0 + b.getD i 0)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, z :: b, h => by
    rw [eqEval_cons, eqEval_eq_prod a b (by simpa using h), List.length_cons, prod_range_succ']
    simp [mul_comm]

theorem boolPoint_getD (n x i : ℕ) (hi : i < n) :
    (boolPoint n x).getD i 0 = if x.testBit i then 1 else 0 := by
  simp [boolPoint, List.getD_eq_getElem?_getD, hi]

/-- **The multilinear extension of `eq(q, ·)` is `eq(q, ·)`.** -/
theorem sum_eqEval_eqEval (q s : List E) (h : q.length = s.length) :
    ∑ x ∈ range (2 ^ q.length), eqEval (boolPoint q.length x) q * eqEval (boolPoint q.length x) s =
      eqEval q s := by
  rw [(isMultilinearFn_iff _ _).mp (isMultilinearFn_eqEval q) s h.symm]
  exact sum_congr rfl fun x _ ↦ by rw [eqEval_comm q]

/-- **The Frobenius on the cube**: `eq(u, q)^(2^k) = eq(u, q^(2^k))` for a cube point `u`. -/
theorem eqEval_boolPoint_pow (k : ℕ) : ∀ (n x : ℕ) (q : List E), q.length = n →
    eqEval (boolPoint n x) q ^ 2 ^ k = eqEval (boolPoint n x) (q.map (· ^ 2 ^ k))
  | 0, _, [], _ => by simp
  | 0, _, _ :: _, h => by simp at h
  | _ + 1, _, [], h => by simp at h
  | n + 1, x, c :: q, h => by
    rw [boolPoint_succ, List.map_cons, eqEval_cons, eqEval_cons, mul_pow,
      eqEval_boolPoint_pow k n (x / 2) q (by simpa using h), frob_add, frob_add, one_pow, bool_frob]

/-- The statement's equality kernel (on arrays) is mumbai's (on lists). -/
theorem eqKernel_toList (p : List E) :
    (UniStatement.eqKernel p).toList = LeanVM.Protocol.Verifier.eqKernel p := by
  unfold UniStatement.eqKernel LeanVM.Protocol.Verifier.eqKernel
  suffices h : ∀ out : Array E,
      (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).toList =
        p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out.toList from h #[1]
  induction p with
  | nil => intro; rfl
  | cons r p ih => intro out; rw [List.foldl_cons, List.foldl_cons, ih]; simp

theorem eqKernel_size (p : List E) : (UniStatement.eqKernel p).size = 2 ^ p.length := by
  rw [← Array.length_toList, eqKernel_toList, length_eqKernel]

theorem eqKernel_getD' (p : List E) {j : ℕ} (hj : j < 2 ^ p.length) :
    (UniStatement.eqKernel p).getD j 0 = eqEval (boolPoint p.length j) p := by
  rw [arr_getD, eqKernel_toList, getD_eqKernel p j hj]

/-! ## Blocks and selectors -/

/-- `selector` as a product: bit `v + i` of the offset against `r_(v + i)`. -/
theorem selector_eq (r : List E) (v off : ℕ) :
    UniStatement.selector r v off = ∏ i ∈ range (r.length - v),
      (if off.testBit (v + i) then r.getD (v + i) 0 else 1 + r.getD (v + i) 0) := by
  unfold UniStatement.selector
  rw [List.range'_eq_map_range, List.foldl_map, foldl_mul_map, one_mul, prod_map_range]

/-- **A block's word as a cube point**: word `off + x` of a stack of `2^|r|` words, `x < 2^v` in a block at a
multiple `off` of `2^v`, is the block's cube point `x` against `r`'s first `v` coordinates, times the block's
selector on the coordinates above. -/
theorem eqEval_block {r : List E} {v off x : ℕ} (hv : v ≤ r.length) (hoff : 2 ^ v ∣ off) (hx : x < 2 ^ v) :
    eqEval (boolPoint r.length (off + x)) r =
      eqEval (boolPoint v x) (r.take v) * UniStatement.selector r v off := by
  obtain ⟨z, rfl⟩ := hoff
  have hb := boolPoint_add v (r.length - v) x z hx
  rw [Nat.add_sub_cancel' hv] at hb
  rw [show 2 ^ v * z + x = x + 2 ^ v * z by ring, hb]
  conv_lhs => arg 2; rw [← List.take_append_drop v r]
  rw [eqEval_append _ _ _ _ (by simp [hv])]
  congr 1
  rw [eqEval_eq_prod _ _ (by simp), length_boolPoint, selector_eq]
  refine prod_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [boolPoint_getD _ _ _ hi']
  have hd : (r.drop v).getD i 0 = r.getD (v + i) 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [hd, Nat.testBit_two_pow_mul]
  simp only [show v ≤ v + i by omega, decide_true, Bool.true_and, Nat.add_sub_cancel_left]
  cases z.testBit i
  · simp
  · simp [one_add_one_eq_zero_E]

/-! ## The ring map in tower order (`towerRingMap`, `towerWeightAt`) -/

/-- The ring map's first `j` stages, stage `i` the map `v ↦ v + f_i v^(2^(2^i))`. -/
def towerT (map : List E) (j : ℕ) (v : E) : E :=
  (List.range j).foldl (fun v i ↦ v + map.getD i 0 * v ^ 2 ^ 2 ^ i) v

theorem towerT_zero (map : List E) (v : E) : towerT map 0 v = v := rfl

theorem towerT_succ (map : List E) (j : ℕ) (v : E) :
    towerT map (j + 1) v = towerT map j v + map.getD j 0 * towerT map j v ^ 2 ^ 2 ^ j := by
  simp [towerT, List.range_succ, List.foldl_append]

theorem foldl_id {α β : Type} (f : α → β → α) : ∀ (l : List β) (v : α), (∀ x ∈ l, ∀ w, f w x = w) →
    l.foldl f v = v
  | [], _, _ => rfl
  | x :: l, v, h => by
    rw [List.foldl_cons, h x (by simp) v]
    exact foldl_id f l v fun y hy w ↦ h y (by simp [hy]) w

/-- **`towerRingMap` is the six stages** for a map of at most six challenges. -/
theorem towerRingMap_eq (v : E) (map : List E) (h : map.length ≤ 6) :
    UniStatement.Flock.towerRingMap v map = towerT map 6 v := by
  have hz : map.zip (List.range map.length) = (List.range map.length).map fun i ↦ (map.getD i 0, i) := by
    refine List.ext_getElem (by simp) fun i h1 _ ↦ ?_
    have hi : i < map.length := by simpa using h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  unfold UniStatement.Flock.towerRingMap towerT
  rw [hz, List.foldl_map, show 6 = map.length + (6 - map.length) by omega, List.range_add,
    List.foldl_append]
  simp only [sqn_eq_pow]
  refine (foldl_id _ _ _ fun x hx w ↦ ?_).symm
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  simp [List.getD_eq_getElem?_getD]

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (x y : β) :
    (if c then (pure (ForInStep.yield x) : Id (ForInStep β)) else pure (ForInStep.yield y)) =
      pure (ForInStep.yield (if c then x else y)) := by
  split <;> rfl

/-- `towerWeightAt`'s first loop, a step: the chain squared (but at `k = 0`), its twisted product pushed. -/
def chainStep (a : List E) (b : List E × Array E) (k : ℕ) : List E × Array E :=
  if k > 0 then
    (List.map (fun c ↦ c * c) b.1,
      b.2.push (List.foldl (fun acc x ↦ acc * (x.2 + x.1)) 1 ((List.map (fun c ↦ c * c) b.1).zip a)))
  else (b.1, b.2.push (List.foldl (fun acc x ↦ acc * (x.2 + x.1)) 1 (b.1.zip a)))

/-- `towerWeightAt`'s stage `j`, a step: entry `kk 2^(j+1)` takes `f_j^(2^k)` times its partner. -/
def stageStep (j : ℕ) (b : Array E × E) (kk : ℕ) : Array E × E :=
  if kk * (2 * 2 ^ j) > 0 then
    (b.1.set! (kk * (2 * 2 ^ j))
        (b.1.getD (kk * (2 * 2 ^ j)) 0 +
          UniStatement.sqn b.2 (2 * 2 ^ j) * b.1.getD (kk * (2 * 2 ^ j) + 2 ^ j) 0),
      UniStatement.sqn b.2 (2 * 2 ^ j))
  else
    (b.1.set! (kk * (2 * 2 ^ j))
        (b.1.getD (kk * (2 * 2 ^ j)) 0 + b.2 * b.1.getD (kk * (2 * 2 ^ j) + 2 ^ j) 0), b.2)

/-- `towerWeightAt`'s stage `j`. -/
def stageRun (map : List E) (g : Array E) (j : ℕ) : Array E :=
  ((List.range' 0 (64 / (2 * 2 ^ j))).foldl (stageStep j) (g, map.getD j 0)).1

/-- **`towerWeightAt` unfolded**: its loops as folds. -/
theorem towerWeightAt_eq_folds (q a map : List E) :
    UniStatement.Flock.towerWeightAt q a map =
      ((List.range' 0 6).foldl (stageRun map) ((List.range' 0 64).foldl (chainStep a) (q, #[])).2).getD 0 0 := by
  simp only [UniStatement.Flock.towerWeightAt, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yield,
    List.forIn_pure_yield_eq_foldl, Id.run, bind_pure_comp, map_pure]
  rfl

theorem push_getD (a : Array E) (x : E) (k : ℕ) :
    (a.push x).getD k 0 = if k < a.size then a.getD k 0 else if k = a.size then x else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h1 : k < a.size
  · simp [h1, show k ≠ a.size by omega]
  · by_cases h2 : k = a.size
    · simp [h2]
    · simp [h1, h2]

theorem set_getD (a : Array E) {i : ℕ} (hi : i < a.size) (x : E) (k : ℕ) :
    (a.set! i x).getD k 0 = if k = i then x else a.getD k 0 := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : k = i
  · subst h; simp [hi]
  · simp [Ne.symm h, h]

theorem set_size (a : Array E) (i : ℕ) (x : E) : (a.set! i x).size = a.size := by
  simp [Array.set!]

/-- The twisted product of `towerWeightAt`'s first loop: `Π_n ((1 + s_n) + c_n) = eq(c, s)`. -/
theorem zipFold_eq : ∀ (c s : List E) (acc : E), c.length = s.length →
    (c.zip (s.map (1 + ·))).foldl (fun acc x ↦ acc * (x.2 + x.1)) acc = acc * eqEval c s
  | [], [], acc, _ => by simp
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: c, z :: s, acc, h => by
    rw [List.map_cons, List.zip_cons_cons, List.foldl_cons, zipFold_eq c s _ (by simpa using h), eqEval_cons]
    ring

/-- `towerWeightAt`'s first loop: after `m` steps the chain is `p^(2^(m − 1))` and the table holds the twisted
products of `p^(2^k)`, `k < m`. -/
theorem chain_fold (q a : List E) : ∀ m : ℕ,
    ((List.range' 0 m).foldl (chainStep a) (q, #[])).1 = q.map (· ^ 2 ^ (m - 1)) ∧
    ((List.range' 0 m).foldl (chainStep a) (q, #[])).2.size = m ∧
    ∀ k < m, ((List.range' 0 m).foldl (chainStep a) (q, #[])).2.getD k 0 =
      ((q.map (· ^ 2 ^ k)).zip a).foldl (fun acc x ↦ acc * (x.2 + x.1)) 1
  | 0 => by simp
  | m + 1 => by
    obtain ⟨h1, h2, h3⟩ := chain_fold q a m
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 0 m).foldl (chainStep a) (q, #[]) = b at h1 h2 h3
    unfold chainStep
    simp only [Nat.one_mul, Nat.zero_add, Nat.add_sub_cancel]
    by_cases hm : m > 0
    · have hstep : ∀ x : E, (x ^ 2 ^ (m - 1)) * (x ^ 2 ^ (m - 1)) = x ^ 2 ^ m := fun x ↦ by
        rw [← sq, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hm]
      rw [ite_pos hm]
      refine ⟨by rw [h1, List.map_map]; exact List.map_congr_left fun x _ ↦ hstep x, ?_, fun k hk ↦ ?_⟩
      · simp [h2]
      · rw [push_getD, h2]
        rcases Nat.lt_or_ge k m with hk' | hk'
        · rw [ite_pos hk', h3 k hk']
        · obtain rfl : k = m := by omega
          rw [ite_neg (by omega), ite_pos rfl, h1, List.map_map]
          congr 2
          exact List.map_congr_left fun x _ ↦ hstep x
    · obtain rfl : m = 0 := by omega
      rw [ite_neg hm]
      refine ⟨by simpa using h1, by simp [h2], fun k hk ↦ ?_⟩
      obtain rfl : k = 0 := by omega
      rw [push_getD, h2, ite_neg (by omega), ite_pos rfl, h1]

/-- The value of `towerWeightAt`'s table entry `k` after `j` stages: `Σ_u T_j(eq(u, q))^(2^k) · eq(u, s)`. -/
def towerV (map q s : List E) (j k : ℕ) : E :=
  ∑ x ∈ range (2 ^ q.length),
    towerT map j (eqEval (boolPoint q.length x) q) ^ 2 ^ k * eqEval (boolPoint q.length x) s

theorem towerV_zero (map q s : List E) (h : q.length = s.length) (k : ℕ) :
    towerV map q s 0 k = eqEval (q.map (· ^ 2 ^ k)) s := by
  have hl : (q.map (· ^ 2 ^ k)).length = s.length := by simp [h]
  rw [← sum_eqEval_eqEval _ s hl, List.length_map]
  unfold towerV
  exact sum_congr rfl fun x _ ↦ by rw [towerT_zero, eqEval_boolPoint_pow k _ x q rfl]

/-- **A stage of the tower**: stage `j` pairs entries `k` and `k + 2^j` by `f_j^(2^k)`, which is `Φ_j`
raised to `2^k`. -/
theorem towerV_step (map q s : List E) (j k : ℕ) :
    towerV map q s j k + map.getD j 0 ^ 2 ^ k * towerV map q s j (k + 2 ^ j) = towerV map q s (j + 1) k := by
  unfold towerV
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [towerT_succ, frob_add, mul_pow, frob_frob, add_comm (2 ^ j) k]
  ring

theorem not_dvd_add_half {j c : ℕ} : ¬ 2 ^ (j + 1) ∣ c * 2 ^ (j + 1) + 2 ^ j := by
  intro h
  have h' := (Nat.dvd_add_right (Dvd.intro_left c rfl)).mp h
  have := Nat.le_of_dvd (by positivity) h'
  rw [pow_succ] at this
  have : 0 < 2 ^ j := by positivity
  omega

/-- **Stage `j`'s loop**: after `m` steps, entries `c 2^(j+1)`, `c < m`, hold stage `j + 1`'s value, the others
stage `j`'s, and the power is `f_j^(2^((m − 1) 2^(j+1)))`. -/
theorem stage_fold (map q s : List E) (j : ℕ) (g : Array E) (hg : g.size = 64)
    (hP : ∀ k < 64, 2 ^ j ∣ k → g.getD k 0 = towerV map q s j k) :
    ∀ m, m ≤ 64 / 2 ^ (j + 1) →
      ((List.range' 0 m).foldl (stageStep j) (g, map.getD j 0)).1.size = 64 ∧
      ((List.range' 0 m).foldl (stageStep j) (g, map.getD j 0)).2 =
        map.getD j 0 ^ 2 ^ ((m - 1) * 2 ^ (j + 1)) ∧
      ∀ k < 64, 2 ^ j ∣ k → ((List.range' 0 m).foldl (stageStep j) (g, map.getD j 0)).1.getD k 0 =
        if 2 ^ (j + 1) ∣ k ∧ k < m * 2 ^ (j + 1) then towerV map q s (j + 1) k else towerV map q s j k
  | 0, _ => by
    refine ⟨hg, by simp, fun k hk hd ↦ ?_⟩
    simp [hP k hk hd]
  | m + 1, hm => by
    obtain ⟨h1, h2, h3⟩ := stage_fold map q s j g hg hP m (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 0 m).foldl (stageStep j) (g, map.getD j 0) = b at h1 h2 h3
    have hX : 0 < 2 ^ (j + 1) := by positivity
    have hle : (m + 1) * 2 ^ (j + 1) ≤ 64 :=
      (Nat.mul_le_mul_right _ hm).trans (Nat.div_mul_le_self 64 _)
    have h2j : 2 * 2 ^ j = 2 ^ (j + 1) := (pow_succ' 2 j).symm
    have hidx : m * 2 ^ (j + 1) + 2 ^ j < 64 := by
      have : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      rw [Nat.add_mul, one_mul] at hle
      omega
    have hidx' : m * 2 ^ (j + 1) < b.1.size := by rw [h1]; omega
    -- The power the step uses, and the one it leaves.
    set f := map.getD j 0 with hf
    have hpow : (if m * (2 * 2 ^ j) > 0 then UniStatement.sqn b.2 (2 * 2 ^ j) else b.2) =
        f ^ 2 ^ (m * 2 ^ (j + 1)) := by
      rw [h2j]
      split_ifs with hpos
      · have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with rfl | h
          · simp at hpos
          · exact h
        rw [sqn_eq_pow, h2, frob_frob]
        congr 2
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      · have hm0 : m = 0 := by
          by_contra h
          exact hpos (Nat.mul_pos (Nat.pos_of_ne_zero h) hX)
        subst hm0
        rw [h2]
    -- The step, as one `set!` with that power.
    have hstep : stageStep j b m =
        (b.1.set! (m * 2 ^ (j + 1)) (b.1.getD (m * 2 ^ (j + 1)) 0 +
            f ^ 2 ^ (m * 2 ^ (j + 1)) * b.1.getD (m * 2 ^ (j + 1) + 2 ^ j) 0),
          if m * (2 * 2 ^ j) > 0 then UniStatement.sqn b.2 (2 * 2 ^ j) else b.2) := by
      rw [← hpow]
      unfold stageStep
      rw [h2j]
      split_ifs <;> rfl
    simp only [Nat.zero_add, Nat.one_mul]
    rw [hstep]
    refine ⟨by rw [set_size, h1], by rw [hpow, Nat.add_sub_cancel], fun k hk hd ↦ ?_⟩
    rw [set_getD _ hidx']
    by_cases hki : k = m * 2 ^ (j + 1)
    · subst hki
      rw [ite_pos rfl, h3 _ (by omega) hd, h3 _ hidx (dvd_add hd (dvd_refl _)), ite_neg (by omega),
        ite_neg (fun h ↦ not_dvd_add_half h.1), towerV_step, ite_pos ⟨Dvd.intro_left m rfl, by
          rw [Nat.add_mul, one_mul]; omega⟩]
    · rw [ite_neg hki, h3 k hk hd]
      by_cases hdk : 2 ^ (j + 1) ∣ k
      · obtain ⟨c, rfl⟩ := hdk
        have hcm : c ≠ m := fun h ↦ hki (by rw [h, mul_comm])
        have e1 : 2 ^ (j + 1) * c < m * 2 ^ (j + 1) ↔ c < m := by
          rw [mul_comm]; exact Nat.mul_lt_mul_right hX
        have e2 : 2 ^ (j + 1) * c < (m + 1) * 2 ^ (j + 1) ↔ c < m + 1 := by
          rw [mul_comm]; exact Nat.mul_lt_mul_right hX
        simp only [dvd_mul_right, true_and, e1, e2]
        by_cases hc : c < m
        · rw [ite_pos hc, ite_pos (by omega)]
        · rw [ite_neg hc, ite_neg (by omega)]
      · simp [hdk]

/-- **Stage `j`** takes the tower's table from stage `j`'s values to stage `j + 1`'s. -/
theorem stageRun_spec (map q s : List E) {j : ℕ} (hj : j < 6) (g : Array E) (hg : g.size = 64)
    (hP : ∀ k < 64, 2 ^ j ∣ k → g.getD k 0 = towerV map q s j k) :
    (stageRun map g j).size = 64 ∧
      ∀ k < 64, 2 ^ (j + 1) ∣ k → (stageRun map g j).getD k 0 = towerV map q s (j + 1) k := by
  have hM : 64 / (2 * 2 ^ j) = 64 / 2 ^ (j + 1) := by rw [pow_succ']
  have hdiv : 2 ^ (j + 1) ∣ 64 := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨h1, -, h3⟩ := stage_fold map q s j g hg hP (64 / 2 ^ (j + 1)) le_rfl
  unfold stageRun
  rw [hM]
  refine ⟨h1, fun k hk hd ↦ ?_⟩
  rw [h3 k hk (dvd_trans (pow_dvd_pow 2 (Nat.le_succ j)) hd),
    ite_pos ⟨hd, by rw [Nat.div_mul_cancel hdiv]; exact hk⟩]

/-- All six stages. -/
theorem stages_fold (map q s : List E) (g : Array E) (hg : g.size = 64)
    (hP : ∀ k < 64, g.getD k 0 = towerV map q s 0 k) : ∀ j, j ≤ 6 →
      ((List.range' 0 j).foldl (stageRun map) g).size = 64 ∧
        ∀ k < 64, 2 ^ j ∣ k → ((List.range' 0 j).foldl (stageRun map) g).getD k 0 = towerV map q s j k
  | 0, _ => ⟨hg, fun k hk _ ↦ hP k hk⟩
  | j + 1, hj => by
    obtain ⟨h1, h2⟩ := stages_fold map q s g hg hP j (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add, Nat.one_mul]
    exact stageRun_spec map q s (by omega) _ h1 h2

/-- **`towerWeightAt` is a multilinear extension**: at `1 + s`, of the six stages of the map applied to
`eq(q, ·)` on the cube. -/
theorem towerWeightAt_eq_sum (q s map : List E) (hqs : q.length = s.length) :
    UniStatement.Flock.towerWeightAt q (s.map (1 + ·)) map =
      ∑ x ∈ range (2 ^ q.length),
        towerT map 6 (eqEval (boolPoint q.length x) q) * eqEval (boolPoint q.length x) s := by
  rw [towerWeightAt_eq_folds]
  obtain ⟨-, hsize, hget⟩ := chain_fold q (s.map (1 + ·)) 64
  have h0 : ∀ k < 64, ((List.range' 0 64).foldl (chainStep (s.map (1 + ·))) (q, #[])).2.getD k 0 =
      towerV map q s 0 k := fun k hk ↦ by
    rw [hget k hk, zipFold_eq _ _ _ (by simp [hqs]), one_mul, towerV_zero map q s hqs]
  obtain ⟨-, hfin⟩ := stages_fold map q s _ hsize h0 6 le_rfl
  rw [hfin 0 (by norm_num) (dvd_zero _)]
  simp [towerV]

/-! ## The multilinear extension of a table -/

/-- **The multilinear extension over `R` variables** of a table, zero past its entries, at `r` (low coordinate
first: word `x` is the cube point `boolPoint R x`). -/
def mleAt (R : ℕ) (r : List E) (W : Array E) : E :=
  ∑ x ∈ range (2 ^ R), W.getD x 0 * eqEval (boolPoint R x) r

theorem addAt_size (W : Array E) (i : ℕ) (x : E) : (addAt W i x).size = W.size := by
  simp [addAt]

theorem addAt_getD (W : Array E) {i : ℕ} (hi : i < W.size) (x : E) (j : ℕ) :
    (addAt W i x).getD j 0 = W.getD j 0 + if j = i then x else 0 := by
  unfold addAt
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [hj, Ne.symm hj]

theorem mleAt_addAt (R : ℕ) (r : List E) (W : Array E) {i : ℕ} (hi : i < W.size) (hW : W.size ≤ 2 ^ R)
    (x : E) : mleAt R r (addAt W i x) = mleAt R r W + x * eqEval (boolPoint R i) r := by
  unfold mleAt
  simp only [addAt_getD W hi, add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq', mem_range]
  rw [ite_pos (by omega)]

theorem mleAt_replicate (R : ℕ) (r : List E) (N : ℕ) : mleAt R r (Array.replicate N 0) = 0 := by
  unfold mleAt
  refine sum_eq_zero fun x _ ↦ ?_
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

/-- **A run of additions**: at `idx u` the value `val u`, `u < n`. -/
theorem mleAt_range_addAt (R : ℕ) (r : List E) (idx : ℕ → ℕ) (val : ℕ → E) :
    ∀ (n : ℕ) (W : Array E), (∀ u < n, idx u < W.size) → W.size ≤ 2 ^ R →
      ((List.range n).foldl (fun W u ↦ addAt W (idx u) (val u)) W).size = W.size ∧
      mleAt R r ((List.range n).foldl (fun W u ↦ addAt W (idx u) (val u)) W) =
        mleAt R r W + ∑ u ∈ range n, val u * eqEval (boolPoint R (idx u)) r
  | 0, W, _, _ => by simp
  | n + 1, W, hidx, hW => by
    obtain ⟨h1, h2⟩ := mleAt_range_addAt R r idx val n W (fun u hu ↦ hidx u (by omega)) hW
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, addAt_size, h1,
      mleAt_addAt R r _ (by rw [h1]; exact hidx n (by omega)) (by rw [h1]; exact hW), h2, sum_range_succ,
      add_assoc]
    exact ⟨rfl, rfl⟩

/-- **Two folds in step**: a fold of tables whose every step adds to `F` what a step of a fold of values adds. -/
theorem foldl_couple {α β : Type} (F : β → E) (P : β → Prop) (stepD : β → α → β) (stepW : E → α → E) :
    ∀ (l : List α), (∀ a ∈ l, ∀ W, P W → P (stepD W a) ∧ ∀ t, F (stepD W a) + t = F W + stepW t a) →
      ∀ W, P W → P (l.foldl stepD W) ∧ ∀ t, F (l.foldl stepD W) + t = F W + l.foldl stepW t
  | [], _, W, hW => ⟨hW, fun t ↦ by simp⟩
  | a :: l, h, W, hW => by
    obtain ⟨hP, hF⟩ := h a (by simp) W hW
    obtain ⟨hP', hF'⟩ := foldl_couple F P stepD stepW l (fun b hb ↦ h b (by simp [hb])) _ hP
    refine ⟨hP', fun t ↦ ?_⟩
    rw [List.foldl_cons, List.foldl_cons]
    linear_combination hF' (stepW t a) + hF t

/-- A fold of values adding `g` at every step. -/
theorem foldl_add_step {α : Type} (g : α → E) (l : List α) (t : E) :
    l.foldl (fun total x ↦ total + g x) t = t + l.foldl (fun total x ↦ total + g x) 0 := by
  rw [foldl_add_map, foldl_add_map, zero_add]

/-! ## Aligned layouts -/

/-- **An aligned layout**: every block of `2^v` words sits at a multiple of `2^v`, inside the stack's
`2^vars` words. -/
def Aligned (layout : StackLayout) : Prop :=
  ∀ c limb v off, (c, limb, v, off) ∈ layout.blocks → 2 ^ v ∣ off ∧ off + 2 ^ v ≤ 2 ^ layout.vars

theorem mem_limbs {layout : StackLayout} {column : Column} {limb v off : ℕ}
    (h : (limb, v, off) ∈ layout.limbs column) : (column, limb, v, off) ∈ layout.blocks := by
  unfold StackLayout.limbs at h
  obtain ⟨⟨c, l, v', o⟩, hmem, he⟩ := List.mem_filterMap.mp h
  by_cases hc : c = column
  · subst hc
    simp only [beq_self_eq_true, ite_true, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hmem
  · simp [hc] at he

/-- `StackLayout.new`'s fold: blocks laid end to end, largest first, each at a multiple of its size. -/
theorem new_fold (f : Array (Column × ℕ × ℕ × ℕ) × ℕ → Column × ℕ × ℕ → Array (Column × ℕ × ℕ × ℕ) × ℕ)
    (hf : ∀ acc x, f acc x = (acc.1.push (x.1, x.2.1, x.2.2, acc.2), acc.2 + 2 ^ x.2.2)) :
    ∀ (L : List (Column × ℕ × ℕ)), L.Pairwise (fun a b ↦ b.2.2 ≤ a.2.2) →
    ∀ (acc : Array (Column × ℕ × ℕ × ℕ)) (o : ℕ), (∀ x ∈ L, 2 ^ x.2.2 ∣ o) →
      (∀ c limb v off, (c, limb, v, off) ∈ acc.toList → 2 ^ v ∣ off ∧ off + 2 ^ v ≤ o) →
      ∀ c limb v off, (c, limb, v, off) ∈ (L.foldl f (acc, o)).1.toList →
        2 ^ v ∣ off ∧ off + 2 ^ v ≤ (L.foldl f (acc, o)).2
  | [], _, acc, o, _, hacc => by simpa using hacc
  | x :: L, hL, acc, o, hdiv, hacc => by
    rw [List.foldl_cons, hf]
    dsimp only
    obtain ⟨hx, hL'⟩ := List.pairwise_cons.mp hL
    refine new_fold f hf L hL' _ _ (fun y hy ↦ ?_) (fun c limb v off hmem ↦ ?_)
    · exact dvd_add (hdiv y (by simp [hy])) (Nat.pow_dvd_pow 2 (hx y hy))
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨h1, h2⟩ := hacc c limb v off hmem
        exact ⟨h1, le_trans h2 (Nat.le_add_right _ _)⟩
      · simp only [Prod.mk.injEq] at hmem
        obtain ⟨-, -, rfl, rfl⟩ := hmem
        exact ⟨hdiv x (by simp), le_rfl⟩

theorem le_pow_log2Ceil {n : ℕ} (hn : 2 ≤ n) : n ≤ 2 ^ UniStatement.log2Ceil n := by
  unfold UniStatement.log2Ceil
  rw [ite_neg (by omega)]
  have := Nat.lt_log2_self (n := n - 1)
  omega

/-- The fold's offset only grows. -/
theorem new_fold_le (f : Array (Column × ℕ × ℕ × ℕ) × ℕ → Column × ℕ × ℕ → Array (Column × ℕ × ℕ × ℕ) × ℕ)
    (hf : ∀ acc x, f acc x = (acc.1.push (x.1, x.2.1, x.2.2, acc.2), acc.2 + 2 ^ x.2.2)) :
    ∀ (L : List (Column × ℕ × ℕ)) (acc : Array (Column × ℕ × ℕ × ℕ)) (o : ℕ), o ≤ (L.foldl f (acc, o)).2
  | [], _, _ => le_rfl
  | x :: L, acc, o => by
    rw [List.foldl_cons, hf]
    dsimp only
    exact le_trans (Nat.le_add_right _ _) (new_fold_le f hf L _ _)

/-- The layout of blocks laid end to end in a sorted order is aligned. -/
theorem aligned_of_sorted (L : List (Column × ℕ × ℕ)) (hL : L.Pairwise fun a b ↦ decide (b.2.2 ≤ a.2.2) = true)
    (c : Column) (limb v off : ℕ)
    (hmem : (c, limb, v, off) ∈ (L.foldl (fun acc x ↦ (acc.1.push (x.1, x.2.1, x.2.2, acc.2), acc.2 + 2 ^ x.2.2))
      ((#[] : Array (Column × ℕ × ℕ × ℕ)), 0)).1.toList) :
    2 ^ v ∣ off ∧ off + 2 ^ v ≤ 2 ^ max (UniStatement.log2Ceil (max (L.foldl (fun acc x ↦
      (acc.1.push (x.1, x.2.1, x.2.2, acc.2), acc.2 + 2 ^ x.2.2))
        ((#[] : Array (Column × ℕ × ℕ × ℕ)), 0)).2 2)) 15 := by
  have hL' : L.Pairwise fun a b ↦ b.2.2 ≤ a.2.2 := hL.imp fun h ↦ by simpa using h
  obtain ⟨h1, h2⟩ := new_fold _ (fun _ _ ↦ rfl) L hL' #[] 0 (fun _ _ ↦ dvd_zero _) (by simp) c limb v off hmem
  refine ⟨h1, h2.trans ?_⟩
  refine (le_max_left _ 2).trans ((le_pow_log2Ceil (le_max_right _ _)).trans ?_)
  exact Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)

/-- **`StackLayout.new`'s layouts are aligned** (sorted largest first: every offset is a sum of larger powers of
two; the stack has at least the words laid). -/
theorem aligned_new (columns : List (Column × ℕ × Bool)) : Aligned (StackLayout.new columns) := by
  intro c limb v off hmem
  unfold StackLayout.new at hmem ⊢
  simp only at hmem ⊢
  exact aligned_of_sorted _ (List.pairwise_mergeSort
    (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _) c limb v off hmem

/-! ## A block's part of the weight -/

/-- `rowEq` is `eq` against `r`'s first `len` coordinates of any point agreeing with it there (zero past it). -/
theorem rowEq_eq (point q r : List E) (len : ℕ) (hq : q.length = len) (hlen : len ≤ r.length)
    (hget : ∀ k < len, q.getD k 0 = point.getD k 0) :
    UniStatement.rowEq point len r = eqEval q (r.take len) := by
  unfold UniStatement.rowEq
  rw [foldl_mul_map, one_mul, prod_map_range, eqEval_eq_prod _ _ (by simp [hq, hlen]), hq]
  refine prod_congr rfl fun k hk ↦ ?_
  have hk' := mem_range.mp hk
  rw [hget k hk']
  simp [List.getD_eq_getElem?_getD, hk']

/-- **A plain or twisted term on a block**: the dense weight `eq(p, ·)^(2^k)` on the block's words, paired with
`eq(·, r)`, is `rowEq` of the twisted point times the block's selector. -/
theorem block_regular {r : List E} {v off : ℕ} (hv : v ≤ r.length) (hoff : 2 ^ v ∣ off) (pt : List E)
    (twist : ℕ) :
    ∑ u ∈ range (2 ^ v), UniStatement.sqn ((UniStatement.eqKernel ((pt ++ List.replicate v 0).take v)).getD u 0)
        twist * eqEval (boolPoint r.length (off + u)) r =
      UniStatement.rowEq (pt.map fun x ↦ UniStatement.sqn x twist) v r * UniStatement.selector r v off := by
  set q := (pt ++ List.replicate v 0).take v with hq
  have hql : q.length = v := by simp [hq]
  have hq' : (q.map (· ^ 2 ^ twist)).length = (r.take v).length := by simp [hql, hv]
  rw [rowEq_eq _ (q.map (· ^ 2 ^ twist)) r v (by simp [hql]) hv, ← sum_eqEval_eqEval _ _ hq', sum_mul]
  · simp only [List.length_map, hql]
    refine sum_congr rfl fun u hu ↦ ?_
    have hu' := mem_range.mp hu
    rw [eqKernel_getD' q (by rw [hql]; exact hu'), hql, sqn_eq_pow, eqEval_boolPoint_pow twist v u q hql,
      eqEval_block hv hoff hu', mul_assoc]
  · intro k hk
    rw [getD_map_zero q (· ^ 2 ^ twist) (zero_frob twist),
      getD_map_zero pt (fun x ↦ UniStatement.sqn x twist) (by rw [sqn_eq_pow]; exact zero_frob twist),
      sqn_eq_pow, hq]
    congr 1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hk, ite_true, List.getElem?_append]
    split_ifs with h
    · rfl
    · simp [List.getElem?_eq_none (show pt.length ≤ k by omega)]

/-- **The ring-switch term on a block**: the dense weight `Φ(eq(p, ·))` on the block's words, paired with
`eq(·, r)`, is `towerWeightAt` of the point's and `1 + r`'s first `v` coordinates times the selector. -/
theorem block_ring {r : List E} {v off : ℕ} (hv : v ≤ r.length) (hoff : 2 ^ v ∣ off) (pt map : List E)
    (hpt : v ≤ pt.length) (hmap : map.length ≤ 6) :
    ∑ u ∈ range (2 ^ v), UniStatement.Flock.towerRingMap
        ((UniStatement.eqKernel ((pt ++ List.replicate v 0).take v)).getD u 0) map *
        eqEval (boolPoint r.length (off + u)) r =
      UniStatement.Flock.towerWeightAt (pt.take v) ((r.map (1 + ·)).take v) map * UniStatement.selector r v off := by
  rw [List.take_append_of_le_length hpt, ← List.map_take,
    towerWeightAt_eq_sum _ _ _ (by simp [hpt, hv]), sum_mul]
  have hql : (pt.take v).length = v := by simp [hpt]
  rw [hql]
  refine sum_congr rfl fun u hu ↦ ?_
  have hu' := mem_range.mp hu
  rw [eqKernel_getD' _ (by rw [hql]; exact hu'), hql, towerRingMap_eq _ _ hmap, eqEval_block hv hoff hu',
    mul_assoc]

/-- **A slot term on `q_flock`'s block**: the dense weight `eq(p, u)` at the words `j + 256 u`, paired with
`eq(·, r)`, is `rowEq` of the slot's bits then the point, times the selector. -/
theorem block_slot {r : List E} {v off : ℕ} (hv : v ≤ r.length) (hoff : 2 ^ v ∣ off) (pt : List E)
    (hpt : pt.length + 8 = v) {j : ℕ} (hj : j < 256) :
    ∑ u ∈ range (UniStatement.eqKernel pt).size,
        (UniStatement.eqKernel pt).getD u 0 * eqEval (boolPoint r.length (off + j + 256 * u)) r =
      UniStatement.rowEq ((List.range 8).map (UniStatement.bitE j) ++ pt)
        ((List.range 8).map (UniStatement.bitE j) ++ pt).length r * UniStatement.selector r v off := by
  obtain rfl : v = 8 + pt.length := by omega
  have hbits : (List.range 8).map (UniStatement.bitE j) = boolPoint 8 j := rfl
  have hlen : ((List.range 8).map (UniStatement.bitE j) ++ pt).length = 8 + pt.length := by
    simp only [List.length_append, List.length_map, List.length_range]
  have h8 : (boolPoint 8 j).length = ((r.take (8 + pt.length)).take 8).length := by
    rw [length_boolPoint, List.length_take, List.length_take]; omega
  have hd : pt.length = ((r.take (8 + pt.length)).drop 8).length := by
    rw [List.length_drop, List.length_take]; omega
  have hsplit : ∀ b : List E, eqEval (boolPoint 8 j ++ b) (r.take (8 + pt.length)) =
      eqEval (boolPoint 8 j) ((r.take (8 + pt.length)).take 8) *
        eqEval b ((r.take (8 + pt.length)).drop 8) := by
    intro b
    conv_lhs => arg 2; rw [← List.take_append_drop 8 (r.take (8 + pt.length))]
    exact eqEval_append _ _ _ _ h8
  rw [hlen, rowEq_eq _ _ r _ hlen hv (fun _ _ ↦ rfl), eqKernel_size, hbits, hsplit,
    ← sum_eqEval_eqEval pt _ hd, mul_sum, sum_mul]
  refine sum_congr rfl fun u hu ↦ ?_
  have hu' := mem_range.mp hu
  have hx : j + 2 ^ 8 * u < 2 ^ (8 + pt.length) := by
    rw [pow_add]
    exact LeanVM.Protocol.Whir.Complete.add_mul_lt (by norm_num; exact hj) hu'
  rw [eqKernel_getD' pt hu', show off + j + 256 * u = off + (j + 2 ^ 8 * u) by ring, eqEval_block hv hoff hx,
    boolPoint_add 8 pt.length j u (by norm_num; exact hj), hsplit]
  ring

/-! ## The twisted points -/

/-- `twistedPoints point m` holds the point squared `t` times at `t ≤ m`. -/
theorem twistedPoints_spec (point : List E) : ∀ m : ℕ,
    (UniStatement.twistedPoints point m).size = m + 1 ∧
      ∀ t ≤ m, (UniStatement.twistedPoints point m).getD t [] = point.map fun x ↦ UniStatement.sqn x t
  | 0 => by
    refine ⟨rfl, fun t ht ↦ ?_⟩
    obtain rfl : t = 0 := by omega
    simp [UniStatement.twistedPoints, UniStatement.sqn]
  | m + 1 => by
    obtain ⟨h1, h2⟩ := twistedPoints_spec point m
    unfold UniStatement.twistedPoints at h1 h2 ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range m).foldl _ _ = a at h1 h2 ⊢
    have hback : a.back?.getD point = point.map fun x ↦ UniStatement.sqn x m := by
      have hm : m < a.size := by omega
      rw [← h2 m le_rfl, Array.back?_eq_getElem?, h1, Nat.add_sub_cancel, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hm]
      rfl
    refine ⟨by simp [h1], fun t ht ↦ ?_⟩
    rw [hback]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, h1] at h2 ⊢
    by_cases htm : t = m + 1
    · subst htm
      simp only [ite_true, Option.getD_some, List.map_map]
      refine List.map_congr_left fun x _ ↦ ?_
      simp only [Function.comp_apply, sqn_eq_pow]
      rw [← sq, ← pow_mul, ← pow_succ]
    · rw [ite_neg htm]
      exact h2 t (by omega)

/-- `weightAt`'s largest twist of each point: at least every non-ring term's twist. -/
theorem maxTwist_spec (f : Array ℕ → Column × ℕ × ℕ × E → Array ℕ)
    (hf : ∀ acc x, f acc x = if x.2.2.1 = UniStatement.ringTwist then acc else acc.modify x.2.1 (max x.2.2.1)) :
    ∀ (terms : List (Column × ℕ × ℕ × E)) (acc : Array ℕ),
      (terms.foldl f acc).size = acc.size ∧ (∀ i, acc.getD i 0 ≤ (terms.foldl f acc).getD i 0) ∧
        ∀ x ∈ terms, x.2.2.1 ≠ UniStatement.ringTwist → x.2.1 < acc.size → x.2.2.1 ≤ (terms.foldl f acc).getD x.2.1 0
  | [], acc => ⟨rfl, fun _ ↦ le_rfl, fun _ h ↦ by simp at h⟩
  | x :: terms, acc => by
    have hstep_size : (f acc x).size = acc.size := by
      rw [hf]; split_ifs <;> simp
    have hstep_mono : ∀ i, acc.getD i 0 ≤ (f acc x).getD i 0 := fun i ↦ by
      rw [hf]
      split_ifs
      · exact le_rfl
      · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
        split_ifs
        · cases acc[i]? <;> simp
        · exact le_rfl
    obtain ⟨h1, h2, h3⟩ := maxTwist_spec f hf terms (f acc x)
    rw [List.foldl_cons]
    refine ⟨by rw [h1, hstep_size], fun i ↦ (hstep_mono i).trans (h2 i), fun y hy hring hlt ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · refine le_trans ?_ (h2 y.2.1)
      rw [hf, ite_neg hring]
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getElem?_eq_getElem hlt]
    · exact h3 y hy hring (by rw [hstep_size]; exact hlt)

/-! ## The theorem -/

/-- **A combined claim well formed for its layout**, what `weightAt` and `denseWeight` need to agree:

* a slot term (`qflockSlot j`) is untwisted, `j < 256`, and its point has `v − 8` coordinates for every block of
  `q_flock` (`v` its variables);
* a ring-switch term's point has at least `v` coordinates for every block of its column;
* the ring map has at most six stages. -/
structure WeightWF (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) : Prop where
  slot : ∀ j p twist coefficient, (Column.qflockSlot j, p, twist, coefficient) ∈ claim.terms →
    twist = 0 ∧ j < 256 ∧
      ∀ limb v off, (limb, v, off) ∈ layout.limbs .qflock → (claim.points.getD p []).length + 8 = v
  ring : ∀ column p coefficient, (column, p, UniStatement.ringTwist, coefficient) ∈ claim.terms →
    ∀ limb v off, (limb, v, off) ∈ layout.limbs column → v ≤ (claim.points.getD p []).length
  map : ∀ map, ringMap = some map → map.length ≤ 6

/-- `weightAt`'s twisted points (its text). -/
def twistedOf (claim : Combined) : Array (Array (List E)) :=
  let points := claim.points.toArray
  let maxTwist : Array ℕ := claim.terms.foldl (fun acc (_, p, twist, _) ↦
    if twist = UniStatement.ringTwist then acc else acc.modify p (max twist)) (Array.replicate points.size 0)
  Array.ofFn (n := points.size) fun p ↦
    UniStatement.twistedPoints (points.getD p.val []) (maxTwist.getD p.val 0)

/-- `weightAt`'s step on a term (its text), given the twisted points. -/
def weightStep (claim : Combined) (layout : StackLayout) (r : List E) (ringMap : Option (List E))
    (twisted : Array (Array (List E))) : E → Column × ℕ × ℕ × E → E :=
  let points := claim.points.toArray
  let onePlusR := r.map (1 + ·)
  fun total (column, p, twist, coefficient) ↦
    if twist = UniStatement.ringTwist then
      (layout.limbs column).foldl (fun total (limb, vars, offset) ↦
        let row := match ringMap with
          | some map => UniStatement.Flock.towerWeightAt ((points.getD p []).take vars) (onePlusR.take vars) map
          | none => 0
        let scale := if limb = 0 then coefficient else coefficient * UniStatement.limbBasis.getD limb 0
        total + scale * (row * UniStatement.selector r vars offset)) total
    else
    let point := (twisted.getD p #[]).getD twist []
    let (column, row, rowLen) : Column × List E × ℕ := match column with
      | .qflockSlot j =>
        let row := (List.range 8).map (UniStatement.bitE j) ++ point
        (.qflock, row, row.length)
      | _ => (column, point, 0)
    (layout.limbs column).foldl (fun total (limb, vars, offset) ↦
      let len := if rowLen > 0 then rowLen else vars
      let eq := UniStatement.rowEq row len r * UniStatement.selector r vars offset
      let scale := if limb = 0 then coefficient else coefficient * UniStatement.limbBasis.getD limb 0
      total + scale * eq) total

theorem weightAt_eq_fold (claim : Combined) (layout : StackLayout) (r : List E) (ringMap : Option (List E)) :
    UniStatement.weightAt claim layout r ringMap =
      claim.terms.foldl (weightStep claim layout r ringMap (twistedOf claim)) 0 := rfl

/-- `denseWeight`'s step on a term (its text). -/
def denseStep (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) :
    Array E → Column × ℕ × ℕ × E → Array E :=
  let points := claim.points.toArray
  fun (W : Array E) (column, p, twist, coefficient) ↦
    let point := points.getD p []
    match column with
    | .qflockSlot j =>
      (layout.limbs .qflock).foldl (fun W (limb, _, offset) ↦
        let scale := limbScale coefficient limb
        let eq := UniStatement.eqKernel point
        (List.range eq.size).foldl (fun W u ↦ addAt W (offset + j + 256 * u) (scale * eq.getD u 0)) W) W
    | _ =>
      (layout.limbs column).foldl (fun W (limb, vars, offset) ↦
        let scale := limbScale coefficient limb
        let eq := UniStatement.eqKernel ((point ++ List.replicate vars 0).take vars)
        (List.range (2 ^ vars)).foldl (fun W u ↦
          let e := eq.getD u 0
          let v := if twist = UniStatement.ringTwist then
              (match ringMap with
                | some map => UniStatement.Flock.towerRingMap e map
                | none => 0)
            else UniStatement.sqn e twist
          addAt W (offset + u) (scale * v)) W) W

theorem denseWeight_eq_fold (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) :
    denseWeight claim layout ringMap =
      claim.terms.foldl (denseStep claim layout ringMap) (Array.replicate (2 ^ layout.vars) 0) := rfl

/-- **The twisted point of a non-ring term** is its point squared `twist` times. -/
theorem twistedOf_getD (claim : Combined) {column : Column} {p twist : ℕ} {c : E}
    (hmem : (column, p, twist, c) ∈ claim.terms) (hring : twist ≠ UniStatement.ringTwist) :
    ((twistedOf claim).getD p #[]).getD twist [] = (claim.points.getD p []).map fun x ↦ UniStatement.sqn x twist := by
  unfold twistedOf
  dsimp only
  by_cases hp : p < claim.points.toArray.size
  · rw [E2ECompleteness.getD_ofFn' _ hp]
    obtain ⟨-, -, h3⟩ := maxTwist_spec _ (fun _ _ ↦ rfl) claim.terms (Array.replicate claim.points.toArray.size 0)
    have hle := h3 (column, p, twist, c) hmem hring (by simpa using hp)
    rw [(twistedPoints_spec _ _).2 twist hle, E2ECompleteness.toArray_getD']
  · have hp' : claim.points.length ≤ p := by simpa using hp
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, hp']

theorem limbScale_eq (c : E) (limb : ℕ) :
    limbScale c limb = if limb = 0 then c else c * UniStatement.limbBasis.getD limb 0 := rfl

/-- **One term's step**: the dense weight's step adds to the multilinear extension what `weightAt`'s step adds. -/
theorem term_step (claim : Combined) (layout : StackLayout) (r : List E) (ringMap : Option (List E))
    (hal : Aligned layout) (hr : layout.vars ≤ r.length) (hwf : WeightWF claim layout ringMap)
    (t : Column × ℕ × ℕ × E) (ht : t ∈ claim.terms) (W : Array E) (hW : W.size = 2 ^ layout.vars) :
    (denseStep claim layout ringMap W t).size = 2 ^ layout.vars ∧
      ∀ s, mleAt r.length r (denseStep claim layout ringMap W t) + s =
        mleAt r.length r W + weightStep claim layout r ringMap (twistedOf claim) s t := by
  obtain ⟨column, p, twist, coefficient⟩ := t
  have hWR : 2 ^ layout.vars ≤ 2 ^ r.length := Nat.pow_le_pow_right (by norm_num) hr
  unfold denseStep weightStep
  dsimp only
  simp only [E2ECompleteness.toArray_getD']
  set pt := claim.points.getD p [] with hpt
  by_cases hs : ∃ j, column = .qflockSlot j
  · -- A slot term: untwisted, on `q_flock`'s blocks.
    obtain ⟨j, rfl⟩ := hs
    obtain ⟨htw, hj, hlen⟩ := hwf.slot j p twist coefficient ht
    subst htw
    have hpt0 : ((twistedOf claim).getD p #[]).getD 0 [] = pt := by
      rw [twistedOf_getD claim ht (by decide)]
      exact List.map_id'' (fun _ ↦ rfl) _
    simp only [show (0 : ℕ) ≠ UniStatement.ringTwist by decide, ite_false, hpt0]
    refine foldl_couple (mleAt r.length r) (fun W ↦ W.size = 2 ^ layout.vars) _ _ _ ?_ W hW
    rintro ⟨limb, v, off⟩ hb W' hW'
    dsimp only
    obtain ⟨hdiv, hbound⟩ := hal _ _ _ _ (mem_limbs hb)
    have hv : pt.length + 8 = v := hlen limb v off hb
    have hvr : v ≤ r.length := by
      have : 2 ^ v ≤ 2 ^ r.length := le_trans (le_trans (Nat.le_add_left _ _) hbound) hWR
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    obtain ⟨h1, h2⟩ := mleAt_range_addAt r.length r (fun u ↦ off + j + 256 * u)
      (fun u ↦ limbScale coefficient limb * (UniStatement.eqKernel pt).getD u 0)
      (UniStatement.eqKernel pt).size W' (fun u hu ↦ by
        rw [eqKernel_size] at hu
        have hx : j + 2 ^ 8 * u < 2 ^ v := by
          rw [show 2 ^ v = 2 ^ 8 * 2 ^ pt.length by rw [← pow_add]; congr 1; omega]
          exact LeanVM.Protocol.Whir.Complete.add_mul_lt (by norm_num; exact hj) hu
        omega) (by rw [hW']; exact hWR)
    refine ⟨h1.trans hW', fun s ↦ ?_⟩
    have hrow : ((List.range 8).map (UniStatement.bitE j) ++ pt).length > 0 := by simp
    rw [h2, ite_pos hrow]
    have hblock := block_slot hvr hdiv pt hv hj
    simp only [mul_assoc, ← mul_sum] at hblock ⊢
    rw [hblock, limbScale_eq]
    ring
  · have hns : ∀ j, column ≠ .qflockSlot j := fun j h ↦ hs ⟨j, h⟩
    split
    · exact absurd rfl (hns _)
    by_cases hring : twist = UniStatement.ringTwist
    · -- The ring-switch term.
      subst hring
      simp only [ite_true]
      refine foldl_couple (mleAt r.length r) (fun W ↦ W.size = 2 ^ layout.vars) _ _ _ ?_ W hW
      rintro ⟨limb, v, off⟩ hb W' hW'
      dsimp only
      obtain ⟨hdiv, hbound⟩ := hal _ _ _ _ (mem_limbs hb)
      have hvpt : v ≤ pt.length := hwf.ring column p coefficient ht limb v off hb
      have hvr : v ≤ r.length := by
        have : 2 ^ v ≤ 2 ^ r.length := le_trans (le_trans (Nat.le_add_left _ _) hbound) hWR
        exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
      rcases ringMap with _ | map
      · dsimp only
        obtain ⟨h1, h2⟩ := mleAt_range_addAt r.length r (fun u ↦ off + u) (fun _ ↦ limbScale coefficient limb * 0)
          (2 ^ v) W' (fun u hu ↦ by rw [hW']; omega) (by rw [hW']; exact hWR)
        refine ⟨h1.trans hW', fun s ↦ ?_⟩
        rw [h2]
        simp
      · dsimp only
        obtain ⟨h1, h2⟩ := mleAt_range_addAt r.length r (fun u ↦ off + u)
          (fun u ↦ limbScale coefficient limb * UniStatement.Flock.towerRingMap
            ((UniStatement.eqKernel ((pt ++ List.replicate v 0).take v)).getD u 0) map)
          (2 ^ v) W' (fun u hu ↦ by rw [hW']; omega) (by rw [hW']; exact hWR)
        refine ⟨h1.trans hW', fun s ↦ ?_⟩
        have hblock := block_ring hvr hdiv pt map hvpt (hwf.map map rfl)
        rw [h2]
        simp only [mul_assoc, ← mul_sum] at hblock ⊢
        rw [hblock, limbScale_eq]
        ring
    · -- A plain or twisted term.
      simp only [hring, ite_false]
      rw [twistedOf_getD claim ht hring]
      simp only [gt_iff_lt, lt_irrefl, ite_false]
      refine foldl_couple (mleAt r.length r) (fun W ↦ W.size = 2 ^ layout.vars) _ _ _ ?_ W hW
      rintro ⟨limb, v, off⟩ hb W' hW'
      dsimp only
      obtain ⟨hdiv, hbound⟩ := hal _ _ _ _ (mem_limbs hb)
      have hvr : v ≤ r.length := by
        have : 2 ^ v ≤ 2 ^ r.length := le_trans (le_trans (Nat.le_add_left _ _) hbound) hWR
        exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
      obtain ⟨h1, h2⟩ := mleAt_range_addAt r.length r (fun u ↦ off + u)
        (fun u ↦ limbScale coefficient limb * UniStatement.sqn
          ((UniStatement.eqKernel ((pt ++ List.replicate v 0).take v)).getD u 0) twist)
        (2 ^ v) W' (fun u hu ↦ by rw [hW']; omega) (by rw [hW']; exact hWR)
      refine ⟨h1.trans hW', fun s ↦ ?_⟩
      have hblock := block_regular hvr hdiv pt twist
      rw [h2]
      simp only [mul_assoc, ← mul_sum] at hblock ⊢
      rw [hblock, limbScale_eq]
      ring

/-- **`weightAt` is the multilinear extension of the dense weight**: for a well-formed combined claim on an
aligned layout, at a point of at least the layout's variables, the verifier's `weightAt` is
`Σ_x W[x] · eq(x, r)` over the `2^|r|` words of the prover's `denseWeight` zero-extended. -/
theorem weightAt_eq_mle (claim : Combined) (layout : StackLayout) (r : List E) (ringMap : Option (List E))
    (hal : Aligned layout) (hr : layout.vars ≤ r.length) (hwf : WeightWF claim layout ringMap) :
    UniStatement.weightAt claim layout r ringMap = mleAt r.length r (denseWeight claim layout ringMap) := by
  rw [weightAt_eq_fold, denseWeight_eq_fold]
  obtain ⟨-, h⟩ := foldl_couple (mleAt r.length r) (fun W ↦ W.size = 2 ^ layout.vars)
    (denseStep claim layout ringMap) (weightStep claim layout r ringMap (twistedOf claim)) claim.terms
    (fun t ht W hW ↦ term_step claim layout r ringMap hal hr hwf t ht W hW) (Array.replicate (2 ^ layout.vars) 0)
    (by simp)
  have := h 0
  rw [add_zero, mleAt_replicate, zero_add] at this
  exact this.symm

/-- **The same on `StackLayout.new`'s layouts** (aligned, `aligned_new`). -/
theorem weightAt_eq_mle_new (claim : Combined) (columns : List (Column × ℕ × Bool)) (r : List E)
    (ringMap : Option (List E)) (hr : (StackLayout.new columns).vars ≤ r.length)
    (hwf : WeightWF claim (StackLayout.new columns) ringMap) :
    UniStatement.weightAt claim (StackLayout.new columns) r ringMap =
      mleAt r.length r (denseWeight claim (StackLayout.new columns) ringMap) :=
  weightAt_eq_mle claim _ r ringMap (aligned_new columns) hr hwf

end UniComplete

/-- info: 'UniComplete.weightAt_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.weightAt_eq_mle

/-- info: 'UniComplete.weightAt_eq_mle_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.weightAt_eq_mle_new

/-- info: 'UniComplete.towerWeightAt_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.towerWeightAt_eq_sum
