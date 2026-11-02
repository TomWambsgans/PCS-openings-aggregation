-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.DecoderDeployed
import QuotientSecurity.Setup

/-!
# `quotient::protocol::reduce`'s claims, and what they say of F1's polynomials

`reduce` (`crates/quotient/src/protocol.rs`) reads the statement and the proof, draws the
challenges, and computes four WHIR claims, each a point and a value: one on the witness table,
one on the wiring table, two on the quotient table. F4a's chain (`QuotientRpm/Chain.lean`,
`Compose/ListChain.lean`'s `chainWith`) computes the challenges byte for byte; this file
transcribes **what `reduce` computes from them** (`reduce`), over `E = F192` (mumbai's `E`,
`formal/Field/F192.lean`'s `F192`, the same type), and proves what those claims mean for F1:

* **`witness_iff`**: a table `c` (as F1 reads it: `c b` the entry whose index has bits `b`) whose
  multilinear extension takes the witness claim's value at its point is exactly a table whose
  four row polynomials (`witnessOfTable c`) satisfy F1's witness claim (`Openings.lean`'s
  `witnessClaim`);
* **`wiring_iff`**: the wiring claim is the wiring table's polynomial taking the fifth value;
* **`quotientClaims_of`**: a quotient table satisfying both claims on it holds a second message
  (`quotientsOfTable`) satisfying F1's two quotient claims, for parameters `P` whose cells are a
  Cantor basis's points and whose `θ`, public weight, rows' vanishing polynomial and target are
  `reduce`'s (`Matches`);
* **`matches_params`**: F1's instance (`Instance.params`, the cells of a Cantor basis, the
  membership public weight) matches `reduce`'s constants when its basis is `beta()`'s words
  (`hβ`), its weights `coordinate_weight`'s (`hc`) and `row_vanishing(m)`'s `tau` solves its system
  (`RowVanishing`).

This was `Concrete.lean`'s comment "The claims against `quotient::protocol::reduce`, coordinate
by coordinate", checked by review and differential tests only; here it is a theorem about a Lean
transcription of `reduce`.

**The transcription.** Line by line `reduce`'s, after the channel: `w` (`wChain`), the row's
cells (`cell`, `rowCells`), the gate (`gate4`), `public` (`publicWeight`, its two folds as
`foldRange`, `coordinate`, `slope`), `target`, `rows`, the denominators, the claims (`claimsOf`),
`extension()`, `sum_point`. `Scalar` is `F192` (the field verifier; the EVM contract records the
same operations, F5). Two steps are modelled by what they compute, not how: the one inversion
(`inverse` by the norm to `GF(2^64)`, then the prefix products of the batch) is each
denominator's field inverse once their product is nonzero, and `coordinates`'s fold over `e` is a
sum. `reduce` returns `none` (`VerifyError::Degenerate`) exactly when a denominator vanishes
(`reduce_eq_some`). The constants `beta()` and `row_vanishing(m)`, which the Rust computes at run
time (a pivot search, a Gaussian elimination), are parameters (`Consts`), constrained only in the
statements that need them (`hβ`, `RowVanishing`); `coordinates`, `coordinate_weight`,
`bit_weight`, `extension` and `Statement::halves` are transcribed.
-/

set_option linter.unusedSectionVars false

namespace Compose

namespace Reduce

open LeanVM.Parameters WhirBridge QuotientSecurity QuotientSecurity.Params Finset Polynomial

/-! ## Folds -/

/-- `(lo..hi).fold(init, f)`: `f` applied to `lo, lo + 1, …, hi − 1` in turn. -/
def foldRange {α : Type} (lo hi : ℕ) (init : α) (f : α → ℕ → α) : α :=
  (List.range' lo (hi - lo)).foldl f init

theorem foldl_range'_mul {M : Type} [CommMonoid M] (g : ℕ → M) :
    ∀ (s n : ℕ) (a : M),
      (List.range' s n).foldl (fun acc k => acc * g k) a = a * ∏ k ∈ range n, g (s + k)
  | _, 0, a => by simp
  | s, n + 1, a => by
    rw [List.range'_succ, List.foldl_cons, foldl_range'_mul g (s + 1) n, prod_range_succ',
      add_zero, mul_assoc, mul_comm (g s)]
    congr 2
    exact prod_congr rfl fun k _ => by rw [add_assoc, add_comm 1 k]

theorem foldl_range'_add {M : Type} [AddCommMonoid M] (g : ℕ → M) :
    ∀ (s n : ℕ) (a : M),
      (List.range' s n).foldl (fun acc k => acc + g k) a = a + ∑ k ∈ range n, g (s + k)
  | _, 0, a => by simp
  | s, n + 1, a => by
    rw [List.range'_succ, List.foldl_cons, foldl_range'_add g (s + 1) n, sum_range_succ',
      add_zero, add_assoc, add_comm (g s)]
    congr 2
    exact sum_congr rfl fun k _ => by rw [add_assoc, add_comm 1 k]

theorem foldRange_mul {M : Type} [CommMonoid M] (lo hi : ℕ) (a : M) (g : ℕ → M) :
    foldRange lo hi a (fun acc k => acc * g k) = a * ∏ k ∈ Ico lo hi, g k := by
  rw [foldRange, foldl_range'_mul, prod_Ico_eq_prod_range]

theorem foldRange_add {M : Type} [AddCommMonoid M] (lo hi : ℕ) (a : M) (g : ℕ → M) :
    foldRange lo hi a (fun acc k => acc + g k) = a + ∑ k ∈ Ico lo hi, g k := by
  rw [foldRange, foldl_range'_add, sum_Ico_eq_sum_range]

/-! ## `K` inside `E` -/

theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem ofK_one : ofK 1 = 1 := map_one (algebraMap K E)

theorem ofK_zero : ofK 0 = 0 := map_zero (algebraMap K E)

theorem ofK_sumFin {n : ℕ} (f : Fin n → K) : ofK (∑ i, f i) = ∑ i, ofK (f i) :=
  map_sum (algebraMap K E) f univ

/-! ## The constants -/

/-- **The constants `reduce` reads**, as the Rust computes them (words of `K = F64`):
`domain::beta()` (`beta[0] = 1`, `S(beta[k + 1]) = beta[k]`, the solution with its low bit clear)
and `domain::row_vanishing(m)` (`tau`). -/
structure Consts where
  beta : ℕ → K
  tau : ℕ → K

/-- `REGION` (`protocol.rs`): the public bits are cells of the span of the first `11` basis
vectors. -/
def region : ℕ := 11

/-- **`domain::coordinates`**: `b[0] = 1`, `b[d] = Σ_{e = 1}^{d} beta[e] · b[d − e]` (the Rust's
fold over `1..=d`, here as a sum; index `d + 1` written with `e + 1`). -/
def coordinates (beta : ℕ → K) : ℕ → K
  | 0 => 1
  | d + 1 => ∑ e : Fin (d + 1), beta (e + 1) * coordinates beta (d - e)
decreasing_by omega

/-- **`bit_weight(j)`**: `F192::new(1 << j, 0, 0)` for `j < 64`, `F192::new(0, 1 << (j − 64), 0)`
above. -/
def bitWeight (j : ℕ) : E :=
  if j < 64 then E.ofLimbs (K.ofBits (1 <<< j)) 0 0 else E.ofLimbs 0 (K.ofBits (1 <<< (j - 64))) 0

/-- **`coordinate_weight(k)`**: `bit_weight(1)` for `0`, zero for `1`, `bit_weight(1 << (k − 1))`
for `2..8`, `None` (a power of `gamma`) from `8` on. -/
def coordinateWeight (k : ℕ) : Option E :=
  if k = 0 then some (bitWeight 1) else if k = 1 then some 0
  else if k < 8 then some (bitWeight (1 <<< (k - 1))) else none

/-- **`extension()`**: `([y / (1 + y), y^2 / (1 + y^2)], ((1 + y)(1 + y^2))⁻¹)`, `y = F192::Y`
(mumbai's `y`, `F192.Y_eq_gen`). -/
def extension : (E × E) × E :=
  let y2 := y * y
  let d0 := 1 + y
  let d1 := 1 + y2
  ((y * d0⁻¹, y2 * d1⁻¹), (d0 * d1)⁻¹)

/-- **`sum_point(log_rows)`**: `m` ones, four zeros, the extension's two coordinates. -/
def sumPoint (m : ℕ) : List E :=
  List.replicate m 1 ++ List.replicate 4 0 ++ [extension.1.1, extension.1.2]

/-! ## The statement -/

/-- One of **`statement::halves`**: `v = u128::from_be_bytes(bytes[16 h..16 h + 16])`
(`halfValue`), then `F192::new(v as u64, (v >> 64) as u64, 0)`. -/
def stmtHalf (b : Fin 32 → UInt8) (h : Fin 2) : E :=
  E.ofLimbs (K.ofBits (halfValue b h % 2 ^ 64)) (K.ofBits (halfValue b h >>> 64)) 0

/-- `y`, the statement's first 32 bytes. -/
def yOf (sb : Vector UInt8 64) : Fin 32 → UInt8 := fun i => sb.get ⟨i, by omega⟩

/-- `root`, the statement's last 32 bytes. -/
def rootOf (sb : Vector UInt8 64) : Fin 32 → UInt8 := fun i => sb.get ⟨32 + i, by omega⟩

/-- **`Statement::halves`**: `y` then `root`, each as its two halves (`channel.statement()`). -/
def stmtHalves (sb : Vector UInt8 64) : Fin 4 → E :=
  ![stmtHalf (yOf sb) 0, stmtHalf (yOf sb) 1, stmtHalf (rootOf sb) 0, stmtHalf (rootOf sb) 1]

/-- The eight public words the target sums: the halves, then `1, 0, 0, 0` (`reduce`'s target adds
`gamma^4`). -/
def stmtWords (sb : Vector UInt8 64) : Fin 8 → E :=
  ![stmtHalves sb 0, stmtHalves sb 1, stmtHalves sb 2, stmtHalves sb 3, 1, 0, 0, 0]

/-! ## `reduce`, after the channel -/

/-- `w_k(t)`: `w_0 = t`, `w_{k+1} = w_k · w_k + w_k` (`reduce`'s `w`, kept up to `k = m + 1`). -/
def wChain (t : E) : ℕ → E
  | 0 => t
  | k + 1 => wChain t k * wChain t k + wChain t k

/-- `reduce`'s `cell(shift, second)`: `a_0 + first a_1 + second (a_2 + first a_3)`, `first =
t + shift`, `second = w_1` or `w_1 + 1`. -/
def cell (t : E) (a : Fin 4 → E) (shift : K) (second : Bool) : E :=
  let first := t + ofK shift
  let second := if second then wChain t 1 + 1 else wChain t 1
  a 0 + first * a 1 + second * (a 2 + first * a 3)

/-- `reduce`'s `row`: the four cells of the row of `t`, `θ = beta()[1]`. -/
def rowCells (c : Consts) (t : E) (a : Fin 4 → E) : Fin 4 → E :=
  ![cell t a 0 false, cell t a 1 false, cell t a (c.beta 1) true, cell t a (c.beta 1 + 1) true]

/-- `gate([x, y, c, v]) = v + x + c + y·c`. -/
def gate4 (row : Fin 4 → E) : E := row 3 + row 0 + row 2 + row 1 * row 2

/-- `reduce`'s `coordinate` for `k < REGION`: `(k + 1..REGION).fold(w[k], |acc, j| acc + b[j − k]
w[j])`, `b = coordinates(REGION)`. -/
def coordinate (c : Consts) (t : E) (k : ℕ) : E :=
  foldRange (k + 1) region (wChain t k) fun acc j => acc + ofK (coordinates c.beta (j - k)) *
    wChain t j

/-- `reduce`'s `slope` for `k < REGION`: `1 + coordinate_weight(k)`, or `1 + gammas[k − 8]`. -/
def slope (γ : E) (k : ℕ) : E :=
  match coordinateWeight k with
  | some weight => 1 + weight
  | none => 1 + [γ, γ * γ, γ * γ * (γ * γ)].getD (k - 8) 0

/-- **`reduce`'s `public`**: `(REGION..m).fold(1, |acc, k| acc (1 + w[k]))`, then times
`1 + coordinate · slope` for each `k < REGION`. -/
def publicWeight (c : Consts) (m : ℕ) (γ t : E) : E :=
  foldRange 0 region (foldRange region m 1 fun acc k => acc * (1 + wChain t k)) fun pub k =>
    pub * (1 + coordinate c t k * slope γ k)

/-- **`reduce`'s `target`**: `s_0 + γ s_1 + γ^2 (s_2 + γ s_3) + γ^4`. -/
def target (statement : Fin 4 → E) (γ : E) : E :=
  statement 0 + γ * statement 1 + γ * γ * (statement 2 + γ * statement 3) + γ * γ * (γ * γ)

/-- **`reduce`'s `rows`**: `(0..m − 1).fold(0, |acc, k| acc + tau[k] w[k])`. -/
def rows (c : Consts) (m : ℕ) (t : E) : E :=
  foldRange 0 (m - 1) 0 fun acc k => acc + ofK (c.tau k) * wChain t k

/-- `d · d_next`, `d = α + x + β t`, `d_next = α + x + β next`. -/
def product (c : Consts) (α β t : E) (a : Fin 4 → E) (next : E) : E :=
  (α + rowCells c t a 0 + β * t) * (α + rowCells c t a 0 + β * next)

/-- **The denominators `reduce` inverts at once**: every `1 + w_k` (`k ≤ m + 1`), the copy
identity's `product + w[m]`, and `rows`. -/
def denominators (c : Consts) (m : ℕ) (α β t : E) (a : Fin 4 → E) (next : E) : List E :=
  (List.range (m + 2)).map (fun k => 1 + wChain t k) ++
    [product c α β t a next + wChain t m, rows c m t]

/-- What `reduce` leaves: the three claims as a point and a value, and the claim at
`sum_point` (`Reduced`, and `verify`'s `Claims`; the roots are the chain's). -/
structure Reduced where
  witness : Claim
  wiring : Claim
  quotient : Claim
  sum : Claim

/-- `inverses[i]`: the inverse of denominator `i` (the one inversion and its prefix products, by
what they compute once the product is nonzero). -/
def inverses (c : Consts) (m : ℕ) (α β t : E) (a : Fin 4 → E) (next : E) (i : ℕ) : E :=
  ((denominators c m α β t a next).getD i 0)⁻¹

/-- **The claims `reduce` outputs**, once the denominators' product is nonzero. -/
def claimsOf (c : Consts) (m : ℕ) (statement : Fin 4 → E) (α β γ t : E) (a : Fin 4 → E)
    (next ρ : E) : Reduced :=
  let w := wChain t
  let row := rowCells c t a
  let x := row 0
  let gate := gate4 row
  let pub := publicWeight c m γ t
  let rows := rows c m t
  let d := α + x + β * t
  let d_next := α + x + β * next
  let product := d * d_next
  let copies := d + d_next + pub * x * product
  let inverses := inverses c m α β t a next
  let u : ℕ → E := fun k => w k * inverses k
  let copy_inverse := inverses (m + 2)
  let rows_inverse := inverses (m + 3)
  let middle := foldRange 3 m (inverses 2) fun acc k => acc * inverses k
  let wiring_scale := middle * inverses 0 * inverses 1
  let quotient_scale := wiring_scale * inverses m * inverses (m + 1)
  let rho2 := ρ * ρ
  let opened := (1 + rho2) * (a 0 + ρ * (a 0 + a 1)) + rho2 * (a 2 + ρ * (a 2 + a 3))
  let identities := (1 + ρ) * copies * rows + ρ * product * gate
  { witness := ⟨[ρ, rho2] ++ (List.range' 2 (m - 1)).map u, opened * middle * inverses m⟩
    wiring := ⟨(List.range m).map u, next * wiring_scale⟩
    quotient := ⟨(List.range (m + 2)).map u ++ [w m * copy_inverse, ρ, extension.1.1,
      extension.1.2], extension.2 * quotient_scale * copy_inverse * rows_inverse * identities⟩
    sum := ⟨sumPoint m, extension.2 * target statement γ⟩ }

section Fields

variable (c : Consts) (m : ℕ) (statement : Fin 4 → E) (α β γ t : E) (a : Fin 4 → E) (next ρ : E)

/-- `reduce`'s `middle`: `(3..m).fold(inverses[2], |acc, k| acc · inverses[k])`. -/
def middle : E :=
  foldRange 3 m (inverses c m α β t a next 2) fun acc k => acc * inverses c m α β t a next k

/-- `reduce`'s `identities`: `(1 + ρ) copies rows + ρ product gate`. -/
def identities (γ ρ : E) : E :=
  (1 + ρ) * ((α + rowCells c t a 0 + β * t) + (α + rowCells c t a 0 + β * next) +
      publicWeight c m γ t * rowCells c t a 0 * product c α β t a next) * rows c m t +
    ρ * product c α β t a next * gate4 (rowCells c t a)

theorem witness_point_eq :
    (claimsOf c m statement α β γ t a next ρ).witness.point =
      ρ :: (ρ * ρ) :: (List.range' 2 (m - 1)).map
        (fun k => wChain t k * inverses c m α β t a next k) := rfl

theorem witness_value_eq :
    (claimsOf c m statement α β γ t a next ρ).witness.value =
      ((1 + ρ * ρ) * (a 0 + ρ * (a 0 + a 1)) + ρ * ρ * (a 2 + ρ * (a 2 + a 3))) *
        middle c m α β t a next * inverses c m α β t a next m := rfl

theorem wiring_point_eq :
    (claimsOf c m statement α β γ t a next ρ).wiring.point =
      (List.range m).map (fun k => wChain t k * inverses c m α β t a next k) := rfl

theorem wiring_value_eq :
    (claimsOf c m statement α β γ t a next ρ).wiring.value =
      next * (middle c m α β t a next * inverses c m α β t a next 0 *
        inverses c m α β t a next 1) := rfl

theorem quotient_point_eq :
    (claimsOf c m statement α β γ t a next ρ).quotient.point =
      (List.range (m + 2)).map (fun k => wChain t k * inverses c m α β t a next k) ++
        [wChain t m * inverses c m α β t a next (m + 2), ρ, extension.1.1, extension.1.2] := rfl

theorem quotient_value_eq :
    (claimsOf c m statement α β γ t a next ρ).quotient.value =
      extension.2 * (middle c m α β t a next * inverses c m α β t a next 0 *
        inverses c m α β t a next 1 * inverses c m α β t a next m *
        inverses c m α β t a next (m + 1)) * inverses c m α β t a next (m + 2) *
        inverses c m α β t a next (m + 3) * identities c m α β t a next γ ρ := rfl

theorem sum_point_eq :
    (claimsOf c m statement α β γ t a next ρ).sum.point = sumPoint m := rfl

theorem sum_value_eq :
    (claimsOf c m statement α β γ t a next ρ).sum.value =
      extension.2 * target statement γ := rfl

end Fields

/-- **`reduce`**, after the channel: `m` cell variables (`log_rows + 2`), the statement's halves,
the challenges `α, β, γ, t, ρ`, the values `a_0..a_3` and `next`. `none` is
`VerifyError::Degenerate`: a denominator vanishes. -/
def reduce (c : Consts) (m : ℕ) (statement : Fin 4 → E) (α β γ t : E) (a : Fin 4 → E)
    (next ρ : E) : Option Reduced :=
  if (denominators c m α β t a next).prod = 0 then none
  else some (claimsOf c m statement α β γ t a next ρ)

theorem reduce_eq_some {c : Consts} {m : ℕ} {statement : Fin 4 → E} {α β γ t : E}
    {a : Fin 4 → E} {next ρ : E} {r : Reduced}
    (h : reduce c m statement α β γ t a next ρ = some r) :
    (denominators c m α β t a next).prod ≠ 0 ∧ r = claimsOf c m statement α β γ t a next ρ := by
  unfold reduce at h
  split_ifs at h with h0
  exact ⟨h0, (Option.some.inj h).symm⟩

/-! ## The chain and the denominators -/

theorem wChain_eq (t : E) : ∀ k, wChain t k = sq^[k] t
  | 0 => rfl
  | k + 1 => by rw [wChain, wChain_eq t k, Function.iterate_succ_apply']; rfl

theorem getD_denominators_lt (c : Consts) (m : ℕ) (α β t : E) (a : Fin 4 → E) (next : E)
    {k : ℕ} (hk : k < m + 2) :
    (denominators c m α β t a next).getD k 0 = 1 + sq^[k] t := by
  rw [denominators, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hk)]
  simp [List.getElem?_map, List.getElem?_range hk, wChain_eq]

theorem getD_denominators_copy (c : Consts) (m : ℕ) (α β t : E) (a : Fin 4 → E) (next : E) :
    (denominators c m α β t a next).getD (m + 2) 0 = product c α β t a next + sq^[m] t := by
  rw [denominators, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [wChain_eq]

theorem getD_denominators_rows (c : Consts) (m : ℕ) (α β t : E) (a : Fin 4 → E) (next : E) :
    (denominators c m α β t a next).getD (m + 3) 0 = rows c m t := by
  rw [denominators, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- **`reduce` does not reject** exactly when no denominator vanishes. -/
theorem prod_denominators_ne_zero {c : Consts} {m : ℕ} {α β t : E} {a : Fin 4 → E} {next : E}
    (h : (denominators c m α β t a next).prod ≠ 0) :
    (∀ k < m + 2, 1 + sq^[k] t ≠ 0) ∧ product c α β t a next + sq^[m] t ≠ 0 ∧
      rows c m t ≠ 0 := by
  have hmem : ∀ x ∈ denominators c m α β t a next, x ≠ 0 := fun x hx h0 =>
    h (List.prod_eq_zero (h0 ▸ hx))
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · refine hmem _ ?_
    rw [denominators]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk,
      by rw [wChain_eq]⟩)
  · have := hmem _ (List.mem_append_right _ (List.mem_cons_self ..))
    rwa [wChain_eq] at this
  · exact hmem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

/-! ## Points as F1 reads them -/

theorem getD_cons_fun {n : ℕ} (x : E) (l : List E) :
    (fun k : Fin (n + 1) => (x :: l).getD k 0) = Fin.cons x (fun k : Fin n => l.getD k 0) := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp

theorem getD_snoc_fun {n : ℕ} (l : List E) (hl : l.length = n) (x : E) :
    (fun k : Fin (n + 1) => (l ++ [x]).getD k 0) = Fin.snoc (fun k : Fin n => l.getD k 0) x := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [List.getD_eq_getElem?_getD, hl]
  · simp only [Fin.snoc_castSucc, Fin.val_castSucc, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]

theorem getD_map_fun {n : ℕ} (s : ℕ) (f : ℕ → E) :
    (fun k : Fin n => ((List.range' s n).map f).getD k 0) = fun k : Fin n => f (s + k) := by
  funext k
  simp [List.getD_eq_getElem?_getD]

theorem getD_map_range_fun {n : ℕ} (f : ℕ → E) :
    (fun k : Fin n => ((List.range n).map f).getD k 0) = fun k : Fin n => f k := by
  funext k
  simp [List.getD_eq_getElem?_getD]

/-! ## The extension -/

theorem y_sq : y * y = y ^ 2 := (pow_two y).symm

theorem one_add_y_ne_zero : (1 : E) + y ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : E => z.limb 1) h
  have e : (1 : E) + y = E.ofLimbs 1 1 0 := by
    rw [ofLimbs_eq, ofK_one, ofK_zero]; ring
  have e0 : (0 : E) = E.ofLimbs 0 0 0 := by
    rw [ofLimbs_eq, ofK_zero]; ring
  simp only [e, e0, limb_ofLimbs] at h1
  exact one_ne_zero h1

theorem one_add_y_sq_ne_zero : (1 : E) + y ^ 2 ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : E => z.limb 2) h
  have e : (1 : E) + y ^ 2 = E.ofLimbs 1 0 1 := by
    rw [ofLimbs_eq, ofK_one, ofK_zero]; ring
  have e0 : (0 : E) = E.ofLimbs 0 0 0 := by
    rw [ofLimbs_eq, ofK_zero]; ring
  simp only [e, e0, limb_ofLimbs] at h1
  exact one_ne_zero h1

theorem extension_eq :
    extension = ((y / (1 + y), y ^ 2 / (1 + y ^ 2)), ((1 + y) * (1 + y ^ 2))⁻¹) := by
  simp only [extension, y_sq, div_eq_mul_inv]

theorem sumPoint_fun (n : ℕ) :
    (fun k : Fin (n + 2 + 1 + 1 + 1 + 1 + 1 + 1) => (sumPoint (n + 2)).getD k 0) =
      QuotientSecurity.sumPoint (n + 2) y := by
  have e : sumPoint (n + 2) = List.replicate (n + 2) 1 ++ [0] ++ [0] ++ [0] ++ [0] ++
      [y / (1 + y)] ++ [y ^ 2 / (1 + y ^ 2)] := by
    simp [sumPoint, extension_eq, List.replicate_succ]
  have hrep : (fun k : Fin (n + 2) => (List.replicate (n + 2) (1 : E)).getD k 0) = fun _ => 1 := by
    funext k; simp [List.getD_eq_getElem?_getD, k.2]
  rw [e, QuotientSecurity.sumPoint, getD_snoc_fun _ (by simp), getD_snoc_fun _ (by simp),
    getD_snoc_fun _ (by simp), getD_snoc_fun _ (by simp), getD_snoc_fun _ (by simp),
    getD_snoc_fun _ (by simp), hrep]

/-! ## The claims, in F1's terms -/

section Claims

variable (c : Consts) (n : ℕ) (statement : Fin 4 → E) (α β γ t : E) (a : Fin 4 → E) (next ρ : E)

theorem inverses_lt {k : ℕ} (hk : k < n + 2 + 2) :
    inverses c (n + 2) α β t a next k = (1 + sq^[k] t)⁻¹ := by
  rw [inverses, getD_denominators_lt c _ α β t a next hk]

theorem inverses_copy :
    inverses c (n + 2) α β t a next (n + 2 + 2) =
      (product c α β t a next + sq^[n + 2] t)⁻¹ := by
  rw [inverses, getD_denominators_copy]

theorem inverses_rows :
    inverses c (n + 2) α β t a next (n + 2 + 3) = (rows c (n + 2) t)⁻¹ := by
  rw [inverses, getD_denominators_rows]

/-- `middle · inverses[m]` is `∏_{2 ≤ k ≤ m} inverses[k]`. -/
theorem middle_mul (hn : 1 ≤ n) (f : ℕ → E) :
    foldRange 3 (n + 2) (f 2) (fun acc k => acc * f k) * f (n + 2) =
      ∏ i : Fin (n + 1), f (i + 2) := by
  have e : ∏ i ∈ range (n + 1), f (i + 2) = ∏ k ∈ Ico 2 (n + 2 + 1), f k := by
    rw [prod_Ico_eq_prod_range, show n + 2 + 1 - 2 = n + 1 by omega]
    exact prod_congr rfl fun i _ => by rw [add_comm]
  rw [foldRange_mul, Fin.prod_univ_eq_prod_range (fun i => f (i + 2)) (n + 1), e,
    prod_eq_prod_Ico_succ_bot (by omega : 2 < n + 2 + 1),
    prod_Ico_succ_top (by omega : 3 ≤ n + 2)]
  ring

/-- `middle · inverses[0] · inverses[1]` is `∏_{k < m} inverses[k]`. -/
theorem wiring_scale_eq (hn : 1 ≤ n) (f : ℕ → E) :
    foldRange 3 (n + 2) (f 2) (fun acc k => acc * f k) * f 0 * f 1 =
      ∏ i : Fin (n + 2), f i := by
  rw [foldRange_mul, Fin.prod_univ_eq_prod_range f (n + 2), range_eq_Ico,
    ← prod_Ico_consecutive _ (by omega : 0 ≤ 3) (by omega : 3 ≤ n + 2), ← range_eq_Ico]
  simp only [prod_range_succ, range_zero, prod_empty]
  ring

/-- `quotient_scale` is `∏_{k ≤ m + 1} inverses[k]`. -/
theorem quotient_scale_eq (hn : 1 ≤ n) (f : ℕ → E) :
    foldRange 3 (n + 2) (f 2) (fun acc k => acc * f k) * f 0 * f 1 * f (n + 2) * f (n + 2 + 1) =
      ∏ i : Fin (n + 2 + 1 + 1), f i := by
  rw [wiring_scale_eq n hn, Fin.prod_univ_eq_prod_range f (n + 2),
    Fin.prod_univ_eq_prod_range f (n + 2 + 1 + 1), prod_range_succ f (n + 2 + 1),
    prod_range_succ f (n + 2)]

/-- The coordinates `u_k = w_k · inverses[k]`, `k < m + 2`, are `claimPoint`'s. -/
theorem u_eq {k : ℕ} (hk : k < n + 2 + 2) :
    wChain t k * inverses c (n + 2) α β t a next k = sq^[k] t / (1 + sq^[k] t) := by
  rw [inverses_lt c n α β t a next hk, wChain_eq, div_eq_mul_inv]

theorem witness_point :
    (fun k : Fin (n + 1 + 1 + 1) =>
        (claimsOf c (n + 2) statement α β γ t a next ρ).witness.point.getD k 0) =
      Fin.cons ρ (Fin.cons (ρ ^ 2) (claimPoint 2 (n + 1) t)) := by
  have hu : (fun k : Fin (n + 1) =>
      wChain t (2 + k) * inverses c (n + 2) α β t a next (2 + k)) = claimPoint 2 (n + 1) t := by
    funext k
    unfold claimPoint
    rw [u_eq c n α β t a next (by have := k.isLt; omega), add_comm 2 (k : ℕ)]
  rw [witness_point_eq, getD_cons_fun, getD_cons_fun, show n + 2 - 1 = n + 1 by omega,
    getD_map_fun, hu, pow_two]

theorem witness_value (hn : 1 ≤ n) :
    (claimsOf c (n + 2) statement α β γ t a next ρ).witness.value =
      (∑ j, opening ρ j * a j) / claimScale 2 (n + 1) t := by
  have hm := middle_mul n hn (inverses c (n + 2) α β t a next)
  have h1 : (1 + ρ * ρ) * (a 0 + ρ * (a 0 + a 1)) + ρ * ρ * (a 2 + ρ * (a 2 + a 3)) =
      ∑ j, opening ρ j * a j := by
    simp [opening, Fin.sum_univ_four]; ring
  have h2 : ∏ i : Fin (n + 1), inverses c (n + 2) α β t a next (i + 2) =
      (claimScale 2 (n + 1) t)⁻¹ := by
    rw [claimScale, ← prod_inv_distrib]
    exact prod_congr rfl fun i _ => by
      rw [inverses_lt c n α β t a next (by have := i.isLt; omega)]
  rw [witness_value_eq, mul_assoc, middle, hm, h1, h2, div_eq_mul_inv]

theorem wiring_point :
    (fun k : Fin (n + 2) =>
        (claimsOf c (n + 2) statement α β γ t a next ρ).wiring.point.getD k 0) =
      claimPoint 0 (n + 2) t := by
  rw [wiring_point_eq, getD_map_range_fun]
  funext k
  unfold claimPoint
  rw [u_eq c n α β t a next (by have := k.isLt; omega), add_zero]

theorem wiring_value (hn : 1 ≤ n) :
    (claimsOf c (n + 2) statement α β γ t a next ρ).wiring.value =
      next / claimScale 0 (n + 2) t := by
  have hw := wiring_scale_eq n hn (inverses c (n + 2) α β t a next)
  have h2 : ∏ i : Fin (n + 2), inverses c (n + 2) α β t a next i =
      (claimScale 0 (n + 2) t)⁻¹ := by
    rw [claimScale, ← prod_inv_distrib]
    exact prod_congr rfl fun i _ => by
      rw [inverses_lt c n α β t a next (by have := i.isLt; omega), add_zero]
  rw [wiring_value_eq, middle, hw, h2, div_eq_mul_inv]

theorem quotient_point :
    (fun k : Fin (n + 2 + 1 + 1 + 1 + 1 + 1 + 1) =>
        (claimsOf c (n + 2) statement α β γ t a next ρ).quotient.point.getD k 0) =
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (n + 2 + 1 + 1) t)
        (sq^[n + 2] t / (product c α β t a next + sq^[n + 2] t))) ρ) (y / (1 + y)))
        (y ^ 2 / (1 + y ^ 2)) : Fin (n + 2 + 1 + 1 + 1 + 1 + 1 + 1) → E) := by
  have e : (claimsOf c (n + 2) statement α β γ t a next ρ).quotient.point =
      (List.range (n + 2 + 1 + 1)).map (fun k => wChain t k * inverses c (n + 2) α β t a next k) ++
        [sq^[n + 2] t / (product c α β t a next + sq^[n + 2] t)] ++ [ρ] ++ [y / (1 + y)] ++
        [y ^ 2 / (1 + y ^ 2)] := by
    rw [quotient_point_eq, extension_eq, inverses_copy, wChain_eq]
    simp [div_eq_mul_inv]
  have hu : (fun k : Fin (n + 2 + 1 + 1) =>
      wChain t k * inverses c (n + 2) α β t a next k) = claimPoint 0 (n + 2 + 1 + 1) t := by
    funext k
    unfold claimPoint
    rw [u_eq c n α β t a next (by have := k.isLt; omega), add_zero]
  rw [e, getD_snoc_fun _ (by simp), getD_snoc_fun _ (by simp), getD_snoc_fun _ (by simp),
    getD_snoc_fun _ (by simp), getD_map_range_fun, hu]

theorem quotient_value (hn : 1 ≤ n) :
    (claimsOf c (n + 2) statement α β γ t a next ρ).quotient.value =
      identities c (n + 2) α β t a next γ ρ / (product c α β t a next + sq^[n + 2] t) /
        rows c (n + 2) t / ((1 + y) * (1 + y ^ 2)) / claimScale 0 (n + 2 + 1 + 1) t := by
  have hq := quotient_scale_eq n hn (inverses c (n + 2) α β t a next)
  have hs : ∏ i : Fin (n + 2 + 1 + 1), inverses c (n + 2) α β t a next i =
      (claimScale 0 (n + 2 + 1 + 1) t)⁻¹ := by
    rw [claimScale, ← prod_inv_distrib]
    exact prod_congr rfl fun i _ => by
      rw [inverses_lt c n α β t a next (by have := i.isLt; omega), add_zero]
  rw [quotient_value_eq, middle, hq, hs, inverses_copy, inverses_rows, extension_eq]
  simp only [div_eq_mul_inv]
  ring

theorem sum_point :
    (fun k : Fin (n + 2 + 1 + 1 + 1 + 1 + 1 + 1) =>
        (claimsOf c (n + 2) statement α β γ t a next ρ).sum.point.getD k 0) =
      QuotientSecurity.sumPoint (n + 2) y := by
  rw [sum_point_eq]
  exact sumPoint_fun n

theorem sum_value :
    (claimsOf c (n + 2) statement α β γ t a next ρ).sum.value =
      target statement γ / ((1 + y) * (1 + y ^ 2)) := by
  rw [sum_value_eq, extension_eq]
  simp only [div_eq_mul_inv]
  ring

/-- **The witness claim is F1's**: a table (`c b` the entry whose index has bits `b`) satisfies
`reduce`'s witness claim exactly when its four row polynomials satisfy F1's witness claim. -/
theorem witness_iff (hn : 1 ≤ n) (hnz : (denominators c (n + 2) α β t a next).prod ≠ 0)
    (cW : (Fin (n + 1 + 1 + 1) → Bool) → E) :
    mle cW (fun k => (claimsOf c (n + 2) statement α β γ t a next ρ).witness.point.getD k 0) =
        (claimsOf c (n + 2) statement α β γ t a next ρ).witness.value ↔
      witnessClaim (witnessOfTable cW) t ρ a := by
  have ht := (prod_denominators_ne_zero hnz).1
  rw [witness_point, witness_value c n statement α β γ t a next ρ hn]
  exact witness_claim cW t ρ a fun i => ht _ (by omega)

/-- **The wiring claim is the wiring polynomial's value**: a table satisfies `reduce`'s wiring
claim exactly when its polynomial takes the fifth value `next` at `t`. -/
theorem wiring_iff (hn : 1 ≤ n) (hnz : (denominators c (n + 2) α β t a next).prod ≠ 0)
    (cF : (Fin (n + 2) → Bool) → E) :
    mle cF (fun k => (claimsOf c (n + 2) statement α β γ t a next ρ).wiring.point.getD k 0) =
        (claimsOf c (n + 2) statement α β γ t a next ρ).wiring.value ↔
      (tablePoly cF).eval t = next := by
  have ht := (prod_denominators_ne_zero hnz).1
  rw [wiring_point, wiring_value c n statement α β γ t a next ρ hn]
  exact wiring_claim cF t next fun i => ht _ (by omega)

end Claims

/-! ## The quotient claims -/

/-- A cell's value, as `Params.cellAt` computes it from the four values. -/
theorem cellAt_eq (P : Params E) (a : Fin 4 → E) (t : E) (i : Fin 4) :
    P.cellAt a t i = a 0 + (t + shift P.θ i) * a 1 +
      ((t + shift P.θ i) ^ 2 + (t + shift P.θ i)) * a 2 +
      ((t + shift P.θ i) ^ 2 + (t + shift P.θ i)) * (t + shift P.θ i) * a 3 := by
  simp [Params.cellAt, digit, Fin.sum_univ_four]

/-- **`reduce`'s cells are F1's** (`cellAt`) when `θ` is `beta()[1]`: `w_1(t + s)` is `w_1(t)`
for the shifts `0, 1` and `w_1(t) + 1` for `θ, θ + 1`. -/
theorem rowCells_eq (c : Consts) (P : Params E) (hθ : P.θ = ofK (c.beta 1)) (t : E)
    (a : Fin 4 → E) (i : Fin 4) : rowCells c t a i = P.cellAt a t i := by
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  have h := P.hθ
  rw [cellAt_eq]
  rw [hθ] at h ⊢
  fin_cases i
  · simp [rowCells, cell, shift, wChain]; ring
  · simp only [rowCells, cell, shift, wChain]
    simp
    linear_combination (-(t + 1) * (a 2 + (t + 1) * a 3)) * two
  · simp only [rowCells, cell, shift, wChain]
    simp
    linear_combination (-(a 2 + (t + ofK (c.beta 1)) * a 3)) * h +
      ((1 - t * ofK (c.beta 1)) * (a 2 + (t + ofK (c.beta 1)) * a 3)) * two
  · simp only [rowCells, cell, shift, wChain]
    simp [ofK_add]
    linear_combination (-(a 2 + (t + (ofK (c.beta 1) + 1)) * a 3)) * h +
      ((-ofK (c.beta 1) - t * (ofK (c.beta 1) + 1)) *
        (a 2 + (t + (ofK (c.beta 1) + 1)) * a 3)) * two

/-- **What `reduce`'s quotient claims need of F1's parameters**: `θ = beta()[1]`, the cells'
vanishing polynomial the digit `w_m`, and the public weight and the rows' vanishing polynomial
evaluated as `reduce` evaluates them. -/
structure Matches (P : Params E) (c : Consts) (n : ℕ) : Prop where
  theta : P.θ = ofK (c.beta 1)
  vCells : P.vCells = digitPoly (n + 2)
  pub : ∀ γ t, (P.pub γ).eval t = publicWeight c (n + 2) γ t
  rows : ∀ t, P.vRows.eval t = rows c (n + 2) t

/-- **The quotient claims are F1's**: for parameters whose cells are a Cantor basis's points and
which match `reduce` (`Matches`), and a statement whose target is `reduce`'s, a quotient table
satisfying both of `reduce`'s claims on it holds a second message (`quotientsOfTable`) satisfying
F1's two quotient claims. -/
theorem quotientClaims_of (c : Consts) (n : ℕ) (statement : Fin 4 → E) (α β γ t : E)
    (a : Fin 4 → E) (next ρ : E) (hn : 1 ≤ n) (P : Params E) (hM : Matches P c n) {N : ℕ}
    (B : CantorBasis E N) (hN : n + 2 ≤ N) (cells : (Fin (n + 2) → Bool) ≃ P.T × Fin 4)
    (hcells : ∀ x, P.pt (cells x) = B.point x) (stmt : Fin P.words → E)
    (htarget : P.target stmt γ = target statement γ)
    (hnz : (denominators c (n + 2) α β t a next).prod ≠ 0)
    (cQ : (Fin (n + 2 + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → E)
    (h1 : mle cQ (fun k => (claimsOf c (n + 2) statement α β γ t a next ρ).quotient.point.getD k 0) =
      (claimsOf c (n + 2) statement α β γ t a next ρ).quotient.value)
    (h2 : mle cQ (fun k => (claimsOf c (n + 2) statement α β γ t a next ρ).sum.point.getD k 0) =
      (claimsOf c (n + 2) statement α β γ t a next ρ).sum.value) :
    quotientClaims P stmt (quotientsOfTable y cQ) α β γ t a next ρ := by
  obtain ⟨ht, -, -⟩ := prod_denominators_ne_zero hnz
  have htQ : ∀ i : Fin (n + 2 + 1 + 1), 1 + sq^[(i : ℕ) + 0] t ≠ 0 := fun i => ht i (by omega)
  have hY := one_add_y_ne_zero
  have hY2 := one_add_y_sq_ne_zero
  have hYY := mul_ne_zero hY hY2
  have hx : ∀ i, rowCells c t a i = P.cellAt a t i := rowCells_eq c P hM.theta t a
  have hvc : P.vCells.eval t = sq^[n + 2] t := by rw [hM.vCells, digitPoly_eval]
  have hden : P.claimDen α β t a next = product c α β t a next + sq^[n + 2] t := by
    rw [Params.claimDen, hvc, product, hx 0]
  have hval : P.claimValue α β γ t ρ a next = identities c (n + 2) α β t a next γ ρ /
      (product c α β t a next + sq^[n + 2] t) / rows c (n + 2) t := by
    rw [Params.claimValue, hden, hM.pub, hM.rows, identities, product, gate4, ← hx 0, ← hx 1,
      ← hx 2, ← hx 3, div_div]
    rfl
  refine ⟨?_, ?_⟩
  · show (1 + ρ) * ((1 + P.vCells.eval t / P.claimDen α β t a next) *
          ((quotientsOfTable y cQ).h P).eval t +
          P.vCells.eval t / P.claimDen α β t a next * (quotientsOfTable y cQ).q.eval t) +
        ρ * ((1 + P.vCells.eval t / P.claimDen α β t a next) *
          (quotientsOfTable y cQ).qGate.eval t +
          P.vCells.eval t / P.claimDen α β t a next * (quotientsOfTable y cQ).junk.eval t) =
      P.claimValue α β γ t ρ a next
    rw [quotientsOfTable_h P y cQ hM.vCells, hval, hden, hvc]
    rw [quotient_point, quotient_value c n statement α β γ t a next ρ hn,
      quotient_mle cQ t _ ρ y hY hY2 htQ, div_left_inj' (claimScale_ne_zero htQ),
      div_left_inj' hYY] at h1
    exact h1
  · rw [sum_point, sum_value, sum_mle B hN y hY hY2 cQ, div_left_inj' hYY] at h2
    rw [htarget, ← h2]
    unfold Params.Quotients.top
    rw [← Equiv.sum_comp cells]
    exact sum_congr rfl fun x _ => by rw [hcells x]; rfl

/-! ## F1's instance matches `reduce` -/

theorem coordinates_zero (beta : ℕ → K) : coordinates beta 0 = 1 := by rw [coordinates]

/-- **`coordinates` is `invSeq`** of the basis, as far as the basis is `beta()`'s words. -/
theorem invSeq_eq (c : Consts) (β' : ℕ → E) (h : ∀ k < 22 + 2, β' k = ofK (c.beta k)) :
    ∀ d < 22 + 2, invSeq β' d = ofK (coordinates c.beta d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases d with _ | d
    · rw [invSeq_zero, coordinates_zero, ofK_one]
    · rw [invSeq, coordinates, ofK_sumFin,
        Fin.sum_univ_eq_sum_range (fun e => invSeq β' e * β' (d + 1 - e)) (d + 1),
        Fin.sum_univ_eq_sum_range (fun e => ofK (c.beta (e + 1) * coordinates c.beta (d - e)))
          (d + 1),
        ← sum_range_reflect (fun e => ofK (c.beta (e + 1) * coordinates c.beta (d - e))) (d + 1)]
      refine sum_congr rfl fun e he => ?_
      have he' := mem_range.mp he
      rw [ofK_mul, ih e (by omega) (by omega), h _ (by omega),
        show d + 1 - 1 - e = d - e by omega, show d - (d - e) = e by omega,
        show d - e + 1 = d + 1 - e by omega, mul_comm]

theorem coordinate_eq (c : Consts) (t : E) (k : ℕ) (hk : k < region) (b : ℕ → E)
    (hb : ∀ i < region, b i = ofK (coordinates c.beta i)) :
    coordinate c t k = (coordPoly b region k).eval t := by
  rw [coordinate, foldRange_add, coordPoly_eval, sum_eq_sum_Ico_succ_bot hk, Nat.sub_self,
    hb 0 (by unfold region; omega), coordinates_zero, ofK_one, one_mul, wChain_eq]
  refine congrArg (sq^[k] t + ·) (sum_congr rfl fun j hj => ?_)
  rw [hb (j - k) (by have := mem_Ico.mp hj; omega), wChain_eq]

theorem slope_eq (cw : ℕ → E) (hc : ∀ k < 8, coordinateWeight k = some (cw k)) (γ : E) (k : ℕ)
    (hk : k < region) : slope γ k = 1 + regionMu cw k γ := by
  by_cases h8 : k < 8
  · simp [slope, hc k h8, regionMu, h8]
  · have hnone : coordinateWeight k = none := by
      unfold coordinateWeight
      simp [show k ≠ 0 by omega, show k ≠ 1 by omega, h8]
    simp only [slope, hnone, regionMu, h8, ite_false]
    unfold region at hk
    interval_cases k <;> simp <;> ring

/-- **`reduce`'s public weight is F1's `pubProd`**, at the region's coordinates `b` and weights
`μ`. -/
theorem publicWeight_eq (c : Consts) (m : ℕ) (γ t : E) (b : ℕ → E)
    (hb : ∀ i < region, b i = ofK (coordinates c.beta i)) (μ : ℕ → E → E)
    (hμ : ∀ k < region, slope γ k = 1 + μ k γ) :
    publicWeight c m γ t = (pubProd b μ region m γ).eval t := by
  rw [publicWeight, foldRange_mul, foldRange_mul, one_mul, pubProd, Polynomial.eval_mul, hiPoly,
    Polynomial.eval_prod, Polynomial.eval_prod, range_eq_Ico]
  refine congrArg₂ (· * ·) (prod_congr rfl fun k _ => ?_) (prod_congr rfl fun k hk => ?_)
  · rw [Polynomial.eval_add, Polynomial.eval_one, digitPoly_eval, wChain_eq]
  · have hk' := (mem_Ico.mp hk).2
    rw [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      coordinate_eq c t k hk' b hb, hμ k hk']

/-- **What `row_vanishing(m)` returns solves its system** (`domain.rs`): `tau[m − 2] = 1` and,
for each `beta[j]`, `2 ≤ j < m`, `Σ_{k ≤ m − 2} [k ≤ j] beta[j − k] tau[k] = 0`. -/
def RowVanishing (c : Consts) (n : ℕ) : Prop :=
  c.tau n = 1 ∧ ∀ j, 2 ≤ j → j < n + 2 →
    ∑ k ∈ range (n + 1), (if k ≤ j then c.beta (j - k) else 0) * c.tau k = 0

theorem rows_eq (c : Consts) (n : ℕ) (t : E) :
    rows c (n + 2) t = (rowsPoly fun k : Fin (n + 1) => ofK (c.tau k)).eval t := by
  rw [rows, foldRange_add, zero_add, rowsPoly_eval, show n + 2 - 1 = n + 1 by omega,
    ← range_eq_Ico, ← Fin.sum_univ_eq_sum_range (fun k => ofK (c.tau k) * wChain t k)]
  exact sum_congr rfl fun k _ => by rw [wChain_eq]

/-- **F1's instance matches `reduce`** when its basis is `beta()`'s words (`hβ`), its weights
`coordinate_weight`'s (`hc`), and `tau` solves `row_vanishing`'s system. -/
theorem matches_params (I : Instance E) (c : Consts)
    (hβ : ∀ k < 22 + 2, I.basis.β k = ofK (c.beta k))
    (hc : ∀ k < 8, coordinateWeight k = some (I.c k)) (hτ : RowVanishing c 22) :
    Matches I.params c 22 where
  theta := hβ 1 (by norm_num)
  vCells := rfl
  pub γ t := by
    show (pubProd (invSeq I.basis.β) (regionMu I.c) 11 (22 + 2) γ).eval t = _
    exact (publicWeight_eq c _ γ t _ (fun i hi => invSeq_eq c _ hβ i (by unfold region at hi; omega))
      _ fun k hk => slope_eq I.c hc γ k hk).symm
  rows t := by
    have hτ1 : (fun k : Fin (22 + 1) => ofK (c.tau k)) (Fin.last 22) = 1 := by
      simp only [Fin.val_last, hτ.1, ofK_one]
    have hsys : ∀ j : Fin (22 + 2), 2 ≤ (j : ℕ) →
        (rowsPoly fun k : Fin (22 + 1) => ofK (c.tau k)).eval (I.basis.β j) = 0 := by
      intro j hj
      rw [rowsPoly_eval]
      have e : ∀ k : Fin (22 + 1), ofK (c.tau k) * sq^[(k : ℕ)] (I.basis.β j) =
          ofK ((if (k : ℕ) ≤ j then c.beta (j - k) else 0) * c.tau k) := by
        intro k
        rw [I.basis.iterate _ _ j.2, ofK_mul, mul_comm]
        split_ifs
        · rw [hβ _ (by omega)]
        · rw [ofK_zero]
      rw [sum_congr rfl fun k _ => e k, ← ofK_sumFin,
        Fin.sum_univ_eq_sum_range (fun k => (if k ≤ (j : ℕ) then c.beta (j - k) else 0) * c.tau k),
        hτ.2 j hj j.2, ofK_zero]
    have hv := rowsPoly_eq_vRows I.basis le24 I.wiring 8
      (fun J => weightedSum (regionWeight I.c J)) (pubProd (invSeq I.basis.β) (regionMu I.c) 11 (22 + 2))
      (membershipPub_hPub I.basis (invSeq I.basis.β) I.c le24 (invSeq_zero _)
        fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd) _ hτ1 hsys
    rw [rows_eq, hv]
    rfl

end Reduce

end Compose
