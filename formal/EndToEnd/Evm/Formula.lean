-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Evm.Graph
import Bridge.Claims
import Bridge.Chain

/-!
# F5's formulas are the statement's claims

F5 reads the graph's nodes as `quotient::protocol::reduce`'s formulas over the field (`Formula`,
`Implementation/Reduce.lean`), with the constants the graph carries (`Graph.lean`: `beta`, `coords`,
`tau`, `y0`, `y1`, `scale`); `Bridge/Claims` reads the statement's `claimsAt 22` as
`Compose.Reduce.reduce` at the statement's constants (`statementConsts`: the statement's `betaAt` and
`rowVanishing 24`). Both transcribe the same Rust. Here, on `E` (`Primitives.F192`, F5's limbs
`limbsEquiv`, which are the statement's `eLimbs`):

* **the constants** are the same elements: `elem_theta` (`β₁`), `elem_tau` (`τ`, through
  `Bridge.tauWords_eq_emitted`), `elem_coords` (`coordinates(11)`, its words checked by kernel
  evaluation, `coords_lanes`), `slope_eq` (`1 + coordinate_weight(k)`), `elem_y0`, `elem_y1`,
  `elem_scale` (`extension()`), `sumPointWords_eq` (`sum_point`);
* `dens_eq`, `check_eq`: F5's denominators are `reduce`'s, so the value the contract requires nonzero
  is the product `reduce` requires nonzero;
* **`formula_claims`**: F5's witness, wiring and quotient lists are `reduce`'s claims (points, then
  values), and its sum value `reduce`'s, at any leaves whose statement halves are `reduce`'s;
* `elem_halfOf`: F5's statement halves (the calldata's 16-byte halves, big-endian) are `reduce`'s
  (`stmtHalves`).
-/

set_option linter.unusedSectionVars false

namespace Evm

open LeanVM.Parameters QuotientRpm Implementation Implementation.Program

local notation "C" => Bridge.statementConsts
local notation "SQ" => QuotientSecurity.sq

/-! ## Elements of numbers -/

/-- F5's limbs of `Primitives.F192` are the statement's. -/
theorem limbsEquiv_eq_eLimbs : limbsEquiv = Soundness.eLimbs := Equiv.ext fun _ => rfl

theorem elem_eq (n : ℕ) : elem limbsEquiv n = E.ofLimbs (K.ofBits (Implementation.limb n 0))
    (K.ofBits (Implementation.limb n 1)) (K.ofBits (Implementation.limb n 2)) := rfl

theorem ofBits_mod (n : ℕ) : K.ofBits (n % 2 ^ 64) = K.ofBits n := Primitives.F64.ofNat_mod n

theorem ofBits_zero : K.ofBits 0 = 0 := rfl

/-- A number below `2^64` is an element of `K`. -/
theorem elem_small {n : ℕ} (h : n < 2 ^ 64) : elem limbsEquiv n = ofK (K.ofBits n) := by
  have h' : n < 18446744073709551616 := by simpa using h
  have h0 : Implementation.limb n 0 = n := by
    simp only [Implementation.limb_eq]
    norm_num
    try omega
  have h1 : Implementation.limb n 1 = 0 := by
    simp only [Implementation.limb_eq]
    norm_num
    try omega
  have h2 : Implementation.limb n 2 = 0 := by
    simp only [Implementation.limb_eq]
    norm_num
    try omega
  rw [elem_eq, ofK_eq_ofLimbs, h0, h1, h2]
  rfl

/-- `2^64` is `y`. -/
theorem elem_B64 : elem limbsEquiv B64 = y := by
  rw [elem_eq]
  have h0 : Implementation.limb B64 0 = 0 := by decide
  have h1 : Implementation.limb B64 1 = 1 := by decide
  have h2 : Implementation.limb B64 2 = 0 := by decide
  rw [h0, h1, h2]
  exact Primitives.F192.Y_eq_gen

theorem word_elem_of_lt {n : ℕ} (h : n < B192) : word limbsEquiv (elem limbsEquiv n) = n := by
  rw [word_elem, Nat.mod_eq_of_lt h]

theorem getD_lt {l : List ℕ} {b : ℕ} (hb : 0 < b) (h : ∀ x ∈ l, x < b) (k : ℕ) : l.getD k 0 < b := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simpa using hb
  | some x => exact h x (List.mem_of_getElem? hk)

/-! ## The constants -/

/-- `β_k` is the graph's `beta` word `k`. -/
theorem betaAt_eq (k : ℕ) : PcsQuotient.Domain.betaAt k = K.ofBits (Emitted.beta.getD k 0) := by
  rw [Bridge.betaAt_eq_getD, Bridge.getD_of_words Bridge.beta_lanes, Bridge.betaWords_eq_emitted,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Emitted.beta[k]? <;> rfl

theorem elem_theta : elem limbsEquiv (Emitted.beta.getD 1 0) = ofK ((C).beta 1) := by
  rw [elem_small (n := Emitted.beta.getD 1 0) (by decide), Bridge.statementConsts_beta, betaAt_eq]

theorem elem_theta1 : elem limbsEquiv (Emitted.beta.getD 1 0 ^^^ 1) = ofK ((C).beta 1 + 1) := by
  rw [elem_xor isF192_primitives, elem_theta, elem_one isF192_primitives, Compose.Reduce.ofK_add,
    Compose.Reduce.ofK_one]

theorem tau_small : ∀ x ∈ Emitted.tau, x < 2 ^ 64 := by decide +kernel

/-- `τ_k` is the graph's `tau` word `k`. -/
theorem statementTau_eq' (k : ℕ) : Bridge.statementTau k = K.ofBits (Emitted.tau.getD k 0) := by
  rw [Bridge.statementTau_eq, Bridge.tauWords_eq_emitted, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Emitted.tau[k]? <;> rfl

theorem elem_tau (k : ℕ) : elem limbsEquiv (Emitted.tau.getD k 0) = ofK ((C).tau k) := by
  rw [elem_small (getD_lt (by norm_num) tau_small k), Bridge.statementConsts_tau, statementTau_eq']

/-- **`coordinates(11)`'s words are the graph's** (kernel evaluation of the statement's
`coordinates`, from its Cantor basis). -/
theorem coords_lanes : (PcsQuotient.Domain.coordinates PcsQuotient.region).map K.lane =
    Emitted.coords.map Nat.toUInt64 := by
  decide +kernel

theorem coords_small : ∀ x ∈ Emitted.coords, x < 2 ^ 64 := by decide +kernel

theorem elem_coords {d : ℕ} (hd : d < 11) :
    elem limbsEquiv (Emitted.coords.getD d 0) = ofK (Compose.Reduce.coordinates (C).beta d) := by
  rw [elem_small (getD_lt (by norm_num) coords_small d), Bridge.statementConsts_beta,
    ← Bridge.ClaimsBridge.coordinates_getD d hd, Bridge.getD_of_words coords_lanes,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Emitted.coords[d]? <;> rfl

/-- `coordinate_weight(k)`, `k < 8`, is the graph's constant `slopeConst k + 1`. -/
theorem coordinateWeight_eq {k : ℕ} (hk : k < 8) :
    Compose.Reduce.coordinateWeight k = some (elem limbsEquiv (slopeConst k ^^^ 1)) := by
  interval_cases k
  · rw [show slopeConst 0 ^^^ 1 = 2 by decide, elem_small (n := 2) (by norm_num),
      ofK_eq_ofLimbs]
    rfl
  · rw [show slopeConst 1 ^^^ 1 = 0 by decide, elem_zero isF192_primitives]
    rfl
  · rw [show slopeConst 2 ^^^ 1 = 4 by decide, elem_small (n := 4) (by norm_num),
      ofK_eq_ofLimbs]
    rfl
  · rw [show slopeConst 3 ^^^ 1 = 16 by decide, elem_small (n := 16) (by norm_num),
      ofK_eq_ofLimbs]
    rfl
  · rw [show slopeConst 4 ^^^ 1 = 256 by decide, elem_small (n := 256) (by norm_num),
      ofK_eq_ofLimbs]
    rfl
  · rw [show slopeConst 5 ^^^ 1 = 65536 by decide, elem_small (n := 65536) (by norm_num),
      ofK_eq_ofLimbs]
    rfl
  · rw [show slopeConst 6 ^^^ 1 = 4294967296 by decide, elem_small (n := 4294967296) (by norm_num),
      ofK_eq_ofLimbs]
    rfl
  · rw [show slopeConst 7 ^^^ 1 = B64 by decide, elem_B64, ← Bridge.ClaimsBridge.ey_eq_y]
    rfl

theorem coordinateWeight_none {k : ℕ} (hk : ¬ k < 8) : Compose.Reduce.coordinateWeight k = none := by
  unfold Compose.Reduce.coordinateWeight
  rw [if_neg (by omega), if_neg (by omega), if_neg hk]

/-- `extension()`: `Y / (1 + Y)`. -/
theorem elem_y0 : elem limbsEquiv Emitted.y0 = Compose.Reduce.extension.1.1 := by
  rw [(consts isF192_primitives).y0, yConst, elem_B64, div_eq_mul_inv]
  rfl

/-- `extension()`: `Y^2 / (1 + Y^2)`. -/
theorem elem_y1 : elem limbsEquiv Emitted.y1 = Compose.Reduce.extension.1.2 := by
  rw [(consts isF192_primitives).y1, yConst, elem_B64, div_eq_mul_inv, pow_two]
  rfl

/-- `extension()`: `1 / ((1 + Y) (1 + Y^2))`. -/
theorem elem_scale : elem limbsEquiv Emitted.scale = Compose.Reduce.extension.2 := by
  rw [(consts isF192_primitives).scale, yConst, elem_B64, pow_two]
  rfl

/-- **`sum_point`'s words** are the words of the statement's fixed point. -/
theorem sumPointWords_eq : sumPointWords = (Compose.Reduce.sumPoint 24).map (word limbsEquiv) := by
  have h1 : word limbsEquiv (1 : E) = 1 := by
    rw [← elem_one isF192_primitives, word_elem_of_lt (n := 1) (by decide)]
  have h0 : word limbsEquiv (0 : E) = 0 := by
    rw [← elem_zero isF192_primitives, word_elem_of_lt (n := 0) (by decide)]
  have hy0 : word limbsEquiv Compose.Reduce.extension.1.1 = Emitted.y0 := by
    rw [← elem_y0, word_elem_of_lt (n := Emitted.y0) (by decide)]
  have hy1 : word limbsEquiv Compose.Reduce.extension.1.2 = Emitted.y1 := by
    rw [← elem_y1, word_elem_of_lt (n := Emitted.y1) (by decide)]
  simp only [sumPointWords, Compose.Reduce.sumPoint, List.map_append, List.map_replicate,
    List.map_cons, List.map_nil, h1, h0, hy0, hy1]

/-! ## The formulas -/

section Formulas

variable (I : Vals E)

local notation "INV" => Compose.Reduce.inverses C 24 I.α I.β I.t I.a I.next

theorem slope_eq (k : ℕ) : Formula.slope limbsEquiv I k = Compose.Reduce.slope I.γ k := by
  unfold Formula.slope Compose.Reduce.slope Formula.gammas
  by_cases hk : k < 8
  · rw [if_pos hk, (consts isF192_primitives).slopes k hk, cConst, coordinateWeight_eq hk]
  · rw [if_neg hk, coordinateWeight_none hk]

theorem cellF_eq (sh : ℕ) (a : K) (h : elem limbsEquiv sh = ofK a) (second : Bool) :
    Formula.cellF limbsEquiv I sh second = Compose.Reduce.cell I.t I.a a second := by
  simp only [Formula.cellF, Compose.Reduce.cell, h, Formula.w, Compose.Reduce.wChain_eq]

theorem x_eq : Formula.x limbsEquiv I = Compose.Reduce.rowCells C I.t I.a 0 :=
  cellF_eq I 0 0 (by rw [elem_zero isF192_primitives, Compose.Reduce.ofK_zero]) false

theorem c1_eq : Formula.c1 limbsEquiv I = Compose.Reduce.rowCells C I.t I.a 1 :=
  cellF_eq I 1 1 (by rw [elem_one isF192_primitives, Compose.Reduce.ofK_one]) false

theorem c2_eq : Formula.c2 limbsEquiv I = Compose.Reduce.rowCells C I.t I.a 2 :=
  cellF_eq I (Emitted.beta.getD 1 0) ((C).beta 1) elem_theta true

theorem c3_eq : Formula.c3 limbsEquiv I = Compose.Reduce.rowCells C I.t I.a 3 :=
  cellF_eq I (Emitted.beta.getD 1 0 ^^^ 1) ((C).beta 1 + 1) elem_theta1 true

theorem gate_eq :
    Formula.gate limbsEquiv I = Compose.Reduce.gate4 (Compose.Reduce.rowCells C I.t I.a) := by
  rw [Formula.gate, c3_eq, x_eq, c2_eq, c1_eq]
  rfl

theorem coord_eq (k : ℕ) : Formula.coord limbsEquiv I k = Compose.Reduce.coordinate C I.t k := by
  unfold Formula.coord Compose.Reduce.coordinate Compose.Reduce.foldRange
  simp only [show Compose.Reduce.region = 11 from rfl, Formula.w, Compose.Reduce.wChain_eq]
  refine Bridge.ClaimsBridge.foldl_congr_mem _ _ _ (fun j hj acc => ?_) _
  have hj' := List.mem_range'_1.mp hj
  rw [elem_coords (by omega)]

theorem pub_eq : Formula.pub limbsEquiv I = Compose.Reduce.publicWeight C 24 I.γ I.t := by
  unfold Formula.pub Compose.Reduce.publicWeight Compose.Reduce.foldRange
  simp only [show Compose.Reduce.region = 11 from rfl, Formula.w, Compose.Reduce.wChain_eq,
    List.range_eq_range', Nat.sub_zero]
  refine Bridge.ClaimsBridge.foldl_congr_mem _ _ _ (fun k _ acc => ?_) _
  rw [coord_eq, slope_eq]

theorem rows_eq : Formula.rows limbsEquiv I = Compose.Reduce.rows C 24 I.t := by
  unfold Formula.rows Compose.Reduce.rows Compose.Reduce.foldRange
  simp only [List.range_eq_range', Formula.w, Compose.Reduce.wChain_eq]
  refine Bridge.ClaimsBridge.foldl_congr_mem _ _ _ (fun k _ acc => ?_) _
  rw [elem_tau]

theorem product_eq :
    Formula.product limbsEquiv I = Compose.Reduce.product C I.α I.β I.t I.a I.next := by
  simp only [Formula.product, Formula.d, Formula.dNext, x_eq, Compose.Reduce.product]

/-- **F5's denominators are `reduce`'s.** -/
theorem dens_eq :
    Formula.dens limbsEquiv I = Compose.Reduce.denominators C 24 I.α I.β I.t I.a I.next := by
  simp only [Formula.dens, Compose.Reduce.denominators, product_eq, rows_eq, Formula.w,
    Compose.Reduce.wChain_eq]

/-- **The value the contract requires nonzero is the product `reduce` requires nonzero.** -/
theorem check_eq :
    Formula.check limbsEquiv I = (Compose.Reduce.denominators C 24 I.α I.β I.t I.a I.next).prod := by
  rw [Formula.check, dens_eq]

theorem identities_eq : Formula.identities limbsEquiv I =
    Compose.Reduce.identities C 24 I.α I.β I.t I.a I.next I.γ I.ρ := by
  simp only [Formula.identities, Formula.copies, Formula.d, Formula.dNext, x_eq, pub_eq, rows_eq,
    product_eq, gate_eq, Compose.Reduce.identities]

theorem inv_lt {k : ℕ} (hk : k < 26) : INV k = (1 + SQ^[k] I.t)⁻¹ := by
  rw [Compose.Reduce.inverses,
    Compose.Reduce.getD_denominators_lt C 24 I.α I.β I.t I.a I.next (show k < 24 + 2 by omega)]

theorem inv_26 : INV (24 + 2) =
    (Compose.Reduce.product C I.α I.β I.t I.a I.next + SQ^[24] I.t)⁻¹ := by
  rw [Compose.Reduce.inverses, Compose.Reduce.getD_denominators_copy]

theorem inv_27 : INV (24 + 3) = (Compose.Reduce.rows C 24 I.t)⁻¹ := by
  rw [Compose.Reduce.inverses, Compose.Reduce.getD_denominators_rows]

theorem prod_map_range' (g : ℕ → E) :
    ∀ (s n : ℕ), ((List.range' s n).map g).prod = ∏ k ∈ Finset.range n, g (s + k)
  | s, 0 => by simp
  | s, n + 1 => by
    rw [List.range'_succ, List.map_cons, List.prod_cons, prod_map_range' g (s + 1) n,
      Finset.prod_range_succ', add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [add_assoc, add_comm 1 k]

theorem invProd_eq (s n : ℕ) :
    Formula.invProd I (List.range' s n) = ∏ k ∈ Finset.range n, (1 + SQ^[s + k] I.t)⁻¹ := by
  rw [Formula.invProd, prod_map_range']
  rfl

theorem middle_eq : Compose.Reduce.middle C 24 I.α I.β I.t I.a I.next =
    (1 + SQ^[2] I.t)⁻¹ * ∏ k ∈ Finset.range 21, (1 + SQ^[3 + k] I.t)⁻¹ := by
  have hp : ∏ k ∈ Finset.range (24 - 3), INV (3 + k) =
      ∏ k ∈ Finset.range 21, (1 + SQ^[3 + k] I.t)⁻¹ :=
    Finset.prod_congr rfl fun k hk => inv_lt I (by simp at hk; omega)
  rw [Compose.Reduce.middle, Compose.Reduce.foldRange_mul, Finset.prod_Ico_eq_prod_range,
    inv_lt I (k := 2) (by norm_num), hp]

theorem u_eq (k : ℕ) (hk : k < 26) :
    Formula.u I k = Compose.Reduce.wChain I.t k * INV k := by
  rw [Formula.u, inv_lt I hk, Compose.Reduce.wChain_eq]
  rfl

theorem witness_points : (List.range 23).map (fun k => Formula.u I (k + 2)) =
    (List.range' 2 (24 - 1)).map (fun k => Compose.Reduce.wChain I.t k * INV k) := by
  rw [List.range'_eq_map_range, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.mp hk
  rw [Function.comp_apply, u_eq I (k + 2) (by omega), Nat.add_comm k 2]

theorem witness_value : Formula.opened I * Formula.invProd I (List.range' 2 23) =
    ((1 + I.ρ * I.ρ) * (I.a 0 + I.ρ * (I.a 0 + I.a 1)) +
        I.ρ * I.ρ * (I.a 2 + I.ρ * (I.a 2 + I.a 3))) *
      Compose.Reduce.middle C 24 I.α I.β I.t I.a I.next * INV 24 := by
  rw [invProd_eq, middle_eq, inv_lt I (k := 24) (by norm_num), Formula.opened]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  ring

theorem wiring_points : (List.range 24).map (Formula.u I) =
    (List.range 24).map (fun k => Compose.Reduce.wChain I.t k * INV k) :=
  List.map_congr_left fun k hk => u_eq I k (by simp at hk; omega)

theorem wiring_value : I.next * Formula.invProd I (List.range 24) =
    I.next * (Compose.Reduce.middle C 24 I.α I.β I.t I.a I.next * INV 0 * INV 1) := by
  rw [List.range_eq_range', invProd_eq, middle_eq, inv_lt I (k := 0) (by norm_num),
    inv_lt I (k := 1) (by norm_num)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  ring

theorem quotient_points : (List.range 26).map (Formula.u I) ++
    [Formula.w I 24 * (Formula.product limbsEquiv I + Formula.w I 24)⁻¹, I.ρ,
      elem limbsEquiv Emitted.y0, elem limbsEquiv Emitted.y1] =
    (List.range (24 + 2)).map (fun k => Compose.Reduce.wChain I.t k * INV k) ++
      [Compose.Reduce.wChain I.t 24 * INV (24 + 2), I.ρ, Compose.Reduce.extension.1.1,
        Compose.Reduce.extension.1.2] := by
  have hm : (List.range 26).map (Formula.u I) =
      (List.range (24 + 2)).map (fun k => Compose.Reduce.wChain I.t k * INV k) :=
    List.map_congr_left fun k hk => u_eq I k (by simp at hk; omega)
  rw [hm, inv_26, product_eq, elem_y0, elem_y1, Formula.w, Compose.Reduce.wChain_eq]

theorem quotient_value : elem limbsEquiv Emitted.scale * Formula.invProd I (List.range 26) *
      (Formula.product limbsEquiv I + Formula.w I 24)⁻¹ * (Formula.rows limbsEquiv I)⁻¹ *
      Formula.identities limbsEquiv I =
    Compose.Reduce.extension.2 * (Compose.Reduce.middle C 24 I.α I.β I.t I.a I.next * INV 0 *
      INV 1 * INV 24 * INV (24 + 1)) * INV (24 + 2) * INV (24 + 3) *
      Compose.Reduce.identities C 24 I.α I.β I.t I.a I.next I.γ I.ρ := by
  rw [inv_26, inv_27, product_eq, rows_eq, elem_scale, identities_eq, Formula.w,
    List.range_eq_range', invProd_eq, middle_eq, inv_lt I (k := 0) (by norm_num),
    inv_lt I (k := 1) (by norm_num), inv_lt I (k := 24) (by norm_num),
    inv_lt I (k := 24 + 1) (by norm_num)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  ring

variable (S : Fin 4 → E)

local notation "R" => Compose.Reduce.claimsOf C 24 S I.α I.β I.γ I.t I.a I.next I.ρ

/-- **F5's claims are `reduce`'s**: its witness, wiring and quotient lists are `reduce`'s claims'
points then values, and its sum value `reduce`'s, at leaves whose statement halves are `reduce`'s. -/
theorem formula_claims (hS : I.s = S) :
    Formula.witness I = (R).witness.point ++ [(R).witness.value] ∧
      Formula.wiring I = (R).wiring.point ++ [(R).wiring.value] ∧
      Formula.quotient limbsEquiv I = (R).quotient.point ++ [(R).quotient.value] ∧
      Formula.sum limbsEquiv I = (R).sum.value := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Compose.Reduce.witness_point_eq, Compose.Reduce.witness_value_eq, Formula.witness,
      witness_points, witness_value]
    rfl
  · rw [Compose.Reduce.wiring_point_eq, Compose.Reduce.wiring_value_eq, Formula.wiring,
      wiring_points, wiring_value]
  · rw [Compose.Reduce.quotient_point_eq, Compose.Reduce.quotient_value_eq, Formula.quotient,
      ← quotient_value, ← quotient_points]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [Compose.Reduce.sum_value_eq, Formula.sum, elem_scale, Formula.target, Compose.Reduce.target,
      hS]

end Formulas

/-! ## The statement's halves -/

theorem beNat_take_drop (l : List UInt8) (s : ℕ) :
    ∀ n, s + n ≤ l.length → beNat ((l.drop s).take n) = Bridge.ClaimsBridge.beN l s n
  | 0, _ => by simp [beNat, Bridge.ClaimsBridge.beN]
  | n + 1, h => by
    have hlt : n < (l.drop s).length := by simp; omega
    rw [List.take_succ, beNat_append, beNat_take_drop l s n (by omega), Bridge.ClaimsBridge.beN,
      List.getElem?_eq_getElem hlt, Option.toList_some, List.getElem_drop]
    simp [beNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s + n < l.length by omega)]

/-- F5's element of a 16-byte half is `statement::halves`'s. -/
theorem elem_beN (b : Vector UInt8 32) (h : Fin 2) :
    elem limbsEquiv (Bridge.ClaimsBridge.beN b.toList (16 * h) 16) =
      Compose.Reduce.stmtHalf (fun i => b.get i) h := by
  rw [← Bridge.ClaimsBridge.halfValue_eq, Compose.Reduce.stmtHalf]
  have hn : QuotientSecurity.halfValue (fun i => b.get i) h < 2 ^ 128 := by
    rw [Bridge.ClaimsBridge.halfValue_eq]
    simpa using Bridge.ClaimsBridge.beN_lt b.toList (16 * h) 16
  generalize QuotientSecurity.halfValue (fun i => b.get i) h = n at hn ⊢
  have h0 : Implementation.limb n 0 = n % 2 ^ 64 := by
    simp only [Implementation.limb_eq]
    norm_num
  have h1 : Implementation.limb n 1 = (n >>> 64) % 2 ^ 64 := by
    simp only [Implementation.limb_eq, Nat.shiftRight_eq_div_pow]
    norm_num
  have h2 : Implementation.limb n 2 = 0 := by
    simp only [Implementation.limb_eq]
    norm_num at hn ⊢
    omega
  rw [elem_eq, h0, h1, h2, ofBits_mod, ofBits_mod, ofBits_zero]

theorem halfOf_y (stmt : PcsQuotient.Statement) (h : Fin 2) :
    halfOf (stmt.y ++ stmt.root) h = Bridge.ClaimsBridge.beN stmt.y.toList (16 * h) 16 := by
  have hh := h.2
  rw [halfOf, Vector.toList_append, List.drop_append_of_le_length (by simp; omega),
    List.take_append_of_le_length (by simp; omega), beNat_take_drop _ _ _ (by simp; omega)]

theorem halfOf_root (stmt : PcsQuotient.Statement) (h : Fin 2) :
    halfOf (stmt.y ++ stmt.root) (2 + h) = Bridge.ClaimsBridge.beN stmt.root.toList (16 * h) 16 := by
  have hh := h.2
  have hy : stmt.y.toList.length = 32 := by simp
  rw [halfOf, Vector.toList_append, show 16 * (2 + (h : ℕ)) = stmt.y.toList.length + 16 * h by omega,
    List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left,
    beNat_take_drop _ _ _ (by simp; omega)]

/-- **F5's statement halves are `reduce`'s** (`statement::halves`, both read big-endian). -/
theorem elem_halfOf (stmt : PcsQuotient.Statement) :
    (fun k : Fin 4 => elem limbsEquiv (halfOf (stmt.y ++ stmt.root) k)) =
      Compose.Reduce.stmtHalves (stmt.y ++ stmt.root) := by
  have hy : Compose.Reduce.yOf (stmt.y ++ stmt.root) = fun i ↦ stmt.y.get i := by
    funext i
    simp [Compose.Reduce.yOf, Vector.get_eq_getElem, Vector.getElem_append_left i.2]
  have hr : Compose.Reduce.rootOf (stmt.y ++ stmt.root) = fun i ↦ stmt.root.get i := by
    funext i
    simp only [Compose.Reduce.rootOf, Vector.get_eq_getElem]
    rw [Vector.getElem_append_right (by omega) (Nat.le_add_right 32 (i : ℕ))]
    simp
  funext k
  fin_cases k
  · show elem limbsEquiv (halfOf (stmt.y ++ stmt.root) (0 : Fin 2)) =
      Compose.Reduce.stmtHalf (Compose.Reduce.yOf (stmt.y ++ stmt.root)) 0
    rw [halfOf_y, elem_beN, hy]
  · show elem limbsEquiv (halfOf (stmt.y ++ stmt.root) (1 : Fin 2)) =
      Compose.Reduce.stmtHalf (Compose.Reduce.yOf (stmt.y ++ stmt.root)) 1
    rw [halfOf_y, elem_beN, hy]
  · show elem limbsEquiv (halfOf (stmt.y ++ stmt.root) (2 + ((0 : Fin 2) : ℕ))) =
      Compose.Reduce.stmtHalf (Compose.Reduce.rootOf (stmt.y ++ stmt.root)) 0
    rw [halfOf_root, elem_beN, hr]
  · show elem limbsEquiv (halfOf (stmt.y ++ stmt.root) (2 + ((1 : Fin 2) : ℕ))) =
      Compose.Reduce.stmtHalf (Compose.Reduce.rootOf (stmt.y ++ stmt.root)) 1
    rw [halfOf_root, elem_beN, hr]

end Evm
