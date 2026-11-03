-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecPiop.Circuit
import RecPiop.LogUp
import RecPiop.Copy
import RecPiop.Dataflow
import RecPiop.Indicator
import RecPiop.Identity
import RecPiop.Sum
import RecPiop.Fold
import RecPiop.Ports
import RecPiop.Rounds
import RecPiop.Numbers

/-!
# RecPiop: the soundness of π2's PIOP, generic over circuits

π2 is the outer proof of the recursive EVM verifier for leanVM 42422001 (`crates/leanvm_rec`,
`PI2.md`, `SPEC-REC.md` §2.3, §12; branch `leanvm-rec` @ 4247e37, the final PIOP: the setup as
`κ`, `κ + σ` claimed at `β` and `ξ = κ(t) + βσ(t)` sent, no `h(t)`, the zero ports first). Its
copy argument carries the computation: every position pulls `(w(ω_i), ω_i)` (but the holes) and
pushes `(P(ω_i), σ(ω_i))`, `P = w + Σ_p I_p (E_p + w) + κ`. Everything here is generic in the
layout (any `N`, row width, regions, blocks, `σ`, `κ`, ports): the circuit's optimisation can
move on.

1. **The circuit** (`RecPiop.Circuit`): `Circuit` (regions of `Forward | Expr | Port` roles, the
   `Expr` formulas of degree at most two, aligned blocks, `σ`, `κ`, the ports); `Valid`, decided
   by `validate` (`validate_eq_true_iff`; `pi2::circuit::Circuit::validate` and
   `spec::Circuit::check_shape`: no formula reads a hole, `κ` only at expression slots, `σ` a
   bijection onto the non-holes and the ports' tags); `Satisfies`, the relation.
2. **The copy argument in characteristic two** (`RecPiop.LogUp`, `RecPiop.Copy`):
   * set-based logUp: the log-derivative sum of a family of (value, tag) pairs is zero as a
     rational function exactly when every pair is even (`cleared_eq_zero_iff`); if some pair is
     odd, at most `(|s| − 1)·|F|` points `(α, β)` make it zero with nonzero denominators
     (`card_logSum_eq_zero_le`, Schwartz–Zippel on the cleared numerator, in leanerVM's
     `sideProduct_collision` style; `prob_logSum_eq_zero_le`);
   * every tag twice, so mod 2 is equality (`eq_of_even_of_pair`): the family zero mod 2 gives
     every non-hole's pull equal to the push meant for it and every port's push equal to its
     public fingerprint (`copy_of_even`, `copy_of_cleared_eq_zero`);
   * the identities give the sum, holes out of the pulls through `1 + 1_S`
     (`logSum_of_copyOK`); **`card_copyOK_le`**, **`prob_copyOK_le`**: a witness that does not
     satisfy the circuit reaches the state after `α, β, γ` with probability at most
     `(3N − 1 + Σ_j d_j)/|F|`; the ports' `d_j` are `0` (three limbs) and `1` (four limbs) for
     limbs in `K` (`RecPiop.Ports`, `bind_elem`, `bind_root`).
3. **The quotient identity** (`RecPiop.Indicator`, `RecPiop.Identity`, `RecPiop.Sum`): the
   (block, role) indicators, one on their coset, zero on the rest of `V_m`, of degree at most
   `N − 2^s` (`ind_eval_mem`, `ind_eval_not_mem`, `natDegree_ind_le`); the push polynomial takes
   the pushes on `V_m`, `1_S` the holes (`pushPoly_eval`, `holePoly_eval`); the identity evaluates
   on `V_m` to the copy argument's (`idPoly_eval_omega`, `copyOK_of_idPoly`); its degrees (`P` at
   most `3(N − 1)`, the identity at most `5N − 1`, `natDegree_pushPoly_le`,
   `natDegree_idPoly_le`) and Schwartz–Zippel in `t` (`card_idPoly_eval_eq_zero_le`); `Σ_V h` is
   `h`'s top novel coefficient (`sum_tablePoly_omega`).
4. **The dataflow lemma** (`RecPiop.Dataflow`): the copy constraints are the witness being a
   fixed point of the circuit's dataflow (`copy_iff_flow`, `satisfies_iff`): expression slots
   (`expr_slot`), constants (`constant_slot`), forward chains (`forward_slot`,
   `forward_chain`, `expr_chain`), and the pushes never read a hole (`push_congr_off_holes`).
5. **The rounds** (`RecPiop.Rounds`, `RecPiop.Fold`): `piop`, π2's PIOP in `Compose.Piop`'s form
   for any chain with π2's rounds (`W` → `α, β, γ`; `Q` → `t`; the fold values and `ξ` → `ρ`; the
   claims), its errors proved: `(3N − 1 + Σ_j d_j)/|F|`, `(5N − 1)/|F|`, `(2^r − 1)/|F|`
   (`sound_zero`, `sound_one`, `sound_two`; `W`'s fold binds the fold values,
   `card_foldAt_eq_le`; with them and `ξ` right, `Q`'s claim is the identity at `t`,
   `qClaim_iff`). In bits at `N = 2^24`, `r = 4`, `|F| = 2^192`, times the lists
   `L_W = 9,952`, `L_Q = 3,564` (`RecPiop.Numbers`): 153.1, 140.6, 163.0.

**Left to the next layers** (named, not assumed here): the tables' layer `Model` (`W`'s candidate's
polynomial and fold values with `cells_fold`, `Q`'s `h` and `q`, the setup's polynomials), the
binding hypothesis `hbind` for the candidates (limbs in `K`: `Ports`), the verifier's arithmetic
(`Z_V(t) = w_m(t)`, the indicators' closed form `w_m/(Ẑ_s(t) + Ẑ_s(c_p))`, the zero coset's
closed form, the fold's siblings), and the Fiat–Shamir layer and the openings (ListChainU's
`hlink`: the openings' claims give `Post2`).

The build fails if a headline theorem's axioms grow beyond Lean's three standard ones.
-/

/-- info: 'RecPiop.Circuit.validate_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.validate_eq_true_iff

/-- info: 'RecPiop.Circuit.push_gamma' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.push_gamma

/-- info: 'RecPiop.card_logSum_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.card_logSum_eq_zero_le

/-- info: 'RecPiop.prob_logSum_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.prob_logSum_eq_zero_le

/-- info: 'RecPiop.cleared_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.cleared_eq_zero_iff

/-- info: 'RecPiop.eq_of_even_of_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.eq_of_even_of_pair

/-- info: 'RecPiop.Circuit.card_entries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.card_entries_le

/-- info: 'RecPiop.Circuit.copy_of_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.copy_of_even

/-- info: 'RecPiop.Circuit.copy_of_cleared_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.copy_of_cleared_eq_zero

/-- info: 'RecPiop.Circuit.logSum_of_copyOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.logSum_of_copyOK

/-- info: 'RecPiop.Circuit.card_copyOK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.card_copyOK_le

/-- info: 'RecPiop.Circuit.prob_copyOK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.prob_copyOK_le

/-- info: 'RecPiop.Circuit.copy_iff_flow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.copy_iff_flow

/-- info: 'RecPiop.Circuit.satisfies_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.satisfies_iff

/-- info: 'RecPiop.Circuit.expr_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.expr_slot

/-- info: 'RecPiop.Circuit.constant_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.constant_slot

/-- info: 'RecPiop.Circuit.forward_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.forward_slot

/-- info: 'RecPiop.Circuit.forward_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.forward_chain

/-- info: 'RecPiop.Circuit.expr_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.expr_chain

/-- info: 'RecPiop.Circuit.push_congr_off_holes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.push_congr_off_holes

/-- info: 'RecPiop.Circuit.flow_congr_off_holes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.flow_congr_off_holes

/-- info: 'RecPiop.Points.ofCantor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Points.ofCantor

/-- info: 'RecPiop.Circuit.ind_eval_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.ind_eval_mem

/-- info: 'RecPiop.Circuit.ind_eval_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.ind_eval_not_mem

/-- info: 'RecPiop.Circuit.natDegree_ind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.natDegree_ind_le

/-- info: 'RecPiop.Circuit.exists_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.exists_pair

/-- info: 'RecPiop.Circuit.pair_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.pair_unique

/-- info: 'RecPiop.Circuit.pushPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.pushPoly_eval

/-- info: 'RecPiop.Circuit.holePoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.holePoly_eval

/-- info: 'RecPiop.Circuit.idPoly_eval_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.idPoly_eval_omega

/-- info: 'RecPiop.Circuit.copyOK_of_idPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.copyOK_of_idPoly

/-- info: 'RecPiop.Circuit.natDegree_pushPoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.natDegree_pushPoly_le

/-- info: 'RecPiop.Circuit.natDegree_idPoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.natDegree_idPoly_le

/-- info: 'RecPiop.Circuit.card_idPoly_eval_eq_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.card_idPoly_eval_eq_zero_le

/-- info: 'RecPiop.SetupPolys.ofInterpolate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.SetupPolys.ofInterpolate

/-- info: 'RecPiop.sum_tablePoly_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.sum_tablePoly_omega

/-- info: 'RecPiop.card_foldAt_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.card_foldAt_eq_le

/-- info: 'RecPiop.Circuit.bind_elem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.bind_elem

/-- info: 'RecPiop.Circuit.bind_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.bind_root

/-- info: 'RecPiop.Circuit.qClaim_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.qClaim_iff

/-- info: 'RecPiop.Circuit.qClaim_iff_normalised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.Circuit.qClaim_iff_normalised

/-- info: 'RecPiop.pre_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.pre_post

/-- info: 'RecPiop.sound_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.sound_zero

/-- info: 'RecPiop.sound_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.sound_one

/-- info: 'RecPiop.sound_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.sound_two

/-- info: 'RecPiop.piop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.piop

/-- info: 'RecPiop.bits_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.bits_copy

/-- info: 'RecPiop.bits_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.bits_t

/-- info: 'RecPiop.bits_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecPiop.bits_rho
