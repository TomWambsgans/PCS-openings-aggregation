-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.DomainBasis
import UniComplete.DomainDigits
import UniComplete.DomainPoly
import UniComplete.DomainCount
import UniComplete.DomainPositions
import UniComplete.DomainActive
import UniComplete.DomainCoord

/-!
# The domain facts of the univariate verifier (milestone 4)

What the honest prover's completeness needs of `formal/UniStatement/UniStatement/Domain.lean`, of
`rowPosition` (`Mapping.lean`) and of `countBits`' checks (`Verifier.lean`), stated for the computable
definitions as they are (namespace `UniComplete.Domain`):

1. **The Cantor basis** (`DomainBasis`): `beta_lanes` (its `32` words, by the kernel), `beta_getD_eq_betaAt`
   (the statement's first `28`), `beta_zero`, `beta_succ` (the Cantor property, on the words), `basisK`,
   `basisE` (`QuotientSecurity.CantorBasis K 32`, `E 32`), `omega_basisK`, `omega_basisE` (`Heap.omega` is
   `point`, `pointE`), `pointE_injOn`, `pointE_xor`, `sq_iterate_pointE`.
2. **The digits** (`DomainDigits`): `digits_eq`, `digits_getD`, `digits_pointE`, `vanishingRatio_digits`.
3. **The subspace polynomials** (`DomainPoly`): `wP`, `wP_monic`, `wP_natDegree`, `wP_eval`, `wP_eval_digits`,
   `wP_eq_prod` (`l ≤ 32`), `wP_eval_eq_zero_iff`, `wP_dvd`, `wP_divByMonic_eval`; and `linProd`, `eq_linProd`.
4. **The active rows' polynomials** (`DomainActive`): `zActP`, `zPadP`, `activeVanishingFromBits_eq`,
   `zActP_monic`, `zActP_natDegree`, `zActP_dvd`, `zPadP_natDegree`, `zActP_eval_pointE_eq_zero_iff`,
   `zPadP_eval_pointE_eq_zero_iff`, `zActP_mul_zPadP`.
5. **The positions** (`DomainPositions`): `mem_activePositions_iff`, `activePositions_length`,
   `activePositions_nodup`, `lt_of_mem_activePositions`, `rowPosition_of_lt`, `rowPosition_bijOn`,
   `isActive_rowPosition`.
6. **The count checks** (`DomainCount`): `intBits_one`, `intBits_high`, `intBits_range`, `byteFold_wire`,
   `byteFold_wire_toArray`.
7. **The coordinate functionals** (`DomainCoord`): `coordinatesAt_pointE` (from the basis values),
   `coordinatesAt_pointE_of_basis`; the instance `r = 18` is the named proposition
   `CoordinateFunctionalsBasis 18`, not kernel-checked (see `DomainCoord`).
-/
