-- Review experiment (adversarial ZK review): two facts behind findings of the review.
import ZK

open QuotientZk.Instance QuotientZk.Deployed QuotientZk.Deployed.Fresh

/-- Where the witness claim's scale `Π (1 + w_{k+2}(t))` vanishes, the verifier's claimed value is
`x / 0 = 0` whatever the values: the legacy theorems' all-masks `hTW` (no `ClaimsND`) then asks the
honest table's claim, generally nonzero, to be `0` (`Instance/Nondeg.lean`'s header). -/
example {E : Type} [Field E] [DecidableEq E] [CharP E 2] (c : DChal E) (v : Vals E)
    (h : QuotientSecurity.claimScale 2 (22 + 1) c.1.1.2 = 0) : valsW c v = 0 := by
  funext i
  simp [valsW, h]

/-- The headline `2^-113` is the skeleton's worst-case grinding (`2^64` nonces a grind, `2^70`
operations): at the Statement prover's fuel (`2^25` nonces, about `2^31` operations of grinding),
`epsFS` is below `2^-157`. -/
example : epsFS (2 ^ 19) (2 ^ 24 + 2 ^ 31) ((2 : ENNReal) ^ 191)⁻¹ ((2 : ENNReal) ^ 2368)⁻¹ ≤
    ((2 : ENNReal) ^ 157)⁻¹ :=
  epsFS_le_of _ _ 99 157 rfl (by norm_num)

/-- The deployed figure, for comparison: `2^-113` at `Q = 2^24 + 2^70` (the next example: `epsFS_le_of`'s
condition fails at `2^142`, so it gives no `2^-114`). -/
example : epsFS (2 ^ 19) (2 ^ 24 + 2 ^ 70) ((2 : ENNReal) ^ 191)⁻¹ ((2 : ENNReal) ^ 2368)⁻¹ ≤
    ((2 : ENNReal) ^ 113)⁻¹ :=
  epsFS_le_of _ _ 143 113 rfl (by norm_num)

example : ¬ ((2 ^ 24 + 2 ^ 70) * 6 * (2 ^ 19 + (2 ^ 24 + 2 ^ 70)) +
    2 * (2 ^ 19 + (2 ^ 24 + 2 ^ 70)) * 3 * 2 ^ 65 + 2 ^ 19 ≤ (2 : ℕ) ^ 142) := by norm_num
