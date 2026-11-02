-- Part of this repository. Transcribed from `crates/leanvm_flock_gas/src/flock_min.rs` and the parts of
-- `crates/leanvm_flock_gas/src/flock.rs` it calls (`PHI_BASIS`, `fixed_challenges`, `lagrange_weights`,
-- `ring_map`, `ring_switch_weight`), adapted there from leanVM (https://github.com/leanEthereum/leanVM), commit
-- 42422001, `crates/verifier/src/flock.rs`. MIT OR Apache-2.0; see NOTICE.md.
module

public import UniStatement.Transcript
public import UniStatement.Tables

/-!
# BLAKE2s by Flock (`flock_min.rs`, SPEC.md §7, `SPEC-FLOCK.md`)

**A swappable module.** The verifier calls `Flock.verify` between `γ` and the `C2` root, reading only its
own messages; it returns the point of `q_flock`'s word coordinates, the claims on the fixed matrices `A0`,
`B0`, and its end on `q_flock`: the ring switch's target with its map (`End.ring`, the slices sent:
(a′), the main line) or the slices' combination left to a bit-slice claim (`End.combination`, extension B).
The gas-iteration branch may change this module; nothing else here depends on its insides.

* **Zerocheck** with a univariate skip over `k ≤ 6` variables: seven fixed coordinates
  (`fixedChallenges`, leanVM's), the rest sampled; `2^k` coset values, then `z`; `log_n − k` rounds of
  degree 2 with `eq` factors; `v_a`, `v_b` (`v_c = running + v_a v_b`).
* **Lincheck**: `α`, then `8` rounds; the 64 slices `s` sent unless `Slices.claim`.
* **The matrices' reduction** (`reduceTerminal`): `k + 6` rounds over the skip's row bits and the column's
  packing bits, `a`, `b`; with the slices, the terminal `factor · ŝ(σ) + running` must vanish (collected);
  without them, the combination `Σ weights_i s_i = running` is left.
* **Ring switch** (with the slices): six challenges, the target `Σ_i g^i Φ(s_i)` (`ringMap`), and the
  weight `Φ(eq(p, ·)) = Σ_k c_k eq(φ^k(p), ·)` (`ringSwitchWeight`, its 64 coefficients).

`Slices.inContract` also computes the weight at a point (`End::Ring`'s `weight`), which the univariate
verifier does not read; it is not computed here (no value the verifier states depends on it).
-/

@[expose] public section

namespace UniStatement.Flock

open LeanVM.Parameters LeanVM.Semantics

/-- `PACKING`: 64 bits a `q_flock` word. -/
def packing : ℕ := 6

/-- `K_BITS`. -/
def kBits : ℕ := 64

/-- `FLOCK_NUM_LINCHECK_ROUNDS = 14 − 6`. -/
def lincheckRounds : ℕ := blake2sR1csLogSize - 6

/-- `BLAKE2S_CONSTANT_COLUMN`. -/
def constantColumn : ℕ := 512

/-- `N_FIXED_CHALLENGES`. -/
def nFixed : ℕ := 7

/-- `PHI_BASIS` (`flock.rs`). -/
def phiBasis : List UInt64 :=
  [0x0000000000000001, 0x033CE8BEDDC8A656, 0x512620375ED2A108, 0x0C9E636090AAFC01,
    0xBA4F3CD82801769C, 0xBA26E7904ADB4A47, 0x467698598926DC01, 0x4418AE808B28BDD0]

/-- `phi(value)`: the `GF(2)`-linear image of the byte `value` in the PHI basis. -/
def phi (value : ℕ) : E :=
  eK ((List.range 8).foldl (fun acc bit ↦ if value.testBit bit then acc ^^^ phiBasis.getD bit 0 else acc) 0)

/-- `MEDIUM_GENERATOR`. -/
def mediumGenerator : E := eNew 0x243F6A8885A308D3 0x13198A2E03707344 0xA4093822299F31D0

/-- `fixed_challenges()`: three PHI points, then `v/(1 + v)` for `v = MEDIUM_GENERATOR^(2^p)`, `p < 4`. -/
def fixedChallenges : List E :=
  let medium (p : ℕ) : E :=
    let v := epow mediumGenerator (2 ^ p)
    v * (1 + v)⁻¹
  [phi 0xF7, phi 0x53, phi 0xB5, medium 0, medium 1, medium 2, medium 3]

/-- `window_denominator(count) = (Π_{k=1}^{count−1} PHI[k])⁻¹`. -/
def windowDenominator (count : ℕ) : E := ((List.range' 1 (count - 1)).foldl (fun acc k ↦ acc * phi k) 1)⁻¹

/-- **`lagrange_weights(count, point)`**: the barycentric weights of `PHI[:count]` at `point`, by prefix
and suffix products of `point + PHI[node]`, the one denominator. -/
def lagrangeWeights (count : ℕ) (pt : E) : List E :=
  let differences : Array E := Array.ofFn (n := count) fun node ↦ pt + phi node.val
  let pre : Array E := (List.range count).foldl (fun acc i ↦ acc.push (acc.back?.getD 1 * differences.getD i 0))
    #[1]
  -- suffix[i] = Π_{j ≥ i} differences[j]
  let suf : Array E := ((List.range count).foldl (fun acc i ↦
    acc.push (acc.back?.getD 1 * differences.getD (count - 1 - i) 0)) #[1]).reverse
  let denominator := windowDenominator count
  (List.range count).map fun i ↦ pre.getD i 1 * suf.getD (i + 1) 1 * denominator

/-- `lagrange_interpolate(count, values, point)`. -/
def lagrangeInterpolate (count : ℕ) (values : List E) (pt : E) : E := dot (lagrangeWeights count pt) values

/-- What becomes of the lincheck's 64 slices (`Slices`). -/
inductive Slices where
  | inContract
  | weighted
  | claim
  deriving DecidableEq, Repr, Inhabited

/-- **A variant** (`Variant`): the skip's variables, and the slices' fate. -/
structure Variant where
  skip : ℕ
  slices : Slices
  deriving DecidableEq, Repr, Inhabited

/-- `MatrixClaim`: `A0`, `B0` at one point (the row's 14 coordinates, then the column's). -/
structure MatrixClaim where
  point : List E
  a : E
  b : E
  deriving Inhabited

/-- `End`. -/
inductive End where
  /-- The ring switch's claim, `Φ` drawn by `map`: `Σ_u W(u) q_flock(u) = target`. -/
  | ring (map : List E) (target : E)
  /-- `Σ_i weights_i ẑ(i, point) = value`. -/
  | combination (weights : List E) (value : E)
  deriving Inhabited

/-- **What the reduction leaves** (`Reduced`). -/
structure Reduced where
  point : List E
  matrices : MatrixClaim
  end_ : End
  deriving Inhabited

/-- `RING_MAP_SHIFTS`. -/
def ringMapShifts : List ℕ := [32, 16, 8, 4, 2, 1]

/-- `ring_map(value, challenges)`: stage by stage, `a ← a + f · a^(2^shift)`. -/
def ringMap (value : E) (challenges : List E) : E :=
  (challenges.zip ringMapShifts).foldl (fun v (f, shift) ↦ v + f * sqn v shift) value

/-- `ring_switch_weight(point, challenges)`'s coefficients: `Φ(a) = Σ_{k<64} c_k a^(2^k)`,
`c_k = Π_{stage (f, shift) with k & shift ≠ 0} f^(2^(k mod shift))`. -/
def ringSwitchCoefficients (challenges : List E) : List E :=
  (List.range kBits).map fun k ↦
    ((challenges.zip ringMapShifts).filter fun (_, shift) ↦ k &&& shift ≠ 0).foldl
      (fun acc (f, shift) ↦ acc * sqn f (k % shift)) 1

/-- `row_low_weights(z_skip, low)`: the skip's Lagrange weights, and their product with `eq(low, ·)` over
the 6 packing bits (`eq` outer, the skip inner). -/
def rowLowWeights (zSkip : Option E) (low : List E) : List E × List E :=
  let skip := match zSkip with
    | some z => lagrangeWeights (2 ^ (packing - low.length)) z
    | none => [1]
  let mle := (eqKernel low).toList
  (skip, mle.flatMap fun m ↦ skip.map fun l ↦ l * m)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The zerocheck** (`zerocheck`): seven fixed coordinates then `log_n − k − 7` sampled; with a skip,
the `2^k` coset values, then `z`, and the claim is the interpolation at `z` of `2^k` zeros and them; the
rounds; `v_a`, `v_b`. -/
def zerocheck (logN k : ℕ) : ChanM m (Option E × List E × E × E × E) := do
  let sampled ← samples F (logN - k - nFixed)
  let r : List (Option E) := (fixedChallenges ++ sampled).map some
  let (zSkip, claim) ← if k > 0 then do
      let coset ← nextScalars (m := m) (2 ^ k)
      let z ← sample F
      pure (some z, lagrangeInterpolate (2 ^ (k + 1)) (List.replicate (2 ^ k) 0 ++ coset) z)
    else pure (none, 0)
  let (chi, running) ← sumcheck F claim 3 r
  let vA ← nextScalar (m := m)
  let vB ← nextScalar (m := m)
  return (zSkip, chi, vA, vB, running + vA * vB)

/-- **The matrices' reduction** (`reduce_terminal`): the terminal's known terms (with the slices), `k + 6`
rounds, `a`, `b`; the claims on `A0`, `B0`; with the slices, the terminal collected; without, the
combination it leaves. -/
def reduceTerminal (zSkip : Option E) (rowLow chiIn chiInPrime : List E) (alpha rLc : E)
    (s : Option (List E)) : ChanM m (MatrixClaim × Option (List E × E)) := do
  let k := packing - rowLow.length
  let (skipWeights, lowWeights) := rowLowWeights zSkip rowLow
  let constantBits := (List.range lincheckRounds).map (bitE (constantColumn / kBits))
  let pinWeight := epow alpha 3 * eqEval constantBits chiInPrime
  let cWeight := epow alpha 2 * eqEval chiIn chiInPrime
  let pin := constantColumn % kBits
  let known := s.map fun s ↦ cWeight * dot lowWeights s + pinWeight * s.getD pin 0
  let (challenges, running) ← sumcheck F (rLc + known.getD 0) 3 (List.replicate (k + packing) none)
  let rho := challenges.take k
  let sigma := challenges.drop k
  let a ← nextScalar (m := m)
  let b ← nextScalar (m := m)
  let skipAtRho := if k > 0 then multilinearEval skipWeights rho else 1
  let factor := (a + alpha * b) * skipAtRho
  let matrices : MatrixClaim := ⟨rho ++ rowLow ++ chiIn ++ sigma ++ chiInPrime, a, b⟩
  match s with
  | some s =>
    requireZero (m := m) (factor * multilinearEval s sigma + running)
    return (matrices, none)
  | none =>
    let lambda := eprod challenges
    let lambdaC := lambda * cWeight
    let lambdaPin := lambda * pinWeight
    let weights := ((eqKernel sigma).toList.zip (lowWeights ++ List.replicate kBits 0)).map
      fun (e, low) ↦ factor * e + lambdaC * low
    let weights := weights.modify pin (· + lambdaPin)
    return (matrices, some (weights, running))

/-- **Flock at `log_n` variables** (`flock_min::verify`), as `variant` has it. -/
def verify (logN : ℕ) (variant : Variant) : ChanM m Reduced := do
  let k := variant.skip
  let (zSkip, chi, vA, vB, vC) ← zerocheck F logN k
  let rowLow := chi.take (packing - k)
  let rest := chi.drop (packing - k)
  let chiIn := rest.take lincheckRounds
  let chiRest := rest.drop lincheckRounds
  let alpha ← sample F
  let claim := vA + alpha * vB + epow alpha 2 * vC + epow alpha 3
  let (roundChallenges, rLc) ← sumcheck F claim 3 (List.replicate lincheckRounds none)
  let chiInPrime := roundChallenges.reverse
  let s ← if variant.slices = .claim then pure none else some <$> nextScalars (m := m) kBits
  let (matrices, combination) ← reduceTerminal F zSkip rowLow chiIn chiInPrime alpha rLc s
  let pt := chiInPrime ++ chiRest
  match s, combination with
  | some s, _ =>
    let map ← samples F ringMapShifts.length
    let images := s.map fun value ↦ ringMap value map
    return ⟨pt, matrices, .ring map (polyEval images gen)⟩
  | none, some (weights, value) => return ⟨pt, matrices, .combination weights value⟩
  | none, none => return ⟨pt, matrices, .combination [] 0⟩

end With

end UniStatement.Flock

end
