-- Part of this repository. Transcribed from `crates/leanvm_flock_gas/src/flock_min.rs`, `ring_tower.rs` and the parts
-- of `crates/leanvm_flock_gas/src/flock.rs` it calls (`PHI_BASIS`, `fixed_challenges`, `lagrange_weights`,
-- `ring_map`, `ring_switch_weight`), adapted there from leanVM (https://github.com/leanEthereum/leanVM), commit
-- 42422001, `crates/verifier/src/flock.rs`; the tower order of the ring map, the deferred matrices' reduction and
-- `Pending` are new there (iteration 2). MIT OR Apache-2.0; see NOTICE.md.
module

public import UniStatement.Transcript
public import UniStatement.Tables

/-!
# BLAKE2s by Flock (`flock_min.rs`, `ring_tower.rs`, SPEC.md §7 and §13, `SPEC-FLOCK.md`)

**A swappable module.** The verifier calls `Flock.verify` (extension W) or `Flock.verifyDeferred` (the
point-claim ABI) between `γ` and the `C2` root, reading only its own messages; it returns the point of
`q_flock`'s word coordinates, the claims on the fixed matrices `A0`, `B0` (or, deferred, what the batching
sumcheck needs to make them: `Pending`), and its end on `q_flock`: the ring switch's target with its map
(`End.ring`, the slices sent: (a′), the main line) or the slices' combination left to a bit-slice claim
(`End.combination`, extension B).

* **Zerocheck** with a univariate skip over `k ≤ 6` variables: seven fixed coordinates
  (`fixedChallenges`, leanVM's), the rest sampled; `2^k` coset values, then `z`; `log_n − k` rounds of
  degree 2 with `eq` factors; `v_a`, `v_b` (`v_c = running + v_a v_b`).
* **Lincheck**: `α`, then `8` rounds; the 64 slices `s` sent unless `Slices.claim` (`front`).
* **The matrices' reduction** (`reduceTerminal`): `k + 6` rounds over the skip's row bits and the column's
  packing bits, `a`, `b`; with the slices, the terminal `factor · ŝ(σ) + running` must vanish (collected);
  without them, the combination `Σ weights_i s_i = running` is left. **Deferred** (`verifyDeferred`, lever 4a,
  iteration 2's point-claim ABI): its rounds are the batching sumcheck's first `k + 6` (`Batch.lean`), and
  `Pending` holds what that sumcheck's terminal needs (`Pending.terminal` with the slices; without them, lever
  5a, `Pending.combination`).
* **Ring switch** (with the slices): six challenges `f_0 … f_5`, then the target `Σ_i x^i Φ(s_i)`.
  `Slices.tower` (lever 1a, the main line): `Φ = Φ_5 ∘ … ∘ Φ_0`, `Φ_j(a) = a + f_j a^(2^(2^j))` (shift 1
  innermost, `towerRingMap`), the target through `K`'s subfields (`towerTarget`: 64 leaves, sums of slices,
  then six levels), the weight `Φ(eq(p, ·))` at a point from the inside out (`towerWeightAt`), or as 64
  coefficients (`towerCoefficients`). The other variants: leanVM's order, shift 32 innermost (`ringMap`, the
  images' `polyEval` at `x`, `ringSwitchCoefficients`).

Lever 1b (the leaves as a greedy `XOR` network, `ring_tower::Tower::xors`) is code generation only: a leaf is
the sum of the slices its mask names (`towerLeaves`), whatever network adds them, so the sums are taken directly
here (the same values). `Slices.inContract` also computes the weight at a point (`End::Ring`'s `weight`), which
the univariate verifier does not read; it is not computed here.
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
  /-- `Slices::Tower` (iteration 2, lever 1a): as `weighted`, the ring map's stages in tower order. -/
  | tower
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

/-- `RING_MAP_SHIFTS`: leanVM's order of the map's stages, shift 32 first. -/
def ringMapShifts : List ℕ := [32, 16, 8, 4, 2, 1]

/-- `ring_map(value, challenges)` (leanVM's order): stage by stage, `a ← a + f · a^(2^shift)`. -/
def ringMap (value : E) (challenges : List E) : E :=
  (challenges.zip ringMapShifts).foldl (fun v (f, shift) ↦ v + f * sqn v shift) value

/-- `ring_switch_weight(point, challenges)`'s coefficients (leanVM's order): `Φ(a) = Σ_{k<64} c_k a^(2^k)`,
`c_k = Π_{stage (f, shift) with k & shift ≠ 0} f^(2^(k mod shift))`. -/
def ringSwitchCoefficients (challenges : List E) : List E :=
  (List.range kBits).map fun k ↦
    ((challenges.zip ringMapShifts).filter fun (_, shift) ↦ k &&& shift ≠ 0).foldl
      (fun acc (f, shift) ↦ acc * sqn f (k % shift)) 1

/-! ### The ring switch in tower order (`ring_tower.rs`, iteration 2's lever 1a) -/

/-- `STAGES`: the map's six stages, stage `j` of shift `2^j`. -/
def towerStages : ℕ := 6

/-- **`ring_tower::ring_map(value, map)`**: `Φ(a)` in tower order, stage `0` first,
`a ← a + f_j a^(2^(2^j))`. -/
def towerRingMap (value : E) (map : List E) : E :=
  (map.zip (List.range map.length)).foldl (fun v (f, j) ↦ v + f * sqn v (2 ^ j)) value

/-- `conjugate(c, j) = c^(|F_j|)`, `|F_j| = 2^(2^j)`. -/
def conjugate (c : E) (j : ℕ) : E := sqn c (2 ^ j)

/-- `into_subfield(e, j) = e^((2^64 − 1) / (2^(2^(j+1)) − 1))`, an element of `F_(j+1)` (`e` itself at
`j = 5`). -/
def intoSubfield (e : E) (j : ℕ) : E :=
  if j = towerStages - 1 then e else epow e ((2 ^ 64 - 1) / (2 ^ (2 ^ (j + 1)) - 1))

/-- **`Tower::theta`**: `θ_j = x^((2^64 − 1) / (2^(2^(j+1)) − 1))`, a generator of `F_(j+1)^*` (`x` is
primitive in `K`); `θ_5 = x`. -/
def towerTheta : List E := (List.range towerStages).map (intoSubfield gen)

/-- **`Tower::leaves`**: for each leaf `w < 64` (its bit `j` set where level `j` took `θ_j`'s part), the slices
it sums, as a mask over `i < 64`: `x^i` decomposed over the tower from `F_6 = K` down, each part
`c = c' + θ_j c''`, `c'' = (c + c^(|F_j|)) / (θ_j + θ_j^(|F_j|))`; the leaves are the `GF(2)` coordinates. -/
def towerLeaves : Array ℕ := Id.run do
  let mut leaves : Array ℕ := Array.replicate kBits 0
  for i in [0:kBits] do
    let mut parts : Array E := #[epow gen i]
    for jj in [0:towerStages] do
      let j := towerStages - 1 - jj
      let theta := towerTheta.getD j 0
      let scale := (theta + conjugate theta j)⁻¹
      let mut next : Array E := Array.replicate (2 * parts.size) 0
      for w in [0:parts.size] do
        let c := parts.getD w 0
        let second := (c + conjugate c j) * scale
        let first := c + theta * second
        next := (next.set! (2 * w) first).set! (2 * w + 1) second
      parts := next
    for w in [0:parts.size] do
      if parts.getD w 0 == 1 then leaves := leaves.modify w (· ||| 2 ^ i)
  return leaves

/-- **`ring_tower::target(slices, map)`**: the ring switch's target `Σ_i x^i Φ(s_i)` by the tower: the 64 leaves
(leaf `w` the sum of the slices its mask names; the Rust adds them by its `XOR` network, the same values), then
six levels, level `j` pairing the nodes `(a, b) ↦ (a + θ_j b) + f_j (a^(|F_j|) + θ_j b^(|F_j|))`. -/
def towerTarget (slices map : List E) : E := Id.run do
  let leaves := towerLeaves
  let mut nodes : Array E := Array.ofFn (n := kBits) fun w ↦
    (List.range kBits).foldl (fun acc i ↦
      if (leaves.getD w.val 0).testBit i then acc + slices.getD i 0 else acc) 0
  for j in [0:towerStages] do
    let f := map.getD j 0
    let theta := towerTheta.getD j 0
    nodes := Array.ofFn (n := nodes.size / 2) fun q ↦
      let a := nodes.getD (2 * q.val) 0
      let b := nodes.getD (2 * q.val + 1) 0
      (a + theta * b) + f * (sqn a (2 ^ j) + theta * sqn b (2 ^ j))
  return nodes.getD 0 0

/-- **`ring_tower::coefficients(map)`**: `Φ = Σ_{k<64} d_k F^k`, `d_0 = 1`,
`d_k = d_(k − 2^j) · f_j^(2^(k − k mod 2^(j+1)))`, `j` the lowest set bit of `k`. -/
def towerCoefficients (map : List E) : List E := Id.run do
  let mut d : Array E := Array.replicate kBits 1
  for k in [1:kBits] do
    let j := trailingZeros k
    let exponent := k - k % (2 ^ (j + 1))
    d := d.set! k (d.getD (k - 2 ^ j) 1 * sqn (map.getD j 0) exponent)
  return d.toList

/-- **`ring_tower::weight_at(point, one_plus_r, map)`**: the weight `Φ(eq(p, ·))` at `r`, given
`a_n = 1 + r_n`: the 64 twisted products `G_k = Π_n (a_n + p_n^(2^k))`, then the stages from the inside,
`G_k ← G_k + f_j^(2^k) G_(k + 2^j)` for `k ≡ 0 mod 2^(j+1)`; `G_0`. -/
def towerWeightAt (point onePlusR map : List E) : E := Id.run do
  let mut chain := point
  let mut g : Array E := #[]
  for k in [0:kBits] do
    if k > 0 then chain := chain.map fun c ↦ c * c
    g := g.push ((chain.zip onePlusR).foldl (fun acc (c, a) ↦ acc * (a + c)) 1)
  for j in [0:towerStages] do
    let step := 2 ^ j
    let mut power := map.getD j 0
    for kk in [0:kBits / (2 * step)] do
      let k := kk * (2 * step)
      if k > 0 then power := sqn power (2 * step)
      g := g.set! k (g.getD k 0 + power * g.getD (k + step) 0)
  return g.getD 0 0

/-- `row_low_weights(z_skip, low)`: the skip's Lagrange weights, and their product with `eq(low, ·)` over
the 6 packing bits (`eq` outer, the skip inner). -/
def rowLowWeights (zSkip : Option E) (low : List E) : List E × List E :=
  let skip := match zSkip with
    | some z => lagrangeWeights (2 ^ (packing - low.length)) z
    | none => [1]
  let mle := (eqKernel low).toList
  (skip, mle.flatMap fun m ↦ skip.map fun l ↦ l * m)

/-- **`known_weights(alpha, chi_in, chi_in')`**: the weights of the matrices' terminal's two known terms, the
`C = I` claim's `α² eq(chi_in, chi_in')` and the constant position's pin `α³ eq(bits(512 / 64), chi_in')`. -/
def knownWeights (alpha : E) (chiIn chiInPrime : List E) : E × E :=
  let constantBits := (List.range lincheckRounds).map (bitE (constantColumn / kBits))
  (epow alpha 2 * eqEval chiIn chiInPrime, epow alpha 3 * eqEval constantBits chiInPrime)

/-- **The matrices' reduction, its rounds run by a later sumcheck** (`Pending`, lever 4a): its claim
`Σ_(x, y) G(x, y) L̂(x) ŝ(y)` over the skip's `k` row bits `x` and the column's 6 packing bits `y`,
`G = Â0 + α B̂0` at the row and column points; what its terminal needs; the slices if sent. -/
structure Pending where
  claim : E
  k : ℕ
  skipWeights : List E
  lowWeights : List E
  cWeight : E
  pinWeight : E
  rowLow : List E
  chiIn : List E
  chiInPrime : List E
  alpha : E
  slices : Option (List E)
  deriving Inhabited

/-- **`Pending::new`**: the matrices' reduction of the lincheck's terminal `r_lc`: with the slices, its claim
has their known part (as `reduceTerminal` starts it); without, it is `r_lc` and their part stays unknown. -/
def Pending.new (zSkip : Option E) (rowLow chiIn chiInPrime : List E) (alpha rLc : E)
    (slices : Option (List E)) : Pending :=
  let (skipWeights, lowWeights) := rowLowWeights zSkip rowLow
  let (cWeight, pinWeight) := knownWeights alpha chiIn chiInPrime
  let known := slices.map fun s ↦
    cWeight * dot lowWeights s + pinWeight * s.getD (constantColumn % kBits) 0
  ⟨rLc + known.getD 0, packing - rowLow.length, skipWeights, lowWeights, cWeight, pinWeight, rowLow, chiIn,
    chiInPrime, alpha, slices⟩

/-- `Pending::rounds`: the variables of the sum, the later sumcheck's first ones. -/
def Pending.rounds (p : Pending) : ℕ := p.k + packing

/-- `Pending::has_slices`. -/
def Pending.hasSlices (p : Pending) : Bool := p.slices.isSome

/-- The claims on `A0`, `B0` at the later sumcheck's point: `(ρ, row_low, chi_in, σ, chi_in')`, `(ρ, σ)` its
first `k + 6` coordinates. -/
def Pending.matrixClaim (p : Pending) (point : List E) (a b : E) : MatrixClaim :=
  let rho := (point.take p.rounds).take p.k
  let sigma := (point.take p.rounds).drop p.k
  ⟨rho ++ p.rowLow ++ p.chiIn ++ sigma ++ p.chiInPrime, a, b⟩

/-- `L̂(ρ)`: the skip's Lagrange weights' extension at `ρ` (`1` without a skip). -/
def Pending.skipAt (p : Pending) (point : List E) : E :=
  if p.k > 0 then multilinearEval p.skipWeights ((point.take p.rounds).take p.k) else 1

/-- **`Pending::terminal(point, a, b)`**: at the later sumcheck's point, with `a = Â0`, `b = B̂0` there, the
summand's value `(a + α b) L̂(ρ) ŝ(σ)`, and the claims on `A0`, `B0`. -/
def Pending.terminal (p : Pending) (point : List E) (a b : E) : E × MatrixClaim :=
  let sigma := (point.take p.rounds).drop p.k
  ((a + p.alpha * b) * p.skipAt point * multilinearEval (p.slices.getD []) sigma, p.matrixClaim point a b)

/-- **`Pending::combination(point, a, b, extension, scale)`** (lever 5a, without the slices): the terminal of
the sumcheck that ran the matrices' rounds as its first, at its point, `extension` the matrices' zero extension
and `scale` their power of `λ` there. Each round maps its claim `c` to `c0 + (c + c2) r + c2 r²`, so the slices'
unknown part of the initial claim reaches the last claim times `Λ`, the product of every coordinate of the
point: the terminal is `Σ_i μ_i s_i = rest`,
`μ = scale (extension (a + α b) L̂(ρ) eq(σ, ·) + Λ (c_weight e + pin_weight [· = pin]))`. Returns `μ` and the
claims on `A0`, `B0`. -/
def Pending.combination (p : Pending) (point : List E) (a b extension scale : E) : List E × MatrixClaim :=
  let sigma := (point.take p.rounds).drop p.k
  let lambda := eprod point
  let factor := scale * extension * (a + p.alpha * b) * p.skipAt point
  let lambdaC := scale * lambda * p.cWeight
  let lambdaPin := scale * lambda * p.pinWeight
  let weights := ((eqKernel sigma).toList.zip (p.lowWeights ++ List.replicate kBits 0)).map
    fun (e, low) ↦ factor * e + lambdaC * low
  (weights.modify (constantColumn % kBits) (· + lambdaPin), p.matrixClaim point a b)

/-- **What the zerocheck and the lincheck leave** (`Front`), the slices if sent, and `q_flock`'s word
coordinates of the slices (`point`: the lincheck's column bits, then the instance bits). -/
structure Front where
  zSkip : Option E
  chi : List E
  rowLow : List E
  chiIn : List E
  chiInPrime : List E
  alpha : E
  rLc : E
  slices : Option (List E)
  point : List E
  deriving Inhabited

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
  let (cWeight, pinWeight) := knownWeights alpha chiIn chiInPrime
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

/-- **`front(log_n, variant)`**: the zerocheck, the row point's split (the skip, the packing bits left to
rounds, the 8 slot bits, the instance bits), the lincheck (`α`, 8 rounds), the slices if sent. -/
def front (logN : ℕ) (variant : Variant) : ChanM m Front := do
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
  return ⟨zSkip, chi, rowLow, chiIn, chiInPrime, alpha, rLc, s, chiInPrime ++ chiRest⟩

/-- **`ring_end(variant, front, s)`**: the ring switch on the sent slices: the map drawn (six challenges), then
the target, in tower order for `Slices.tower` (`towerTarget`), else leanVM's (`ringMap`'s images at `x`). -/
def ringEnd (variant : Variant) (s : List E) : ChanM m End := do
  let map ← samples F ringMapShifts.length
  let target := if variant.slices = .tower then towerTarget s map
    else polyEval (s.map fun value ↦ ringMap value map) gen
  return .ring map target

/-- **Flock at `log_n` variables** (`flock_min::verify`), as `variant` has it: the front, the matrices'
reduction, then the ring switch's map and target (with the slices) or the combination (without). -/
def verify (logN : ℕ) (variant : Variant) : ChanM m Reduced := do
  let fr ← front F logN variant
  let (matrices, combination) ←
    reduceTerminal F fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices
  match fr.slices, combination with
  | some s, _ => return ⟨fr.point, matrices, ← ringEnd F variant s⟩
  | none, some (weights, value) => return ⟨fr.point, matrices, .combination weights value⟩
  | none, none => return ⟨fr.point, matrices, .combination [] 0⟩

/-- **`flock_min::verify_deferred`** (lever 4a, iteration 2's point-claim ABI): the front; with the slices sent,
the ring switch's map and target; and the matrices' reduction left pending, for the batching sumcheck to run
its `k + 6` rounds (`Batch.lean`). Without the slices there is no end yet (`none`): the batching sumcheck's
terminal leaves the combination (`Pending.combination`). -/
def verifyDeferred (logN : ℕ) (variant : Variant) : ChanM m (List E × Option End × Pending) := do
  let fr ← front F logN variant
  let pending := Pending.new fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices
  let end_ ← match fr.slices with
    | some s => some <$> ringEnd F variant s
    | none => pure none
  return (fr.point, end_, pending)

end With

end UniStatement.Flock

end
