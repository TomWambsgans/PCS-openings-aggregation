-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `crates/leanvm_univariate/src/prover/flock.rs`
-- (branch `leanvm-univariate-prover2`: `prove`, `sliced`, `Pending`'s tables) and the honest provers of
-- `crates/leanvm_flock_gas/src/flock_min.rs`'s tests (`sliced`, `walked`, `prove_sums`); the zerocheck and the lincheck
-- are leanVM 42422001's Flock (`crates/lv42_flock/src/{zerocheck.rs, zerocheck/skip.rs, lincheck.rs}` on that branch),
-- written here as the sums they compute, not as leanVM's packed passes.
import UniComplete.Honest
import UniComplete.VerifierH

/-!
# Flock's honest prover (BLAKE2s by Flock's zerocheck and lincheck)

**`flockProve H : FlockProver m`** writes exactly what `Flock.verifyDeferred` (`verifyDeferredH`) reads, in its
order, at any skip `k ≤ 6` (the main line `flockMain = ⟨3, .tower⟩`), on `q_flock`'s words `q` (`2^(8 + κ)` words,
`log_n = 14 + κ`). Its witness is the R1CS's: block `t`, position `j < 2^14` is bit `j mod 64` of word
`j / 64 + 256 t` (`zAt`, Lv42's `batchBlock` of `bitTable`); a full index `i < 2^log_n` is position `i mod 2^14` of
block `i / 2^14`, so its bits are, low first, the skip's `k`, the `6 − k` packing bits left to rounds (`row_low`),
the 8 slot bits (`chi_in`), the `κ` instance bits (`chi_rest`).

1. **The zerocheck** (`zerocheckW`) of `Az ∘ Bz + z = 0` (`C = I`, characteristic two):
   * the `log_n − k − 7` sampled eq coordinates (drawn); `r` = leanVM's seven fixed ones, then them;
   * with a skip (`k > 0`): the `2^k` coset values `P(φ(2^k + i))` of the skip polynomial
     `P(X) = Σ_b eq(r, b) (Â(X, b) B̂(X, b) + Ẑ(X, b))`, `Â(X, b) = Σ_{x < 2^k} L_x(X) Az(x + 2^k b)` the univariate
     extension over the first `2^k` PHI nodes (`L_x(X) = lagrangeWeights (2^k) X`, the verifier's own weights);
     `P` vanishes on `φ(0..2^k)` when the R1CS holds on every row; then `z` (drawn), the tables folded at `z`
     (`skipFold`), the claim the verifier computes (`lagrangeInterpolate (2^(k+1)) (0^(2^k) ++ coset) z`);
   * the `log_n − k` eq-factored rounds (`zcRounds`), low variable first, each `(c1, c2)` of
     `q(X) = Σ_b eq(r_{>j}, b) (a b' + c)(X, b)` (the verifier derives `c0` from its claim), then the challenge;
   * `v_a`, `v_b`, the folded tables' values; `v_c = running + v_a v_b`, the verifier's.
2. **The lincheck** (`lcRounds`): `α` (drawn); the weights `W(j) = (Aᵀe)_j + α (Bᵀe)_j + α² e_j + α³ [j = 512]`,
   `e(row) = lowWeights[row mod 64] · eq(chi_in, row / 64)` (`rowWeightsOf`, the verifier's `rowLowWeights`), and the
   witness `Ẑ(j) = Σ_t eq(chi_rest, t) z_t(j)`; 8 rounds over the slot bits, **high bit first** (the verifier's
   `chi_in' = rounds.reverse`), each `(c0, c2)` of `Σ_{j} W Ẑ` (the verifier derives `c1`), then the challenge;
   what is left is the 64 slices `s_y = Ẑ(y, chi_in')`, sent (unless `Slices.claim`).
3. **The ring map** (`ringEndW`): its 6 challenges (drawn), the target the verifier computes (`towerTarget s map`
   in tower order).
4. **What is left** (`assemble`): the slices' point `chi_in' ++ chi_rest`, the end `.ring map target`, the pending
   matrices' reduction `Pending.new …` exactly as `verifyDeferred` computes it (its `r_lc` the verifier's last
   lincheck claim, tracked by the prover through the same `roundPoly` arithmetic), and the tables of the batch's
   `λ³` product sum (`sliced`, the Rust's): `G'(x + 2^k y) = Σ_{row ≡ x} eq((row_low, chi_in), row / 2^k)
   Σ_h eq(chi_in', h) (A + α B)[row][y + 64 h]`, `L̂(x + 2^k y) = skip[x]`, `ŝ(x + 2^k y) = s_y`, over `k + 6`
   variables.

**Decisions.**

* The prover tracks the verifier's claims (the zerocheck's and the lincheck's running claims, `polyEval` of the
  message the verifier rebuilds) instead of recomputing them from the tables, so that its `pending` is the
  verifier's by construction (`FlockSyncs` is a transcript statement) and the algebra (`PendingSumHolds`) is that
  the tracked claims are the true sums.
* The R1CS's products are its walks (`blake2sFlockSpec.r1cs.rows`, `.cols`, which compute `A W`, `Aᵀ e`:
  `BlockR1CS.rows_fst`, `cols_fst`); the matrices are never evaluated by a proof.
* Sums are left folds (`sumTo`); tables are arrays built once (`Array.ofFn` of closures over let-bound arrays).
* Without the slices (`Slices.claim`, extension B) the end is a placeholder (`.combination [] 0`: there is no ring
  switch, the batch's terminal leaves the combination) and the tables carry the true slices; the theorems are
  stated with the slices sent.
* The variant's skip `k` is the prover's; `assemble` reads it back as `Pending.new` does
  (`packing − row_low.length`), so `tables.rounds = pending.rounds` by definition.

**The relations** the honest output satisfies (stated here, proved in `FlockProver*.lean`): `FlockRingHolds` (the
ring claim on `q_flock`), `PendingSumHolds` (the product sum of the tables is the pending claim),
`PendingTerminalHolds` (at every point the tables' extensions multiply to `Pending.terminal` with `A0`, `B0`'s
values).
-/

namespace UniComplete.FlockP

open UniStatement UniStatement.Flock LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
  LeanVM.Protocol.KeccakHash

/-! ## Sums and the witness -/

/-- `Σ_{i < n} f i`, a left fold (the prover's sums). -/
def sumTo (n : ℕ) (f : ℕ → E) : E := (List.range n).foldl (fun acc i ↦ acc + f i) 0

/-- The BLAKE2s R1CS of one block (`blake2sFlockSpec.r1cs`): `2^14` positions, `C = I`. -/
abbrev flockR1cs : Lv42.Protocol.BlockR1CS E (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn) :=
  Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs

/-- **The witness**: position `j` (`< 2^14`) of block `t`, bit `j mod 64` of `q_flock`'s word `j / 64 + 256 t`
(`batchBlock` of `bitTable`: the packing bit low, the slot above, the block's words `256 t … 256 t + 255`). -/
def zAt (q : Array K) (t j : ℕ) : E := Lv42.Protocol.cellBit (q.getD (j / 64 + 256 * t) 0) (j % 64)

/-- Block `t` as the R1CS's table. -/
def blockOf (q : Array K) (t : ℕ) :
    CompPoly.CMlPolynomialEval E (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn) :=
  Vector.ofFn fun j ↦ zAt q t j.val

/-- `Az`, `Bz`, `z` on the `2^log_n` positions, full index `j + 2^14 t`. -/
structure Wit where
  a : Array E
  b : Array E
  c : Array E

/-- **The witness's tables**: each block's walk `(A z_t, B z_t)` once, then read at every position. -/
def witOf (logN : ℕ) (q : Array K) : Wit :=
  let walks : Array (Array E × Array E) := Array.ofFn (n := 2 ^ (logN - blake2sR1csLogSize)) fun t ↦
    let w := flockR1cs.rows (blockOf q t.val)
    (w.1.toArray, w.2.toArray)
  ⟨Array.ofFn (n := 2 ^ logN) fun i ↦ (walks.getD (i.val / 2 ^ 14) (#[], #[])).1.getD (i.val % 2 ^ 14) 0,
    Array.ofFn (n := 2 ^ logN) fun i ↦ (walks.getD (i.val / 2 ^ 14) (#[], #[])).2.getD (i.val % 2 ^ 14) 0,
    Array.ofFn (n := 2 ^ logN) fun i ↦ zAt q (i.val / 2 ^ 14) (i.val % 2 ^ 14)⟩

/-! ## The zerocheck -/

/-- **A table at the skip's point**: `T_z(b) = Σ_{x < 2^k} w_x T(x + 2^k b)` (`w` the skip's Lagrange weights at the
point). -/
def skipFold (k : ℕ) (w : List E) (t : Array E) : Array E :=
  Array.ofFn (n := t.size / 2 ^ k) fun b ↦ sumTo (2 ^ k) fun x ↦ w.getD x 0 * t.getD (x + 2 ^ k * b.val) 0

/-- **The skip polynomial's coset values** `P(φ(2^k + i))`, `i < 2^k`:
`Σ_b eq(r, b) (Â B̂ + Ẑ)(φ(2^k + i), b)`. -/
def cosetValues (k : ℕ) (r : List E) (wit : Wit) : List E :=
  let eqR := eqKernel r
  (List.range (2 ^ k)).map fun i ↦
    let lw := lagrangeWeights (2 ^ k) (phi (2 ^ k + i))
    let a := skipFold k lw wit.a
    let b := skipFold k lw wit.b
    let c := skipFold k lw wit.c
    sumTo eqR.size fun j ↦ eqR.getD j 0 * (a.getD j 0 * b.getD j 0 + c.getD j 0)

/-- **An eq-factored round's message** `(c1, c2)` (the verifier derives `c0`): `q(X) = Σ_i e_i (a b' + c)(X, i)`,
`e = eq(r_{>j}, ·)`, the tables' pairs `(2i, 2i + 1)` the round's variable. -/
def zcRound (eqRest : Array E) (a b c : Array E) : E × E :=
  (List.range eqRest.size).foldl (fun (acc : E × E) i ↦
    let e := eqRest.getD i 0
    let a0 := a.getD (2 * i) 0
    let a1 := a.getD (2 * i + 1) 0
    let b0 := b.getD (2 * i) 0
    let b1 := b.getD (2 * i + 1) 0
    let c0 := c.getD (2 * i) 0
    let c1 := c.getD (2 * i + 1) 0
    (acc.1 + e * (a0 * (b0 + b1) + (a0 + a1) * b0 + (c0 + c1)), acc.2 + e * ((a0 + a1) * (b0 + b1)))) (0, 0)

/-- Where the zerocheck's rounds start: the skip's point (if any), the verifier's claim, the tables. -/
structure ZcStart where
  zSkip : Option E
  claim : E
  a : Array E
  b : Array E
  c : Array E

/-- What the zerocheck's rounds leave: the point, the verifier's last claim, the tables' values. -/
structure ZcOut where
  chi : List E
  running : E
  va : E
  vb : E

/-- What the lincheck's rounds leave: the challenges (in round order), the verifier's last claim, the folded
witness (the slices). -/
structure LcOut where
  challenges : List E
  claim : E
  z : Array E

/-- **A fold, high variable first** (the lincheck's): `v'[i] = v[i] + x (v[i] + v[i + half])`. -/
def foldHigh (v : Array E) (x : E) : Array E :=
  Array.ofFn (n := v.size / 2) fun i ↦
    let a := v.getD i.val 0
    let b := v.getD (i.val + v.size / 2) 0
    a + x * (a + b)

/-- **A lincheck round's message** `(c0, c2)` (the verifier derives `c1`): `q(X) = Σ_{i < half} W(X, i) Ẑ(X, i)`, the
round's variable the top bit. -/
def lcRound (w z : Array E) : E × E :=
  (List.range (w.size / 2)).foldl (fun (acc : E × E) i ↦
    let w0 := w.getD i 0
    let w1 := w.getD (i + w.size / 2) 0
    let z0 := z.getD i 0
    let z1 := z.getD (i + w.size / 2) 0
    (acc.1 + w0 * z0, acc.2 + (w0 + w1) * (z0 + z1))) (0, 0)

/-- `e(row) = lowWeights[row mod 64] · eq(chi_in, row / 64)`: the rows' weights the zerocheck's point gives the
lincheck (the skip's Lagrange weights at `z` times `eq(row_low, ·)` on the packing bits, `eq(chi_in, ·)` on the
slot bits). -/
def rowWeightsOf (lowWeights chiIn : List E) :
    CompPoly.CMlPolynomialEval E (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn) :=
  let eqIn := eqKernel chiIn
  Vector.ofFn fun row ↦ lowWeights.getD (row.val % 64) 0 * eqIn.getD (row.val / 64) 0

/-- **The lincheck's weights** `W(j) = (Aᵀe)_j + α (Bᵀe)_j + α² e_j + α³ [j = 512]` (the R1CS's backward walk). -/
def lincheckWeights (e : CompPoly.CMlPolynomialEval E (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn))
    (alpha : E) : Array E :=
  let ab := flockR1cs.cols e
  let a := ab.1.toArray
  let b := ab.2.toArray
  let ee := e.toArray
  let pin := epow alpha 3
  Array.ofFn (n := 2 ^ blake2sR1csLogSize) fun j ↦
    a.getD j.val 0 + alpha * b.getD j.val 0 + epow alpha 2 * ee.getD j.val 0 +
      if j.val = constantColumn then pin else 0

/-- **The lincheck's witness** `Ẑ(j) = Σ_t eq(chi_rest, t) z_t(j)`: the blocks at the instance point. -/
def lincheckWitness (q : Array K) (chiRest : List E) : Array E :=
  let eqT := eqKernel chiRest
  Array.ofFn (n := 2 ^ blake2sR1csLogSize) fun j ↦ sumTo eqT.size fun t ↦ eqT.getD t 0 * zAt q t j.val

/-! ## The matrices' tables (`sliced`) -/

/-- **`G'(x, y) = (Â0 + α B̂0)((x, row_low, chi_in), (y, chi_in'))`** at index `x + 2^k y` (`sliced`): for each
packing position `y` one forward walk of the column weights `w[y + 64 h] = eq(chi_in', h)`, then
`Σ_{row ≡ x mod 2^k} eq((row_low, chi_in), row / 2^k) (left + α right)[row]`. -/
def sliced (k : ℕ) (low chiIn chiInPrime : List E) (alpha : E) : Array E :=
  let high := eqKernel chiInPrime
  let rows := eqKernel (low ++ chiIn)
  let cols : Array (Array E) := Array.ofFn (n := kBits) fun y ↦
    let w : CompPoly.CMlPolynomialEval E (Lv42.Parameters.Flock.kSkip + Lv42.Parameters.Flock.kIn) :=
      Vector.ofFn fun j ↦ if j.val % kBits = y.val then high.getD (j.val / kBits) 0 else 0
    let lr := flockR1cs.rows w
    let left := lr.1.toArray
    let right := lr.2.toArray
    Array.ofFn (n := 2 ^ k) fun x ↦ sumTo (2 ^ (blake2sR1csLogSize - k)) fun row' ↦
      rows.getD row' 0 * (left.getD (x.val + 2 ^ k * row') 0 + alpha * right.getD (x.val + 2 ^ k * row') 0)
  Array.ofFn (n := 2 ^ k * kBits) fun i ↦ (cols.getD (i.val / 2 ^ k) #[]).getD (i.val % 2 ^ k) 0

/-- `L̂(x + 2^k y) = skip[x]`. -/
def skipTable (k : ℕ) (skip : List E) : Array E :=
  Array.ofFn (n := 2 ^ k * kBits) fun i ↦ skip.getD (i.val % 2 ^ k) 0

/-- `ŝ(x + 2^k y) = s_y`. -/
def sliceTable (k : ℕ) (s : List E) : Array E :=
  Array.ofFn (n := 2 ^ k * kBits) fun i ↦ s.getD (i.val / 2 ^ k) 0

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **The zerocheck's eq-factored rounds**, one per eq coordinate: the message `(c1, c2)`, the challenge, the
verifier's claim `polyEval ([claim + r (c1 + c2)] ++ [c1, c2]) x` (its `roundPoly` with the eq factor), the tables
folded low variable first. -/
def zcRounds : List E → E → Array E → Array E → Array E → WrM m ZcOut
  | [], claim, a, b, _ => pure ⟨[], claim, a.getD 0 0, b.getD 0 0⟩
  | r :: rest, claim, a, b, c => do
    let msg := zcRound (eqKernel rest) a b c
    sendScalar msg.1
    sendScalar msg.2
    let x ← sampleW H
    let claim' := polyEval ([claim + r * esum [msg.1, msg.2]] ++ [msg.1, msg.2]) x
    let out ← zcRounds rest claim' (foldE a x) (foldE b x) (foldE c x)
    return ⟨x :: out.chi, out.running, out.va, out.vb⟩

/-- **The skip's start** (with `k > 0`, `k` skip variables): the tables folded at `z`
(`L_x(z) = lagrangeWeights (2^k) z`) and the verifier's claim, the interpolation at `z` of `2^k` zeros and the
coset values. -/
def startAt (k : ℕ) (coset : List E) (z : E) (wit : Wit) : ZcStart :=
  let lw := lagrangeWeights (2 ^ k) z
  ⟨some z, lagrangeInterpolate (2 ^ (k + 1)) (List.replicate (2 ^ k) 0 ++ coset) z, skipFold k lw wit.a,
    skipFold k lw wit.b, skipFold k lw wit.c⟩

/-- Without a skip: the tables themselves, the claim `0`. -/
def startNone (wit : Wit) : ZcStart := ⟨none, 0, wit.a, wit.b, wit.c⟩

/-- **The skip** (`zerocheck`'s second step): with `k > 0`, the coset values sent, `z` drawn. -/
def skipW (k : ℕ) (r : List E) (wit : Wit) : WrM m ZcStart :=
  if k > 0 then do
    let coset := cosetValues k r wit
    sendScalars coset
    let z ← sampleW H
    return startAt k coset z wit
  else pure (startNone wit)

/-- **The zerocheck** (`zerocheck`'s order): the sampled coordinates; with a skip, the coset values and `z`; the
rounds; `v_a`, `v_b`. Returns what the verifier's `zerocheck` returns. -/
def zerocheckW (logN k : ℕ) (wit : Wit) : WrM m (Option E × List E × E × E × E) := do
  let sampled ← samplesW H (logN - k - nFixed)
  let st ← skipW H k (fixedChallenges ++ sampled) wit
  let zc ← zcRounds H (fixedChallenges ++ sampled) st.claim st.a st.b st.c
  sendScalar zc.va
  sendScalar zc.vb
  return (st.zSkip, zc.chi, zc.va, zc.vb, zc.running + zc.va * zc.vb)

/-- **The lincheck's rounds**, high variable first: the message `(c0, c2)`, the challenge, the verifier's claim
`polyEval ([c0, claim + c2] ++ [c2]) x` (its `roundPoly` without an eq factor), the tables folded. -/
def lcRounds : ℕ → E → Array E → Array E → WrM m LcOut
  | 0, claim, _, z => pure ⟨[], claim, z⟩
  | n + 1, claim, w, z => do
    let msg := lcRound w z
    sendScalar msg.1
    sendScalar msg.2
    let x ← sampleW H
    let claim' := polyEval ([msg.1, claim + esum [msg.2]] ++ [msg.2]) x
    let out ← lcRounds n claim' (foldHigh w x) (foldHigh z x)
    return ⟨x :: out.challenges, out.claim, out.z⟩

/-- The slices sent, unless `Slices.claim`; returns them as the verifier's front holds them. -/
def sendSlices (variant : Variant) (s : List E) : WrM m (Option (List E)) :=
  if variant.slices = .claim then pure none else do
    sendScalars s
    pure (some s)

end With

/-- The lincheck's claim `v_a + α v_b + α² v_c + α³` from the zerocheck's output. -/
def lcClaim (zc : Option E × List E × E × E × E) (alpha : E) : E :=
  zc.2.2.1 + alpha * zc.2.2.2.1 + epow alpha 2 * zc.2.2.2.2 + epow alpha 3

/-- The lincheck's weights at the zerocheck's point (`front`'s split: `row_low`, `chi_in`). -/
def lcWeightsOf (k : ℕ) (zc : Option E × List E × E × E × E) (alpha : E) : Array E :=
  lincheckWeights (rowWeightsOf (rowLowWeights zc.1 (zc.2.1.take (packing - k))).2
    ((zc.2.1.drop (packing - k)).take lincheckRounds)) alpha

/-- The lincheck's witness at the zerocheck's instance coordinates (`chi_rest`). -/
def lcWitnessOf (k : ℕ) (q : Array K) (zc : Option E × List E × E × E × E) : Array E :=
  lincheckWitness q ((zc.2.1.drop (packing - k)).drop lincheckRounds)

/-- **The front** from the zerocheck's output, `α`, the lincheck's output and the slices sent (if any): the
verifier's `Front` (the point's split as `front` makes it, `chi_in' = rounds.reverse`) and the true slices. -/
def frontOf (variant : Variant) (zc : Option E × List E × E × E × E) (alpha : E) (lc : LcOut)
    (slices : Option (List E)) : Front × List E :=
  let k := variant.skip
  let chi := zc.2.1
  let chiInPrime := lc.challenges.reverse
  (⟨zc.1, chi, chi.take (packing - k), (chi.drop (packing - k)).take lincheckRounds, chiInPrime, alpha, lc.claim,
      slices, chiInPrime ++ (chi.drop (packing - k)).drop lincheckRounds⟩, lc.z.toList)

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **Flock's front** (`front`'s order): the zerocheck, `α`, the lincheck, the slices (sent unless
`Slices.claim`). Returns the verifier's `Front` and the true slices. -/
def frontW (logN : ℕ) (variant : Variant) (q : Array K) : WrM m (Front × List E) := do
  let zc ← zerocheckW H logN variant.skip (witOf logN q)
  let alpha ← sampleW H
  let lc ← lcRounds H lincheckRounds (lcClaim zc alpha) (lcWeightsOf variant.skip zc alpha)
    (lcWitnessOf variant.skip q zc)
  let slices ← sendSlices variant lc.z.toList
  return frontOf variant zc alpha lc slices

/-- **The ring switch's end** (`ring_end`): the map's 6 challenges, the target as the verifier computes it. -/
def ringEndW (variant : Variant) (s : List E) : WrM m End := do
  let map ← samplesW H ringMapShifts.length
  return .ring map (if variant.slices = .tower then towerTarget s map
    else polyEval (s.map fun value ↦ ringMap value map) gen)

/-- The end: the ring switch's with the slices sent; without them a placeholder (no ring switch). -/
def endW (variant : Variant) : Option (List E) → WrM m End
  | some s => ringEndW H variant s
  | none => pure (.combination [] 0)

end With

/-- **What Flock leaves** from the front, the true slices and the end: the slices' point, the end, the pending
reduction as `verifyDeferred` computes it, the batch's tables (`G'`, `L̂`, `ŝ` over `k + 6` variables). -/
def assemble (fr : Front) (s : List E) (end_ : End) : FlockOut :=
  let k := packing - fr.rowLow.length
  ⟨fr.point, end_, Pending.new fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices,
    ⟨sliced k fr.rowLow fr.chiIn fr.chiInPrime fr.alpha, skipTable k (rowLowWeights fr.zSkip fr.rowLow).1,
      sliceTable k s, k + packing⟩⟩

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **Flock's honest prover** (`prover::flock::prove`, deferred): the front, the ring switch's map (with the
slices sent), what is left. -/
def flockProve : FlockProver m := fun logN variant q ↦ do
  let frs ← frontW H logN variant q
  let end_ ← endW H variant frs.1.slices
  return assemble frs.1 frs.2 end_

end With

/-! ## What the honest output satisfies -/

/-- **The ring relation is true of `q_flock`**: `Σ_u Φ(eq(point, u)) q_flock[u] = target`, the weight the batch's
`denseWeight` puts on `q_flock`'s words for the ring-switch term (`towerRingMap` of `eqKernel point`), over the
`2^|point|` words. Without a ring end it holds of nothing. -/
def FlockRingHolds (out : FlockOut) (q : Array K) : Prop :=
  match out.end_ with
  | .ring map target =>
    ∑ u ∈ Finset.range (2 ^ out.point.length),
      towerRingMap ((eqKernel out.point).getD u 0) map * ofK (q.getD u 0) = target
  | .combination _ _ => False

/-- **The pending product sum is the pending claim**: `Σ_i G'_i L̂_i ŝ_i = pending.claim`, over the tables'
`2^(k + 6)` entries (the batch's `λ³` component's sum, `productRound`'s). -/
def PendingSumHolds (out : FlockOut) : Prop :=
  ∑ i ∈ Finset.range (2 ^ out.tables.rounds),
    out.tables.g.getD i 0 * out.tables.l.getD i 0 * out.tables.s.getD i 0 = out.pending.claim

/-- **The pending terminal**: at every point `r` of the batch (its first `k + 6` coordinates the tables'), with
`a`, `b` the multilinear extensions of `A0`, `B0` at the matrices' claim's point, `Pending.terminal`'s value
`(a + α b) L̂(ρ) ŝ(σ)` is the product of the tables' multilinear extensions at `r`'s first `k + 6` coordinates
(what the batch's folds leave: `g[0] l[0] s[0]`). -/
def PendingTerminalHolds (out : FlockOut) : Prop :=
  ∀ r : List E, out.tables.rounds ≤ r.length →
    (out.pending.terminal r
        (multilinearEval ((flockMatrixStack true).toList.map ofK) (out.pending.matrixClaim r 0 0).point)
        (multilinearEval ((flockMatrixStack false).toList.map ofK) (out.pending.matrixClaim r 0 0).point)).1 =
      multilinearEval out.tables.g.toList (r.take out.tables.rounds) *
        multilinearEval out.tables.l.toList (r.take out.tables.rounds) *
        multilinearEval out.tables.s.toList (r.take out.tables.rounds)

/-- `q_flock`'s words as Lv42's column (`qflockColumn`'s form). -/
def colOf (κ : ℕ) (q : Array K) : LeanVM.Protocol.Column (Lv42.Parameters.Flock.kIn + κ) :=
  ⟨Vector.ofFn fun u ↦ q.getD u.val 0⟩

/-- **Flock's relation on `q_flock`** (`TraceHonest.flock`): every block satisfies the BLAKE2s R1CS and holds `1`
at the constant position. -/
def FlockHolds (κ : ℕ) (q : Array K) : Prop :=
  Lv42.Protocol.BlockR1CS.BatchHolds Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs
    Lv42.Parameters.Flock.constPos (Lv42.Protocol.bitTable (colOf κ q))

theorem qflockColumn_eq (tr : Trace) : qflockColumn tr = colOf (tr.height 5) tr.qflock := rfl

end UniComplete.FlockP
