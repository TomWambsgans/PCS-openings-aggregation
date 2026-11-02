-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): `StackClaim.Holds`, `IsMultilinearFn`, `boolPoint`
-- (`Protocol/EndToEnd/Claims.lean`), `eqEval_cons`, `eqEval_append`, `boolPoint_add`, `boolPoint_two_mul`
-- (`Protocol/Whir/Complete/Tables.lean`), through this repository's `E2ECompleteness.ProverOpening`
-- (`openingWithH_proveOpeningWithH`, `exists_failed_pow_opening`, `stackWeight_cube`), `Bridge.Opening`
-- (`stackClaims_eq`), `Completeness.Opening` (`isMultilinearFn_of_isMultiaffine`) and `WhirBridge.LargeParams`
-- (`admissible_large`).
import UniStatement.Opening
import E2ECompleteness.ProverOpening
import Bridge.Opening
import Completeness.Opening

/-!
# Honest WHIR openings at the univariate verifier's plain layouts

The univariate verifier opens each of its five commitments with one point claim (`UniStatement.pcsOpenWith`): the
Statement's opening (`PcsQuotient.openingWith`, mumbai's WHIR verifier) at the **plain layout**
`plainLayout vars = Layout.ofChunks vars vars vars [(0, 2^vars)]` (lane `l` holds block `l` of `2^(vars−6)`
words), at `vars = 27` (`C1`, `C2`), `24` (the setup), `28` (`A0`, `B0`). Here, at a pure Keccak-256 `H` and a
pure permutation `F` (`Id`, as `E2ECompleteness.ProverOpening` states its lemmas):

* **`stackEval`**: the stack's multilinear extension, `UniStatement.multilinearEval` of its words, the **low
  coordinate first** (word index bit `j` ↔ `pt[j]`), what the batching sumcheck's folds
  (`cur[i] = cur[2i] + r (cur[2i] + cur[2i+1])`) produce. `stackEval_eq`: it is
  `Σ_x stack[x] · eq(bits of x, pt)`, `eq` mumbai's `eqEval` and the bits `boolPoint` (bit `0` first).
* **The bit order** (`stackWeight_plain`): at the plain layout a claim's weight on the stack at the cube point of
  word `x` is `eq(bits of x, point)` with **the same order**: WHIR's `StackClaim.Holds` reads word `x` of the
  column at `boolPoint μ x` (bit `i` of `x` at coordinate `i`), and the weight `stackWeight` takes the point's
  first `vars − 6` coordinates against the low bits of `x` (the entry in the lane, `eqEval`) and its last `6`
  against the high bits (the lane, `eqBits`, low bit first). So the order WHIR's claim reads is `stackEval`'s:
  **no mismatch** (`plain_holds`). WHIR's internal rotation of the stack (lane bits first, `basisTable`,
  `stackTable`) is on both the weight table and the committed word, and is inside `openingWithH_proveOpeningWithH`.
* **`plain_holds`**, **`plain_multilinear`**: the point claim `⟨pt, stackEval stack pt⟩` holds of the stack's
  column (`colOf`) in WHIR's semantics, for `stack.size = 2^vars`, `pt.length = vars`; every stack claim of a plain
  layout has a multilinear weight (through Bridge-Defs' `stackClaims_eq` and F2's multiaffine weights).
* **`weightShape_plain`**, **`admissible_plain`**: `WeightShape (plainLayout v)` for `6 ≤ v ≤ 64` (the layout is
  `64` block lanes, `plainLayout_eq`), and admissibility at rate `1/2` for `24 ≤ v ≤ 28` (`WhirBridge.admissible_large`,
  decided there by `decide +kernel`); `plainShapes` the two at `24 ..= 28`.
* **`pcsOpen_honest`**: every proof `proveOpeningWithH` produces for the point claim on the stack's commitment
  (`commitWithH`) is accepted by `openingWithH` against the commitment's root. **`pcsOpenWith_honest`**: the same
  for the verifier's `UniStatement.pcsOpenWith (fun s ↦ pure (F s))`, Keccak-256 over `F` (`keccak256With`), the root
  read back from its two halves (`rootOf (digestScalars root)`, `rootOf_digestScalars`: how the verifier reads
  `C1`'s and `C2`'s roots from the stream); **`pcsOpenWith_honest'`** with the Statement's own prover and
  commitment (`PcsQuotient.proveOpeningWith`, `PcsQuotient.commitWith`).
* **`pcsOpen_fails_only_at_pow`**: if the prover returns `none`, the opening program reached a `17`-bit proof of
  work at a sponge where every nonce below `fuel` fails (`exists_failed_pow_opening`), for any claims of `vars`
  coordinates, whatever the stack.

Decisions: `commitWithH` takes Keccak-256 only (`commitWithH H vars stack`, no permutation: the Merkle tree hashes,
it does not permute). The layouts' facts are proved for every size (`plainLayout_eq`: `(2^v + 2^(v−6) − 1) / 2^(v−6)
= 64`), not decided on each; only admissibility is a kernel decision (on the ladders, `WhirBridge.LargeParams`). No
stack is evaluated: the stacks are arbitrary.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.Verifier (eqEval)

namespace UniComplete

/-! ## The stack's multilinear extension -/

/-- **The stack's multilinear extension** at `pt`, low coordinate first: word index bit `j` ↔ `pt[j]`
(`UniStatement.multilinearEval`, the batching sumcheck's folds). -/
def stackEval (stack : Array K) (pt : List E) : E :=
  UniStatement.multilinearEval (stack.toList.map ofK) pt

theorem sum_range_two_mul (f : ℕ → E) :
    ∀ n, ∑ x ∈ Finset.range (2 * n), f x = ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1))
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul f n, Finset.sum_range_succ, add_assoc]

theorem foldOnce_size (cur : Array E) (r : E) : (UniStatement.foldOnce cur r).size = cur.size / 2 := by
  simp [UniStatement.foldOnce]

theorem foldOnce_getD (cur : Array E) (r : E) {i : ℕ} (hi : i < cur.size / 2) :
    (UniStatement.foldOnce cur r).getD i 0 =
      cur.getD (2 * i) 0 + r * (cur.getD (2 * i) 0 + cur.getD (2 * i + 1) 0) := by
  unfold UniStatement.foldOnce
  rw [E2ECompleteness.getD_ofFn' _ hi]

/-- **The folds compute the multilinear extension**, low coordinate first: on a table of `2^|pt|` entries, the
folds by `pt` leave `Σ_x a[x] · eq(bits of x, pt)`. -/
theorem foldl_foldOnce : ∀ (pt : List E) (a : Array E), a.size = 2 ^ pt.length →
    (pt.foldl UniStatement.foldOnce a).getD 0 0 =
      ∑ x ∈ Finset.range (2 ^ pt.length), a.getD x 0 * eqEval (boolPoint pt.length x) pt
  | [], a, _ => by simp [eqEval, boolPoint]
  | r :: rs, a, h => by
    have hs : (UniStatement.foldOnce a r).size = 2 ^ rs.length := by
      rw [foldOnce_size, h, List.length_cons, pow_succ', Nat.mul_div_cancel_left _ (by norm_num)]
    rw [List.foldl_cons, foldl_foldOnce rs _ hs, List.length_cons, pow_succ', sum_range_two_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < a.size / 2 := by
      rw [h, List.length_cons, pow_succ', Nat.mul_div_cancel_left _ (by norm_num)]
      exact Finset.mem_range.1 hi
    rw [foldOnce_getD a r hi', Whir.Complete.boolPoint_two_mul, Whir.Complete.boolPoint_two_mul_add_one,
      Whir.Complete.eqEval_cons, Whir.Complete.eqEval_cons]
    have h2 : (1 : E) + 1 = 0 := CharTwo.add_self_eq_zero 1
    linear_combination (-(a.getD (2 * i + 1) 0 * eqEval (boolPoint rs.length i) rs)) * h2

/-- **`stackEval` is the stack's multilinear extension**: `Σ_x stack[x] · eq(bits of x, pt)`, bit `0` of `x`
against `pt[0]`, for a stack of `2^|pt|` words. -/
theorem stackEval_eq (stack : Array K) (pt : List E) (hs : stack.size = 2 ^ pt.length) :
    stackEval stack pt =
      ∑ x ∈ Finset.range (2 ^ pt.length), ofK (stack.getD x 0) * eqEval (boolPoint pt.length x) pt := by
  unfold stackEval UniStatement.multilinearEval
  rw [foldl_foldOnce pt _ (by simp [hs])]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' : x < stack.size := hs ▸ Finset.mem_range.1 hx
  congr 1
  simp [Array.getD_eq_getD_getElem?, hx']

/-! ## The plain layout -/

open UniStatement (plainLayout)

/-- **The plain layout of `2^v` words** (`v ≥ 6`): `64` lanes, lane `l` block `l`, public. -/
theorem plainLayout_eq {v : ℕ} (hv : 6 ≤ v) :
    plainLayout v = ⟨v, v, (List.range 64).map PcsQuotient.Lane.block, none, []⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, v = k + 6 := ⟨v - 6, by omega⟩
  have hk : k + 6 - PcsQuotient.laneFold = k := by simp [PcsQuotient.laneFold]
  have hdiv : (2 ^ (k + 6) + 2 ^ k - 1) / 2 ^ k = 64 := by
    have hp : 0 < 2 ^ k := by positivity
    rw [pow_add]
    generalize 2 ^ k = L at hp ⊢
    apply Nat.div_eq_of_lt_le <;> omega
  simp only [plainLayout, PcsQuotient.Layout.ofChunks, hk, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, zero_mul, zero_add, hdiv]

/-- **The plain layout has the weight table's shape** (`WeightShape`) at every size `6 ≤ v ≤ 64`. -/
theorem weightShape_plain {v : ℕ} (h1 : 6 ≤ v) (h2 : v ≤ 64) :
    E2ECompleteness.WeightShape (plainLayout v) := by
  rw [plainLayout_eq h1]
  exact ⟨h1, h2, by simp, by simp [PcsQuotient.Layout.logLane], fun s hs ↦ by simp at hs⟩

/-- **The plain layouts of `2^24 ..= 2^28` words are admissible** at rate `1/2` (`WhirBridge.admissible_large`). -/
theorem admissible_plain {v : ℕ} (h1 : 24 ≤ v) (h2 : v ≤ 28) :
    Whir.Admissible (plainLayout v).logN PcsQuotient.logInvRate :=
  WhirBridge.admissible_large h1 h2

/-- **Both facts at the univariate verifier's sizes**, `24 ≤ v ≤ 28`. -/
theorem plainShapes {v : ℕ} (h1 : 24 ≤ v) (h2 : v ≤ 28) :
    E2ECompleteness.WeightShape (plainLayout v) ∧ Whir.Admissible v PcsQuotient.logInvRate :=
  ⟨weightShape_plain (by omega) (by omega), admissible_plain h1 h2⟩

/-! ## The claim's weight, and its meaning -/

/-- **A plain layout's claim weight at the cube point of word `x`** is `eq(bits of x, point)`, bit `0` of `x`
against the point's first coordinate: the order `stackEval` reads. -/
theorem stackWeight_plain {v : ℕ} (h1 : 6 ≤ v) (h2 : v ≤ 64) (c : PcsQuotient.Claim)
    (hc : c.point.length = v) {x : ℕ} (hx : x < 2 ^ v) :
    PcsQuotient.stackWeight (plainLayout v) c (boolPoint v x) = eqEval (boolPoint v x) c.point := by
  have hL := weightShape_plain h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, v = k + 6 := ⟨v - 6, by omega⟩
  have hℓ : (plainLayout (k + 6)).logLane = k := by
    rw [plainLayout_eq h1]
    simp [PcsQuotient.Layout.logLane, PcsQuotient.laneFold]
  have hp : 0 < 2 ^ k := by positivity
  have hy : x % 2 ^ k < 2 ^ k := Nat.mod_lt _ hp
  have hl : x / 2 ^ k < 64 := by
    rw [Nat.div_lt_iff_lt_mul hp]
    rw [pow_add] at hx
    generalize 2 ^ k = L at hx ⊢
    omega
  have hw := E2ECompleteness.stackWeight_cube hL c hc hl (by rw [hℓ]; exact hy)
  rw [hℓ, show (plainLayout (k + 6)).logN = k + 6 from rfl, Nat.mod_add_div] at hw
  rw [hw, plainLayout_eq h1]
  simp only [PcsQuotient.Layout.weightAt, PcsQuotient.Layout.claimWeights, PcsQuotient.Layout.scales,
    PcsQuotient.Layout.logLane, PcsQuotient.laneFold, List.map_map, Function.comp_def,
    E2ECompleteness.toArray_getD', Nat.add_sub_cancel]
  rw [E2ECompleteness.eqKernelA_getD_take c.point (by omega) hy,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, Option.map_some,
    Option.getD_some, E2ECompleteness.OpeningTr.eqBits_eq, WhirBridge.eqBits_eq_boolPoint,
    List.length_drop, hc, Nat.add_sub_cancel_left]
  conv_rhs => rw [← Nat.mod_add_div x (2 ^ k), Whir.Complete.boolPoint_add k 6 _ _ hy,
    ← List.take_append_drop k c.point]
  rw [Whir.Complete.eqEval_append _ _ _ _ (by simp [hc]), mul_comm]

/-- **The point claim `⟨pt, stackEval stack pt⟩` holds** of the stack's column in WHIR's semantics, at the plain
layout of `2^v` words, for a stack of `2^v` words and a point of `v` coordinates. -/
theorem plain_holds {v : ℕ} (h1 : 6 ≤ v) (h2 : v ≤ 64) (stack : Array K) (hs : stack.size = 2 ^ v)
    (pt : List E) (hpt : pt.length = v) :
    ∀ sc ∈ PcsQuotient.stackClaims (plainLayout v) [⟨pt, stackEval stack pt⟩],
      EndToEnd.StackClaim.Holds v sc (E2ECompleteness.colOf v stack) := by
  intro sc hsc
  have hp : (plainLayout v).logPiece = none := rfl
  simp only [PcsQuotient.stackClaims, hp, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    List.append_nil, List.map_cons, List.map_nil, List.mem_singleton] at hsc
  subst hsc
  unfold EndToEnd.StackClaim.Holds
  dsimp only
  conv_rhs => rw [stackEval_eq stack pt (by rw [hs, hpt]), hpt, Finset.sum_range]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [stackWeight_plain h1 h2 ⟨pt, stackEval stack pt⟩ hpt x.isLt, mul_comm]
  congr 2
  simp [E2ECompleteness.colOf, Vector.getD, Array.getD_eq_getD_getElem?, x.isLt]

/-- **Every stack claim of a plain layout has a multilinear weight** (`IsMultilinearFn`, what mumbai's
completeness of the opening asks): F2's weights are multiaffine (`Stacking.isMultiaffine_claims`, through
Bridge-Defs' `stackClaims_eq`, the layout public). -/
theorem plain_multilinear (v : ℕ) (claims : List PcsQuotient.Claim) :
    ∀ sc ∈ PcsQuotient.stackClaims (plainLayout v) claims, EndToEnd.IsMultilinearFn v sc.1 := by
  intro sc hsc
  rw [Bridge.stackClaims_eq (plainLayout v) (Or.inl rfl) claims] at hsc
  exact Completeness.isMultilinearFn_of_isMultiaffine
    ((Bridge.layoutTr (plainLayout v)).stacking.isMultiaffine_claims (claims.map Bridge.claimTr) sc hsc)

/-! ## The honest openings are accepted -/

/-- **An honest opening at a plain layout is accepted** (`24 ≤ vars ≤ 28`), at a pure Keccak-256 `H` and
permutation `F`: every proof the Statement's opening prover (`proveOpeningWithH`) makes of the point claim
`⟨pt, stackEval stack pt⟩` on the stack's commitment is accepted by the Statement's opening check against the
commitment's root. -/
theorem pcsOpen_honest (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {vars : ℕ}
    (h1 : 24 ≤ vars) (h2 : vars ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ vars) (pt : List E)
    (hpt : pt.length = vars) {π : Compile.Proof}
    (hπ : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) H vars stack) stack [⟨pt, stackEval stack pt⟩] = some π) :
    E2ECompleteness.openingWithH (m := Id) H F (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) H vars stack).root [⟨pt, stackEval stack pt⟩] π = true :=
  E2ECompleteness.openingWithH_proveOpeningWithH H F fuel (plainLayout vars)
    (weightShape_plain (by omega) (by omega)) (admissible_plain h1 h2) stack _ (List.cons_ne_nil _ _)
    (fun c hc ↦ by rw [List.mem_singleton] at hc; subst hc; exact hpt)
    (plain_holds (by omega) (by omega) stack hs pt hpt) (plain_multilinear vars _) hπ

/-- **A root read back from its two halves** (`next_root`, how the verifier reads `C1`'s and `C2`'s roots from
the stream) is the root. -/
theorem rootOf_digestScalars (d : Digest) : UniStatement.rootOf (digestScalars d) = d := by
  simp [UniStatement.rootOf, digestOfScalars_digestScalars]

/-- **`PCS_OPEN` accepts the honest opening** (`UniStatement.pcsOpenWith` over `F`, Keccak-256 over `F`), at the
root the stream carries as two halves: `pcsOpen_honest` at `H = keccak256With F` through `openingWith_eqH`. -/
theorem pcsOpenWith_honest (F : KeccakState → KeccakState) (fuel : ℕ) {vars : ℕ} (h1 : 24 ≤ vars)
    (h2 : vars ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ vars) (pt : List E) (hpt : pt.length = vars)
    {π : Compile.Proof}
    (hπ : E2ECompleteness.proveOpeningWithH (m := Id) (keccak256With (m := Id) fun s ↦ pure (F s))
      (fun s ↦ pure (F s)) fuel (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) (keccak256With (m := Id) fun s ↦ pure (F s)) vars stack) stack
      [⟨pt, stackEval stack pt⟩] = some π) :
    UniStatement.pcsOpenWith (m := Id) (fun s ↦ pure (F s)) vars
      (UniStatement.rootOf (digestScalars
        (E2ECompleteness.commitWithH (m := Id) (keccak256With (m := Id) fun s ↦ pure (F s)) vars stack).root))
      [⟨pt, stackEval stack pt⟩] π = true := by
  rw [rootOf_digestScalars, UniStatement.pcsOpenWith, E2ECompleteness.openingWith_eqH]
  exact pcsOpen_honest _ F fuel h1 h2 stack hs pt hpt hπ

/-- **The same with the Statement's prover and commitment** over `F` (`PcsQuotient.proveOpeningWith`,
`PcsQuotient.commitWith`), through `proveOpeningWith_eqH`, `commitWith_eqH`. -/
theorem pcsOpenWith_honest' (F : KeccakState → KeccakState) (fuel : ℕ) {vars : ℕ} (h1 : 24 ≤ vars)
    (h2 : vars ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ vars) (pt : List E) (hpt : pt.length = vars)
    {π : Compile.Proof}
    (hπ : PcsQuotient.proveOpeningWith (m := Id) (fun s ↦ pure (F s)) fuel (plainLayout vars)
      (PcsQuotient.commitWith (m := Id) (fun s ↦ pure (F s)) vars stack) stack
      [⟨pt, stackEval stack pt⟩] = some π) :
    UniStatement.pcsOpenWith (m := Id) (fun s ↦ pure (F s)) vars
      (UniStatement.rootOf (digestScalars
        (PcsQuotient.commitWith (m := Id) (fun s ↦ pure (F s)) vars stack).root))
      [⟨pt, stackEval stack pt⟩] π = true := by
  rw [E2ECompleteness.proveOpeningWith_eqH, E2ECompleteness.commitWith_eqH] at hπ
  rw [E2ECompleteness.commitWith_eqH]
  exact pcsOpenWith_honest F fuel h1 h2 stack hs pt hpt hπ

/-! ## The prover fails only at a proof of work -/

/-- **The opening prover fails only at a proof of work** at a plain layout (`24 ≤ vars ≤ 28`): if it makes no
proof, the opening program reaches a `17`-bit proof of work at a sponge where every nonce below `fuel` fails; for
any claims of `vars` coordinates and any stack. -/
theorem pcsOpen_fails_only_at_pow (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
    {vars : ℕ} (h1 : 24 ≤ vars) (h2 : vars ≤ 28) (stack : Array K) (claims : List PcsQuotient.Claim)
    (hlen : ∀ c ∈ claims, c.point.length = vars)
    (h : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) H vars stack) stack claims = none) :
    ∃ hist k sp, (Whir.Complete.openingProgram vars PcsQuotient.logInvRate
        (PcsQuotient.stackClaims (plainLayout vars) claims)).after hist =
          some (.grind Whir.queryGrindingBits k) ∧
      ∀ n < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf n)
        (Compile.powStep F sp (Compile.nonceOf n)).1 = false :=
  E2ECompleteness.exists_failed_pow_opening H F fuel (plainLayout vars)
    (weightShape_plain (by omega) (by omega)) (admissible_plain h1 h2) stack claims hlen h

end UniComplete

/-! ## Axioms -/

/-- info: 'UniComplete.stackEval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.stackEval_eq

/-- info: 'UniComplete.plainLayout_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.plainLayout_eq

/-- info: 'UniComplete.weightShape_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.weightShape_plain

/-- info: 'UniComplete.admissible_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.admissible_plain

/-- info: 'UniComplete.plainShapes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.plainShapes

/-- info: 'UniComplete.stackWeight_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.stackWeight_plain

/-- info: 'UniComplete.plain_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.plain_holds

/-- info: 'UniComplete.plain_multilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.plain_multilinear

/-- info: 'UniComplete.pcsOpen_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.pcsOpen_honest

/-- info: 'UniComplete.rootOf_digestScalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.rootOf_digestScalars

/-- info: 'UniComplete.pcsOpenWith_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.pcsOpenWith_honest

/-- info: 'UniComplete.pcsOpenWith_honest'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.pcsOpenWith_honest'

/-- info: 'UniComplete.pcsOpen_fails_only_at_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.pcsOpen_fails_only_at_pow
