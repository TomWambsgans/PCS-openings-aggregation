-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/pi2/verifier.rs`
-- (`SpecPair`, `Group`, `Spec`, `Spec::of`, `subspace_coefficients`, `zero_coset`, `normalised_constants`,
-- `tag_walk`) and `crates/leanvm_rec/src/pi2/circuit.rs` (`coset_constants`, `vanishing`, `pair_constants`,
-- `Circuit::max_gamma`), branch `leanvm-rec` @ 2b22581. The Cantor basis is `formal/UniStatement`'s (`beta`, `point`).
import RecStatement.Basic

/-!
# What the verifier is built from (`Spec::of`)

From the circuit (`Circuit`, the data the Rust emits), the verifier's constants, computed here as the Rust
computes them, in `K`:

* the blocks' vanishing polynomials `Z_{U_s}` of `U_s = span(β_r, …, β_{r+s−1})` (`r` the rows' log):
  `Z_{U_0}(x) = x`, `Z_{U_s} = Z_{U_{s−1}}² + e_s Z_{U_{s−1}}`, `e_s = Z_{U_{s−1}}(β_{r+s−1})`
  (`cosetConstants`, `vanishing`);
* each pair's `Ẑ_s(c_p) = Z_{U_s}(c_p) / Π_{j ≤ s} e_j`, `c_p = ω_{first_row · 2^r + role}` (`pairConstants`), and the
  normalised recursion's constants `c_s = Π_{j < s} e_j / e_s` (`normalisedConstants`): `Ẑ_s = Ẑ_{s−1} + c_s Ẑ_{s−1}²`;
* the **groups**: the pairs of one role, one pull flag and one formula (equal as values), in first appearance;
* the **zero coset** (`zeroCosetOf`): the public terms of value zero, if their tags are an aligned coset `c + V_k`
  (`k ≥ 1`), with the coefficients `a_i` of `V_k`'s subspace polynomial `w_k = s^k = Σ a_i X^(2^i)`
  (`subspaceCoefficients`); the other terms stay, in order;
* `maxGamma`, the highest power of `γ` a coefficient takes; the **walk** (`tagWalk`), the order the public terms
  are summed in.
-/

namespace RecStatement

open LeanVM.Parameters UniStatement

/-- `vanishing(x, e, s)`: `Z_{U_s}(x)`, by `z ↦ z² + e_j z` for `j < s`. -/
def vanishing (x : K) (e : List K) (s : ℕ) : K :=
  (List.range s).foldl (fun z j ↦ z * z + e.getD j 0 * z) x

/-- **`coset_constants(r, count)`**: `e_1 … e_count`, `e_s = Z_{U_{s−1}}(β_{r+s−1})`. -/
def cosetConstants (r count : ℕ) : List K :=
  (List.range count).foldl (fun e s ↦ e ++ [vanishing (beta.getD (r + s) 0) e s]) []

/-- **`pair_constants(pair, r, e)`**: `Z_{U_s}(c_p)` and `Π_{j < s} e_j`, `c_p = ω_{first_row · 2^r + role}`. -/
def pairConstants (p : Pair) (r : ℕ) (e : List K) : K × K :=
  (vanishing (point (p.firstRow * 2 ^ r + p.role)) e p.logRows, (e.take p.logRows).foldl (· * ·) 1)

/-- **`normalised_constants(e)`**: `c_s = Π_{j < s} e_j / e_s`. -/
def normalisedConstants (e : List K) : List K :=
  (e.foldl (fun (acc : List K × K) x ↦ (acc.1 ++ [acc.2 * x⁻¹], acc.2 * x)) ([], 1)).1

/-- **`subspace_coefficients(k)`**: the coefficients `a_i` of `w_k = s^k = Σ_{i ≤ k} a_i X^(2^i)`, low first:
`s(Σ a_i X^(2^i)) = Σ a_i² X^(2^(i+1)) + Σ a_i X^(2^i)`. -/
def subspaceCoefficients (k : ℕ) : List K :=
  (List.range k).foldl (fun a _ ↦
    (List.range (a.length + 1)).map fun i ↦
      (if i = 0 then 0 else a.getD (i - 1) 0 * a.getD (i - 1) 0) + a.getD i 0) [1]

/-- A pair as the verifier needs it (`SpecPair`): its block's rows' log `s` and `Ẑ_s(c_p)`. -/
structure SpecPair where
  logRows : ℕ
  z : K
  deriving DecidableEq, Repr, Inhabited

/-- **A group** (`Group`): the pairs of one role, one pull flag and one formula. -/
structure Group where
  role : ℕ
  formula : Formula
  pulls : Bool
  pairs : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- **What the verifier is built from** (`Spec`). -/
structure Spec where
  logN : ℕ
  logRow : ℕ
  pairs : List SpecPair
  groups : List Group
  /-- The pull-less pairs (the holes). -/
  pullLess : List ℕ
  /-- `c_1, …`: `Ẑ_s = Ẑ_{s−1} + c_s Ẑ_{s−1}²`. -/
  c : List K
  reads : List Read
  /-- The public terms but the zero coset's. -/
  publicTerms : List PublicTerm
  maxGamma : ℕ
  /-- The zero coset: its first tag, `k`, and `w_k`'s coefficients. -/
  zeroCoset : Option (ℕ × ℕ × List K)
  deriving Inhabited

/-- The highest power of `γ` in a linear form (`max_gamma`'s `lin`). -/
def Lin.maxGamma (l : Lin) : ℕ :=
  ((l.terms.map fun t ↦ t.1.gamma) ++ (l.constant.map (·.gamma)).toList).foldl max 0

/-- **`Circuit::max_gamma`**: over the formulas (a product's coefficient's power plus its two forms') and the public
terms. -/
def Circuit.maxGamma (c : Circuit) : ℕ :=
  let formulas := c.formulas.map fun f ↦
    ((f.products.map fun (k, a, b) ↦ k.gamma + a.maxGamma + b.maxGamma) ++ [f.lin.maxGamma]).foldl max 0
  (formulas ++ c.publicTerms.map (·.value.maxGamma)).foldl max 0

/-- The groups: each pair joins the first group of its role, pull flag and formula, or starts one. -/
def groupsOf (c : Circuit) : List Group :=
  (List.range c.pairs.length).foldl (fun gs i ↦
    let p := c.pairs.getD i default
    let f := c.formulas.getD p.formula default
    match gs.findIdx? (fun g ↦ g.role = p.role ∧ g.pulls = p.pulls ∧ g.formula = f) with
    | some j => gs.modify j fun g ↦ { g with pairs := g.pairs ++ [i] }
    | none => gs ++ [⟨p.role, f, p.pulls, [i]⟩]) []

/-- A term of value zero (no terms, no constant). -/
def PublicTerm.isZero (t : PublicTerm) : Bool := t.value.terms.isEmpty && t.value.constant.isNone

/-- **`zero_coset(public)`**: the zero-valued terms, if their tags are exactly an aligned coset of `2^k` tags
(`k ≥ 1`): its first tag, `k` and `w_k`'s coefficients, and the other terms; or none and all the terms. -/
def zeroCosetOf (terms : List PublicTerm) : Option (ℕ × ℕ × List K) × List PublicTerm :=
  let zeros := terms.filter (·.isZero)
  let tags := (zeros.map (·.tag)).mergeSort (· ≤ ·)
  let n := tags.length
  let first := tags.headD 0
  let consecutive := (List.range (n - 1)).all fun i ↦ tags.getD (i + 1) 0 = tags.getD i 0 + 1
  if 2 ≤ n ∧ n = 2 ^ Nat.log2 n ∧ first % n = 0 ∧ consecutive then
    let k := Nat.log2 n
    (some (first, k, subspaceCoefficients k), terms.filter fun t ↦ !t.isZero)
  else (none, terms)

/-- **`Spec::of(circuit)`** (the circuit's validity, which the Rust asserts, is not checked here). -/
def Spec.of (c : Circuit) : Spec :=
  let (m, r) := (c.logN, c.logRow)
  let e := cosetConstants r (m - r)
  let (coset, rest) := zeroCosetOf c.publicTerms
  { logN := m
    logRow := r
    pairs := c.pairs.map fun p ↦
      let (z, norm) := pairConstants p r e
      ⟨p.logRows, z * norm⁻¹⟩
    groups := groupsOf c
    pullLess := (List.range c.pairs.length).filter fun i ↦ !(c.pairs.getD i default).pulls
    c := normalisedConstants e
    reads := c.reads
    publicTerms := rest
    maxGamma := c.maxGamma
    zeroCoset := coset }

/-- The scalars the proof sends after the roots (`Spec::values`): the `2^r` fold values and `ξ`. -/
def Spec.values (s : Spec) : ℕ := 2 ^ s.logRow + 1

/-- The largest block (`Spec::max_log_rows`). -/
def Spec.maxLogRows (s : Spec) : ℕ := (s.pairs.map (·.logRows)).foldl max 0

/-- The number of set bits of `n` below bit `64` (`u32::count_ones` of a tag). -/
def popCount64 (n : ℕ) : ℕ := (List.range 64).countP fun b ↦ n.testBit b

/-- **`tag_walk(public)`**: from the smallest tag, each next the term whose tag differs from the last in the fewest
bits (the smallest tag on a tie). -/
def tagWalk (tags : List ℕ) : List ℕ := Id.run do
  let order := ((List.range tags.length).mergeSort fun a b ↦ tags.getD a 0 ≤ tags.getD b 0)
  let mut left := order
  let mut out : List ℕ := []
  let mut at? : Option ℕ := none
  for _ in [0:tags.length] do
    match left with
    | [] => pure ()
    | j0 :: _ =>
      let k := match at? with
        | none => j0
        | some tag =>
          (left.foldl (fun (best : Option (ℕ × ℕ × ℕ)) j ↦
            let key := (popCount64 (tags.getD j 0 ^^^ tag), tags.getD j 0)
            match best with
            | none => some (key.1, key.2, j)
            | some (b1, b2, bj) => if key.1 < b1 ∨ (key.1 = b1 ∧ key.2 < b2) then some (key.1, key.2, j)
                else some (b1, b2, bj)) none).elim j0 (·.2.2)
      left := left.erase k
      at? := some (tags.getD k 0)
      out := out ++ [k]
  return out

end RecStatement
