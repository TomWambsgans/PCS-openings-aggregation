-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/pi2/verifier.rs`
-- (`reduce`'s arithmetic after the transcript: `coeff`, `lin`, `formula`, the digits, the row's cells by the
-- siblings' fold, the blocks' `Ẑ_s(t)`, the groups' and the public side's fractions along `tag_walk`, the zero coset in
-- closed form, the pushes' sum, the identity, the one inversion, the claims), branch `leanvm-rec` @ 2b22581. `sq` is
-- `formal/QuotientSecurity`'s (`Cantor.lean`).
import Mathlib.Algebra.Field.Basic
import QuotientSecurity.Cantor

/-!
# The verifier's arithmetic at `t`, over any field

`pi2::verifier::reduce` after it has read the stream and drawn its challenges: a function of the public scalars,
`α, β, γ, t`, the fold values `a_k`, `ξ` and `ρ`, **generic in the field** as the Rust is generic in its
`Scalar` (the deployed verifier runs it on `E`, `RecStatement.Verifier`; the lemmas, `RecStatement.Lemmas`, prove
what it computes over any field of characteristic two). Every intermediate value is a field of `Out`, in the Rust's
order (`PI2.md` §2, steps 1–7):

1. the digits `w_0 … w_{m+2}`, `w_{l+1} = w_l² + w_l` (`sq`);
2. the row's cells `v_c` by the siblings' fold (`cellsList`, `PI2.md` §9 lever 3a: the odd child is the even one
   plus the difference);
3. `Ẑ_s(t)` for every block size (`zHat`), each group's indicators summed as one fraction `N_g/D_g`
   (`fraction`), `w_m` factored out;
4. the public side, its terms along the walk (`walkDens`: `β ω_τ` updated by the bits that differ) and the zero
   coset's closed form `β^(2^k−1)/F(Y)` (`cosetSum`);
5. the pushes' sum `A/B` and the pull-less groups' `S_n/S_d` (`pushSums`);
6. `d_pull`, `D_n`, `Y`, `X`; the one inversion of `S_d Y · w_{m+2} · D`; the digits' inverses down from
   `1/w_{m+2}`;
7. the claims: `W` at `(ρ, ρ², …, w_r, …, w_{m−1})` (`foldAt`'s value), `Q` at `(u, ρ', y_0, y_1)` and at the top
   coefficient, the setup at `(w_0, …, w_{m−1}, β)`.

**Deviations, none changing a value**: the Rust skips a product by a coefficient equal to one and a zero
coefficient of the subspace polynomial (here the product is taken: `1 · x = x`, `0 · x = 0`); `γ^g` is read from
the list of powers as the Rust's `gammas[g]` (for `g = 0` the Rust takes the value itself, `gammas[0] = 1`); the
inverse is the field's (the Rust's is the norm's, `RecStatement.Inverse`, the same value; the runner checks it).
-/

namespace RecStatement

open QuotientSecurity

variable {F : Type} [Field F]

/-! ## The circuit's formulas over `F` -/

/-- **A coefficient over `F`**: a value times `γ^gamma`. -/
structure CoeffF (F : Type) where
  value : F
  gamma : ℕ

/-- **A linear form over `F`**: `Σ coefficient · cell` plus a constant. -/
structure LinF (F : Type) where
  terms : List (CoeffF F × ℕ)
  constant : Option (CoeffF F)

/-- **A formula over `F`**: a linear form plus products of two linear forms. -/
structure FormulaF (F : Type) where
  lin : LinF F
  products : List (CoeffF F × LinF F × LinF F)

/-- **A group over `F`**: its role, its formula, whether it pulls, its pairs. -/
structure GroupF (F : Type) where
  role : ℕ
  formula : FormulaF F
  pulls : Bool
  pairs : List ℕ

/-- `coeff(c, gammas)`: the value times `γ^gamma`, read from the powers. -/
def CoeffF.eval (gs : List F) (c : CoeffF F) : F := c.value * gs.getD c.gamma 0

/-- `lin(l, cell, gammas)`. -/
def LinF.eval (gs : List F) (cell : ℕ → F) (l : LinF F) : F :=
  l.terms.foldl (fun acc t ↦ acc + t.1.eval gs * cell t.2) (match l.constant with
    | none => 0
    | some c => c.eval gs)

/-- `formula(f, cell, gammas)`. -/
def FormulaF.eval (gs : List F) (cell : ℕ → F) (f : FormulaF F) : F :=
  f.products.foldl (fun acc p ↦ acc + p.1.eval gs * (p.2.1.eval gs cell * p.2.2.eval gs cell))
    (f.lin.eval gs cell)

/-- `powers(γ, n)`: `[1, γ, …, γ^(n−1)]`. -/
def powersList (γ : F) (n : ℕ) : List F := (List.range n).map (γ ^ ·)

/-! ## The verifier's constants over `F` -/

/-- **What the arithmetic is built from**, over `F`: the shape, the pairs (`(s, Ẑ_s(c_p))`), the groups, the
normalised recursion's constants, the public terms (tag, value) and the walk's order, the zero coset (first tag, `k`,
`w_k`'s coefficients), the highest power of `γ`, the extension's coordinates `(y_0, y_1)` and scale `s`, and the
points `ω`. -/
structure CoreSpec (F : Type) where
  logN : ℕ
  logRow : ℕ
  pairs : List (ℕ × F)
  groups : List (GroupF F)
  c : List F
  publicTerms : List (ℕ × LinF F)
  walk : List ℕ
  zeroCoset : Option (ℕ × ℕ × List F)
  maxGamma : ℕ
  y0 : F
  y1 : F
  scale : F
  ω : ℕ → F

/-- The largest block's rows' log. -/
def CoreSpec.maxLogRows (S : CoreSpec F) : ℕ := (S.pairs.map (·.1)).foldl max 0

/-- **What the transcript gives the arithmetic**: the public scalars and the proof's values and challenges. -/
structure Inputs (F : Type) where
  scalars : List F
  α : F
  β : F
  γ : F
  t : F
  a : List F
  ξ : F
  ρ : F

/-! ## The steps -/

/-- **The digits** `w_0(t), …, w_{count−1}(t)`, `w_l = s^l(t)`. -/
def digitsList (t : F) (count : ℕ) : List F := (List.range count).map fun l ↦ sq^[l] t

/-- One level of the row's fold (`PI2.md` §9 lever 3a): each parent `k`, at `z = w_l + ω(2k)`, gives its even
child `p_j + z (p_j + p_{j+half})` and its odd child, the even one plus the difference `p_j + p_{j+half}`. -/
def foldLevel (ω : ℕ → F) (w : List F) (l : ℕ) (layer : List (List F)) : List (List F) :=
  let half := 2 ^ l
  (List.range layer.length).flatMap fun k ↦
    let parent := layer.getD k []
    let z := w.getD l 0 + ω (2 * k)
    let d := (List.range half).map fun j ↦ parent.getD j 0 + parent.getD (j + half) 0
    let even := (List.range half).map fun j ↦ parent.getD j 0 + z * d.getD j 0
    let odd := (List.range half).map fun j ↦ even.getD j 0 + d.getD j 0
    [even, odd]

/-- **The row's cells** `v_c = w(t + ω_c)` from the fold values, the top variable folded first. -/
def cellsList (ω : ℕ → F) (w : List F) (r : ℕ) (a : List F) : List F :=
  ((List.range r).reverse.foldl (fun layer l ↦ foldLevel ω w l layer) [a]).map (·.getD 0 0)

/-- **`Ẑ_s(x)`**: `Ẑ_0(x) = x`, `Ẑ_{s+1}(x) = Ẑ_s(x) + c_{s+1} Ẑ_s(x)²`. -/
def zHat (c : List F) : ℕ → F → F
  | 0, x => x
  | s + 1, x => zHat c s x + c.getD s 0 * (zHat c s x * zHat c s x)

/-- **`vanishing(x, e, s)`**: `Z_{U_s}(x)` by `z ↦ z² + e_j z` for `j < s` (`pi2::circuit::vanishing`). -/
def vanishingF (x : F) (e : List F) (s : ℕ) : F :=
  (List.range s).foldl (fun z j ↦ z * z + e.getD j 0 * z) x

/-- **`coset_constants`**: `e_s = Z_{U_s}(b_s)` for `s < count`, `b` the subspace's basis (`β_{r+s}`). -/
def cosetConstantsF (b : ℕ → F) (count : ℕ) : List F :=
  (List.range count).foldl (fun e s ↦ e ++ [vanishingF (b s) e s]) []

/-- **`normalised_constants(e)`**: `c_s = Π_{j < s} e_j / e_s`. -/
def normalisedConstantsF (e : List F) : List F :=
  (e.foldl (fun (acc : List F × F) x ↦ (acc.1 ++ [acc.2 * x⁻¹], acc.2 * x)) ([], 1)).1

/-- **A sum of inverses as one fraction**: `Σ 1/x_i = N/D` by `N ← N x + D`, `D ← D x`, from `(1, x_0)`. -/
def fraction : List F → F × F
  | [] => (0, 1)
  | x :: xs => xs.foldl (fun nd y ↦ (nd.1 * y + nd.2, nd.2 * y)) (1, x)

/-- Each group's indicators' denominators `Ẑ_s(t) + Ẑ_s(c_p)`, `Ẑ_s(t)` read from `zt`. -/
def groupDens (S : CoreSpec F) (zt : List F) (g : GroupF F) : List F :=
  g.pairs.map fun p ↦ let q := S.pairs.getD p (0, 0); zt.getD q.1 0 + q.2

/-- `β ω_τ` along the walk: the first `β ω_τ`, each next the last one plus `β β_b` (`β_b = ω(2^b)`) for every bit `b`
in which the tags differ. -/
def betaTagNext (ω : ℕ → F) (β : F) (last : Option (ℕ × F)) (tag : ℕ) : F :=
  match last with
  | none => β * ω tag
  | some (lt, lv) => (List.range 28).foldl (fun acc b ↦
      if (lt ^^^ tag).testBit b then acc + β * ω (2 ^ b) else acc) lv

/-- **The public terms' denominators** `α + F_J + β ω_τ`, in the walk's order. -/
def walkDens (S : CoreSpec F) (gs pubs : List F) (α β : F) : List F :=
  (S.walk.foldl (fun (acc : List F × Option (ℕ × F)) j ↦
    let term := S.publicTerms.getD j (0, ⟨[], none⟩)
    let bt := betaTagNext S.ω β acc.2 term.1
    (acc.1 ++ [α + term.2.eval gs (fun c ↦ pubs.getD c 0) + bt], some (term.1, bt))) ([], none)).1

/-- `x` squared `i` times: `x^(2^i)`. -/
def sqIter (x : F) (i : ℕ) : F := (fun y ↦ y * y)^[i] x

/-- One step of `subspace_coefficients`: `s(Σ a_i X^(2^i)) = Σ a_i² X^(2^(i+1)) + Σ a_i X^(2^i)`. -/
def subspaceStep (a : List F) : List F :=
  (List.range (a.length + 1)).map fun i ↦
    (if i = 0 then 0 else a.getD (i - 1) 0 * a.getD (i - 1) 0) + a.getD i 0

/-- **`subspace_coefficients(k)`**: the coefficients `a_i` of `w_k = s^k = Σ_{i ≤ k} a_i X^(2^i)`, low first. -/
def subspaceCoeffsF (k : ℕ) : List F := (List.range k).foldl (fun a _ ↦ subspaceStep a) [1]

/-- `b_rest`: `[β^(2^k − 2^0), …, β^(2^k − 2^(k−1)), 1]`, `b_rest_i = b_rest_{i+1} · β^(2^i)` down from `i = k − 1`. -/
def bRestList (β : F) (k : ℕ) : List F :=
  (List.range k).reverse.foldl (fun acc i ↦
    (if i + 1 = k then sqIter β i else acc.headD 1 * sqIter β i) :: acc) [1]

/-- **The zero coset's sum in closed form** `(β^(2^k−1), F(Y))`, `Y = α + β ω_c`,
`F(Y) = Y^(2^k) + Σ_{i<k} a_i Y^(2^i) β^(2^k − 2^i)`. -/
def cosetSum (ω : ℕ → F) (α β : F) (tag k : ℕ) (a : List F) : F × F :=
  let y := α + β * ω tag
  let rest := bRestList β k
  ((rest.headD 1), (List.range k).foldl (fun f i ↦ f + a.getD i 0 * (sqIter y i * rest.getD i 1)) (sqIter y k))

/-- The public side's fraction: the walked terms' and the zero coset's, combined. -/
def publicSide (S : CoreSpec F) (gs pubs : List F) (α β : F) : Option (F × F) :=
  let side := if S.publicTerms.isEmpty then none else some (fraction (walkDens S gs pubs α β))
  let coset := S.zeroCoset.map fun (tag, k, a) ↦ cosetSum S.ω α β tag k a
  match side, coset with
  | some (n, d), some (nz, dz) => some (n * dz + d * nz, d * dz)
  | side, none => side
  | none, coset => coset

/-- **One group's step of the pushes' sum**: a group adds `N_g X/D_g` to `A/B` (`X = E_g(v_{c ⊕ k_g}) + v_0`; one
pair, `X/d`), and a pull-less group `N_g/D_g` to `S_n/S_d`. -/
def pushStep (gs cells : List F) (v0 : F) (acc : Option (F × F) × Option (F × F)) (gf : GroupF F × (F × F)) :
    Option (F × F) × Option (F × F) :=
  let g := gf.1
  let nd := gf.2
  let value := g.formula.eval gs (fun c ↦ cells.getD (c ^^^ g.role) 0) + v0
  let single := g.pairs.length = 1
  let term := if single then value else nd.1 * value
  let ab := match acc.1 with
    | some (a, b) => some (a * nd.2 + b * term, b * nd.2)
    | none => some (term, nd.2)
  let s := if g.pulls then acc.2 else match acc.2 with
    | some (a, b) => if single then some (a * nd.2 + b, b * nd.2) else some (a * nd.2 + b * nd.1, b * nd.2)
    | none => some (nd.1, nd.2)
  (ab, s)

/-- **The pushes' sum and the pull-less groups'** `(A, B, S_n, S_d)` (`pushStep` over the groups). -/
def pushSums (S : CoreSpec F) (gs cells : List F) (v0 : F) (fracs : List (F × F)) : F × F × F × F :=
  let r := (S.groups.zip fracs).foldl (pushStep gs cells v0) (none, none)
  ((r.1.map (·.1)).getD 0, (r.1.map (·.2)).getD 1, (r.2.map (·.1)).getD 0, (r.2.map (·.2)).getD 1)

/-- **Every value the arithmetic computes**, in the Rust's order. -/
structure Out (F : Type) where
  digits : List F
  cells : List F
  zt : List F
  groupFracs : List (F × F)
  publicDens : List F
  publicSide : Option (F × F)
  num : F
  den : F
  sNum : F
  sDen : F
  dPull : F
  dNum : F
  y : F
  x : F
  publicNum : F
  publicDen : F
  p1 : F
  p2 : F
  all : F
  invAll : F
  invP2 : F
  target : F
  invP1 : F
  invTop : F
  wInvs : List F
  rhoQ : F
  combination : F
  uList : List F
  digitsScale : F
  quotientValue : F
  rhos : List F
  fold : F
  witnessPoint : List F
  quotientPoint : List F
  sumPoint : List F
  sumValue : F
  setupPoint : List F

/-- `1/w_l = (1 + w_l)/w_{l+1}` down from `1/w_{m+2}`: the list `1/w_0, …, 1/w_{m+2}`. -/
def wInvsList (w : List F) (top : ℕ) (invTop : F) : List F :=
  (List.range top).reverse.foldl (fun acc l ↦ ((1 + w.getD l 0) * acc.headD 0) :: acc) [invTop]

/-- `W`'s fold at `(ρ, ρ², …)`: `fold_j ← fold_j + ρ^(2^l) (fold_j + fold_{j+half})`, the top variable first. -/
def foldW (rhos : List F) (r : ℕ) (a : List F) : F :=
  ((List.range r).reverse.foldl (fun cur l ↦
    (List.range (2 ^ l)).map fun j ↦ cur.getD j 0 + rhos.getD l 0 * (cur.getD j 0 + cur.getD (j + 2 ^ l) 0)) a).getD 0 0

/-- **The arithmetic** (`reduce` after the transcript). -/
def CoreSpec.run (S : CoreSpec F) (inp : Inputs F) : Out F :=
  let m := S.logN
  let r := S.logRow
  let t := inp.t
  let w := digitsList t (m + 3)
  let cells := cellsList S.ω w r inp.a
  let v0 := cells.getD 0 0
  let zt := (List.range (S.maxLogRows + 1)).map fun s ↦ zHat S.c s t
  let fracs := S.groups.map fun g ↦ fraction (groupDens S zt g)
  let gs := powersList inp.γ (S.maxGamma + 1)
  let dens := walkDens S gs inp.scalars inp.α inp.β
  let side := publicSide S gs inp.scalars inp.α inp.β
  let (num, den, sNum, sDen) := pushSums S gs cells v0 fracs
  let wm := w.getD m 0
  let wTop := w.getD (m + 2) 0
  let dPull := inp.α + v0 + inp.β * t
  let dNum := (inp.α + v0 + inp.ξ) * den + wm * num
  let y := dPull * dNum + wm * den
  let x := (sDen + wm * sNum) * dNum + dPull * den * sDen
  let publicNum := (side.map (·.1)).getD 0
  let publicDen := (side.map (·.2)).getD 1
  let p1 := sDen * y
  let p2 := p1 * wTop
  let all := p2 * publicDen
  let invAll := all⁻¹
  let invP2 := invAll * publicDen
  let target := publicNum * invAll * p2
  let invP1 := invP2 * wTop
  let invTop := invP2 * p1
  let wInvs := wInvsList w (m + 2) invTop
  let rhoQ := wm * den * sDen * invP1
  let combination := x * invP1
  let uList := (List.range (m + 2)).map fun l ↦ 1 + wInvs.getD l 0 + wInvs.getD (l + 1) 0
  let digitsScale := t * wInvs.getD (m + 2) 0
  let quotientValue := S.scale * digitsScale * combination
  let rhos := (List.range r).map fun l ↦ sqIter inp.ρ l
  { digits := w
    cells := cells
    zt := zt
    groupFracs := fracs
    publicDens := dens
    publicSide := side
    num := num
    den := den
    sNum := sNum
    sDen := sDen
    dPull := dPull
    dNum := dNum
    y := y
    x := x
    publicNum := publicNum
    publicDen := publicDen
    p1 := p1
    p2 := p2
    all := all
    invAll := invAll
    invP2 := invP2
    target := target
    invP1 := invP1
    invTop := invTop
    wInvs := wInvs
    rhoQ := rhoQ
    combination := combination
    uList := uList
    digitsScale := digitsScale
    quotientValue := quotientValue
    rhos := rhos
    fold := foldW rhos r inp.a
    witnessPoint := rhos ++ (w.drop r).take (m - r)
    quotientPoint := uList ++ [rhoQ, S.y0, S.y1]
    sumPoint := List.replicate m 1 ++ [0, 0, 0] ++ [S.y0, S.y1]
    sumValue := S.scale * target
    setupPoint := w.take m ++ [inp.β] }

end RecStatement
