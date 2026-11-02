-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribes `quotient::protocol::reduce` (crates/quotient/src/protocol.rs) and the smart constructors of
-- `crates/evm/src/record.rs` (`Sym`'s `Add`, `Mul`, `frobenius`), adapted from leanVM
-- (https://github.com/leanEthereum/leanVM, branch PCS-openings-aggregation, commit 651453c6).
import Implementation.Interp

/-!
# The reduction, read off the graph

`quotient::protocol::reduce` again, over node indices: every operation the Rust verifier does on
its scalars is looked up in the emitted graph (`look`), after the folds `record.rs`'s `Sym` does on
constants (`add`, `mul`, `frob`). The program is `reduceIds`; `reduceIds_eq` checks, by evaluation
in the kernel, that it finds every node it asks for, that the words it gives are `outputs`, and
that the value it requires nonzero is `nonzero`'s. So the graph holds the Rust verifier's
computation in the order of `reduce`, and `Semantics.lean` can read its values off this program.

Nothing here is trusted: a node the program asks for and the graph lacks makes `reduceIds` `none`
and `reduceIds_eq` fail.
-/

namespace Implementation.Program

open Emitted

/-! ## Looking up nodes -/

/-- The first index, from `i` on, of a node in a list. -/
def findFrom (n : Node) : List Node → Nat → Option Nat
  | [], _ => none
  | m :: l, i => if m = n then some i else findFrom n l (i + 1)

/-- The index of a node in the graph. -/
def look (n : Node) : Option Nat := findFrom n nodes 0

/-- The constant at an index, if that node is one. -/
def constAt (i : Nat) : Option Nat :=
  match nodes[i]? with
  | some (.const c) => some c
  | _ => none

/-- `S::constant`. -/
def cnst (c : Nat) : Option Nat := look (.const c)

/-- `Sym + Sym`: two constants fold, zero is dropped, `x + x` is zero. -/
def add (a b : Nat) : Option Nat :=
  match constAt a, constAt b with
  | some x, some y => cnst (x ^^^ y)
  | _, _ =>
    if constAt a = some 0 then some b
    else if constAt b = some 0 then some a
    else if a = b then cnst 0
    else look (.add (min a b) (max a b))

/-- `Sym * Sym`: two constants fold, zero absorbs, one is dropped. -/
def mul (a b : Nat) : Option Nat :=
  match constAt a, constAt b with
  | some x, some y => cnst (mulE x y)
  | _, _ =>
    if constAt a = some 0 ∨ constAt b = some 0 then cnst 0
    else if constAt a = some 1 then some b
    else if constAt b = some 1 then some a
    else look (.mul (min a b) (max a b))

/-- `Sym::frobenius`. -/
def frob (a : Nat) : Option Nat :=
  match constAt a with
  | some x => cnst (frobE x)
  | none => look (.frob a)

/-! ## The transcript (`contract::Recorder`) -/

/-- The leaves: the seed, the statement's halves, the roots' scalars, the challenges and the five
values, as `reduce` reads them. -/
structure Leaves where
  one : Nat
  s : List Nat
  alpha : Nat
  beta : Nat
  gamma : Nat
  t : Nat
  a : List Nat
  next : Nat
  rho : Nat
  deriving Repr, DecidableEq

/-- The transcript as the recorder writes it: the witness root's two scalars, three challenges,
the quotient root's, `t`, the five values, `ρ`. -/
def chain : Option Leaves := do
  let seed ← look .seed
  let one ← cnst 1
  let s ← [0, 1, 2, 3].mapM fun k => look (.statement k)
  let r0 ← look (.root 0)
  let r1 ← look (.root 1)
  let st1 ← look (.hash seed [r0, r1])
  let alpha ← look (.low st1)
  let st2 ← look (.hash st1 [])
  let beta ← look (.low st2)
  let st3 ← look (.hash st2 [])
  let gamma ← look (.low st3)
  let q0 ← look (.root 2)
  let q1 ← look (.root 3)
  let st4 ← look (.hash st3 [q0, q1])
  let t ← look (.low st4)
  let a ← [0, 1, 2, 3].mapM fun i => look (.input i)
  let next ← look (.input 4)
  let st5 ← look (.hash st4 (a ++ [next]))
  let rho ← look (.low st5)
  pure { one, s, alpha, beta, gamma, t, a, next, rho }

/-! ## The arithmetic of `reduce` -/

/-- `w_0 .. w_n`: `w_{k+1} = w_k^2 + w_k`. -/
def wChain (t : Nat) : Nat → Option (List Nat)
  | 0 => some [t]
  | n + 1 => do
    let ws ← wChain t n
    let w := ws.getLastD 0
    let sq ← mul w w
    let w' ← add sq w
    pure (ws ++ [w'])

/-- A fold of `reduce`, over a list of indices. -/
def foldO (f : Nat → Nat → Option Nat) : Nat → List Nat → Option Nat
  | acc, [] => some acc
  | acc, k :: ks => do
    let acc' ← f acc k
    foldO f acc' ks

/-- A map of `reduce`, over a list of indices. -/
def mapO (f : Nat → Option Nat) : List Nat → Option (List Nat)
  | [] => some []
  | k :: ks => do
    let r ← f k
    let rs ← mapO f ks
    pure (r :: rs)

/-- `x^(2^n)`, by `n` squarings. -/
def squareN (x : Nat) : Nat → Option Nat
  | 0 => some x
  | n + 1 => do
    let y ← squareN x n
    mul y y

/-- One round of `inverse`'s loop: `ones = norm^(2^k - 1)` becomes `norm^(2^(2k+1) - 1)`. -/
def invRound (norm : Nat) (p : Nat × Nat) : Option (Nat × Nat) := do
  let shifted ← squareN p.1 p.2
  let ones ← mul shifted p.1
  let sq ← mul ones ones
  let ones' ← mul sq norm
  pure (ones', 2 * p.2 + 1)

/-- Five rounds. -/
def invRounds (norm : Nat) : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, p => some p
  | n + 1, p => do
    let q ← invRound norm p
    invRounds norm n q

/-- `protocol::inverse`: `x^-1 = m · N(x)^(2^64 - 2)`, `m = x^(2^64) x^(2^128)`, `N(x) = x m`. -/
def inverse (x : Nat) : Option Nat := do
  let f1 ← frob x
  let f2 ← frob f1
  let m ← mul f1 f2
  let norm ← mul x m
  let p ← invRounds norm 5 (norm, 1)
  let sq ← mul p.1 p.1
  mul m sq

/-- The prefix products: `prefix[i]` the product of the first `i` values. -/
def prefixes : Nat → List Nat → Option (List Nat)
  | acc, [] => some [acc]
  | acc, d :: ds => do
    let acc' ← mul acc d
    let rest ← prefixes acc' ds
    pure (acc :: rest)

/-- The inverses, from the last: `inverses[i] = running · prefix[i]`, then `running ·= d_i`. The
pairs `(prefix[i], d_i)` come last first; the result too. -/
def backInv : Nat → List (Nat × Nat) → Option (List Nat)
  | _, [] => some []
  | running, (p, d) :: rest => do
    let inv ← mul running p
    let running' ← mul running d
    let tail ← backInv running' rest
    pure (inv :: tail)

/-- `w_1 + 1` for the cells of the second half of a row, `w_1` for the first. -/
def secondOf (w1 one : Nat) (second : Bool) : Option Nat := if second then add w1 one else some w1

/-- `cell(shift, second)`: `a_0 + (t + shift) a_1 + w_1' (a_2 + (t + shift) a_3)`. -/
def cell (L : Leaves) (w1 : Nat) (shift : Nat) (second : Bool) : Option Nat := do
  let sh ← cnst shift
  let first ← add L.t sh
  let snd ← secondOf w1 L.one second
  let m1 ← mul first (L.a.getD 1 0)
  let s1 ← add (L.a.getD 0 0) m1
  let m3 ← mul first (L.a.getD 3 0)
  let s3 ← add (L.a.getD 2 0) m3
  let m2 ← mul snd s3
  add s1 m2

/-- The constant that weighs coordinate `k < 8` of the public region, plus one
(`1 + coordinate_weight(k)`): bit weights `x^1`, `0`, `x^2`, `x^4`, …, `x^32`, `y`. -/
def slopeConst (k : Nat) : Nat :=
  1 ^^^ (if k = 0 then 2 else if k = 1 then 0 else if k < 7 then 2 ^ (2 ^ (k - 1)) else B64)

/-- The slope of coordinate `k`: the constant `1 + coordinate_weight(k)` below 8, then
`1 + γ^(2^(k - 8))`. -/
def slopeOf (one : Nat) (gammas : List Nat) (k : Nat) : Option Nat :=
  if k < 8 then cnst (slopeConst k) else add one (gammas.getD (k - 8) 0)

/-- What `reduce` leaves, as indices: the claims' points then values, the sum's value, and the
product it requires nonzero. -/
structure Out where
  witness : List Nat
  wiring : List Nat
  quotient : List Nat
  sum : Nat
  check : Nat
  deriving Repr, DecidableEq

/-- **`reduce`, over the graph.** -/
def reduceIds : Option Out := do
  let L ← chain
  let m := 24
  let one := L.one
  let t := L.t
  let w ← wChain t (m + 1)
  let w1 := w.getD 1 0
  let theta := beta.getD 1 0
  let c0 ← cell L w1 0 false
  let c1 ← cell L w1 1 false
  let c2 ← cell L w1 theta true
  let c3 ← cell L w1 (theta ^^^ 1) true
  let x := c0
  -- `gate([x, y, c, v]) = v + x + c + y · c`
  let g1 ← add c3 c0
  let g2 ← add g1 c2
  let g3 ← mul c1 c2
  let gate ← add g2 g3
  -- the public weight
  let gamma := L.gamma
  let gamma2 ← mul gamma gamma
  let gamma4 ← mul gamma2 gamma2
  let gammas := [gamma, gamma2, gamma4]
  let pub0 ← foldO (fun acc k => do
      let o ← add one (w.getD k 0)
      mul acc o) one (List.range' 11 (m - 11))
  let pubW ← foldO (fun acc k => do
      let coordinate ← foldO (fun acc' j => do
          let bc ← cnst (coords.getD (j - k) 0)
          let p ← mul bc (w.getD j 0)
          add acc' p) (w.getD k 0) (List.range' (k + 1) (11 - (k + 1)))
      let slope ← slopeOf one gammas k
      let cs ← mul coordinate slope
      let o ← add one cs
      mul acc o) pub0 (List.range 11)
  -- the target
  let s := L.s
  let tg1 ← mul gamma (s.getD 1 0)
  let tg2 ← add (s.getD 0 0) tg1
  let tg3 ← mul gamma (s.getD 3 0)
  let tg4 ← add (s.getD 2 0) tg3
  let tg5 ← mul gamma2 tg4
  let tg6 ← add tg2 tg5
  let target ← add tg6 gamma4
  -- the rows' polynomial
  let zr ← cnst 0
  let rows ← foldO (fun acc k => do
      let tk ← cnst (tau.getD k 0)
      let p ← mul tk (w.getD k 0)
      add acc p) zr (List.range (m - 1))
  -- the copy identity
  let ax ← add L.alpha x
  let bt ← mul L.beta t
  let d ← add ax bt
  let bn ← mul L.beta L.next
  let dNext ← add ax bn
  let product ← mul d dNext
  let dd ← add d dNext
  let px ← mul pubW x
  let pxp ← mul px product
  let copies ← add dd pxp
  -- one inversion
  let ws ← mapO (fun k => add one (w.getD k 0)) (List.range (m + 2))
  let cw ← add product (w.getD m 0)
  let dens := ws ++ [cw, rows]
  let pre ← prefixes one dens
  let total := pre.getD dens.length 0
  let running ← inverse total
  let invsRev ← backInv running ((List.range dens.length).reverse.map fun i => (pre.getD i 0, dens.getD i 0))
  let inverses := invsRev.reverse
  let u ← mapO (fun k => mul (w.getD k 0) (inverses.getD k 0)) (List.range (m + 2))
  let copyInverse := inverses.getD (m + 2) 0
  let rowsInverse := inverses.getD (m + 3) 0
  let middle ← foldO (fun acc k => mul acc (inverses.getD k 0)) (inverses.getD 2 0) (List.range' 3 (m - 3))
  let ws0 ← mul middle (inverses.getD 0 0)
  let wiringScale ← mul ws0 (inverses.getD 1 0)
  let qs0 ← mul wiringScale (inverses.getD m 0)
  let quotientScale ← mul qs0 (inverses.getD (m + 1) 0)
  -- the claims
  let rho := L.rho
  let a := L.a
  let rho2 ← mul rho rho
  let o1 ← add one rho2
  let o2 ← add (a.getD 0 0) (a.getD 1 0)
  let o3 ← mul rho o2
  let o4 ← add (a.getD 0 0) o3
  let o5 ← mul o1 o4
  let o6 ← add (a.getD 2 0) (a.getD 3 0)
  let o7 ← mul rho o6
  let o8 ← add (a.getD 2 0) o7
  let o9 ← mul rho2 o8
  let opened ← add o5 o9
  let sc ← cnst Emitted.scale
  let i1 ← add one rho
  let i2 ← mul i1 copies
  let i3 ← mul i2 rows
  let i4 ← mul rho product
  let i5 ← mul i4 gate
  let identities ← add i3 i5
  let wv0 ← mul opened middle
  let witnessValue ← mul wv0 (inverses.getD m 0)
  let wiringValue ← mul L.next wiringScale
  let wmc ← mul (w.getD m 0) copyInverse
  let cy0 ← cnst y0
  let cy1 ← cnst y1
  let qv0 ← mul sc quotientScale
  let qv1 ← mul qv0 copyInverse
  let qv2 ← mul qv1 rowsInverse
  let quotientValue ← mul qv2 identities
  let sum ← mul sc target
  pure {
    witness := [rho, rho2] ++ (u.drop 2).take (m - 1) ++ [witnessValue]
    wiring := u.take m ++ [wiringValue]
    quotient := u ++ [wmc, rho, cy0, cy1, quotientValue]
    sum
    check := total }

/-- The fixed point of the sum's claim (`protocol::sum_point`), as words: `[1; 24]`, `[0; 4]`, then
`y0`, `y1`. -/
def sumPointWords : List Nat := List.replicate 24 1 ++ List.replicate 4 0 ++ [y0, y1]

/-- The words the contract writes for its calls, from what `reduce` leaves (`quotient::build`):
for each call, the root, the layout's id (`256 · table + log_rows`), the number of claims, then
the claims. -/
def wordsOf (o : Out) : List Word :=
  [.calldata 64, .const (256 * 1 + 22), .const 1] ++ o.witness.map .node ++
    [.storedRoot, .const (256 * 2 + 22), .const 1] ++ o.wiring.map .node ++
    [.calldata 96, .const (256 * 3 + 22), .const 2] ++ o.quotient.map .node ++
    sumPointWords.map .const ++ [.node o.sum]

/-- **The graph is `reduce`'s**: every node the program asks for is in the graph, the program
gives the words the contract writes, and the value it requires nonzero is the product of the
denominators. -/
theorem reduceIds_eq : (reduceIds.map fun o => (wordsOf o, [o.check])) = some (outputs, nonzero) := by
  decide +kernel

end Implementation.Program
