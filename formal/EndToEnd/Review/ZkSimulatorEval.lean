-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.ComputableClosed

/-!
# Running the compiled simulator's parts

`lake env lean Review/ZkSimulatorEval.lean` (from `formal/EndToEnd`): `#eval` interprets the compiled
definitions of `ZK/Computable*.lean` and `QuotientZk/Instance/Compiled.lean` on `F64 ⊂ F192`.

* **The simulator is a compiled function**: `zkSimulatorClosed` has the type the Statement's
  `ZeroKnowledgeWith` takes, and is not `noncomputable`.
* **The novel basis** (`subRoots`, `subWAt`, `encOf`): `W_k` vanishes on the words `K(q)`, `q < 2^k`,
  and is `Π_{q < 2^k} (x + K(q))` (checked against the product for `k ≤ 8`, so the recurrence is the
  subspace polynomial); an entry `X_y(K(p))` of the encoding is the product of its bits' `Ŵ_k`.
* **The barycentric accumulation** (`lagAcc`, the route of `sigmaAtC`), on the cube of `m = 6` bits
  of the deployed basis (`64` cells): at a cell it returns the value given there; and an interpolant
  of degree `< 64` is reproduced at a point off the cells.
* **The public evaluations** (`pubAtC`, `θ`, `v_cells`) at a sample challenge; the witness claim's
  bytes `claimMsgP … 5` (`25` coordinates and the value, `24` bytes each).

The deployed `σ(t)` (`sigmaAtC`, `3·2^24` products) is run by `Review/ZkSigmaEval.lean` (about an
hour interpreted, `0.25` ms a cell, after `27` s building the circuit): at a cell it is the point of the
cell's successor. The simulator's view (up to about `2·10^14` operations, `ZK/Computable.lean`) is not
run.
-/

open QuotientSecurity QuotientSecurity.Hiding QuotientZk.Instance QuotientZk.Instance.Compiled
open PcsQuotient.EndToEnd Primitives LeanVM.Parameters

namespace PcsQuotient.EndToEnd.Eval

/-- An element of `E` by its limbs. -/
def showE (x : E) : String :=
  s!"({(F192.limb x 0).toU64}, {(F192.limb x 1).toU64}, {(F192.limb x 2).toU64})"

/-- The simulator is a compiled function of the Statement's type. -/
def simulatorClosed : Statement → StateT RpmSimState ProbComp (Option Proof) :=
  zkSimulatorClosed

/-! ## The novel basis -/

/-- `K(q)`. -/
def wK (q : ℕ) : K := deployedRep.w.word q

/-- The normalizers for `ℓ = 22`. -/
def roots22 : Array K := subRoots deployedRep.w.v 22

/-- `W_k(x)` as the product over its subspace. -/
def subNaive (k : ℕ) (x : K) : K := ((List.range (2 ^ k)).map fun q => x + wK q).prod

/-- `W_k` vanishes on `K(q)`, `q < 2^k`, and is the subspace product, `k ≤ 8`, at three points. -/
def checkSub : Bool :=
  (List.range 9).all fun k =>
    ((List.range (2 ^ k)).all fun q => subWAt roots22 k (wK q) == 0) &&
      ([12345, 987654321, 0xdeadbeefcafe].all fun x =>
        subWAt roots22 k (wK x) == subNaive k (wK x))

/-- An entry of the encoding is the product of its bits' normalized subspace polynomials. -/
def checkEnc : Bool :=
  let tab := encTab deployedRep.w roots22 22 [3, 77, 4000000]
  let e : Fin 3 → Fin (2 ^ 22) → K := encOf tab 22
  let y : Fin (2 ^ 22) := ⟨0b1011001, by norm_num⟩
  let direct := ((List.range 22).filter fun k => (0b1011001 : ℕ).testBit k).foldl
    (fun a k => a * ((roots22.getD k 0)⁻¹ * subWAt roots22 k (wK 77))) 1
  e ⟨1, by norm_num⟩ y == direct && e ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ == 1

/-! ## The barycentric accumulation on a small cube -/

/-- The cells of `m = 6` bits of the deployed basis, in `E`. -/
def node6 (p : ℕ) : E := algebraMap K E (deployedBasis.point (bitsN 6 p))

/-- Values at the cells: a polynomial of degree `< 64` evaluated there (`f(x) = x^63 + Y x^5 + 7`). -/
def f6 (x : E) : E := x ^ 63 + F192.Y * x ^ 5 + 7

def checkLag : Bool :=
  let r := fun p => f6 (node6 p)
  let t := F192.new 0x1234 0x5678 0x9abc
  (lagAcc (node6 17) node6 r 64).1 == r 17 && (lagAcc t node6 r 64).1 == f6 t

/-! ## The public evaluations and a claim -/

/-- A sample challenge: `α, β, γ, t, ρ`, the rest zero. -/
def chal : DChal E :=
  ((((F192.new 3 5 7, F192.new 11 13 17, F192.new 19 23 29),
      F192.new 0x9e3779b97f4a7c15 0x6a09e667f3bcc908 0xbb67ae8584caa73b),
      F192.new 0x3c6ef372fe94f82b 0xa54ff53a5f1d36f1 0x510e527fade682d1),
    ((0, fun _ => default), fun _ => 0), ((0, fun _ => default), fun _ => 0), fun _ => default)

def vals : Vals E := (![F192.new 1 2 3, F192.new 4 5 6, F192.new 7 8 9, F192.new 10 11 12],
  F192.new 13 14 15)

def evalPublic : String :=
  let t := chal.1.1.2
  let γ := chal.1.1.1.2.2
  s!"θ = {showE peD.θ}; v_cells(t) = {showE (peD.vCells t)}; pub(γ)(t) = {showE (pubAtC γ t)}; \
    claim bytes at step 5: {match claimMsgP deployedRep peD (tgtD ⟨Vector.replicate 32 1, Vector.replicate 32 2⟩) F192.Y 5 chal vals with
      | [.bytes b] => b.length | _ => 0}"

end PcsQuotient.EndToEnd.Eval

open PcsQuotient.EndToEnd.Eval in
#eval checkSub

open PcsQuotient.EndToEnd.Eval in
#eval checkEnc

open PcsQuotient.EndToEnd.Eval in
#eval checkLag

open PcsQuotient.EndToEnd.Eval in
#eval evalPublic
