-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Setup.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.PublicWeight
import QuotientSecurity.Distance

/-!
# The setting of the statements

The definitions `Statement.lean` is written on: the circuit, the relation, what a proof is, and
the two experiments of zero knowledge. Three things carry the meaning of the theorems and are
defined elsewhere, where they should be read:

* what the verifier checks: `Params.Accepts` (`Protocol.lean`), run against the oracle by
  `verify` and `experiment` (`RandomOracle.lean`);
* the honest prover: `realNI`, `proverRO`, `viewAt` (`NonInteractive.lean`), on the masked
  polynomials `committed` (`Simulation.lean`);
* the simulator: `simNI` (`NonInteractive.lean`), which draws its values with `simValues`
  (`ZeroKnowledge.lean`) and reads the statement, the oracle's state and public polynomials.
-/

open OracleSpec OracleComp Polynomial

namespace QuotientSecurity

/-- **A circuit**: `2^22` rows of four cells, a cell being named by 24 bits. Its points are the
span of a Cantor basis, `wiring` says which cells must be equal, and `c k` is the weight that bit
`k < 8` of a cell's index gives it in a public word. `soundness`, `zero_knowledge` and
`completeness` hold for every circuit, and mean what the circuit makes them mean: with the
identity wiring and zero weights, every statement has a satisfying assignment.
`soundness_circuit` is for an instance whose wiring lays a loop-free χ circuit `C` (`Laid`,
`CircuitLayout.lean`) and whose weights are `coordinate_weight`'s (`c = coordWeight x Y`); that
`C` is `quotient::circuit::membership` is not yet in Lean. -/
structure Instance (F : Type) [Field F] [CharP F 2] where
  basis : CantorBasis F (22 + 2)
  wiring : Equiv.Perm (Fin (22 + 2) → Bool)
  c : ℕ → F

namespace Instance

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] (I : Instance F)

/-- The protocol's parameters on this circuit: the cells, the polynomials the verifier
evaluates, the public words. -/
noncomputable def params : Params F :=
  membershipParams I.basis le24 I.wiring (invSeq I.basis.β) I.c (invSeq_zero _)
    fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd

/-- The degrees a proof's polynomials may have: the sizes of the tables they are committed in. -/
noncomputable def bounds : I.params.Bounds :=
  membershipBounds I.basis le24 I.wiring (invSeq I.basis.β) I.c (invSeq_zero _)
    fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd

/-- **The relation**, on an assignment `w` of a field element to every cell. `cellBits (y, r)` is
the cell of row `y` with role `r` (`X`, `Y`, `C`, `V`): bits 0 and 1 of a cell are its role, the
other twenty-two its row.

1. Every row satisfies the gate `V + X + C + Y·C = 0`: on bits it says the `V` cell holds
   `X ⊕ (C ∧ ¬Y)`, Keccak's χ.
2. Cells wired together are equal.
3. Each public word is the weighted sum of its cells: word `J` reads the cells whose bits 8 to
   10 spell `J` and whose bits from 11 on are zero, each with the product of `c k` over its set
   bits `k < 8`.

The cells are arbitrary field elements, and the relation alone does not make them bits: with the
identity wiring and zero weights every statement satisfies it (`formal/Review/Degenerate.lean`).
What makes them a computation is the circuit the wiring lays (`Pinning.lean`). For an instance
whose wiring lays a loop-free χ circuit `C` (`Laid`: every `X`, `Y`, `C` cell on the cycle of
what it reads, public word 5's 128 bits on the zero's cycle, word 4's bit 0 the one's anchor and
its other bits on the zero's cycle) and whose weights are `coordinate_weight`'s with `x ≠ 1`,
`Y ≠ 1`, and a statement whose words 4 and 5 are 1 and 0: word 5 pins the zero's cycle to 0
(`zero_pinned`), then word 4 pins the one's cycle to 1 (`one_pinned`), `cells_determined`
(carried to an instance's cells by `Instance.cells_determined`) makes every output a bit, and a
satisfying assignment is `C`'s computation on some input bits whose public words are the
statement's (`Instance.proves_of_relation`). For the statement `(y, root)`, whose words are
`statementWords` (its four halves, then `1, 0, 0, 0`), `soundness_circuit` and
`soundness_circuit_bits` are the end theorems that say so. Conversely, on `wiringOf C` every
computation of `C` satisfies the relation for its public words (`relation_wiringOf`,
`relation_statementWords`). The deployed circuit as a Lean `C`, and its computation being
Keccak-256 membership, are not yet in Lean (layer F0 of `formal/README.md`). -/
def Relation (stmt : Fin 8 → F) (w : (Fin (22 + 2) → Bool) → F) : Prop :=
  (∀ y : Fin 22 → Bool, gate (w (cellBits (y, 0))) (w (cellBits (y, 1)))
      (w (cellBits (y, 2))) (w (cellBits (y, 3))) = 0) ∧
    (∀ x, w (I.wiring x) = w x) ∧
    ∀ J : Fin 8, ∑ x, regionWeight I.c J x * w x = stmt J

/-- The witness polynomial of a first message `g`: `sum_j X_j * g_j(X^4 + X)`, on the basis
`X_j = 1, X, X^2 + X, X^3 + X^2`. -/
noncomputable def witnessPoly (g : Fin 4 → F[X]) : F[X] := ∑ j, digit j * (g j).comp rowPoly

/-- **The cells a first message holds**: its witness polynomial at each cell's point. -/
noncomputable def cellsOf (g : Fin 4 → F[X]) (x : Fin (22 + 2) → Bool) : F :=
  (witnessPoly g).eval (I.basis.point x)

/-! ## Soundness: proofs and adversaries

The commitment is ideal and binding: a proof carries its polynomials, and the random oracle is
asked about them directly. -/

/-- **A statement with a proof of it.** `stmt`: eight words. `g`: the first message, four
polynomials of degree at most `2^23`. `R`: the second, five polynomials of degree at most
`2^26`: the sum's polynomial in two parts, the two quotients, and a fifth that shares their
table and that an honest prover leaves zero. `v`: five field elements. These degrees are what
the tables can hold, rounded up. -/
abbrev Proof := QuotientSecurity.Proof I.params I.bounds

/-- **An adversary**: any computation, deterministic given the oracle's answers, that asks the
random oracle and outputs a statement with a proof. -/
abbrev Adversary := OracleComp (ofFn (Answer I.params I.bounds)) I.Proof

/-! ## Zero knowledge: the two experiments

The commitment is ideal and its openings reveal nothing: a commitment is a handle drawn at
random in `H`, and of the four claims the experiments output only whether they are true. -/

section Experiments

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
variable [Fintype K] [DecidableEq K] [FiniteDimensional K E]
variable [SampleableType K] [SampleableType E] {H : Type} [SampleableType H]
variable (I : Instance E)

variable (H) in
/-- The oracle's table: what it has answered so far. -/
abbrev Table := (ofFn (ZAnswer I.params H)).QueryCache

variable (H) in
/-- **What an experiment outputs**: the two handles, the five field elements, the verdict, the
three challenges, and the oracle's table afterwards. -/
abbrev View := Outcome (E := E) H × I.Table H

/-- The cells of a witness given by four polynomials over `K`. -/
noncomputable def witnessCells (gK : Fin 4 → K[X]) : (Fin (22 + 2) → Bool) → E :=
  I.cellsOf fun j => (gK j).map (algebraMap K E)

/-- **The real experiment**: the honest prover on the witness `gK`, each polynomial masked by
three random coefficients, against the random oracle in the state `c₀`. -/
noncomputable def real (c₀ : I.Table H) (stmt : Fin 8 → E) (gK : Fin 4 → K[X]) :
    ProbComp (I.View H) :=
  realNI c₀ stmt gK (digitPoly 22)

variable (K) in
/-- **The simulator**: given the statement and the oracle's state, and no witness. It is `simNI`,
which draws the handles, the challenges and four values, and writes its challenges in the
oracle's table. -/
noncomputable def sim (c₀ : I.Table H) (stmt : Fin 8 → E) : ProbComp (I.View H) :=
  simNI (K := K) c₀ stmt

end Experiments

end Instance

end QuotientSecurity
