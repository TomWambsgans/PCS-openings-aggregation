-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The WHIR prover's arrays (`stackTableA`, `foldPairsW`, `roundC0A`, `roundC2A`, `stackWordFast`) are
-- leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Whir.lean`,
-- `Statement/Prover/Ntt.lean`).
import ZK.CoreDefs
import E2ECompleteness.Staging

/-!
# The deployed core's parts

`CoreD` (`ZK/CoreDefs.lean`) splits into statements about the two tables and the openings' views,
each a fact about functions (no permutation, no run):

* **the stacks** (`StackW`, `StackQ`): the joint model's stack of a secret table (`stackD` of the
  honest table `TWD`, `TQD` plus `stackR` of the model's padding) is, lane `l` entry `y`, the
  statement's stack array (`witnessStack`, `quotientStack` at the coins `decodeCoins (eD s)`) at
  `l · 2^ℓ + y`; the quotient's off the degenerate `α, β`;
* **the codewords** (`CodeW`, `CodeQ`): the model's row at a position (the novel basis at the point
  `F64(p)`, `codeAt`, against each lane) is, as a 64-word leaf image (`leafWords`), the statement's
  WHIR word at that position (`stackWordFast`);
* **the leaf bytes** (`RowBytes`): `rowBytes` is the leaf image's words, little-endian;
* **the lane rounds and the folded table** (`ViewW`, `ViewQ`): the joint view's first six round
  messages and its `f¹` are mumbai's round messages (`roundC0A`, `roundC2A`) of the statement's weight
  table (`weightTable` at the batching powers) and stack table (`stackTableA`), folded by the view's
  `φ` (`foldsA`), and mumbai's table after the six folds.
-/

open Polynomial QuotientSecurity QuotientSecurity.Hiding
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient.Domain
open QuotientZk.Joint QuotientZk.Instance
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## The statement's tables -/

/-- The witness table's coefficients (`proveWith`'s `wHat`). -/
noncomputable def wHatD (w : Secret) : Array K :=
  coefficients (cellVars logRows) 0 (E2ECompleteness.cellsOf w)

/-- **The statement's witness stack** at the coins `c`. -/
noncomputable def wStackD (w : Secret) (c : Masks × Padding × Padding) : Array K :=
  witnessStack logRows (wHatD w) (maskEntries c.1) c.2.1

/-- **The statement's quotient stack** at the coins `c` and the challenges `α, β, γ`
(`E2ECompleteness.quotientStackOf`, `proveWith`'s, `quotientStackOf_eq`). -/
noncomputable def qStackD (w : Secret) (c : Masks × Padding × Padding) (abc : E × E × E) :
    Array K :=
  E2ECompleteness.quotientStackOf (membership logRows) (E2ECompleteness.cellsOf w) c.2.2 (wHatD w)
    (maskEntries c.1) abc.1 abc.2.1 abc.2.2

/-- The joint model's witness stack. -/
noncomputable def stackWm (w : Secret) (s : RandD K) : ιW → YW → K :=
  (Lw.toGadget okW).stackD (TWD w s.1) + (Lw.toGadget okW).stackR s.2.1

/-- The joint model's quotient stack at `α, β, γ`. -/
noncomputable def stackQm (w : Secret) (abc : E × E × E) (s : RandD K) : ιQ → YQ → K :=
  (Lq.toGadget okQ).stackD (TQD w abc s.1) + (Lq.toGadget okQ).stackR s.2.2

/-! ## The tables -/

/-- **The witness stacks agree**: lane `l`, entry `y` is the array's entry `l · 2^19 + y`. -/
def StackW : Prop :=
  ∀ (w : Secret) (s : RandD K) (l : ιW) (y : YW),
    stackWm w s l y = (wStackD w (decodeCoins (eD s))).getD ((l : ℕ) * 2 ^ 19 + y) 0

/-- **The quotient stacks agree**, for a witness of the relation, off the degenerate `α, β`. -/
def StackQ : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w → ∀ (s : RandD K) (abc : E × E × E),
    ¬ BadABD w s.1 (abc.1, abc.2.1) → ∀ (l : ιQ) (y : YQ),
      stackQm w abc s l y = (qStackD w (decodeCoins (eD s)) abc).getD ((l : ℕ) * 2 ^ 22 + y) 0

/-! ## The codewords -/

/-- **The witness codeword's rows**: for a stack `T` read off the array `A` (`40` lanes of `2^19`),
the model's row at `p < 2^20`, as the leaf image, is the WHIR word's row. -/
def CodeW : Prop :=
  ∀ (T : ιW → YW → K) (A : Array K), (∀ l y, T l y = A.getD ((l : ℕ) * 2 ^ 19 + y) 0) →
    A.size = 40 * 2 ^ 19 → ∀ p < 2 ^ 20,
      Render.leafWords (QuotientZk.Deployed.rowAt (codeAt deployedRep Lw.logLane p) T) =
        stackWordFast 25 1 A p

/-- **The quotient codeword's rows** (`63` lanes of `2^22`, positions below `2^23`). -/
def CodeQ : Prop :=
  ∀ (T : ιQ → YQ → K) (A : Array K), (∀ l y, T l y = A.getD ((l : ℕ) * 2 ^ 22 + y) 0) →
    A.size = 63 * 2 ^ 22 → ∀ p < 2 ^ 23,
      Render.leafWords (QuotientZk.Deployed.rowAt (codeAt deployedRep Lq.logLane p) T) =
        stackWordFast 28 1 A p

/-- **A leaf's bytes are its image's words**, little-endian. -/
def RowBytes : Prop :=
  ∀ {n : ℕ} (row : Fin n → K), n ≤ 64 → rowBytes deployedRep row = (Render.leafWords row).flatMap kBytes

/-! ## The lane rounds and the folded table -/

/-- `j` folds of a table (`foldPairsW`), the challenges in order. -/
def foldsA (φs : List E) (A : Array E) : Array E := φs.foldl (fun A r ↦ foldPairsW r A) A

/-- **Mumbai's round message** of the weight table `W` and the table `f` after the folds `φs`. -/
def roundMsgArr (W f : Array E) (φs : List E) : E × E :=
  (roundC0A (foldsA φs W) (foldsA φs f), roundC2A (foldsA φs W) (foldsA φs f))

/-- **The witness opening's level-0 view is mumbai's arrays'**: for a stack `T` read off the array
`A`, the joint view's lane round `j < 6` is the round message of the statement's weight table (the
claim at `pointW c` and the gadget, batched by the powers of `λ`) and stack table after the first `j`
folds, and its `f¹` is the stack table after the six. -/
def ViewW : Prop :=
  ∀ (c : DChal E) (T : ιW → YW → K) (A : Array K), (∀ l y, T l y = A.getD ((l : ℕ) * 2 ^ 19 + y) 0) →
    A.size = 40 * 2 ^ 19 → ∀ (v : E) {Q : Type} [Fintype Q] [DecidableEq Q] (enc : Q → YW → K),
    let lv := Gadget.levelMap (Lw.toGadget okW) Lw.pos (Lw.claimW fun _ => pointW c)
      ![1, F192.Y, F192.Y ^ 2] (Gadget.powers 1 (lam₁ c)) (phi₁ c) enc T
    let W₀ := weightTable (witnessLayout logRows) (powers (lam₁ c) 2) [⟨pointW c, v⟩]
    let f₀ := stackTableA 25 A
    (∀ j : Fin 6, lv.1 j = roundMsgArr W₀ f₀ ((List.ofFn (phi₁ c)).take j)) ∧
      Array.ofFn lv.2.1 = foldsA (List.ofFn (phi₁ c)) f₀

/-- **The quotient opening's level-0 view is mumbai's arrays'** (two claims, at `pointQ` and
`pointS`, and the gadget; `63` lanes of `2^22`). -/
def ViewQ : Prop :=
  ∀ (c : DChal E) (vals : Vals E) (T : ιQ → YQ → K) (A : Array K),
    (∀ l y, T l y = A.getD ((l : ℕ) * 2 ^ 22 + y) 0) → A.size = 63 * 2 ^ 22 →
    ∀ (v₁ v₂ : E) {Q : Type} [Fintype Q] [DecidableEq Q] (enc : Q → YQ → K),
    let lv := Gadget.levelMap (Lq.toGadget okQ) Lq.pos
      (Lq.claimW ![pointQ P₀D F192.Y c vals, pointS F192.Y])
      ![1, F192.Y, F192.Y ^ 2] (Gadget.powers 2 (lam₂ c)) (phi₂ c) enc T
    let W₀ := weightTable (quotientLayout logRows) (powers (lam₂ c) 3)
      [⟨pointQ P₀D F192.Y c vals, v₁⟩, ⟨pointS F192.Y, v₂⟩]
    let f₀ := stackTableA 28 A
    (∀ j : Fin 6, lv.1 j = roundMsgArr W₀ f₀ ((List.ofFn (phi₂ c)).take j)) ∧
      Array.ofFn lv.2.1 = foldsA (List.ofFn (phi₂ c)) f₀

end PcsQuotient.EndToEnd.Core
