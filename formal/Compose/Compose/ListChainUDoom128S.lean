-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Follows `formal/Compose/Compose/ListChainUDoom128.lean` of this repository (`trace_whirU'`,
-- `knowledgeSoundness_listChainU_closed128`), with two generalisations for π2's verifier
-- (`formal/RecCompose`): the setup's openings' stacks read off the proof, and the protocol a function of
-- the setup's output.
import Compose.ListChainUDoom128

/-!
# The chain with WHIR openings, the setup's stacks and the protocol read off the setup

`ListChainUDoom128.lean`'s `knowledgeSoundness_listChainU_closed128` fixes two things in advance that
π2's verifier (`formal/RecCompose`) reads off the setup:

* **a setup opening's stack** (`Tgt.setup root q₀`: `q₀` fixed). π2's setup table (`κ`, `κ + σ`) is the
  circuit's for π1's contract IV, a function of π1's setup roots, which the setup computes over `π`. Here
  each opening has an **optional stack read off the proof** (`stk o : Option (Pf → Column _)`, the proof
  carrying the setup's roots): `some f`, the setup committed `f π` under the opening's root
  (`WhirOp.OKP`) and the opening's claims hold of it (`WhirOp.SetupHoldsP`); `none`, an opening nothing is
  concluded of (its acceptance is required, its doom charged; π1's three openings, which π2's contract
  makes before its own);
* **the protocol** (`R : Piop U.K M`): π2's PIOP is the compiled circuit's at π1's contract IV and the
  setup's tables, a function of the setup's roots. Here `R : σ → Piop U.K M`, read at the setup's output
  (`sOf` of the proof, `hsOf`). A fresh query's bad event reads the protocol at the setup's output when
  the setup's queries are all in the history (`advBadS`), else at `default` (no query of the setup is a
  label, `hlabel`, so before the setup's end no input parses as a chain step and the protocol is not read).

**`knowledgeSoundness_listChainU_closed128S`**: the bound of `knowledgeSoundness_listChainU_closed128`,
`maxErrK` bounded uniformly over the setup's outputs (`hme`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

section Defs

variable {F St M Pf : Type} [SampleableType F]

/-- **What the openings need, the setup's stacks read off the proof**: a round's opening as `WhirOp.OK`'s;
a setup opening with a stack `f` (`stk o = some f`), that the setup's queries make the word under its root
the honest encoding of `f` at the proof the setup fixes; a setup opening without one, nothing. -/
def WhirOp.OKP {σ : Type} (tc : ℕ → TableCode M) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : WhirOp Pf F M) → Option (Pf → Column o.S.L.logN)) (o : WhirOp Pf F M) : Prop :=
  match o.tgt with
  | .round i read => (tc i).height = rootHeight o.S.L.logN o.S.R ∧
      (tc i).leafLen = 8 * 2 ^ laneFold ∧
      (∀ w q, q ∈ Candidates o.S.L.logN o.S.R (code₀ o.S.L.logN o.S.R).thr
        (wordOfMerkle (tc i).height (2 ^ laneFold) w) → read q ∈ (tc i).dec w) ∧
      ∀ π ch q, (∀ cl ∈ (o.cl π ch).claims, o.S.L.tableEval q cl.point = cl.value) →
        good i π ch (some (read q))
  | .setup root _ => ∀ f, stk o = some f →
      ∀ (T : KTable) (H : Hist) (p : Pf),
        (∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → x ∈ H) →
          Set.InjOn (viewT T) ↑H →
            ∃ word : Word, HonestWord o.S.L.logN o.S.R word
                (f (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p)) ∧
              ∀ v < 2 ^ rootHeight o.S.L.logN o.S.R,
                Rom.extract (ansOf H (viewT T))
                  (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p)))
                  (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold) v = word v

/-- **A setup opening's stack satisfies its claims**, when it has one (nothing for a round's opening or a
setup opening without a stack). -/
def WhirOp.SetupHoldsP (stk : (o : WhirOp Pf F M) → Option (Pf → Column o.S.L.logN))
    (o : WhirOp Pf F M) (π : Pf) (ch : List (List F)) : Prop :=
  match o.tgt with
  | .round _ _ => True
  | .setup _ _ => ∀ f, stk o = some f → ∀ cl ∈ (o.cl π ch).claims, o.S.L.tableEval (f π) cl.point = cl.value

end Defs

/-! ## The trace -/

section Trace

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (U : ChainSpecU F St) (R : Piop U.K M) (view : Pf → St × List (RMsg F))

open Classical in
/-- **The trace, the setup's stacks read off the proof** (`trace_whirU'` with `WhirOp.OKP` and
`WhirOp.SetupHoldsP` for `WhirOp.OK` and `WhirOp.SetupHolds`). -/
theorem trace_whirP {σ : Type} (ops : List (WhirOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : WhirOp Pf F M) → Option (Pf → Column o.S.L.logN))
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (hok : ∀ o ∈ ops, WhirOp.OKP tc good setup fix stk o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHoldsP stk o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll U.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = U.K.rounds.length →
      (∀ i (h : i < cs.length), (U.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (U.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (tag : List UInt8) (T : KTable)
    (hlabT : ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix A₀) T).map Sigma.fst ∧
      (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length))
    (hev : BreaksOK U.K (fun i => (tc i).commit) R view check
        (fun bs => ∀ k < ops.length, bs.getD k false = true)
        (evalWithAnswerFn (QueryImpl.ofFn T)
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).1 ∧
      ¬ DoomF view ops (evalWithAnswerFn (QueryImpl.ofFn T)
          (expL view (preU U view (withSetupG setup fix A₀)) ops)) ∧
      ¬ PairTr tag (evalWithAnswerFn (QueryImpl.ofFn T)
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).2) :
    FreshBad (advBadU' U (fun i => (tc i).commit) R view (withSetupG setup fix A₀)) T ∅
      ((tableQueryLog (expL view (preU U view (withSetupG setup fix A₀)) ops) T).map
        Sigma.fst) := by
  sorry

end Trace

/-! ## Knowledge soundness, the protocol read off the setup -/

section Closed

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (U : ChainSpecU F St) (view : Pf → St × List (RMsg F))

/-- **Knowledge soundness of the chain with WHIR openings, the setup's stacks and the protocol read off the
setup** (`knowledgeSoundness_listChainU_closed128` with `R : σ → Piop`, read at the setup's output `sOf π`,
and `WhirOp.OKP`): the verifier accepts while no candidate of round `0`'s root read off the adversary's
(and the setup's) queries satisfies the first round's state of the protocol at the setup's output with
probability at most

`Pr[DoomF] + Pr[PairTr tag] + N (me + (nRf + 2) N / 2^256)`, `N = QS + Q + nQ + Σ_k QO_k`,

`me` bounding `maxErrK` at every output of the setup, when no query of the setup is a label (`hlabel`). -/
theorem knowledgeSoundness_listChainU_closed128S {σ : Type} [Inhabited σ] (R : σ → Piop U.K M)
    (sOf : Pf → σ) (ops : List (WhirOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : WhirOp Pf F M) → Option (Pf → Column o.S.L.logN))
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (QS Q : ℕ) (hSq : IsTotalQueryBound setup QS) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q)
    (hsOf : ∀ s p, sOf (fix s p) = s)
    (hok : ∀ o ∈ ops, WhirOp.OKP tc good setup fix stk o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHoldsP stk o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll U.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = U.K.rounds.length →
      (∀ i (h : i < cs.length), (U.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (U.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ (R (sOf π)).post (view π).1 p m c)
    (hlabel : ∀ (T : KTable) (x : List UInt8),
      Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → ∀ s, x ≠ U.label s)
    (tag : List UInt8)
    (hlab : ∀ T : KTable, ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix A₀) T).map
        Sigma.fst ∧
      (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length))
    (me : ℝ≥0∞) (hme : ∀ s, maxErrK U.K (fun i => (tc i).commit) (R s) ≤ me) :
    Pr{let z ← (simulateQ randomOracle
        (expU U view (withSetupG setup fix A₀) (opsRun view ops))).run' ∅}[
        BreaksOK U.K (fun i => (tc i).commit) (R (sOf z.1.1)) view check
          (fun bs => ∀ k < ops.length, bs.getD k false = true) z] ≤
      Pr{let z ← (simulateQ randomOracle
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[DoomF view ops z] +
      Pr{let z ← (simulateQ randomOracle
          (expL view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[PairTr tag z.2] +
      ((QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum : ℕ) : ℝ≥0∞) *
        (me + (((U.nRf + 2) * (QS + Q + U.K.nQ + (ops.map fun o => o.S.QO).sum) : ℕ) : ℝ≥0∞) /
            2 ^ 256) := by
  sorry

end Closed

end Compose
