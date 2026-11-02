-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Generalises `formal/Compose/Compose/Deployed.lean` and `DeployedWired.lean` of this repository
-- (two proof openings and the setup's, hard-wired: each opening's stage logged so that its doom at
-- its end is an event of F2's `ours_sound`, the trace through the undoomed openings, the setup's
-- word through `WiringMatch`) to the `k`-round chain of `ListChainK.lean` with any list of WHIR
-- openings; the trace ends in `ListChainKAdv.lean`'s `trace_advK`, through
-- `ListChainKComposed.lean`'s `breaksK_imp`.
import Compose.ListChainKComposed
import WhirBridge.Large

/-!
# The `k`-round chain with WHIR openings: the doom terms discharged

`ListChainKComposed.lean`'s `knowledgeSoundness_listChainK` leaves each opening's doom (`εD`,
`εS`) as a hypothesis. Here the openings are `opening::verify` (F2's `ourVerifier`), run one after
the other after the chain, each a `WhirOp`:

* its **shape** (`WhirShape`): a layout and rate, the opening's query count `QO` and its doom
  bound `bnd QA` against an adversary of `QA` queries, from F2: `WhirShape.large` for every
  public layout `Layout.new` accepts at `2^24 ..= 2^28` words (`ours_sound_public_at`,
  `QO = largeQueries log_n`), `WhirShape.small` for the deployed witness, wiring and quotient
  layouts (`ours_sound`, `QO = 10122`);
* its claims and its proof, read off the proof and the challenges;
* what it opens (`Tgt`): round `i`'s root (`.round i read`, the stack read back as a message of
  the protocol), or a fixed root the proof carries (`.setup root q₀`, the setup's commitment to
  the stack `q₀`).

The verifier runs the chain, then the openings in their order (`opsRun`), and accepts when its
own check holds and every opening accepts (`BreaksOK`).

**The doom terms**: each opening's stage is logged (`expW`, `stageK`: the run up to the end of
opening `k`, logged from the start, as `Deployed.lean`'s `innerW`), so opening `k` accepting while
doomed at its end (`EOp`) is an event of `romExperiment` of the run before it, and its probability
is at most `bnd (Q + nQ + Σ_{k' < k} QO_{k'})` (`prEvent_stageK_le`, F2's soundness; the later
stages keep it, `prEvent_stagesK_keep`); their sum is `doomSum` (`prEvent_doomAt_le`). The stage
logs are not read by the verifier: `map_expW` (the experiment, its logs dropped, is
`ListChainKAdv.lean`'s `expK` with the openings as `post`).

**The trace** (`trace_whir`): with no opening doomed at its end and no bad fresh query, each round
with a root has a candidate, read off the **adversary's** queries, satisfying its opening's claims
(the opening's word is the Merkle word of the stage's history, `wordOfMerkle_eq_extract`, which is
the adversary's, `merkleWord_stable`; the decoder lists it, `WhirOp.OK`), and each setup opening's
stack satisfies its claims (the setup's queries make its word the honest word,
`candidates_honest`); so `breaksK_imp` gives the list game, and `trace_advK` a bad fresh query.

**`knowledgeSoundness_listChainK_closed`**: for the setup (any computation of the oracles, `QS`
queries) then the adversary (`Q` queries), the verifier accepts while no candidate of round `0`'s
root, read off their queries, satisfies the first round's state with probability at most

`doomSum ops (QS + Q + nQ) + N (maxErrK + 5 N / 2^256)`,  `N = QS + Q + nQ + Σ_k QO_k`,

with no hypothesis on the openings beyond what they open (`WhirOp.OK`: a round's decoder lists the
candidates and their claims give the protocol's `good`; a setup's root commits to its stack's
encoding, `SetupHolds` giving `goodS`) and the composition's `hfit`, `hlink`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open LeanVM.Protocol.Rom (romExperiment romExperiment_map)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The openings -/

/-- **A WHIR opening's shape**: a layout at an admissible shape (rate `2^-R`), the opening's query
count `QO`, and its doom bound: against an adversary of `QA` queries that outputs a root, claims
on the layout and a proof, `opening::verify` accepts while every candidate table of the root's word
violates a claim with probability at most `bnd QA`. -/
structure WhirShape where
  L : Layout
  R : ℕ
  QO : ℕ
  bnd : ℕ → ℝ≥0∞
  adm : Whir.Admissible L.logN R
  queries : ∀ w, IsTotalQueryBound (ourVerifier L R w) QO
  sound : ∀ (A : OracleComp KeccakCalls ((Digest × Stmt L.stacking) × Proof)) (QA : ℕ),
    IsTotalQueryBound A QA →
      Pr{let z ← romExperiment A (ourVerifier L R)}[z.1.2 = true ∧ OpeningDoomed L R z.1.1 z.2] ≤
        bnd QA

/-- **A public layout of `2^24 ..= 2^28` words that `Layout::new` accepts** (`NewOK`): F2's
`ours_sound_public_at`, at the shape's own query count `QO = largeQueries log_n`. -/
@[reducible] noncomputable def WhirShape.large (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ))
    (hS : NewOK vars logChunk logN chunks) (h1 : largeMin ≤ logN) (h2 : logN ≤ largeMax) :
    WhirShape where
  L := Layout.new vars logChunk logN chunks
  R := logInvRate
  QO := largeQueries logN
  bnd := openingBoundAt (largeQueries logN)
  adm := admissible_large h1 h2
  queries w := isTotalQueryBound_large (Layout.new vars logChunk logN chunks) h1 h2 w
  sound A QA hA := ours_sound_public_at vars logChunk logN chunks hS h1 h2 A QA hA

/-- **The deployed layouts** (witness, wiring, quotient at `17 ≤ log_rows ≤ 22`): F2's
`ours_sound`, at the uniform `10122` queries. -/
@[reducible] noncomputable def WhirShape.small (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows) (L : Layout) (hL : L = witnessLayout r ∨ L = wiringLayout r ∨ L = quotientLayout r) : WhirShape where
  L := L
  R := logInvRate
  QO := 10122
  bnd := openingBound
  adm := by
    rcases hL with rfl | rfl | rfl
    · exact (layouts_ok r h1 h2).1
    · exact (layouts_ok r h1 h2).2.1
    · exact (layouts_ok r h1 h2).2.2
  queries w := ourVerifier_queryBound L logInvRate w
  sound A QA hA := ours_sound r h1 h2 L hL A QA hA

/-- **What an opening opens**: round `i`'s root, its stacks read back as messages of the protocol
by `read`; or a root the proof carries (the setup's commitment), committing to the stack `q₀`. -/
inductive Tgt (Pf M : Type) (μ : ℕ) where
  | round (i : ℕ) (read : Column μ → M)
  | setup (root : Pf → Bytes32) (q₀ : Column μ)

/-- **An opening of the verifier**: its shape, its claims and its proof (read off the proof and
the challenges), and what it opens. -/
structure WhirOp (Pf F M : Type) where
  S : WhirShape
  cl : Pf → List (List F) → Stmt S.L.stacking
  prf : Pf → Proof
  tgt : Tgt Pf M S.L.logN

variable {F St M Pf : Type} [SampleableType F]
variable (K : ChainSpec F St) (C : ℕ → ListCommit M) (R : Piop K M)
  (view : Pf → St × List (RMsg F))

/-- The root an opening reads: its round's, from the message the chain absorbed, or the setup's,
from the proof. -/
def WhirOp.root (o : WhirOp Pf F M) (π : Pf) : Bytes32 :=
  match o.tgt with
  | .round i _ => ((msgK view π i).1).getD (Vector.replicate 32 0)
  | .setup r _ => r π

/-- An opening's input: the root, its claims, its proof. -/
def WhirOp.input (o : WhirOp Pf F M) (π : Pf) (ch : List (List F)) :
    (Digest × Stmt o.S.L.stacking) × Proof :=
  ((ofB (WhirOp.root view o π), o.cl π ch), o.prf π)

/-- **The verifier's openings**, one after the other: their verdicts. -/
def opsRun : List (WhirOp Pf F M) → Pf → List (List F) → OracleComp KeccakCalls (List Bool)
  | [], _, _ => pure []
  | o :: os, π, ch => ourVerifier o.S.L o.S.R (WhirOp.input view o π ch) >>= fun b =>
      (b :: ·) <$> opsRun os π ch

/-- **What the openings need**: a round's opening, that its root's decoder `tc i` (a Merkle tree
of the opening's height) lists every candidate of the word read back (`read`), and that a candidate
satisfying the opening's claims is `good` for the protocol; a setup's opening, that the setup's
queries make the word under its root the honest encoding of its stack `q₀`. -/
def WhirOp.OK {σ : Type} (tc : ℕ → TableCode M) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf) (o : WhirOp Pf F M) : Prop :=
  match o.tgt with
  | .round i read => (tc i).height = rootHeight o.S.L.logN o.S.R ∧
      (tc i).leafLen = 8 * 2 ^ laneFold ∧
      (∀ w q, q ∈ Candidates o.S.L.logN o.S.R (code₀ o.S.L.logN o.S.R).thr
        (wordOfMerkle (tc i).height (2 ^ laneFold) w) → read q ∈ (tc i).dec w) ∧
      ∀ π ch q, (∀ cl ∈ (o.cl π ch).claims, o.S.L.tableEval q cl.point = cl.value) →
        good i π ch (some (read q))
  | .setup root q₀ => ∃ word : Word, HonestWord o.S.L.logN o.S.R word q₀ ∧
      ∀ (T : KTable) (H : Hist) (p : Pf),
        (∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → x ∈ H) →
          Set.InjOn (viewT T) ↑H → ∀ v < 2 ^ rootHeight o.S.L.logN o.S.R,
            Rom.extract (ansOf H (viewT T))
              (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p)))
              (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold) v = word v

/-- **A setup opening's stack satisfies its claims** (nothing for a round's opening). -/
def WhirOp.SetupHolds (o : WhirOp Pf F M) (π : Pf) (ch : List (List F)) : Prop :=
  match o.tgt with
  | .round _ _ => True
  | .setup _ q₀ => ∀ cl ∈ (o.cl π ch).claims, o.S.L.tableEval q₀ cl.point = cl.value

/-- **The openings as `ListChainKComposed.lean`'s**: every root's opening and the setup's accept
when every opening accepts. -/
def opW (ops : List (WhirOp Pf F M)) (check : Pf → List (List F) → Prop)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (goodS : Pf → List (List F) → Prop) :
    OpeningsK Pf F (List Bool) M where
  check π ch _ := check π ch
  acc _ _ _ bs := ∀ k < ops.length, bs.getD k false = true
  good := good
  accS _ _ bs := ∀ k < ops.length, bs.getD k false = true
  goodS := goodS

/-- **Knowledge soundness is broken**: the verifier's check holds, the openings accept (`acc`),
and no candidate of round `0`'s root read off the adversary's transcript satisfies the first
round's state. -/
def BreaksOK {β : Type} (check : Pf → List (List F) → Prop) (acc : β → Prop) (z : OutK Pf F β) :
    Prop :=
  check z.1.1 z.1.2.1 ∧ acc z.1.2.2 ∧
    ∀ c ∈ extractorK C view z, ¬ R.pre (view z.1.1).1 [] (c, (msgK view z.1.1 0).2)

theorem breaksK_of_breaksOK (ops : List (WhirOp Pf F M)) (check : Pf → List (List F) → Prop)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (goodS : Pf → List (List F) → Prop)
    (z : OutK Pf F (List Bool))
    (h : BreaksOK K C R view check (fun bs => ∀ k < ops.length, bs.getD k false = true) z) :
    BreaksK K C R view (opW ops check good goodS) z :=
  ⟨⟨h.1, fun _ _ _ => h.2.1, h.2.1⟩, h.2.2⟩

/-! ## The experiment with each opening's stage logged -/

/-- The run before the openings: the proof, the challenges, the adversary's transcript. -/
abbrev PreK (Pf F : Type) := Pf × List (List F) × Transcript

/-- What the stages record: each opening's verdict and the transcript of the run to its end. -/
abbrev Stg := ℕ → Bool × Transcript

/-- Nothing recorded yet. -/
def stg₀ : Stg := fun _ => (false, [])

/-- The adversary, its queries logged, then the chain. -/
def preK (A : OracleComp KeccakCalls Pf) : OracleComp KeccakCalls (PreK Pf F) :=
  loggedKC A >>= fun pt => K.chain hash256 (view pt.1).1 (view pt.1).2 >>= fun ch =>
    pure (pt.1, ch, pt.2)

/-- **Opening `k`'s stage**: the run so far, then the opening, logged from the start; its verdict
and the transcript at its end recorded at `k`. -/
def stageK (o : WhirOp Pf F M) (k : ℕ) (X : OracleComp KeccakCalls (PreK Pf F × Stg)) :
    OracleComp KeccakCalls (PreK Pf F × Stg) :=
  (fun p : ((PreK Pf F × Stg) × Bool) × Transcript =>
      (p.1.1.1, Function.update p.1.1.2 k (p.1.2, p.2))) <$>
    (simulateQ logImplKC (X >>= fun x =>
      (x, ·) <$> ourVerifier o.S.L o.S.R (WhirOp.input view o x.1.1 x.1.2.1))).run []

/-- The openings' stages, from index `k` on. -/
def stagesK : List (WhirOp Pf F M) → ℕ → OracleComp KeccakCalls (PreK Pf F × Stg) →
    OracleComp KeccakCalls (PreK Pf F × Stg)
  | [], _, X => X
  | o :: os, k, X => stagesK os (k + 1) (stageK view o k X)

/-- **The experiment, every opening's stage logged.** -/
def expW (ops : List (WhirOp Pf F M)) (A : OracleComp KeccakCalls Pf) :
    OracleComp KeccakCalls (PreK Pf F × Stg) :=
  stagesK view ops 0 ((fun x => (x, stg₀)) <$> preK K view A)

/-! ### The stage logs are not read -/

/-- The verdicts recorded. -/
def verdOf (s : Stg) : ℕ → Bool := fun j => (s j).1

/-- Verdicts written from index `k` on. -/
def writeV (k : ℕ) (bs : List Bool) (v : ℕ → Bool) : ℕ → Bool :=
  fun j => if k ≤ j then bs.getD (j - k) (v j) else v j

theorem verdOf_update (s : Stg) (k : ℕ) (e : Bool × Transcript) :
    verdOf (Function.update s k e) = Function.update (verdOf s) k e.1 := by
  funext j
  by_cases h : j = k
  · subst h
    simp [verdOf]
  · simp [verdOf, Function.update_of_ne h]

theorem writeV_nil (k : ℕ) (v : ℕ → Bool) : writeV k [] v = v := by
  funext j
  simp [writeV]

theorem writeV_cons (k : ℕ) (b : Bool) (bs : List Bool) (v : ℕ → Bool) :
    writeV k (b :: bs) v = writeV (k + 1) bs (Function.update v k b) := by
  funext j
  simp only [writeV, Function.update_apply]
  by_cases hjk : j = k
  · subst hjk
    simp
  · by_cases hk : k ≤ j
    · have hk1 : k + 1 ≤ j := by omega
      simp only [hk, hk1, hjk, ite_true, ite_false]
      obtain ⟨d, rfl⟩ : ∃ d, j = k + 1 + d := ⟨j - (k + 1), by omega⟩
      rw [show k + 1 + d - k = d + 1 by omega, show k + 1 + d - (k + 1) = d by omega]
      simp
    · have hk1 : ¬ k + 1 ≤ j := by omega
      simp [hk, hk1, hjk]

theorem writeV_zero (bs : List Bool) : writeV 0 bs (fun _ => false) = fun j => bs.getD j false := by
  funext j
  simp [writeV]

theorem verdOf_stg₀ : verdOf stg₀ = fun _ => false := rfl

/-- **The verdicts of the stages are the openings'**, whatever is read of the run before. -/
theorem map_stagesK {γ : Type} : ∀ (ops : List (WhirOp Pf F M)) (k : ℕ)
    (X : OracleComp KeccakCalls (PreK Pf F × Stg)) (Φ : PreK Pf F → (ℕ → Bool) → γ),
    (fun z => Φ z.1 (verdOf z.2)) <$> stagesK view ops k X =
      X >>= fun x => (fun bs => Φ x.1 (writeV k bs (verdOf x.2))) <$>
        opsRun view ops x.1.1 x.1.2.1
  | [], k, X, Φ => by
    simp only [stagesK, opsRun, map_pure, writeV_nil]
    rw [map_eq_bind_pure_comp]
    rfl
  | o :: os, k, X, Φ => by
    rw [stagesK, map_stagesK os (k + 1) (stageK view o k X) Φ, stageK, bind_map_left,
      bind_logged_fst _ [] _ (fun xb : (PreK Pf F × Stg) × Bool =>
        (fun bs => Φ xb.1.1 (writeV (k + 1) bs (Function.update (verdOf xb.1.2) k xb.2))) <$>
          opsRun view os xb.1.1.1 xb.1.1.2.1) ?h]
    case h =>
      intro p
      simp only [verdOf_update]
    simp only [opsRun, bind_assoc, bind_map_left, map_bind, Functor.map_map, writeV_cons]

/-- What the theorem reads of an outcome of the logged experiment. -/
def projS (x : PreK Pf F) (v : ℕ → Bool) : OutK Pf F (ℕ → Bool) := ((x.1, (x.2.1, v)), x.2.2)

/-- The verdicts of an outcome as a function. -/
def verdFn (z : OutK Pf F (List Bool)) : OutK Pf F (ℕ → Bool) :=
  ((z.1.1, (z.1.2.1, fun j => z.1.2.2.getD j false)), z.2)

/-- **The logged experiment, its stage logs dropped, is `expK` with the openings.** -/
theorem map_expW (ops : List (WhirOp Pf F M)) (A : OracleComp KeccakCalls Pf) :
    (fun z => projS z.1 (verdOf z.2)) <$> expW K view ops A =
      verdFn <$> expK K view A (opsRun view ops) := by
  rw [expW, map_stagesK view ops 0 _ projS, bind_map_left]
  simp only [verdOf_stg₀, writeV_zero, preK, expK, verK, bind_assoc, pure_bind, map_bind,
    map_pure]
  refine bind_congr fun pt => bind_congr fun ch => ?_
  rw [map_eq_bind_pure_comp]
  rfl

/-! ### The queries -/

theorem isTotalQueryBound_chainK (s : St) (ms : List (RMsg F)) :
    IsTotalQueryBound (K.chain hash256 s ms) K.nQ := by
  have h := isTotalQueryBound_runM (K.label s) (absorbs K.lim K.rounds ms)
  rw [length_absorbs] at h
  show IsTotalQueryBound (K.chalsOf <$> runM hash256 (K.label s) (absorbs K.lim K.rounds ms))
    (nSteps K.rounds + 1)
  exact (isQueryBound_map_iff _ _ _ _ _).mpr h

theorem isTotalQueryBound_preK (A : OracleComp KeccakCalls Pf) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) : IsTotalQueryBound (preK K view A) (QA + K.nQ) := by
  have h := isTotalQueryBound_bind
    (ob := fun pt : Pf × Transcript => K.chain hash256 (view pt.1).1 (view pt.1).2 >>= fun ch =>
      (pure (pt.1, ch, pt.2) : OracleComp KeccakCalls (PreK Pf F)))
    (isTotalQueryBound_loggedKC_run A QA [] hA) fun pt =>
      isTotalQueryBound_bind
        (ob := fun ch => (pure (pt.1, ch, pt.2) : OracleComp KeccakCalls (PreK Pf F))) (n₂ := 0)
        (isTotalQueryBound_chainK K (view pt.1).1 (view pt.1).2) fun _ => trivial
  rwa [Nat.add_zero] at h

theorem isTotalQueryBound_stageK (o : WhirOp Pf F M) (k : ℕ)
    (X : OracleComp KeccakCalls (PreK Pf F × Stg)) (QX : ℕ) (hX : IsTotalQueryBound X QX) :
    IsTotalQueryBound (stageK view o k X) (QX + o.S.QO) := by
  unfold stageK
  refine (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_loggedKC_run _ _ _ ?_)
  exact isTotalQueryBound_bind hX fun x =>
    (isQueryBound_map_iff _ _ _ _ _).mpr (o.S.queries _)

theorem isTotalQueryBound_stagesK : ∀ (ops : List (WhirOp Pf F M)) (k : ℕ)
    (X : OracleComp KeccakCalls (PreK Pf F × Stg)) (QX : ℕ), IsTotalQueryBound X QX →
      IsTotalQueryBound (stagesK view ops k X) (QX + (ops.map fun o => o.S.QO).sum)
  | [], _, X, QX, h => by simpa [stagesK] using h
  | o :: os, k, X, QX, h => by
    have := isTotalQueryBound_stagesK os (k + 1) _ _ (isTotalQueryBound_stageK view o k X QX h)
    simpa [stagesK, Nat.add_assoc] using this

theorem isTotalQueryBound_expW (ops : List (WhirOp Pf F M)) (A : OracleComp KeccakCalls Pf)
    (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    IsTotalQueryBound (expW K view ops A) (QA + K.nQ + (ops.map fun o => o.S.QO).sum) :=
  isTotalQueryBound_stagesK view ops 0 _ _
    ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_preK K view A QA hA))

/-! ### Each opening's doom is F2's -/

theorem run'_simulateQ_map {α β : Type} (Y : OracleComp KeccakCalls α) (f : α → β)
    (c : KeccakCalls.QueryCache) :
    (simulateQ randomOracle (f <$> Y)).run' c = f <$> (simulateQ randomOracle Y).run' c := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, StateT.run'_eq,
    Functor.map_map]

/-- A stage keeps what is recorded at the other indices. -/
theorem prEvent_stageK_keep (o : WhirOp Pf F M) (k j : ℕ) (hj : j ≠ k)
    (X : OracleComp KeccakCalls (PreK Pf F × Stg)) (E : PreK Pf F → Bool × Transcript → Prop) :
    Pr{let z ← (simulateQ randomOracle (stageK view o k X)).run' ∅}[E z.1 (z.2 j)] =
      Pr{let z ← (simulateQ randomOracle X).run' ∅}[E z.1 (z.2 j)] := by
  rw [stageK, run'_simulateQ_map, prEvent_map]
  simp only [Function.update_of_ne hj]
  exact (prEvent_run'_loggedKC _ [] ∅
    (fun w : (PreK Pf F × Stg) × Bool => E w.1.1 (w.1.2 j))).trans
    (prEvent_run'_bind_keep X _ ∅ (fun x => E x.1 (x.2 j)))

/-- **The later stages keep what is recorded before them.** -/
theorem prEvent_stagesK_keep (E : PreK Pf F → Bool × Transcript → Prop) :
    ∀ (ops : List (WhirOp Pf F M)) (k j : ℕ), j < k →
      ∀ X : OracleComp KeccakCalls (PreK Pf F × Stg),
        Pr{let z ← (simulateQ randomOracle (stagesK view ops k X)).run' ∅}[E z.1 (z.2 j)] =
          Pr{let z ← (simulateQ randomOracle X).run' ∅}[E z.1 (z.2 j)]
  | [], _, _, _, _ => rfl
  | o :: os, k, j, hj, X => by
    rw [stagesK, prEvent_stagesK_keep E os (k + 1) j (by omega)]
    exact prEvent_stageK_keep view o k j (by omega) X E

/-- **Opening `o` accepts while doomed at its end**: every candidate of the word extracted under
its root from the transcript at its end violates one of its claims. -/
def EOp (o : WhirOp Pf F M) (x : PreK Pf F) (e : Bool × Transcript) : Prop :=
  e.1 = true ∧ OpeningDoomed o.S.L o.S.R (WhirOp.input view o x.1 x.2.1) (cacheOfTr e.2)

/-- **A stage's doom is F2's**, for the adversary that runs the protocol up to it. -/
theorem prEvent_stageK_le (o : WhirOp Pf F M) (k : ℕ) (X : OracleComp KeccakCalls (PreK Pf F × Stg))
    (QX : ℕ) (hX : IsTotalQueryBound X QX) :
    Pr{let z ← (simulateQ randomOracle (stageK view o k X)).run' ∅}[EOp view o z.1 (z.2 k)] ≤
      o.S.bnd QX := by
  rw [stageK, run'_simulateQ_map, prEvent_map]
  simp only [Function.update_self]
  have h := prEvent_loggedPrefix X
    (fun x => ourVerifier o.S.L o.S.R (WhirOp.input view o x.1.1 x.1.2.1))
    (fun x b c => b = true ∧ OpeningDoomed o.S.L o.S.R (WhirOp.input view o x.1.1 x.1.2.1) c)
    (readsInl_openingDoomed o.S.L o.S.R fun x : PreK Pf F × Stg => WhirOp.input view o x.1.1 x.1.2.1)
  have hs := o.S.sound ((fun x : PreK Pf F × Stg => WhirOp.input view o x.1.1 x.1.2.1) <$> X) QX
    ((isQueryBound_map_iff _ _ _ _ _).mpr hX)
  rw [romExperiment_map, prEvent_map] at hs
  exact (le_of_eq h).trans hs

/-- Some opening, from index `k` on, accepts while doomed at its end. -/
def DoomAt : List (WhirOp Pf F M) → ℕ → PreK Pf F × Stg → Prop
  | [], _, _ => False
  | o :: os, k, z => EOp view o z.1 (z.2 k) ∨ DoomAt os (k + 1) z

/-- **The openings' doom terms**: each opening's bound at the queries before it. -/
noncomputable def doomSum : List (WhirOp Pf F M) → ℕ → ℝ≥0∞
  | [], _ => 0
  | o :: os, QA => o.S.bnd QA + doomSum os (QA + o.S.QO)

/-- **Some opening is doomed at its end with probability at most `doomSum`.** -/
theorem prEvent_doomAt_le : ∀ (ops : List (WhirOp Pf F M)) (k : ℕ)
    (X : OracleComp KeccakCalls (PreK Pf F × Stg)) (QX : ℕ), IsTotalQueryBound X QX →
      Pr{let z ← (simulateQ randomOracle (stagesK view ops k X)).run' ∅}[DoomAt view ops k z] ≤
        doomSum ops QX
  | [], _, _, _, _ => by
    simp only [DoomAt, doomSum]
    exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ h => h)
  | o :: os, k, X, QX, hX => by
    simp only [DoomAt, doomSum, stagesK]
    refine (prEvent_or_le _ _ _).trans (add_le_add ?_ (prEvent_doomAt_le os (k + 1) _ _
      (isTotalQueryBound_stageK view o k X QX hX)))
    rw [prEvent_stagesK_keep view (EOp view o) os (k + 1) k (by omega)]
    exact prEvent_stageK_le view o k X QX hX

theorem not_doomAt : ∀ (ops : List (WhirOp Pf F M)) (k : ℕ) (z : PreK Pf F × Stg),
    ¬ DoomAt view ops k z → ∀ m (hm : m < ops.length), ¬ EOp view ops[m] z.1 (z.2 (k + m))
  | [], _, _, _, _, hm => absurd hm (by simp)
  | o :: os, k, z, h, 0, _ => fun h' => h (Or.inl h')
  | o :: os, k, z, h, m + 1, hm => by
    have := not_doomAt os (k + 1) z (fun h' => h (Or.inr h')) m (by simpa using hm)
    rw [show k + (m + 1) = k + 1 + m by omega]
    exact this

/-! ### The run against a table -/

theorem stageK_run (o : WhirOp Pf F M) (k : ℕ) (X : OracleComp KeccakCalls (PreK Pf F × Stg))
    (T : KTable) :
    tableQueryLog (stageK view o k X) T = tableQueryLog X T ++
        tableQueryLog (ourVerifier o.S.L o.S.R (WhirOp.input view o
          (evalWithAnswerFn (QueryImpl.ofFn T) X).1.1
          (evalWithAnswerFn (QueryImpl.ofFn T) X).1.2.1)) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (stageK view o k X) =
        ((evalWithAnswerFn (QueryImpl.ofFn T) X).1,
          Function.update (evalWithAnswerFn (QueryImpl.ofFn T) X).2 k
            (evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier o.S.L o.S.R (WhirOp.input view o
              (evalWithAnswerFn (QueryImpl.ofFn T) X).1.1
              (evalWithAnswerFn (QueryImpl.ofFn T) X).1.2.1)),
            (tableQueryLog X T ++ tableQueryLog (ourVerifier o.S.L o.S.R (WhirOp.input view o
              (evalWithAnswerFn (QueryImpl.ofFn T) X).1.1
              (evalWithAnswerFn (QueryImpl.ofFn T) X).1.2.1)) T).filterMap inlEntry)) := by
  obtain ⟨h1l, h1e⟩ := run_keep X
    (fun x => ourVerifier o.S.L o.S.R (WhirOp.input view o x.1.1 x.1.2.1)) T
  obtain ⟨h2l, h2e⟩ := run_logged (X >>= fun x =>
    (x, ·) <$> ourVerifier o.S.L o.S.R (WhirOp.input view o x.1.1 x.1.2.1)) T
  constructor
  · rw [stageK, tableQueryLog_map, h2l, h1l]
  · rw [stageK, evalWithAnswerFn_map, h2e, h1e, h1l]

theorem stagesK_fst (T : KTable) : ∀ (ops : List (WhirOp Pf F M)) (k : ℕ)
    (X : OracleComp KeccakCalls (PreK Pf F × Stg)),
    (evalWithAnswerFn (QueryImpl.ofFn T) (stagesK view ops k X)).1 =
      (evalWithAnswerFn (QueryImpl.ofFn T) X).1
  | [], _, _ => rfl
  | o :: os, k, X => by
    rw [stagesK, stagesK_fst T os (k + 1), (stageK_run view o k X T).2]

theorem stagesK_below (T : KTable) : ∀ (ops : List (WhirOp Pf F M)) (k : ℕ)
    (X : OracleComp KeccakCalls (PreK Pf F × Stg)) (j : ℕ), j < k →
    (evalWithAnswerFn (QueryImpl.ofFn T) (stagesK view ops k X)).2 j =
      (evalWithAnswerFn (QueryImpl.ofFn T) X).2 j
  | [], _, _, _, _ => rfl
  | o :: os, k, X, j, hj => by
    rw [stagesK, stagesK_below T os (k + 1) _ j (by omega), (stageK_run view o k X T).2]
    exact Function.update_of_ne (by omega) _ _

theorem stagesK_log (T : KTable) : ∀ (ops : List (WhirOp Pf F M)) (k : ℕ)
    (X : OracleComp KeccakCalls (PreK Pf F × Stg)),
    tableQueryLog (stagesK view ops k X) T = tableQueryLog X T ++
      tableQueryLog (opsRun view ops (evalWithAnswerFn (QueryImpl.ofFn T) X).1.1
        (evalWithAnswerFn (QueryImpl.ofFn T) X).1.2.1) T
  | [], _, _ => by simp [stagesK, opsRun]
  | o :: os, k, X => by
    rw [stagesK, stagesK_log T os (k + 1), (stageK_run view o k X T).1, (stageK_run view o k X T).2]
    simp only [opsRun, tableQueryLog_bind, tableQueryLog_map, List.append_assoc]

theorem stagesK_at (T : KTable) : ∀ (ops : List (WhirOp Pf F M)) (k : ℕ)
    (X : OracleComp KeccakCalls (PreK Pf F × Stg)) (m : ℕ) (hm : m < ops.length)
    (o : WhirOp Pf F M), ops[m] = o →
    (evalWithAnswerFn (QueryImpl.ofFn T) (stagesK view ops k X)).2 (k + m) =
      (evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier o.S.L o.S.R (WhirOp.input view o
          (evalWithAnswerFn (QueryImpl.ofFn T) X).1.1 (evalWithAnswerFn (QueryImpl.ofFn T) X).1.2.1)),
        (tableQueryLog X T ++ tableQueryLog (opsRun view (ops.take (m + 1))
          (evalWithAnswerFn (QueryImpl.ofFn T) X).1.1
          (evalWithAnswerFn (QueryImpl.ofFn T) X).1.2.1) T).filterMap inlEntry)
  | [], _, _, _, hm, _, _ => absurd hm (by simp)
  | o' :: os, k, X, 0, _, o, ho => by
    simp only [List.getElem_cons_zero] at ho
    subst ho
    rw [stagesK]
    simp only [Nat.add_zero]
    rw [stagesK_below view T os (k + 1) _ k (by omega), (stageK_run view o' k X T).2]
    simp [opsRun, tableQueryLog_map, Function.update_self]
  | o' :: os, k, X, m + 1, hm, o, ho => by
    simp only [List.getElem_cons_succ] at ho
    rw [stagesK, show k + (m + 1) = k + 1 + m by omega,
      stagesK_at T os (k + 1) _ m (by simpa using hm) o ho, (stageK_run view o' k X T).1,
      (stageK_run view o' k X T).2]
    simp only [List.take_succ_cons, opsRun, tableQueryLog_bind, tableQueryLog_map,
      List.append_assoc]

theorem opsRun_log_take (T : KTable) (π : Pf) (ch : List (List F)) :
    ∀ (ops : List (WhirOp Pf F M)) (m : ℕ), ∃ rest,
      tableQueryLog (opsRun view ops π ch) T =
        tableQueryLog (opsRun view (ops.take m) π ch) T ++ rest
  | [], _ => ⟨[], by simp [opsRun]⟩
  | o :: os, 0 => ⟨tableQueryLog (opsRun view (o :: os) π ch) T, by simp [opsRun]⟩
  | o :: os, m + 1 => by
    obtain ⟨rest, h⟩ := opsRun_log_take T π ch os m
    refine ⟨rest, ?_⟩
    simp only [List.take_succ_cons, opsRun, tableQueryLog_bind, tableQueryLog_map, h,
      List.append_assoc]

theorem preK_run (A : OracleComp KeccakCalls Pf) (T : KTable) :
    tableQueryLog (preK K view A) T = tableQueryLog A T ++
        tableQueryLog (K.chain hash256 (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1
          (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).2) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (preK K view A) =
        (evalWithAnswerFn (QueryImpl.ofFn T) A,
          evalWithAnswerFn (QueryImpl.ofFn T) (K.chain hash256
            (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1
            (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).2),
          (tableQueryLog A T).filterMap inlEntry) := by
  obtain ⟨hl, he⟩ := run_logged A T
  have hl' : tableQueryLog (loggedKC A) T = tableQueryLog A T := hl
  have he' : evalWithAnswerFn (QueryImpl.ofFn T) (loggedKC A) =
      (evalWithAnswerFn (QueryImpl.ofFn T) A, (tableQueryLog A T).filterMap inlEntry) := he
  constructor
  · simp only [preK, tableQueryLog_bind, hl', he', tableQueryLog_pure, List.append_nil]
  · simp only [preK, evalWithAnswerFn_bind, he', evalWithAnswerFn_pure]

/-! ## The setup -/

/-- **The setup, then the adversary**: the setup computes its commitments with the oracle, the
adversary is given them, and `fix` writes them in the proof the verifier reads. -/
def withSetupG {σ : Type} (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCalls Pf) : OracleComp KeccakCalls Pf :=
  setup >>= fun s => fix s <$> A₀ s

theorem withSetupG_run {σ : Type} (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCalls Pf) (T : KTable) :
    tableQueryLog (withSetupG setup fix A₀) T = tableQueryLog setup T ++
        tableQueryLog (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup)) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀) =
        fix (evalWithAnswerFn (QueryImpl.ofFn T) setup)
          (evalWithAnswerFn (QueryImpl.ofFn T) (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup))) := by
  constructor
  · rw [withSetupG, tableQueryLog_bind, tableQueryLog_map]
  · rw [withSetupG, evalWithAnswerFn_bind, evalWithAnswerFn_map]

theorem isTotalQueryBound_withSetupG {σ : Type} (setup : OracleComp KeccakCalls σ)
    (fix : σ → Pf → Pf) (A₀ : σ → OracleComp KeccakCalls Pf) (QS Q : ℕ)
    (hS : IsTotalQueryBound setup QS) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q) :
    IsTotalQueryBound (withSetupG setup fix A₀) (QS + Q) :=
  isTotalQueryBound_bind hS fun s => (isQueryBound_map_iff _ _ _ _ _).mpr (hQ s)

/-- With a 32-byte setup, the experiment is `ListChainKRpm.lean`'s two-oracle game. -/
theorem kcGameG_eq (setup : OracleComp KeccakCalls Bytes32) (fix : Bytes32 → Pf → Pf)
    (A₀ : Bytes32 → OracleComp KeccakCalls Pf) {β : Type}
    (post : Pf → List (List F) → OracleComp KeccakCalls β) :
    kcGameG setup fix A₀ (verK K view post) = expK K view (withSetupG setup fix A₀) post := rfl

/-! ## The trace -/

variable [Fintype F] [DecidableEq F]

variable {K C R} in
/-- No collision: the table is injective on the log. -/
theorem injOn_of_not_freshBadK {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBadK K C R) T ∅ L) : Set.InjOn T ↑L.toFinset := by
  have nb : ∀ y ∈ L, ¬ listBadK K C R (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadK K C R) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy w hw hyw
  have hy' := List.mem_toFinset.mp hy
  have hw' := List.mem_toFinset.mp hw
  by_contra hne
  rcases before_trichotomy L y w hy' hw' hne with h | h
  · exact nb w hw' (Or.inl (Or.inl ⟨y, h, hyw⟩))
  · exact nb y hy' (Or.inl (Or.inl ⟨w, h, hyw.symm⟩))

/-- A round's message carries a root when the messages fit the rounds. -/
theorem exists_root_of_fits {ms : List (RMsg F)} (hf : FitsAll K.rounds ms) (i : ℕ)
    (hi : i < K.rounds.length) (hr : (K.spec i).root) :
    ∃ r, (ms.getD i (none, [])).1 = some r ∧ r ∈ K.rootsK ms := by
  have hfi := fitsAll_getD hf i hi
  have hlen := hf.length_eq
  obtain ⟨hfi1, -⟩ := hfi
  have hsome : (ms.getD i (none, [])).1.isSome = true := by
    rw [hfi1]
    exact hr
  obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨r, hr', ?_⟩
  have hms : ms.take K.rounds.length = ms := List.take_of_length_le (le_of_eq hlen)
  have hil : i < ms.length := by omega
  have hmem : ms.getD i (none, []) ∈ ms := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
    exact List.getElem_mem hil
  simp only [ChainSpec.rootsK, hms]
  exact List.mem_filterMap.mpr ⟨_, hmem, hr'⟩

open Classical in
/-- **The trace of the logged experiment**: on every table of both oracles, a run that breaks
knowledge soundness while no opening is doomed at its end asks a bad fresh query. -/
theorem trace_whir {σ : Type} (ops : List (WhirOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (hok : ∀ o ∈ ops, WhirOp.OK tc good setup fix o)
    (hcov : ∀ i < K.rounds.length, (K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHolds o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → good i π ch cs[i]) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (T : KTable)
    (hev : BreaksOK K (fun i => (tc i).commit) R view check (fun v => ∀ k < ops.length, v k = true)
        (projS (evalWithAnswerFn (QueryImpl.ofFn T) (expW K view ops (withSetupG setup fix A₀))).1
          (verdOf (evalWithAnswerFn (QueryImpl.ofFn T)
            (expW K view ops (withSetupG setup fix A₀))).2)) ∧
      ¬ DoomAt view ops 0 (evalWithAnswerFn (QueryImpl.ofFn T)
        (expW K view ops (withSetupG setup fix A₀)))) :
    FreshBad (advBadK K (fun i => (tc i).commit) R view (withSetupG setup fix A₀)) T ∅
      ((tableQueryLog (expW K view ops (withSetupG setup fix A₀)) T).map Sigma.fst) := by
  -- The run's parts, against the table.
  obtain ⟨hsl, hse⟩ := withSetupG_run setup fix A₀ T
  obtain ⟨hpl, hpe⟩ := preK_run K view (withSetupG setup fix A₀) T
  have hproj0 := congrArg (evalWithAnswerFn (QueryImpl.ofFn T))
    (map_expW K view ops (withSetupG setup fix A₀))
  have hlog0 := congrArg (fun oa => tableQueryLog oa T)
    (map_expW K view ops (withSetupG setup fix A₀))
  simp only [evalWithAnswerFn_map] at hproj0
  simp only [tableQueryLog_map] at hlog0
  have hzl0 := stagesK_log view T ops 0
    ((fun x => (x, stg₀)) <$> preK K view (withSetupG setup fix A₀))
  have hz10 := stagesK_fst view T ops 0
    ((fun x => (x, stg₀)) <$> preK K view (withSetupG setup fix A₀))
  have hzat0 := stagesK_at view T ops 0
    ((fun x => (x, stg₀)) <$> preK K view (withSetupG setup fix A₀))
  have hX₀l0 := tableQueryLog_map T (fun x => (x, stg₀)) (preK K view (withSetupG setup fix A₀))
  simp only [evalWithAnswerFn_map, hpe, Nat.zero_add] at hzl0 hz10 hzat0
  rw [hpl] at hX₀l0
  rw [hX₀l0] at hzl0 hzat0
  set A := withSetupG setup fix A₀ with hAdef
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set z := evalWithAnswerFn (QueryImpl.ofFn T) (expW K view ops A) with hz
  set zK := evalWithAnswerFn (QueryImpl.ofFn T) (expK K view A (opsRun view ops)) with hzK
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A with hp
  set ch := evalWithAnswerFn (QueryImpl.ofFn T) (K.chain hash256 (view p).1 (view p).2) with hch
  set lA := tableQueryLog A T with hlA
  set lC := tableQueryLog (K.chain hash256 (view p).1 (view p).2) T with hlC
  set tA : Transcript := lA.filterMap inlEntry with htA
  have hproj : projS z.1 (verdOf z.2) = verdFn zK := hproj0
  have hlogW : tableQueryLog (expW K view ops A) T =
      tableQueryLog (expK K view A (opsRun view ops)) T := hlog0
  have hz1 : z.1 = (p, ch, tA) := hz10
  have hzl : tableQueryLog (expW K view ops A) T =
      (lA ++ lC) ++ tableQueryLog (opsRun view ops p ch) T := hzl0
  have hzat : ∀ m (hm : m < ops.length) (o : WhirOp Pf F M), ops[m] = o →
      z.2 m = (evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier o.S.L o.S.R
          (WhirOp.input view o p ch)),
        ((lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).filterMap
          inlEntry) := hzat0
  -- `expK`'s outcome.
  have hK11 : zK.1.1 = p := by
    have := congrArg (fun w : OutK Pf F (ℕ → Bool) => w.1.1) hproj
    simp only [projS, verdFn, hz1] at this
    exact this.symm
  have hK121 : zK.1.2.1 = ch := by
    have := congrArg (fun w : OutK Pf F (ℕ → Bool) => w.1.2.1) hproj
    simp only [projS, verdFn, hz1] at this
    exact this.symm
  have hK2 : zK.2 = tA := by
    have := congrArg (fun w : OutK Pf F (ℕ → Bool) => w.2) hproj
    simp only [projS, verdFn, hz1] at this
    exact this.symm
  -- The event.
  obtain ⟨hB, hnd⟩ := hev
  have hverd : ∀ m < ops.length, (z.2 m).1 = true := fun m hm => hB.2.1 m hm
  have hBK : BreaksOK K CC R view check (fun bs => ∀ k < ops.length, bs.getD k false = true)
      zK := by
    have h := hB
    rw [hproj] at h
    exact h
  have hcheck : check p ch := by
    have := hBK.1
    rwa [hK11, hK121] at this
  have hnotdoom : ∀ m (hm : m < ops.length), ¬ EOp view ops[m] z.1 (z.2 m) := by
    intro m hm
    have := not_doomAt view ops 0 z hnd m hm
    rwa [Nat.zero_add] at this
  -- No bad fresh query, from here on.
  by_contra hnb
  set Lk := (tableQueryLog (expW K view ops A) T).map Sigma.fst with hLkdef
  set L := Lk.filterMap Sum.getLeft? with hLdef
  set LA := (lA.map Sigma.fst).filterMap Sum.getLeft? with hLAdef
  have hk : ¬ FreshBad (kcBadK K CC R) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBadK K view A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBadK K CC R) (viewT T) ∅ L := fun h =>
    hk (freshBad_kcK K CC R T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := refers_beforeK hl
  have hinj : Set.InjOn (viewT T) ↑L.toFinset := injOn_of_not_freshBadK hl
  have hLk : Lk = lA.map Sigma.fst ++
      ((lC ++ tableQueryLog (opsRun view ops p ch) T).map Sigma.fst) := by
    rw [hLkdef, hzl]
    simp only [List.map_append, List.append_assoc]
  obtain ⟨rest, hLA⟩ : ∃ rest, L = LA ++ rest :=
    ⟨_, by rw [hLdef, hLk, List.filterMap_append]⟩
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, viewT T w ∈ K.rootsK (view p).2 → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBadK K view A) T ∅ Lk hr (.inl w) hwk (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    rw [hLk]
    exact subset_before_append _ _ hwA' q hq
  -- A history between the adversary's and the run's reads the adversary's word.
  have hstab : ∀ (H : List (List UInt8)), (∀ y ∈ LA, y ∈ H) → (∀ y ∈ H, y ∈ L) →
      ∀ r ∈ K.rootsK (view p).2, ∀ ht ℓ,
        merkleWord H.toFinset (viewT T) ht ℓ r = merkleWord LA.toFinset (viewT T) ht ℓ r := by
    intro H hAH hHL r hr' ht ℓ
    refine merkleWord_stable (H := LA.toFinset) (H' := H.toFinset) (T := viewT T) (r := r)
      (fun y hy => List.mem_toFinset.mpr (hAH y (List.mem_toFinset.mp hy)))
      (fun w hw hwr => List.mem_toFinset.mpr
        (hroot w (hHL w (List.mem_toFinset.mp hw)) (hwr ▸ hr')))
      (fun y hy w hw h => ?_) ht ℓ
    have hyA := List.mem_toFinset.mp hy
    have hyL : y ∈ L := by rw [hLA]; exact List.mem_append_left _ hyA
    have hb := hord w (hHL w (List.mem_toFinset.mp hw)) y hyL h
    rw [hLA, before_append_of_mem LA rest hyA] at hb
    exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  -- The stages' histories.
  set Hm : ℕ → List (List UInt8) := fun m =>
    (((lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).map
      Sigma.fst).filterMap Sum.getLeft? with hHm
  have hHmL : ∀ m, ∀ y ∈ Hm m, y ∈ L := by
    intro m y hy
    obtain ⟨rest', hrest'⟩ := opsRun_log_take view T p ch ops (m + 1)
    have hL' : L = (((lA ++ lC) ++ (tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T ++
        rest')).map Sigma.fst).filterMap Sum.getLeft? := by
      rw [hLdef, hLkdef, hzl, hrest']
    rw [hL']
    have hy' : y ∈ (((lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).map
        Sigma.fst).filterMap Sum.getLeft? := hy
    simp only [List.map_append, List.filterMap_append, List.mem_append] at hy' ⊢
    tauto
  have hLAHm : ∀ m, ∀ y ∈ LA, y ∈ Hm m := by
    intro m y hy
    show y ∈ (((lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).map
      Sigma.fst).filterMap Sum.getLeft?
    rw [List.map_append, List.map_append, List.filterMap_append, List.filterMap_append]
    exact List.mem_append_left _ (List.mem_append_left _ hy)
  have hinjm : ∀ m, Set.InjOn (viewT T) ↑(Hm m).toFinset := fun m =>
    hinj.mono fun y hy => List.mem_toFinset.mpr (hHmL m y (List.mem_toFinset.mp hy))
  -- An undoomed opening has a candidate of its stage's word satisfying its claims.
  have hcand : ∀ m (hm : m < ops.length) (o : WhirOp Pf F M), ops[m] = o →
      ∃ q ∈ Candidates o.S.L.logN o.S.R (code₀ o.S.L.logN o.S.R).thr
          (Rom.extract (ansOf (Hm m).toFinset (viewT T)) (ofB (WhirOp.root view o p))
            (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold)),
        ∀ cl ∈ (o.cl p ch).claims, o.S.L.tableEval q cl.point = cl.value := by
    intro m hm o ho
    have hv := hverd m hm
    have hd := hnotdoom m hm
    rw [ho] at hd
    rw [hzat m hm o ho] at hv hd
    rw [hz1] at hd
    have hOD : ¬ OpeningDoomed o.S.L o.S.R (WhirOp.input view o p ch)
        (cacheOfTr (((lA ++ lC) ++
          tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T).filterMap inlEntry)) :=
      fun h => hd ⟨hv, h⟩
    unfold OpeningDoomed at hOD
    push Not at hOD
    obtain ⟨q, hq, hqc⟩ := hOD
    have hsnd : ∀ e ∈ (lA ++ lC) ++ tableQueryLog (opsRun view (ops.take (m + 1)) p ch) T,
        e.2 = T e.1 := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · exact tableQueryLog_snd_dep T _ e he
        · exact tableQueryLog_snd_dep T _ e he
      · exact tableQueryLog_snd_dep T _ e he
    rw [cacheOfTr_eq_ansOf T _ hsnd] at hq
    exact ⟨q, hq, hqc⟩
  -- Every round with a root has a candidate, read off the adversary's queries, that is good.
  have htrH : histOfTr tA = LA.toFinset := by
    simp only [histOfTr, htA, hLAdef, map_fst_filterMap_inlEntry]
  have htrT : ∀ d ∈ histOfTr tA, tableOfTr tA d = viewT T d := by
    intro d hd
    refine tableOfTr_eq (viewT T) tA (fun e he => ?_) d (by simpa [histOfTr] using hd)
    obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he
    obtain ⟨d', u⟩ := q
    cases d' with
    | inl x =>
      simp only [inlEntry, Option.some.injEq] at hqe
      subst hqe
      have := tableQueryLog_snd_dep T _ _ hq
      simp only at this
      simp [viewT, this]
    | inr s => simp [inlEntry] at hqe
  have hfit' := hfit p ch hcheck
  have hD : ∀ i < K.rounds.length, (K.spec i).root →
      ¬ DoomK CC view (opW ops check good goodS) i zK := by
    intro i hi hri hDK
    obtain ⟨o, hoops, rd, htgt⟩ := hcov i hi hri
    obtain ⟨m, hm, ho⟩ := List.mem_iff_getElem.mp hoops
    obtain ⟨q, hq, hqc⟩ := hcand m hm o ho
    have hokO : WhirOp.OK tc good setup fix o := hok o hoops
    obtain ⟨r, hmr, hrr⟩ := exists_root_of_fits K hfit' i hi hri
    unfold WhirOp.OK at hokO
    rw [htgt] at hokO
    obtain ⟨hht, hlf, hcomp, hgood⟩ := hokO
    have hroot_o : WhirOp.root view o p = r := by
      unfold WhirOp.root
      rw [htgt]
      show ((msgK view p i).1).getD (Vector.replicate 32 0) = r
      simp only [msgK]
      rw [hmr]
      rfl
    rw [hroot_o] at hq
    have hword := candidates_congr (μ := o.S.L.logN) (R := o.S.R)
      (A := (code₀ o.S.L.logN o.S.R).thr)
      (W := Rom.extract (ansOf (Hm m).toFinset (viewT T)) (ofB r) (rootHeight o.S.L.logN o.S.R)
        (2 ^ laneFold))
      (W' := wordOfMerkle (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold)
        (merkleWord (Hm m).toFinset (viewT T) (rootHeight o.S.L.logN o.S.R) (8 * 2 ^ laneFold)
          (toB (ofB r))))
      fun v hv => (wordOfMerkle_eq_extract (hinjm m) _ _ _ hv).symm
    have htoB : toB (ofB r) = r := LeanVM.Rpm.digestToRpm_ofRpm _
    rw [hword, htoB, hstab (Hm m) (hLAHm m) (hHmL m) r hrr] at hq
    have hmem : rd q ∈ (tc i).dec
        (merkleWord LA.toFinset (viewT T) (tc i).height (tc i).leafLen r) :=
      hcomp _ q (by rw [hht, hlf]; exact hq)
    have hgq : good i p ch (some (rd q)) := hgood p ch q hqc
    obtain ⟨-, hdoom⟩ := hDK
    refine hdoom (some (rd q)) ?_ ?_
    · rw [hK2, hK11, optC_congr (CC i) htrT, htrH]
      unfold optC
      simp only [msgK] at hmr ⊢
      rw [hmr]
      exact List.mem_map.mpr ⟨rd q, hmem, rfl⟩
    · rw [hK11, hK121]
      exact hgq
  -- Every setup opening's stack satisfies its claims.
  have hSH : ∀ o ∈ ops, WhirOp.SetupHolds o p ch := by
    intro o hoops
    obtain ⟨m, hm, ho⟩ := List.mem_iff_getElem.mp hoops
    obtain ⟨q, hq, hqc⟩ := hcand m hm o ho
    have hokO : WhirOp.OK tc good setup fix o := hok o hoops
    unfold WhirOp.SetupHolds
    unfold WhirOp.OK at hokO
    rcases htg : o.tgt with ⟨i, rd⟩ | ⟨root, q₀⟩
    · trivial
    · rw [htg] at hokO
      obtain ⟨word, hhon, hsw⟩ := hokO
      have hsub : ∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst →
          x ∈ (Hm m).toFinset := by
        intro x hx
        refine List.mem_toFinset.mpr (hLAHm m x (mem_filterMap_getLeft?.mpr ?_))
        rw [hsl, List.map_append]
        exact List.mem_append_left _ hx
      have hroot_o : WhirOp.root view o p = root p := by
        unfold WhirOp.root
        rw [htg]
      rw [hroot_o, hse] at hq
      have hword := candidates_congr (μ := o.S.L.logN) (R := o.S.R)
        (A := (code₀ o.S.L.logN o.S.R).thr)
        (W := Rom.extract (ansOf (Hm m).toFinset (viewT T))
          (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup)
            (evalWithAnswerFn (QueryImpl.ofFn T)
              (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup))))))
          (rootHeight o.S.L.logN o.S.R) (2 ^ laneFold))
        (W' := word) fun v hv => hsw T (Hm m).toFinset
          (evalWithAnswerFn (QueryImpl.ofFn T) (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup)))
          hsub (hinjm m) v hv
      rw [hword] at hq
      have hq₀ := candidates_honest o.S.adm hhon hq
      subst hq₀
      exact hqc
  have hgS : goodS p ch := hS p ch hSH
  -- The list game, then a bad fresh query.
  have hBK' := breaksK_of_breaksOK K CC R view ops check good goodS zK hBK
  rcases breaksK_imp K CC R view (opW ops check good goodS) (fun π ch' _ h => hfit π ch' h)
      (fun π ch' _ cs h hl' hg hs => hlink π ch' cs h hl' hg hs) zK hBK' with
    ⟨i, hi, hri, hDK⟩ | hDS | hwin
  · exact hD i hi hri hDK
  · obtain ⟨-, hng⟩ := hDS
    refine hng ?_
    show goodS zK.1.1 zK.1.2.1
    rw [hK11, hK121]
    exact hgS
  · have := trace_advK K CC R view A (opsRun view ops) T hwin
    rw [← hlogW] at this
    exact hnb this

/-! ## Knowledge soundness with the openings' terms discharged -/

/-- **Knowledge soundness of the `k`-round chain with WHIR openings, every opening's doom
discharged by F2**, in mumbai's two-oracle model. The setup (`QS` queries) computes its
commitments, the adversary (`Q` queries) is given them, `fix` writes them in the proof; the
verifier runs the chain, then `opening::verify` for each opening of `ops` in order. With the
openings' matches (`WhirOp.OK`: each round's decoder `tc i` lists its opening's candidates and
their claims make them `good`; each setup root commits to its stack), every round with a root
opened (`hcov`), the setup's stacks' claims giving `goodS` (`hS`), and the composition's `hfit`,
`hlink`: the verifier accepts while no candidate of round `0`'s root read off the adversary's (and
the setup's) queries satisfies the first round's state with probability at most

`doomSum ops (QS + Q + nQ) + N (maxErrK + 5 N / 2^256)`,  `N = QS + Q + nQ + Σ_k QO_k`:

opening `k`'s term is its shape's `bnd` at the queries before it (`QS + Q + nQ + Σ_{k'<k}
QO_{k'}`), and `maxErrK` is round `j`'s error `R.err j` times the product of the list bounds
`(tc i).bound` of the roots of the rounds `0..j`. -/
theorem knowledgeSoundness_listChainK_closed {σ : Type} (ops : List (WhirOp Pf F M))
    (tc : ℕ → TableCode M) (check : Pf → List (List F) → Prop)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (goodS : Pf → List (List F) → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf) (A₀ : σ → OracleComp KeccakCalls Pf)
    (QS Q : ℕ) (hSq : IsTotalQueryBound setup QS) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q)
    (hok : ∀ o ∈ ops, WhirOp.OK tc good setup fix o)
    (hcov : ∀ i < K.rounds.length, (K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHolds o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → good i π ch cs[i]) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c) :
    Pr{let z ← (simulateQ randomOracle
        (expK K view (withSetupG setup fix A₀) (opsRun view ops))).run' ∅}[
        BreaksOK K (fun i => (tc i).commit) R view check
          (fun bs => ∀ k < ops.length, bs.getD k false = true) z] ≤
      doomSum ops (QS + Q + K.nQ) +
        ((QS + Q + K.nQ + (ops.map fun o => o.S.QO).sum : ℕ) : ℝ≥0∞) *
          (maxErrK K (fun i => (tc i).commit) R +
            5 * ((QS + Q + K.nQ + (ops.map fun o => o.S.QO).sum : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set A := withSetupG setup fix A₀ with hAdef
  have hA : IsTotalQueryBound A (QS + Q) :=
    isTotalQueryBound_withSetupG setup fix A₀ QS Q hSq hQ
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set accF : (ℕ → Bool) → Prop := fun v => ∀ k < ops.length, v k = true with haccF
  -- The event on the logged experiment.
  have h1 : Pr{let z ← (simulateQ randomOracle (expK K view A (opsRun view ops))).run' ∅}[
        BreaksOK K CC R view check (fun bs => ∀ k < ops.length, bs.getD k false = true) z] =
      Pr{let z ← (simulateQ randomOracle (expW K view ops A)).run' ∅}[
        BreaksOK K CC R view check accF (projS z.1 (verdOf z.2))] := by
    calc _ = Pr{let z ← (simulateQ randomOracle (expK K view A (opsRun view ops))).run' ∅}[
          BreaksOK K CC R view check accF (verdFn z)] := rfl
      _ = Pr{let w ← verdFn <$> (simulateQ randomOracle (expK K view A (opsRun view ops))).run' ∅}[
          BreaksOK K CC R view check accF w] := (prEvent_map _ _ _).symm
      _ = Pr{let w ← (simulateQ randomOracle (verdFn <$> expK K view A (opsRun view ops))).run' ∅}[
          BreaksOK K CC R view check accF w] := by rw [run'_simulateQ_map]
      _ = Pr{let w ← (simulateQ randomOracle ((fun z => projS z.1 (verdOf z.2)) <$>
            expW K view ops A)).run' ∅}[BreaksOK K CC R view check accF w] := by
          rw [map_expW]
      _ = _ := by rw [run'_simulateQ_map, prEvent_map]
  rw [h1]
  set mx := (simulateQ randomOracle (expW K view ops A)).run' ∅
  refine (prEvent_mono mx _ (fun z => DoomAt view ops 0 z ∨
    (BreaksOK K CC R view check accF (projS z.1 (verdOf z.2)) ∧ ¬ DoomAt view ops 0 z))
    fun z h => ?_).trans ((prEvent_or_le _ _ _).trans (add_le_add ?_ ?_))
  · by_cases hd : DoomAt view ops 0 z
    · exact Or.inl hd
    · exact Or.inr ⟨h, hd⟩
  · exact prEvent_doomAt_le view ops 0 _ (QS + Q + K.nQ)
      ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_preK K view A (QS + Q) hA))
  · refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (expW K view ops A)
      (QS + Q + K.nQ + (ops.map fun o => o.S.QO).sum) (isTotalQueryBound_expW K view ops A _ hA)
      (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
      (Set.finite_range _) _ (advBadK K CC R view A) _ (fun S hS' c t ht hcard => ?_)
      (fun T h => trace_whir K R view ops tc check good goodS setup fix A₀ hok hcov hS hfit hlink
        T h)
    have hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
      fun v => hS' _ ⟨v, rfl⟩
    refine (prob_advBadK K CC R view A S hS₀ c t ht).trans ?_
    rw [add_comm]
    gcongr
    have hk : K.rounds.length < K.nQ := by
      have := nSteps_ge_length K.rounds
      simp only [ChainSpec.nQ]
      omega
    have : 4 * (cacheDom c).card + 3 + K.rounds.length ≤
        5 * (QS + Q + K.nQ + (ops.map fun o => o.S.QO).sum) := by omega
    calc ((4 * (cacheDom c).card + 3 + K.rounds.length : ℕ) : ℝ≥0∞)
        ≤ ((5 * (QS + Q + K.nQ + (ops.map fun o => o.S.QO).sum) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast this
      _ = 5 * ((QS + Q + K.nQ + (ops.map fun o => o.S.QO).sum : ℕ) : ℝ≥0∞) := by
          push_cast; ring


/-! ## The decoders and the setups the openings come with -/

section Helpers

/-- **A round's opening with the computable decoder** (`Decoder.lean`'s `tableCode`: the level-0
Johnson list of the shape's certified code, read back as tables, at most
`(certOf log_n R 0).listHi` of them): `WhirOp.OK` holds once a table satisfying the opening's
claims is `good`. -/
theorem whirOp_ok_tableCode {σ : Type} (S : WhirShape) (cl : Pf → List (List F) → Stmt S.L.stacking)
    (prf : Pf → Proof) (i : ℕ) (rd : Tab S.L → M) (tc : ℕ → TableCode M)
    (htc : tc i = tableCode S.L S.R S.adm rd)
    (good : ℕ → Pf → List (List F) → Option M → Prop)
    (hg : ∀ π ch (t : Tab S.L), (∀ cl' ∈ (cl π ch).claims, tabEval S.L t cl'.point = cl'.value) →
      good i π ch (some (rd t)))
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf) :
    WhirOp.OK tc good setup fix
      (⟨S, cl, prf, .round i (fun q => rd (tabOf S.L q))⟩ : WhirOp Pf F M) := by
  unfold WhirOp.OK
  dsimp only
  rw [htc]
  exact ⟨rfl, rfl, fun w q hq => read_mem_tableCode_dec S.adm rd w q hq,
    fun π ch q h => hg π ch (tabOf S.L q) fun cl' hcl' => (tabEval_tabOf _ _ _).trans (h cl' hcl')⟩

/-- At a large shape, the decoder's list is `L₀ = largeList log_n` (`listHi_large`). -/
theorem tableCode_bound_large (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ))
    (hS : NewOK vars logChunk logN chunks) (h1 : largeMin ≤ logN) (h2 : logN ≤ largeMax)
    (rd : Tab (WhirShape.large vars logChunk logN chunks hS h1 h2).L → M) :
    (tableCode (WhirShape.large vars logChunk logN chunks hS h1 h2).L
      (WhirShape.large vars logChunk logN chunks hS h1 h2).R
      (WhirShape.large vars logChunk logN chunks hS h1 h2).adm rd).bound = largeList logN :=
  listHi_large logN h1 h2

/-- **The setup of a stack at a shape**: the Merkle tree of its encoding (`WiringSetup.lean`'s
`wiringSetup` of `stackWord`), its root as 32 bytes. -/
def stackSetupS (S : WhirShape) (q₀ : Column S.L.logN) : OracleComp KeccakCalls Bytes32 :=
  wiringSetup (rootHeight S.L.logN S.R) (LeanVM.Protocol.Whir.Complete.stackWord S.L.logN q₀)

/-- The stack's setup makes `2^(ht + 1)` queries. -/
theorem isTotalQueryBound_stackSetupS (S : WhirShape) (q₀ : Column S.L.logN) :
    IsTotalQueryBound (stackSetupS S q₀) (2 ^ (rootHeight S.L.logN S.R + 1)) :=
  (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_buildTreeM _ _)

/-- **A setup opening of the stack's setup**: `WhirOp.OK` holds when the proof carries the setup's
root (`hfix`): the setup's queries make the word under it the stack's encoding
(`extract_wiringSetup`, `honest_stackWord`). -/
theorem whirOp_ok_stack (S : WhirShape) (cl : Pf → List (List F) → Stmt S.L.stacking)
    (prf : Pf → Proof) (root : Pf → Bytes32) (q₀ : Column S.L.logN) (tc : ℕ → TableCode M)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (fix : Bytes32 → Pf → Pf)
    (hfix : ∀ s p, root (fix s p) = s) :
    WhirOp.OK tc good (stackSetupS S q₀) fix (⟨S, cl, prf, .setup root q₀⟩ : WhirOp Pf F M) := by
  refine ⟨LeanVM.Protocol.Whir.Complete.stackWord S.L.logN q₀, honest_stackWord _ _ q₀,
    fun T H p hsub hinj v hv => ?_⟩
  show Rom.extract (ansOf H (viewT T))
    (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) (stackSetupS S q₀)) p)))
    (rootHeight S.L.logN S.R) (2 ^ laneFold) v = _
  rw [hfix]
  exact extract_wiringSetup _ _ _ (LeanVM.Protocol.Whir.Complete.wellShaped_stackWord _ q₀) T H
    hsub hinj v hv

end Helpers

/-! ## In the random-permutation model -/

/-- `BreaksOK` reads the transcript through its answers only. -/
theorem breaksOK_congr {β : Type} (check : Pf → List (List F) → Prop) (acc : β → Prop)
    (z : Pf × (List (List F) × β)) (tr tr' : Transcript) (h : ∀ x, lookTr tr x = lookTr tr' x)
    (hz : BreaksOK K C R view check acc (z, tr)) : BreaksOK K C R view check acc (z, tr') := by
  obtain ⟨hH, hT⟩ := histOfTr_tableOfTr_congr h
  refine ⟨hz.1, hz.2.1, fun c hc => hz.2.2 c ?_⟩
  unfold extractorK at hc ⊢
  simp only at hc ⊢
  rwa [hH, hT]

/-- **The openings follow the duplex discipline.** -/
theorem duplexVm_opsRun : ∀ (ops : List (WhirOp Pf F M)) (π : Pf) (ch : List (List F)),
    LeanVM.Rpm.DuplexVm (opsRun view ops π ch) []
  | [], _, _ => trivial
  | o :: os, π, ch => by
    refine LeanVM.Rpm.DuplexVm.bind (duplexVm_ourVerifier _ _ _) fun b => ?_
    rw [map_eq_bind_pure_comp]
    exact LeanVM.Rpm.DuplexVm.bind (duplexVm_opsRun os π ch) fun _ => trivial

/-- **Knowledge soundness of the `k`-round chain with WHIR openings in the random-permutation
model** (leanerVM's model: one uniformly random permutation of Keccak-f[1600]'s state, queried
forward and inverse; Keccak-256 the sponge over it), every opening's doom discharged. The setup
computes its 32-byte commitment with Keccak-256 over `π` (at most `QS` Keccak-256 calls, `QSπ`
calls of `π`); the adversary, with coins, `π` and `π⁻¹`, makes at most `Q` calls given it; the
verifier (the chain and the openings, `QVπ` calls of `π`) accepts while no candidate of round
`0`'s root, read off the setup's log and the Keccak-256 evaluations of the adversary's permutation
transcript, satisfies the first round's state with probability at most the two-oracle bound for an
adversary of `QS + Q` queries (the derandomized adversary recomputes the public setup), plus
`(QSπ + Q + QVπ)² / 2^508`. -/
theorem knowledgeSoundness_listChainK_closed_rpm (ops : List (WhirOp Pf F M))
    (tc : ℕ → TableCode M) (check : Pf → List (List F) → Prop)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (goodS : Pf → List (List F) → Prop)
    (setup : OracleComp KeccakCalls Bytes32) (hSH : LeanVM.Rpm.HOnly setup) (QS QSπ : ℕ)
    (hSq : IsTotalQueryBound setup QS)
    (hSπ : Common.QueryCostAtMost setup LeanVM.Rpm.hashBlocks QSπ) (fix : Bytes32 → Pf → Pf)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf) (Q : ℕ)
    (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q) (QVπ : ℕ)
    (hVπ : ∀ π, Common.QueryCostAtMost (verK K view (opsRun view ops) π) LeanVM.Rpm.hashBlocks QVπ)
    (hok : ∀ o ∈ ops, WhirOp.OK tc good setup fix o)
    (hcov : ∀ i < K.rounds.length, (K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHolds o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → good i π ch cs[i]) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c) :
    Pr{let z ← Common.runWithRandomPermutation
        (rpmGameG setup fix A (verK K view (opsRun view ops)))}[
        BreaksOK K (fun i => (tc i).commit) R view check
          (fun bs => ∀ k < ops.length, bs.getD k false = true)
          (z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))] ≤
      doomSum ops (QS + (QS + Q) + K.nQ) +
        ((QS + (QS + Q) + K.nQ + (ops.map fun o => o.S.QO).sum : ℕ) : ℝ≥0∞) *
          (maxErrK K (fun i => (tc i).commit) R +
            5 * ((QS + (QS + Q) + K.nQ + (ops.map fun o => o.S.QO).sum : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        ((QSπ + Q + QVπ : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 := by
  obtain ⟨A', hA', hle⟩ := rpm_le_kcG setup hSH QS QSπ hSq hSπ fix A Q hA
    (verK K view (opsRun view ops)) (duplexVm_verK K view _ fun π ch => duplexVm_opsRun view ops π ch)
    QVπ hVπ
    (fun z tr => BreaksOK K (fun i => (tc i).commit) R view check
      (fun bs => ∀ k < ops.length, bs.getD k false = true) (z, tr))
    (fun z tr tr' h hz => breaksOK_congr K (fun i => (tc i).commit) R view check
      (fun bs : List Bool => ∀ k < ops.length, bs.getD k false = true) z tr tr' h hz)
  refine hle.trans (add_le_add ?_ le_rfl)
  rw [kcGameG_eq]
  exact knowledgeSoundness_listChainK_closed K R view ops tc check good goodS setup fix A' QS
    (QS + Q) hSq hA' hok hcov hS hfit hlink

end Compose
