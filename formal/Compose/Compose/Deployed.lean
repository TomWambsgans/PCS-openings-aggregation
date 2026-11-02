-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Coupling

/-!
# The deployed openings: F2's `ours_sound` discharges the witness and quotient terms

The deployed verifier runs the reduction's chain, then `opening::verify` three times
(`WhirBridge.ourVerifier`): the witness table's opening at the proof's first root, the wiring
table's at the circuit's commitment, the quotient table's at the second root, each with the claims
the reduction hands it (`Deploy`: the layouts, the rate, the commitment, the claim maps).
`deployedExp` is that run, logged so that the cache at the end of each opening is read off a
transcript (`Coupling.lean`): the adversary's own (`tA`, which the extractor reads), the run's up
to the witness opening (`tW`), and the whole run's (`tQ`).

* **`prEvent_EW_le`, `prEvent_EQ_le`**: the witness and the quotient openings accept while every
  candidate of their root's extracted word has a table violating one of their claims
  (`OpeningDoomed`, at the end of the opening) with probability at most `openingBound` of the
  adversary that runs the protocol up to the opening: F2's **`ours_sound`**, through
  `prEvent_loggedPrefix` (the logged run is `romExperiment`) and `romExperiment_map`.
* **`trace_deployed`**: if neither is doomed, and the wiring opening's claim holds, an accepted run
  whose extracted list holds no witness asks a bad fresh query. Two candidates of the opening
  are read back as F1's messages (`WitnessMatch`, `QuotientMatch`: the decoder lists every
  candidate of mumbai's extraction, and a candidate whose table satisfies an opening's claims is a
  message satisfying F1's), the opening's word is `merkleWord`'s (`wordOfMerkle_eq_extract`), and
  the history at the end of the opening reads as the adversary's (`merkleWord_stable`).
* **`knowledgeSoundness_deployed`**: the verifier accepts while the adversary's extractor's list
  holds no witness with probability at most
  `openingBound (Q + 6) + εσ + openingBound (Q + 6 + 2 QO) + N (max L₁ (L₁ L₂) · roundError + 5 N / 2^256)`,
  `N = Q + 6 + 3 QO`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open LeanVM.Protocol.Rom (romExperiment romExperiment_map)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds}

/-- The three openings' proofs: the witness table's, the wiring table's, the quotient table's. -/
abbrev OpenProofs := Proof × Proof × Proof

/-- **What the deployed verifier hands the openings**: the layouts, the rate, the circuit's
commitment, and the claims of each opening as a function of the reduction's proof and challenges. -/
structure Deploy (F : Type) where
  R : ℕ
  Lw : Layout
  Lσ : Layout
  LQ : Layout
  indexRoot : Digest
  clW : RootProof F → Chals F → Stmt Lw.stacking
  clσ : RootProof F → Chals F → Stmt Lσ.stacking
  clQ : RootProof F → Chals F → Stmt LQ.stacking

/-- The protocol up to the openings: the adversary (its Keccak-256 queries logged), its proof,
and the chain's challenges. -/
structure S0 (F : Type) where
  π : RootProof F
  o : OpenProofs
  tA : Transcript
  ch : Chals F

/-- A digest from its 32 bytes. -/
abbrev ofB (b : Bytes32) : Digest := LeanVM.Digest.ofRpm b

variable (W : Wire P B) (D : Deploy F)

/-- The adversary, its log, and the chain. -/
def DA (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) : OracleComp KeccakCalls (S0 F) :=
  loggedKC A >>= fun pt => chainWith W hash256 pt.1.1 >>= fun ch => pure ⟨pt.1.1, pt.1.2, pt.2, ch⟩

/-- The witness opening's input: the first root, its claims, its proof. -/
def wIn (a : S0 F) : (Digest × Stmt D.Lw.stacking) × Proof :=
  ((ofB a.π.r₁, D.clW a.π a.ch), a.o.1)

/-- The wiring opening's input: the circuit's commitment, its claim, its proof. -/
def σIn (a : S0 F) : (Digest × Stmt D.Lσ.stacking) × Proof :=
  ((D.indexRoot, D.clσ a.π a.ch), a.o.2.1)

/-- The quotient opening's input: the second root, its two claims, its proof. -/
def qIn (a : S0 F) : (Digest × Stmt D.LQ.stacking) × Proof :=
  ((ofB a.π.r₂, D.clQ a.π a.ch), a.o.2.2)

/-- The run up to the witness opening, logged: `((a, bW), tW)`. -/
def innerW (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) :
    OracleComp KeccakCalls ((S0 F × Bool) × Transcript) :=
  (simulateQ logImplKC (DA W A >>= fun a => (a, ·) <$> ourVerifier D.Lw D.R (wIn D a))).run []

/-- Then the wiring opening: `(((a, bW), tW), bσ)`. -/
def midσ (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) :
    OracleComp KeccakCalls (((S0 F × Bool) × Transcript) × Bool) :=
  innerW W D A >>= fun x => (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1)

/-- **The deployed run**, logged: `(((((a, bW), tW), bσ), bQ), tQ)`. -/
def deployedExp (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) :
    OracleComp KeccakCalls (((((S0 F × Bool) × Transcript) × Bool) × Bool) × Transcript) :=
  (simulateQ logImplKC (midσ W D A >>= fun y => (y, ·) <$>
    ourVerifier D.LQ D.R (qIn D y.1.1.1))).run []

/-- An outcome of the deployed run. -/
abbrev DOut (F : Type) := ((((S0 F × Bool) × Transcript) × Bool) × Bool) × Transcript

/-! ## The events -/

/-- The witness opening accepts while doomed at its end. -/
def EW (z : DOut F) : Prop :=
  z.1.1.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1.1.1.1) (cacheOfTr z.1.1.1.2)

/-- The quotient opening accepts while doomed at its end. -/
def EQ (z : DOut F) : Prop :=
  z.1.2 = true ∧ OpeningDoomed D.LQ D.R (qIn D z.1.1.1.1.1) (cacheOfTr z.2)

/-- The wiring opening accepts while the wiring claim is false. -/
def WDd (z : DOut F) : Prop :=
  z.1.1.2 = true ∧ ¬ wiringClaim P z.1.1.1.1.1.ch.t z.1.1.1.1.1.π.v.2

/-- The deployed verifier accepts: its own check and the three openings. -/
def AcceptedD (z : DOut F) : Prop :=
  reductionCheck P z.1.1.1.1.1.ch.α z.1.1.1.1.1.ch.β z.1.1.1.1.1.ch.t z.1.1.1.1.1.π.v.1
    z.1.1.1.1.1.π.v.2 ∧ z.1.1.1.1.2 = true ∧ z.1.1.2 = true ∧ z.1.2 = true

/-- **Knowledge soundness is broken**: the deployed verifier accepts while the adversary's
extractor's list holds no witness of the statement. -/
def BreaksD (c₁ : TableCode B.Msg₁) (z : DOut F) : Prop :=
  AcceptedD (P := P) z ∧ ∀ g ∈ adversaryExtractor c₁ z.1.1.1.1.1.tA z.1.1.1.1.1.π,
    ¬ P.Sat (W.decode z.1.1.1.1.1.π.stmt) (P.cells g.1)

/-! ## The openings' terms are `ours_sound`'s -/

theorem readsInl_openingDoomed {α : Type} (L : Layout) (R : ℕ)
    (f : α → (Digest × Stmt L.stacking) × Proof) :
    ReadsInl fun (a : α) (b : Bool) (c : KeccakCalls.QueryCache) =>
      b = true ∧ OpeningDoomed L R (f a) c := by
  intro a b c c' h
  have hc : (fun x => c (.inl x)) = fun x => c' (.inl x) := funext h
  simp only [OpeningDoomed, hc]

theorem isTotalQueryBound_DA (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) : IsTotalQueryBound (DA W A) (Q + 6) := by
  have h : ∀ pt : (RootProof F × OpenProofs) × Transcript, IsTotalQueryBound
      (chainWith W hash256 pt.1.1 >>= fun ch =>
        (pure ⟨pt.1.1, pt.1.2, pt.2, ch⟩ : OracleComp KeccakCalls (S0 F))) (6 + 0) :=
    fun pt => isTotalQueryBound_bind (chain_queryBound_kc W pt.1.1) fun ch =>
      (trivial : IsTotalQueryBound (pure ⟨pt.1.1, pt.1.2, pt.2, ch⟩ :
        OracleComp KeccakCalls (S0 F)) 0)
  have := isTotalQueryBound_bind (isTotalQueryBound_loggedKC_run A Q [] hQ) h
  rwa [Nat.add_zero] at this

set_option maxHeartbeats 2000000 in
/-- **The witness opening's term is `ours_sound`'s** for the adversary that runs the protocol up
to it. -/
theorem prEvent_EW_le (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : IsTotalQueryBound A Q) (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows)
    (hLw : D.Lw = witnessLayout r ∨ D.Lw = wiringLayout r ∨ D.Lw = quotientLayout r)
    (hR : D.R = logInvRate) :
    Pr{let z ← (simulateQ randomOracle (deployedExp W D A)).run' ∅}[EW D z] ≤
      openingBound (Q + 6) := by
  have hs := ours_sound r h1 h2 D.Lw hLw ((wIn D) <$> DA W A) (Q + 6)
    ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_DA W A Q hQ))
  rw [romExperiment_map, prEvent_map, ← hR] at hs
  calc Pr{let z ← (simulateQ randomOracle (deployedExp W D A)).run' ∅}[EW D z]
      = Pr{let z ← (simulateQ randomOracle (midσ W D A >>= fun y => (y, ·) <$>
          ourVerifier D.LQ D.R (qIn D y.1.1.1))).run' ∅}[
          z.1.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1.1.1) (cacheOfTr z.1.1.2)] :=
        prEvent_run'_loggedKC (midσ W D A >>= fun y => (y, ·) <$>
          ourVerifier D.LQ D.R (qIn D y.1.1.1)) [] ∅
          fun w : (((S0 F × Bool) × Transcript) × Bool) × Bool =>
            w.1.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D w.1.1.1.1) (cacheOfTr w.1.1.2)
    _ = Pr{let z ← (simulateQ randomOracle (midσ W D A)).run' ∅}[
          z.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1.1) (cacheOfTr z.1.2)] :=
        prEvent_run'_bind_keep (midσ W D A) (fun y => ourVerifier D.LQ D.R (qIn D y.1.1.1)) ∅
          fun y : ((S0 F × Bool) × Transcript) × Bool =>
            y.1.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D y.1.1.1) (cacheOfTr y.1.2)
    _ = Pr{let z ← (simulateQ randomOracle (innerW W D A)).run' ∅}[
          z.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1) (cacheOfTr z.2)] :=
        prEvent_run'_bind_keep (innerW W D A) (fun x => ourVerifier D.Lσ D.R (σIn D x.1.1)) ∅
          fun x : (S0 F × Bool) × Transcript =>
            x.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D x.1.1) (cacheOfTr x.2)
    _ = Pr{let z ← romExperiment (DA W A) (fun a => ourVerifier D.Lw D.R (wIn D a))}[
          z.1.2 = true ∧ OpeningDoomed D.Lw D.R (wIn D z.1.1) z.2] :=
        prEvent_loggedPrefix (DA W A) (fun a => ourVerifier D.Lw D.R (wIn D a))
          (fun a b c => b = true ∧ OpeningDoomed D.Lw D.R (wIn D a) c)
          (readsInl_openingDoomed D.Lw D.R (wIn D))
    _ ≤ openingBound (Q + 6) := hs

theorem isTotalQueryBound_midσ (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q QO : ℕ)
    (hQ : IsTotalQueryBound A Q)
    (hO : ∀ (L : Layout) w, IsTotalQueryBound (ourVerifier L D.R w) QO) :
    IsTotalQueryBound (midσ W D A) (Q + 6 + QO + QO) := by
  have hin : IsTotalQueryBound (innerW W D A) (Q + 6 + QO) := by
    refine isTotalQueryBound_loggedKC_run _ _ _ ?_
    exact isTotalQueryBound_bind (ob := fun a => (a, ·) <$> ourVerifier D.Lw D.R (wIn D a))
      (isTotalQueryBound_DA W A Q hQ) fun a =>
        (isQueryBound_map_iff (ourVerifier D.Lw D.R (wIn D a)) (fun b => (a, b)) QO _ _).mpr
          (hO D.Lw (wIn D a))
  exact isTotalQueryBound_bind (ob := fun x => (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1)) hin
    fun x => (isQueryBound_map_iff (ourVerifier D.Lσ D.R (σIn D x.1.1)) (fun b => (x, b)) QO _
      _).mpr (hO D.Lσ _)

set_option maxHeartbeats 2000000 in
/-- **The quotient opening's term is `ours_sound`'s** for the adversary that runs the protocol up
to it. -/
theorem prEvent_EQ_le (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q QO : ℕ)
    (hQ : IsTotalQueryBound A Q)
    (hO : ∀ (L : Layout) w, IsTotalQueryBound (ourVerifier L D.R w) QO)
    (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows)
    (hLQ : D.LQ = witnessLayout r ∨ D.LQ = wiringLayout r ∨ D.LQ = quotientLayout r)
    (hR : D.R = logInvRate) :
    Pr{let z ← (simulateQ randomOracle (deployedExp W D A)).run' ∅}[EQ D z] ≤
      openingBound (Q + 6 + QO + QO) := by
  have hs := ours_sound r h1 h2 D.LQ hLQ ((fun y => qIn D y.1.1.1) <$> midσ W D A)
    (Q + 6 + QO + QO)
    ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_midσ W D A Q QO hQ hO))
  rw [romExperiment_map, prEvent_map, ← hR] at hs
  calc Pr{let z ← (simulateQ randomOracle (deployedExp W D A)).run' ∅}[EQ D z]
      = Pr{let z ← romExperiment (midσ W D A) (fun y => ourVerifier D.LQ D.R (qIn D y.1.1.1))}[
          z.1.2 = true ∧ OpeningDoomed D.LQ D.R (qIn D z.1.1.1.1.1) z.2] :=
        prEvent_loggedPrefix (midσ W D A)
          (fun y : ((S0 F × Bool) × Transcript) × Bool => ourVerifier D.LQ D.R (qIn D y.1.1.1))
          (fun (y : ((S0 F × Bool) × Transcript) × Bool) b c =>
            b = true ∧ OpeningDoomed D.LQ D.R (qIn D y.1.1.1) c)
          (readsInl_openingDoomed D.LQ D.R
            fun y : ((S0 F × Bool) × Transcript) × Bool => qIn D y.1.1.1)
    _ ≤ openingBound (Q + 6 + QO + QO) := hs

/-! ## The decoders and the claims -/

/-- **The witness table's decoder and claims**: the decoder lists every candidate of mumbai's
extraction, read back as F1's first message (`read`), and a candidate whose table satisfies the
witness opening's claims reads back as a message satisfying F1's witness claim. -/
structure WitnessMatch (c₁ : TableCode B.Msg₁) where
  read : Column D.Lw.logN → B.Msg₁
  height : c₁.height = rootHeight D.Lw.logN D.R
  leaf : c₁.leafLen = 8 * 2 ^ laneFold
  complete : ∀ (w : Fin (2 ^ c₁.height) → Option (List UInt8)) (q : Column D.Lw.logN),
    q ∈ Candidates D.Lw.logN D.R (code₀ D.Lw.logN D.R).thr
      (wordOfMerkle c₁.height (2 ^ laneFold) w) → read q ∈ c₁.dec w
  claims : ∀ (π : RootProof F) (ch : Chals F) (q : Column D.Lw.logN),
    (∀ cl ∈ (D.clW π ch).claims, D.Lw.tableEval q cl.point = cl.value) →
      witnessClaim (read q).1 ch.t ch.ρ π.v.1

/-- **The quotient table's decoder and claims**, as `WitnessMatch` for the second message and
the two quotient claims. -/
structure QuotientMatch (c₂ : TableCode B.Msg₂) where
  read : Column D.LQ.logN → B.Msg₂
  height : c₂.height = rootHeight D.LQ.logN D.R
  leaf : c₂.leafLen = 8 * 2 ^ laneFold
  complete : ∀ (w : Fin (2 ^ c₂.height) → Option (List UInt8)) (q : Column D.LQ.logN),
    q ∈ Candidates D.LQ.logN D.R (code₀ D.LQ.logN D.R).thr
      (wordOfMerkle c₂.height (2 ^ laneFold) w) → read q ∈ c₂.dec w
  claims : ∀ (π : RootProof F) (ch : Chals F) (q : Column D.LQ.logN),
    (∀ cl ∈ (D.clQ π ch).claims, D.LQ.tableEval q cl.point = cl.value) →
      quotientClaims P (W.decode π.stmt) (read q).1 ch.α ch.β ch.γ ch.t π.v.1 π.v.2 ch.ρ

/-! ## Runs against a table -/

theorem run_keep {α β : Type} (mx : OracleComp KeccakCalls α) (g : α → OracleComp KeccakCalls β)
    (T : KTable) :
    tableQueryLog (mx >>= fun x => (x, ·) <$> g x) T =
        tableQueryLog mx T ++ tableQueryLog (g (evalWithAnswerFn (QueryImpl.ofFn T) mx)) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (mx >>= fun x => (x, ·) <$> g x) =
        (evalWithAnswerFn (QueryImpl.ofFn T) mx,
          evalWithAnswerFn (QueryImpl.ofFn T) (g (evalWithAnswerFn (QueryImpl.ofFn T) mx))) := by
  constructor
  · rw [tableQueryLog_bind, map_eq_bind_pure_comp, tableQueryLog_bind, Function.comp_apply,
      tableQueryLog_pure, List.append_nil]
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_map]

theorem run_logged {α : Type} (v : OracleComp KeccakCalls α) (T : KTable) :
    tableQueryLog ((simulateQ logImplKC v).run []) T = tableQueryLog v T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) ((simulateQ logImplKC v).run []) =
        (evalWithAnswerFn (QueryImpl.ofFn T) v, (tableQueryLog v T).filterMap inlEntry) := by
  refine ⟨log_loggedKC_run T v [], ?_⟩
  have := eval_loggedKC_run T v []
  rwa [List.nil_append] at this

/-- The adversary and the chain against a table. -/
theorem DA_run (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (T : KTable) :
    let p := evalWithAnswerFn (QueryImpl.ofFn T) A
    let x₀ := W.label p.1.stmt
    let x₁ := Wire.afterRoot (viewT T x₀) p.1.r₁
    let x₂ := (viewT T x₁).toList
    let x₃ := (viewT T x₂).toList
    let x₄ := Wire.afterRoot (viewT T x₃) p.1.r₂
    let x₅ := W.afterValues (viewT T x₄) p.1.v
    (tableQueryLog (DA W A) T).map Sigma.fst =
        (tableQueryLog A T).map Sigma.fst ++
          [.inl x₀, .inl x₁, .inl x₂, .inl x₃, .inl x₄, .inl x₅] ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (DA W A) =
        ⟨p.1, p.2, (tableQueryLog A T).filterMap inlEntry,
          ⟨W.chal (viewT T x₁), W.chal (viewT T x₂), W.chal (viewT T x₃), W.chal (viewT T x₄),
            W.chal (viewT T x₅)⟩⟩ := by
  intro p x₀ x₁ x₂ x₃ x₄ x₅
  obtain ⟨hl, he⟩ := run_logged A T
  have hl' : tableQueryLog (loggedKC A) T = tableQueryLog A T := hl
  have he' : evalWithAnswerFn (QueryImpl.ofFn T) (loggedKC A) =
      (p, (tableQueryLog A T).filterMap inlEntry) := he
  constructor
  · unfold DA
    rw [tableQueryLog_bind, hl', he']
    simp only [chainWith, hash256, callKeccak256, bind_assoc, pure_bind,
      tableQueryLog_bind, tableQueryLog_pure, List.map_append, List.append_nil,
      evalWithAnswerFn_liftM_query]
    rfl
  · unfold DA
    rw [evalWithAnswerFn_bind, he']
    simp only [chainWith, hash256, callKeccak256, bind_assoc, pure_bind,
      evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
    rfl

/-- A transcript of a run against a table answers as the table, on the Keccak-256 inputs the run
asked. -/
theorem lookTr_filterMap (T : KTable) (x : List UInt8) :
    ∀ l : List ((d : List UInt8 ⊕ KeccakState) × KeccakCalls d), (∀ q ∈ l, q.2 = T q.1) →
      lookTr (l.filterMap inlEntry) x =
        if x ∈ (l.map Sigma.fst).filterMap Sum.getLeft? then
          some (LeanVM.Digest.ofRpm (viewT T x)) else none
  | [], _ => by simp [lookTr]
  | ⟨d, u⟩ :: l, h => by
    have ih := lookTr_filterMap T x l fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hu : u = T d := h ⟨d, u⟩ List.mem_cons_self
    cases d with
    | inr s =>
      rw [List.filterMap_cons_none (rfl : inlEntry ⟨.inr s, u⟩ = none)]
      simpa using ih
    | inl y =>
      simp only [List.filterMap_cons, inlEntry, List.map_cons, Sum.getLeft?_inl, List.mem_cons]
      by_cases hxy : y = x
      · subst hxy
        subst hu
        simp [lookTr]
        rfl
      · have : lookTr ((y, toB u) :: l.filterMap inlEntry) x = lookTr (l.filterMap inlEntry) x := by
          simp [lookTr, hxy]
        rw [this, ih]
        simp [Ne.symm hxy]

/-! ## The trace -/

theorem candidates_congr {μ R A' : ℕ} {W₁ W₂ : Word}
    (h : ∀ v < 2 ^ (μ - laneBits + R), W₁ v = W₂ v) :
    Candidates μ R A' W₁ = Candidates μ R A' W₂ := by
  ext q
  simp only [Candidates, Set.mem_ofPred_eq]
  have hA : ∀ S, Agrees μ R W₁ q S ↔ Agrees μ R W₂ q S := fun S => by
    unfold Agrees laneOf
    constructor
    · intro hA v hv u
      rw [← h v v.isLt]
      exact hA v hv u
    · intro hA v hv u
      rw [h v v.isLt]
      exact hA v hv u
  simp only [hA]

omit D in
/-- No collision: the table is injective on the log. -/
theorem injOn_of_not_freshBad {L : List (List UInt8)} {T : Table}
    {C₁ : ListCommit B.Msg₁} {C₂ : ListCommit B.Msg₂}
    (hnb : ¬ FreshBad (listBad W C₁ C₂) T ∅ L) : Set.InjOn T ↑L.toFinset := by
  have nb : ∀ y ∈ L, ¬ listBad W C₁ C₂ (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad W C₁ C₂) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz hyz
  have hy' := List.mem_toFinset.mp hy
  have hz' := List.mem_toFinset.mp hz
  by_contra hne
  rcases before_trichotomy L y z hy' hz' hne with h | h
  · exact nb z hz' (Or.inl (Or.inl ⟨y, h, hyz⟩))
  · exact nb y hy' (Or.inl (Or.inl ⟨z, h, hyz.symm⟩))

/-- The history of a logged stage's transcript, as `ansOf`. -/
theorem cacheOfTr_eq_ansOf (T : KTable) (l : List ((d : List UInt8 ⊕ KeccakState) × KeccakCalls d))
    (hl : ∀ q ∈ l, q.2 = T q.1) :
    (fun x => cacheOfTr (l.filterMap inlEntry) (.inl x)) =
      ansOf ((l.map Sigma.fst).filterMap Sum.getLeft?).toFinset (viewT T) := by
  funext x
  rw [cacheOfTr_inl, lookTr_filterMap T x l hl]
  unfold ansOf
  simp only [List.mem_toFinset]

open Classical in
/-- **The trace of the deployed run**: on every table of both oracles, a run that breaks
knowledge soundness while neither the witness nor the quotient opening is doomed at its end and
the wiring claim holds asks a bad fresh query. -/
theorem trace_deployed (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) (mW : WitnessMatch D c₁)
    (mQ : QuotientMatch W D c₂) (A : OracleComp KeccakCalls (RootProof F × OpenProofs))
    (T : KTable)
    (hev : BreaksD W c₁ (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)) ∧
      ¬ EW D (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)) ∧
      ¬ WDd (P := P) (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)) ∧
      ¬ EQ D (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A))) :
    FreshBad (advBad W c₁.commit c₂.commit A) T ∅
      ((tableQueryLog (deployedExp W D A) T).map Sigma.fst) := by
  -- The runs, stage by stage.
  obtain ⟨hLda, hEda⟩ := DA_run W A T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set π := p.1
  set a := evalWithAnswerFn (QueryImpl.ofFn T) (DA W A)
  obtain ⟨h1l, h1e⟩ := run_keep (DA W A) (fun a => ourVerifier D.Lw D.R (wIn D a)) T
  obtain ⟨h2l, h2e⟩ := run_logged (DA W A >>= fun a => (a, ·) <$> ourVerifier D.Lw D.R (wIn D a)) T
  have hI : innerW W D A =
      (simulateQ logImplKC (DA W A >>= fun a => (a, ·) <$> ourVerifier D.Lw D.R (wIn D a))).run [] :=
    rfl
  obtain ⟨h3l, h3e⟩ := run_keep (innerW W D A) (fun x => ourVerifier D.Lσ D.R (σIn D x.1.1)) T
  have hM : midσ W D A = innerW W D A >>= fun x => (x, ·) <$> ourVerifier D.Lσ D.R (σIn D x.1.1) :=
    rfl
  obtain ⟨h4l, h4e⟩ := run_keep (midσ W D A) (fun y => ourVerifier D.LQ D.R (qIn D y.1.1.1)) T
  obtain ⟨h5l, h5e⟩ := run_logged (midσ W D A >>= fun y => (y, ·) <$>
    ourVerifier D.LQ D.R (qIn D y.1.1.1)) T
  have hD : deployedExp W D A = (simulateQ logImplKC (midσ W D A >>= fun y => (y, ·) <$>
      ourVerifier D.LQ D.R (qIn D y.1.1.1))).run [] := rfl
  set lA := tableQueryLog A T
  set lDA := tableQueryLog (DA W A) T
  set lW := tableQueryLog (ourVerifier D.Lw D.R (wIn D a)) T
  set lWfull := tableQueryLog (DA W A >>= fun a => (a, ·) <$> ourVerifier D.Lw D.R (wIn D a)) T
  set lfull := tableQueryLog (deployedExp W D A) T
  have hlWfull : lWfull = lDA ++ lW := h1l
  -- The outcome.
  have hlfull : lfull = tableQueryLog (midσ W D A >>= fun y => (y, ·) <$>
      ourVerifier D.LQ D.R (qIn D y.1.1.1)) T := by
    show tableQueryLog (deployedExp W D A) T = _
    rw [hD]
    exact h5l
  set z := evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)
  have hz1 : z.1 = evalWithAnswerFn (QueryImpl.ofFn T) (midσ W D A >>= fun y => (y, ·) <$>
      ourVerifier D.LQ D.R (qIn D y.1.1.1)) := by
    show (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)).1 = _
    rw [hD, h5e]
  have hz2 : z.2 = lfull.filterMap inlEntry := by
    show (evalWithAnswerFn (QueryImpl.ofFn T) (deployedExp W D A)).2 = _
    rw [hD, h5e, hlfull]
  have hz11 : z.1.1 = evalWithAnswerFn (QueryImpl.ofFn T) (midσ W D A) := by
    rw [hz1, h4e]
  have hmid : evalWithAnswerFn (QueryImpl.ofFn T) (midσ W D A) =
      (evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A),
        evalWithAnswerFn (QueryImpl.ofFn T)
          (ourVerifier D.Lσ D.R (σIn D (evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A)).1.1))) := by
    rw [hM]
    exact h3e
  have hinner : evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A) =
      ((a, evalWithAnswerFn (QueryImpl.ofFn T) (ourVerifier D.Lw D.R (wIn D a))),
        lWfull.filterMap inlEntry) := by
    rw [hI, h2e, h1e]
  have hza : z.1.1.1.1.1 = a := by
    rw [hz11, hmid, hinner]
  have hzW : z.1.1.1.2 = lWfull.filterMap inlEntry := by
    rw [hz11, hmid, hinner]
  have hzQ : z.2 = lfull.filterMap inlEntry := hz2
  -- The full log: the adversary's, the chain's, the witness opening's, then the rest.
  have hlmid : tableQueryLog (midσ W D A) T = lWfull ++
      tableQueryLog (ourVerifier D.Lσ D.R
        (σIn D (evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A)).1.1)) T := by
    rw [hM, h3l, hI, h2l]
  set rest := tableQueryLog (ourVerifier D.Lσ D.R
        (σIn D (evalWithAnswerFn (QueryImpl.ofFn T) (innerW W D A)).1.1)) T ++
      tableQueryLog (ourVerifier D.LQ D.R
        (qIn D (evalWithAnswerFn (QueryImpl.ofFn T) (midσ W D A)).1.1.1)) T
  have hrest : lfull = lWfull ++ rest := by
    rw [hlfull, h4l, hlmid, List.append_assoc]
  set Lk := lfull.map Sigma.fst
  set L := Lk.filterMap Sum.getLeft?
  set LA := (lA.map Sigma.fst).filterMap Sum.getLeft?
  set HW := (lWfull.map Sigma.fst).filterMap Sum.getLeft?
  set rW := (rest.map Sigma.fst).filterMap Sum.getLeft?
  have hLHW : L = HW ++ rW := by
    simp only [L, Lk, HW, rW, hrest, List.map_append, List.filterMap_append]
  set x₀ := W.label π.stmt
  set x₁ := Wire.afterRoot (viewT T x₀) π.r₁
  set x₂ := (viewT T x₁).toList
  set x₃ := (viewT T x₂).toList
  set x₄ := Wire.afterRoot (viewT T x₃) π.r₂
  set x₅ := W.afterValues (viewT T x₄) π.v
  set rd := (lW.map Sigma.fst).filterMap Sum.getLeft?
  have hHWA : HW = LA ++ ([x₀, x₁, x₂, x₃, x₄, x₅] ++ rd) := by
    simp only [HW, LA, rd, hlWfull, List.map_append, hLda, List.filterMap_append]
    rw [show [(Sum.inl x₀ : List UInt8 ⊕ KeccakState), .inl x₁, .inl x₂, .inl x₃, .inl x₄,
        .inl x₅] = [x₀, x₁, x₂, x₃, x₄, x₅].map Sum.inl from rfl, filterMap_getLeft?_map_inl,
      List.append_assoc]
  -- The adversary's transcript and the stage transcripts read as the table.
  set tA := lA.filterMap inlEntry
  have hsndA : ∀ q ∈ lA, q.2 = T q.1 := tableQueryLog_snd_dep T A
  have hsndW : ∀ q ∈ lWfull, q.2 = T q.1 := tableQueryLog_snd_dep T _
  have hsndF : ∀ q ∈ lfull, q.2 = T q.1 := tableQueryLog_snd_dep T _
  have hA_H : histOfTr tA = LA.toFinset := by
    simp only [histOfTr, tA, LA, map_fst_filterMap_inlEntry]
  have hA_T : ∀ d ∈ histOfTr tA, tableOfTr tA d = viewT T d := by
    intro d hd
    refine tableOfTr_eq (viewT T) tA (fun e he => ?_) d (by simpa [histOfTr] using hd)
    obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he
    obtain ⟨d', u⟩ := q
    cases d' with
    | inl x =>
      simp only [inlEntry, Option.some.injEq] at hqe
      subst hqe
      have := hsndA _ hq
      simp only at this
      simp [viewT, this]
    | inr s => simp [inlEntry] at hqe
  -- The event.
  obtain ⟨⟨⟨hchk, hbW, hbσ, hbQ⟩, hsat⟩, hEW, hWD, hEQ⟩ := hev
  unfold EW at hEW
  unfold WDd at hWD
  unfold EQ at hEQ
  rw [hza] at hchk hsat hEW hWD hEQ
  rw [hzW] at hEW
  rw [hzQ] at hEQ
  have hπa : a.π = π := by rw [hEda]
  have htAa : a.tA = tA := by rw [hEda]
  -- No bad fresh query, from here on.
  by_contra hnb
  have hk : ¬ FreshBad (kcBad W c₁.commit c₂.commit) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBad A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBad W c₁.commit c₂.commit) (viewT T) ∅ L := fun h =>
    hk (freshBad_kc W c₁.commit c₂.commit T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := refers_before hl
  have hinj := injOn_of_not_freshBad W hl
  have hLA_L : ∀ y ∈ LA, y ∈ L := fun y hy => by
    rw [hLHW, hHWA]
    exact List.mem_append_left _ (List.mem_append_left _ hy)
  have hHW_L : ∀ y ∈ HW, y ∈ L := fun y hy => by
    rw [hLHW]
    exact List.mem_append_left _ hy
  have hLA_HW : ∀ y ∈ LA, y ∈ HW := fun y hy => by
    rw [hHWA]
    exact List.mem_append_left _ hy
  -- No fresh answer after the adversary's queries is a root it announced.
  have hLsplit : L = LA ++ (([x₀, x₁, x₂, x₃, x₄, x₅] ++ rd) ++ rW) := by
    rw [hLHW, hHWA, List.append_assoc]
  have hLk : Lk = lA.map Sigma.fst ++
      ([.inl x₀, .inl x₁, .inl x₂, .inl x₃, .inl x₄, .inl x₅] ++ (lW.map Sigma.fst ++
        rest.map Sigma.fst)) := by
    simp only [Lk, hrest, hlWfull, List.map_append, List.append_assoc]
    rw [hLda, List.append_assoc]
  have hroot : ∀ w ∈ L, (viewT T w = π.r₁ ∨ viewT T w = π.r₂) → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBad A) T ∅ Lk hr (.inl w) hwk (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    rw [hLk]
    exact subset_before_append _ _ hwA' q hq
  -- A history between the adversary's and the run's reads the adversary's word.
  have hstabW : ∀ (H : List (List UInt8)), (∀ y ∈ LA, y ∈ H) → (∀ y ∈ H, y ∈ L) →
      ∀ (r : Bytes32), (r = π.r₁ ∨ r = π.r₂) → ∀ ht ℓ,
        merkleWord H.toFinset (viewT T) ht ℓ r = merkleWord LA.toFinset (viewT T) ht ℓ r := by
    intro H hAH hHL r hr' ht ℓ
    refine merkleWord_stable (fun y hy => List.mem_toFinset.mpr (hAH y (List.mem_toFinset.mp hy)))
      (fun w hw hwr => List.mem_toFinset.mpr (hroot w (hHL w (List.mem_toFinset.mp hw)) ?_))
      (fun y hy w hw h => ?_) ht ℓ
    · rcases hr' with rfl | rfl
      · exact Or.inl hwr
      · exact Or.inr hwr
    · have hyA := List.mem_toFinset.mp hy
      have hb := hord w (hHL w (List.mem_toFinset.mp hw)) y (hLA_L y hyA) h
      rw [hLsplit, before_append_of_mem LA _ hyA] at hb
      exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  -- The adversary's extractor reads the table on the adversary's queries.
  have hext : ∀ (c : TableCode B.Msg₁), c.dec (merkleWord (histOfTr tA) (tableOfTr tA) c.height
      c.leafLen π.r₁) = c.dec (merkleWord LA.toFinset (viewT T) c.height c.leafLen π.r₁) := by
    intro c
    have := (c.commit).congr (histOfTr tA) (tableOfTr tA) (viewT T) π.r₁ hA_T
    rw [hA_H] at this ⊢
    exact this
  -- The witness opening: a candidate of its word satisfies its claims.
  have hODW : ¬ OpeningDoomed D.Lw D.R (wIn D a) (cacheOfTr (lWfull.filterMap inlEntry)) :=
    fun h => hEW ⟨hbW, h⟩
  unfold OpeningDoomed at hODW
  push Not at hODW
  obtain ⟨q, hq, hqc⟩ := hODW
  rw [cacheOfTr_eq_ansOf T lWfull hsndW] at hq
  have hwordW := candidates_congr (μ := D.Lw.logN) (R := D.R)
    (A' := (code₀ D.Lw.logN D.R).thr)
    (W₁ := Rom.extract (ansOf HW.toFinset (viewT T)) (wIn D a).1.1 (rootHeight D.Lw.logN D.R)
      (2 ^ laneFold))
    (W₂ := wordOfMerkle (rootHeight D.Lw.logN D.R) (2 ^ laneFold)
      (merkleWord HW.toFinset (viewT T) (rootHeight D.Lw.logN D.R) (8 * 2 ^ laneFold)
        (toB (wIn D a).1.1)))
    fun v hv => (wordOfMerkle_eq_extract (hinj.mono (fun y hy =>
      List.mem_toFinset.mpr (hHW_L y (List.mem_toFinset.mp hy)))) _ _ _ hv).symm
  rw [hwordW] at hq
  have hrW : toB (wIn D a).1.1 = π.r₁ := by
    simp only [wIn, hπa]
    exact LeanVM.Rpm.digestToRpm_ofRpm _
  rw [hrW, hstabW HW hLA_HW hHW_L π.r₁ (Or.inl rfl)] at hq
  have hgW := mW.complete (merkleWord LA.toFinset (viewT T) c₁.height c₁.leafLen π.r₁) q (by
    rw [mW.height, mW.leaf]
    exact hq)
  have hcW := mW.claims π (a.ch) q (by
    intro cl hcl
    have := hqc cl (by simpa [wIn, hπa] using hcl)
    exact this)
  -- The quotient opening, likewise, on the whole run's history.
  have hODQ : ¬ OpeningDoomed D.LQ D.R (qIn D a) (cacheOfTr (lfull.filterMap inlEntry)) :=
    fun h => hEQ ⟨hbQ, h⟩
  unfold OpeningDoomed at hODQ
  push Not at hODQ
  obtain ⟨q', hq', hqc'⟩ := hODQ
  rw [cacheOfTr_eq_ansOf T lfull hsndF] at hq'
  have hwordQ := candidates_congr (μ := D.LQ.logN) (R := D.R)
    (A' := (code₀ D.LQ.logN D.R).thr)
    (W₁ := Rom.extract (ansOf L.toFinset (viewT T)) (qIn D a).1.1 (rootHeight D.LQ.logN D.R)
      (2 ^ laneFold))
    (W₂ := wordOfMerkle (rootHeight D.LQ.logN D.R) (2 ^ laneFold)
      (merkleWord L.toFinset (viewT T) (rootHeight D.LQ.logN D.R) (8 * 2 ^ laneFold)
        (toB (qIn D a).1.1)))
    fun v hv => (wordOfMerkle_eq_extract hinj _ _ _ hv).symm
  rw [hwordQ] at hq'
  have hrQ : toB (qIn D a).1.1 = π.r₂ := by
    simp only [qIn, hπa]
    exact LeanVM.Rpm.digestToRpm_ofRpm _
  rw [hrQ, hstabW L hLA_L (fun y hy => hy) π.r₂ (Or.inr rfl)] at hq'
  have hgQ := mQ.complete (merkleWord LA.toFinset (viewT T) c₂.height c₂.leafLen π.r₂) q' (by
    rw [mQ.height, mQ.leaf]
    exact hq')
  have hcQ := mQ.claims π (a.ch) q' (by
    intro cl hcl
    exact hqc' cl (by simpa [qIn, hπa] using hcl))
  -- The verifier's claims hold for the two candidates; the witness candidate fails the relation.
  set g := mW.read q
  set R := mQ.read q'
  have hσc : wiringClaim P a.ch.t a.π.v.2 := by
    by_contra h
    exact hWD ⟨hbσ, h⟩
  rw [hπa] at hchk hσc
  have hacc : P.Accepts (W.decode π.stmt) g.1 R.1 a.ch.α a.ch.β a.ch.γ a.ch.t π.v.1 π.v.2 a.ch.ρ :=
    (accepts_iff _ _ _ _ _ _ _ _ _ _).mpr ⟨hcW, hσc, hchk, hcQ⟩
  have hgsat : ¬ P.Sat (W.decode π.stmt) (P.cells g.1) := by
    rw [hπa, htAa] at hsat
    refine hsat g ?_
    show g ∈ c₁.dec (merkleWord (histOfTr tA) (tableOfTr tA) c₁.height c₁.leafLen π.r₁)
    rw [hext]
    exact hgW
  -- The candidates read off the adversary's queries are those read off the run's.
  have hg : g ∈ c₁.commit.cands L.toFinset (viewT T) π.r₁ := by
    show g ∈ c₁.dec (merkleWord L.toFinset (viewT T) c₁.height c₁.leafLen π.r₁)
    rw [hstabW L hLA_L (fun y hy => hy) π.r₁ (Or.inl rfl)]
    exact hgW
  have hR : R ∈ c₂.commit.cands L.toFinset (viewT T) π.r₂ := by
    show R ∈ c₂.dec (merkleWord L.toFinset (viewT T) c₂.height c₂.leafLen π.r₂)
    rw [hstabW L hLA_L (fun y hy => hy) π.r₂ (Or.inr rfl)]
    exact hgQ
  rw [hEda] at hacc
  refine hl (trace_core W c₁.commit c₂.commit L (viewT T) π g R (fun y hy => ?_) hg hR hacc hgsat)
  rw [hLsplit]
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hy))

/-! ## Knowledge soundness of the deployed verifier -/

theorem isTotalQueryBound_deployedExp (A : OracleComp KeccakCalls (RootProof F × OpenProofs))
    (Q QO : ℕ) (hQ : IsTotalQueryBound A Q)
    (hO : ∀ (L : Layout) w, IsTotalQueryBound (ourVerifier L D.R w) QO) :
    IsTotalQueryBound (deployedExp W D A) (Q + 6 + QO + QO + QO) :=
  isTotalQueryBound_loggedKC_run _ _ _ (isTotalQueryBound_bind
    (ob := fun y : ((S0 F × Bool) × Transcript) × Bool =>
      (y, ·) <$> ourVerifier D.LQ D.R (qIn D y.1.1.1))
    (isTotalQueryBound_midσ W D A Q QO hQ hO) fun y =>
      (isQueryBound_map_iff (ourVerifier D.LQ D.R (qIn D y.1.1.1)) (fun b => (y, b)) QO _ _).mpr
        (hO D.LQ _))

/-- **Knowledge soundness of the deployed verifier in mumbai's two-oracle model**: the chain, then
`opening::verify` (F2's `ourVerifier`) for the witness, wiring and quotient tables. For every
adversary of at most `Q` queries, with every opening of at most `QO` queries, the decoders and
claims matched to F1's (`WitnessMatch`, `QuotientMatch`), and the wiring opening's term `εσ`:
the verifier accepts while the adversary's extractor's list (`adversaryExtractor`: the adversary's
queries only) holds no witness of the statement with probability at most
`openingBound (Q + 6) + εσ + openingBound (Q + 6 + 2 QO) + N (max L₁ (L₁ L₂) · roundError + 5 N / 2^256)`,
`N = Q + 6 + 3 QO`, the two `openingBound`s being F2's `ours_sound` for the witness and the
quotient opening. -/
theorem knowledgeSoundness_deployed (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂)
    (mW : WitnessMatch D c₁) (mQ : QuotientMatch W D c₂)
    (A : OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q QO : ℕ)
    (hQ : IsTotalQueryBound A Q)
    (hO : ∀ (L : Layout) w, IsTotalQueryBound (ourVerifier L D.R w) QO)
    (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows)
    (hLw : D.Lw = witnessLayout r ∨ D.Lw = wiringLayout r ∨ D.Lw = quotientLayout r)
    (hLQ : D.LQ = witnessLayout r ∨ D.LQ = wiringLayout r ∨ D.LQ = quotientLayout r)
    (hR : D.R = logInvRate) (εσ : ℝ≥0∞)
    (hσ : Pr{let z ← (simulateQ randomOracle (deployedExp W D A)).run' ∅}[WDd (P := P) z] ≤ εσ) :
    Pr{let z ← (simulateQ randomOracle (deployedExp W D A)).run' ∅}[BreaksD W c₁ z] ≤
      openingBound (Q + 6) + εσ + openingBound (Q + 6 + QO + QO) +
        ((Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) * ((listFactor c₁.commit.bound c₂.commit.bound :
          ℝ≥0∞) * (roundError P B : ℝ≥0∞) + 5 * ((Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set mx := (simulateQ randomOracle (deployedExp W D A)).run' ∅
  have hrest : Pr{let z ← mx}[BreaksD W c₁ z ∧ ¬ EW D z ∧ ¬ WDd (P := P) z ∧ ¬ EQ D z] ≤
      ((Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) * ((listFactor c₁.commit.bound c₂.commit.bound :
        ℝ≥0∞) * (roundError P B : ℝ≥0∞) +
        5 * ((Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
    refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (deployedExp W D A)
      (Q + 6 + QO + QO + QO) (isTotalQueryBound_deployedExp W D A Q QO hQ hO)
      (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
      (Set.finite_range _) _ (advBad W c₁.commit c₂.commit A) _ (fun S hS c t ht hcard => ?_)
      (fun T h => trace_deployed W D c₁ c₂ mW mQ A T h)
    have hS' : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
      fun v => hS _ ⟨v, rfl⟩
    refine (prob_advBad W c₁.commit c₂.commit A S hS' c t ht).trans ?_
    rw [add_comm]
    gcongr
    have : 4 * (cacheDom c).card + 5 ≤ 5 * (Q + 6 + QO + QO + QO) := by omega
    calc ((4 * (cacheDom c).card + 5 : ℕ) : ℝ≥0∞) ≤ ((5 * (Q + 6 + QO + QO + QO) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast this
      _ = 5 * ((Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) := by push_cast; ring
  have hsplit : ∀ z, BreaksD W c₁ z → EW D z ∨ WDd (P := P) z ∨ EQ D z ∨
      (BreaksD W c₁ z ∧ ¬ EW D z ∧ ¬ WDd (P := P) z ∧ ¬ EQ D z) := by
    intro z hb
    by_cases h1 : EW D z
    · exact Or.inl h1
    by_cases h2 : WDd (P := P) z
    · exact Or.inr (Or.inl h2)
    by_cases h3 : EQ D z
    · exact Or.inr (Or.inr (Or.inl h3))
    exact Or.inr (Or.inr (Or.inr ⟨hb, h1, h2, h3⟩))
  refine (prEvent_mono mx _ _ hsplit).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add (prEvent_EW_le W D A Q hQ r h1 h2 hLw hR) ((prEvent_or_le _ _ _).trans
    (add_le_add hσ ((prEvent_or_le _ _ _).trans (add_le_add
      (prEvent_EQ_le W D A Q QO hQ hO r h1 h2 hLQ hR) hrest))))).trans (le_of_eq ?_)
  simp only [add_assoc]

end Compose
