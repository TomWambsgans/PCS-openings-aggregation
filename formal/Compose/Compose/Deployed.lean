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

end Compose
