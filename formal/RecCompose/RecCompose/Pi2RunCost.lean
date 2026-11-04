-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's analogue of `formal/UniComplete/UniComplete/
-- ProverCost.lean`, `VerifierHCost.lean`, `Rec3ProverCost.lean` and `Rec3ProbExp.lean`'s `cost_stagedU3`, for
-- `Pi2ProbStaged`'s staged run (`pi2Staged`: the setup, π1-rec3's honest prover, π1-rec3's graph, π2's honest prover
-- `crates/leanvm_rec/src/pi2/prover.rs`, the contract `formal/RecStatement`); uses
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean` (`cost_openingWithH`, `cost_proveOpeningWithH`,
-- `qc_commitWithH`) and leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`.
import RecCompose.Pi2P1

/-!
# The block count of π2's staged run (`Pi2RunCost`)

**`pi2RunCost_p1k hD hg : Pi2RunCost D C Fa (p1k D) pi2RunN`**, **`pi2RunN_le : pi2RunN ≤ 2^50`** (`pi2RunN` is
below `2^48.0`): at the real deployment (`hD`) and the graphs' agreement (`hg`, for the graph's calls' sizes), the
staged run at π1-rec3's honest prover makes at most `pi2RunN` block calls (`hashBlocks`: a Keccak-256 of `n` bytes
`⌊n / 136⌋ + 1`, a Keccak-f[1600] one).

`pi2RunN = 2 · setup2 + 2^47 + 3 · gOpen + 2 · ivC + treeW + 1 + 6 + treeQ + 1 + 4 + openW + openS + openQ +
  (1 + 10 + 3 · 1080 + 6 · cOpen)`:

* the setup twice (`setup2`: π1's `setupCost`, π2's setup tree `treeCost 25`), π1-rec3's prover (`2^47`,
  `proverCost3_flockProve3H`);
* the graph's three `PCS_OPEN`s (`gOpen`: a call of at most `31` words, `GraphsAgree` and `RecGraph.Emitted`'s calls),
  π2's IV twice (`ivC`: `σ`'s `4 · 2^24` bytes, `κ`'s `8 · 2^24`, the encoding's `25184 + 64`, the IV's `208`), the
  seed (`80` bytes), `W`'s tree (`treeCost 24`);
* the chain (`536`, `32`, `32` bytes), `Q`'s tree (`treeCost 28`), `t` (`64` bytes), `ρ` (`440` bytes);
* π2's prover's three openings (`openW`, `openS`, `openQ`: E2ECompleteness's `cost_proveOpeningWithH`);
* the contract on π2's honest stream (at most `1080` bytes): its seed, its walk (`10` blocks beyond the channel's
  potential `3 · 1080`, UniComplete's `CC` calculus), its six openings (`cOpen`: a claim count of at most `2`, at most
  `255` variables, every call's third word a count `numberWord 1` or `numberWord 2`).

The calculus: `CP X c P` (at most `c` block calls, every outcome satisfying `P`, any budget beyond left over), on
UniComplete's `CostP`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open RecStatement
open UniStatement (Chan ChanM)
open E2ECompleteness.Cost (QC qc_pure qc_H qc_H_le qc_commitWithH treeCost vOpen blockFactor)
open UniComplete.Cost (CostP costP_query_bind costP_of_qc CC cc_bind cc_mono cc_seq cc_free cc_pure cc_forIn_list
  cc_sampleH cc_nextScalar cc_nextInteger cc_nextRoot cc_nextScalars cc_finish len_digestBytes pot Inv)
open LeanVM.Protocol.Verifier (whirBound costHeight)

namespace RecCompose.Pi2G

namespace Cost2

/-! ## Costs with a postcondition and any budget left over -/

/-- **At most `c` block calls**, every outcome satisfying `P`, any extra budget left over. -/
def CP {α : Type} (X : OracleComp KeccakCalls α) (c : ℕ) (P : α → Prop) : Prop :=
  ∀ m, CostP X (c + m) fun a r ↦ P a ∧ m ≤ r

section Calculus

variable {α β : Type}

theorem costP_budget {X : OracleComp KeccakCalls α} {n n' m : ℕ} {P : α → Prop}
    (h : CostP X n fun a r ↦ P a ∧ m ≤ r) (hn : n ≤ n') : CostP X n' fun a r ↦ P a ∧ m ≤ r := by
  induction X using OracleComp.inductionOn generalizing n n' with
  | pure a => exact ⟨h.1, h.2.trans hn⟩
  | query_bind t k ih =>
    rw [costP_query_bind] at h ⊢
    exact ⟨h.1.trans hn, fun u ↦ ih u (h.2 u) (by omega)⟩

theorem CP.bind {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {c₁ c₂ : ℕ} {P : α → Prop}
    {Q : β → Prop} (hX : CP X c₁ P) (hf : ∀ a, P a → CP (f a) c₂ Q) : CP (X >>= f) (c₁ + c₂) Q := by
  intro m
  rw [show c₁ + c₂ + m = c₁ + (c₂ + m) by omega]
  exact UniComplete.Cost.CostP.bind (hX (c₂ + m)) fun a r h ↦ costP_budget (hf a h.1 m) h.2

theorem CP.mono {X : OracleComp KeccakCalls α} {c c' : ℕ} {P P' : α → Prop} (h : CP X c P) (hc : c ≤ c')
    (hP : ∀ a, P a → P' a) : CP X c' P' := by
  intro m
  have h1 := h (m + (c' - c))
  rw [show c + (m + (c' - c)) = c' + m by omega] at h1
  exact UniComplete.Cost.CostP.mono h1 fun a r h ↦ ⟨hP a h.1, by omega⟩

theorem cp_of_qc {X : OracleComp KeccakCalls α} {c : ℕ} (h : QC X c) : CP X c fun _ ↦ True :=
  fun m ↦ UniComplete.Cost.CostP.mono (costP_of_qc h m) fun _ _ hr ↦ ⟨trivial, hr⟩

theorem cp_pure (a : α) {P : α → Prop} (h : P a) : CP (pure a : OracleComp KeccakCalls α) 0 P :=
  fun m ↦ ⟨h, Nat.le_add_left m 0⟩

theorem CP.toQC {X : OracleComp KeccakCalls α} {c : ℕ} {P : α → Prop} (h : CP X c P) : QC X c := by
  have h0 := h 0
  rw [Nat.add_zero] at h0
  exact UniComplete.Cost.CostP.toQC h0

theorem cp_H (x : List UInt8) : CP (callKeccak256 x) (x.length / 136 + 1) fun _ ↦ True := cp_of_qc (qc_H x)

/-- A hash of fewer than `136 · k` bytes, at most `k` blocks. -/
theorem cp_H_le {x : List UInt8} {k : ℕ} (hx : x.length < 136 * k) : CP (callKeccak256 x) k fun _ ↦ True :=
  cp_of_qc (qc_H_le hx)

theorem CP.bind_le {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {c₁ c₂ c : ℕ} {P : α → Prop}
    {Q : β → Prop} (hX : CP X c₁ P) (hf : ∀ a, P a → CP (f a) c₂ Q) (h : c₁ + c₂ ≤ c) : CP (X >>= f) c Q :=
  (hX.bind hf).mono h fun _ h ↦ h

/-- A loop whose steps on the list's elements cost at most `c` each. -/
theorem qc_forIn_mem {γ : Type} (l : List γ) (b : β) (f : γ → β → OracleComp KeccakCalls (ForInStep β)) {c : ℕ}
    (hf : ∀ a ∈ l, ∀ s, QC (f a s) c) : QC (forIn l b f) (l.length * c) := by
  induction l generalizing b with
  | nil => exact qc_pure _ _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (hf a List.mem_cons_self b).bind_le (b := l.length * c) (fun s ↦ ?_) (by simp [Nat.succ_mul]; omega)
    cases s with
    | done b => exact qc_pure _ _
    | yield b => exact ih b (fun a ha ↦ hf a (List.mem_cons_of_mem _ ha))

end Calculus

/-! ## Lengths -/

theorem length_flatMap_const {γ δ : Type} (f : γ → List δ) (k : ℕ) (hf : ∀ x, (f x).length = k) :
    ∀ l : List γ, (l.flatMap f).length = k * l.length
  | [] => by simp
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f k hf l, List.length_cons]
    ring

theorem length_le64 (n : ℕ) : (le64 n).length = 8 := by simp [le64]

theorem length_layoutWord (code m : ℕ) (L : PcsQuotient.Layout) : (layoutWord code m L).length = 32 := by
  unfold layoutWord
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate, List.length_map,
    List.length_range]
  decide +kernel

theorem length_pi1Iv (s : UniStatement.Shape) (programIv : List UInt8) (roots : UniStatement.SetupRoots) :
    (pi1Iv s programIv roots).length = 32 := by
  unfold pi1Iv pi1IvWith UniStatement.contractIvForWith
  dsimp only
  split
  · simp [UniStatement.contractIvWith, len_digestBytes]
  · simp [len_digestBytes]

theorem name_length : RecStatement.name.length = 16 := by decide +kernel

theorem ivTag_length : RecStatement.ivTag.length = 16 := by decide +kernel

theorem encoding_length : Data.circuit.encoding.length = 25184 := by decide +kernel

theorem programIv_length : UniStatement.programIv.length = 32 := by decide +kernel

/-! ## The setup, the IV, the seed -/

/-- The setup's blocks: π1's three trees, π2's setup tree (`2^25` words). -/
noncomputable def setup2 (D : RecDeployment) : ℕ := UniComplete.Cost.setupCost D.pi1 + treeCost 25

theorem circuit_logN {D : RecDeployment} (hD : D.Real) (roots : UniStatement.SetupRoots) :
    (D.circuitAt roots).circuit.logN = 24 := by
  rw [RecDeployment.circuitAt, hD.1]
  rfl

theorem qc_setupTreesWithH2 {D : RecDeployment} (hD : D.Real) :
    QC (Pi2H.setupTreesWithH callKeccak256 callKeccakF1600 D) (setup2 D) := by
  unfold Pi2H.setupTreesWithH Pi2H.setupTreeWithH setup2
  refine E2ECompleteness.Cost.QC.bind_le (b := treeCost 25) (UniComplete.Cost.cost_setupTreesWithH D.pi1)
    (fun t1 ↦ E2ECompleteness.Cost.QC.bind_le (c := treeCost 25) (qc_commitWithH _ _) (fun _ ↦ qc_pure _ 0) ?_)
    le_rfl
  rw [circuit_logN hD]
  decide

/-- π2's IV's blocks: `σ`'s `4 · 2^24` bytes, `κ`'s `8 · 2^24`, the encoding and the two digests, the IV's preimage. -/
noncomputable def ivC : ℕ := (4 * 2 ^ 24) / 136 + 1 + ((8 * 2 ^ 24) / 136 + 1) + ((25184 + 64) / 136 + 1) + (208 / 136 + 1)

theorem cp_ivOfH {D : RecDeployment} (hD : D.Real) (roots : RecSetupRoots) :
    CP (Pi2H.ivOfH callKeccak256 D roots) ivC fun iv ↦ iv.length = 32 := by
  have hc : (D.circuitAt roots.pi1).circuit = Data.circuit := by rw [RecDeployment.circuitAt, hD.1]
  have hn : (D.circuitAt roots.pi1).n = 2 ^ 24 := by rw [Pi2Circuit.n, hc]; rfl
  unfold Pi2H.ivOfH Pi2H.digestWithH Pi2H.ivWithH
  simp only [bind_assoc, pure_bind]
  refine CP.bind_le (cp_H_le (k := (4 * 2 ^ 24) / 136 + 1) ?_) (fun _ _ ↦
    CP.bind_le (cp_H_le (k := (8 * 2 ^ 24) / 136 + 1) ?_) (fun _ _ ↦
    CP.bind_le (cp_H_le (k := (25184 + 64) / 136 + 1) ?_) (fun _ _ ↦
    CP.bind_le (cp_H_le (k := 208 / 136 + 1) ?_) (fun _ _ ↦ cp_pure _ (len_digestBytes _)) le_rfl) le_rfl) le_rfl)
    (by unfold ivC; omega)
  · rw [length_flatMap_const _ 4 (fun i ↦ by simp [length_le64]), List.length_range, hn]
    omega
  · rw [length_flatMap_const _ 8 (fun i ↦ length_le64 _), List.length_range, hn]
    omega
  · simp only [List.length_append, len_digestBytes, hc, encoding_length]
    omega
  · simp only [List.length_append, ivTag_length, len_digestBytes, RecDeployment.pi1IvAt, length_pi1Iv,
      layoutWords, length_layoutWord]
    omega

/-! ## π2's prover's stream -/

theorem run_sendRoot2 (h : E × E) (s : UniComplete.Wr) :
    (UniComplete.sendRoot (m := OracleComp KeccakCalls) h).run s =
      pure ((), { s with stream := s.stream ++ (UniStatement.rootWord h).toArray }) := rfl

theorem run_sendScalars2 (xs : List E) (s : UniComplete.Wr) :
    (UniComplete.sendScalars (m := OracleComp KeccakCalls) xs).run s =
      pure ((), { s with stream := s.stream ++ (xs.flatMap UniComplete.scalarWire).toArray }) := rfl

/-- **The public values' writes**: the state grows by their bytes. -/
theorem run_sendPublic : ∀ (l : List (Read × PublicValue)) (s : UniComplete.Wr),
    ∃ s' : UniComplete.Wr, (sendPublic (m := OracleComp KeccakCalls) l).run s = pure ((), s') ∧
      s'.absorbed = s.absorbed ∧ s'.stream.size = s.stream.size + (Pi2S.publicWire l).length
  | [], s => ⟨s, rfl, rfl, by simp [Pi2S.publicWire]⟩
  | (.integer b, .integer x) :: rest, s => by
    obtain ⟨s', h, ha, hs⟩ := run_sendPublic rest
      { s with stream := s.stream ++ (UniComplete.integerWire x b).toArray }
    refine ⟨s', ?_, ha, ?_⟩
    · show (UniComplete.sendInteger x b >>= fun _ ↦ sendPublic rest).run s = _
      rw [StateT.run_bind]
      exact h
    · rw [hs]
      simp [Pi2S.publicWire]
      omega
  | (.integer _, .root _) :: rest, s => run_sendPublic rest s
  | (.integer _, .scalar _) :: rest, s => run_sendPublic rest s
  | (.root, .integer _) :: rest, s => run_sendPublic rest s
  | (.root, .root bytes) :: rest, s => by
    obtain ⟨s', h, ha, hs⟩ := run_sendPublic rest
      { s with stream := s.stream ++ (UniStatement.rootWord (halvesOf bytes)).toArray }
    refine ⟨s', ?_, ha, ?_⟩
    · show (UniComplete.sendRoot (halvesOf bytes) >>= fun _ ↦ sendPublic rest).run s = _
      rw [StateT.run_bind]
      exact h
    · rw [hs]
      simp [Pi2S.publicWire]
      omega
  | (.root, .scalar _) :: rest, s => run_sendPublic rest s
  | (.scalar, .integer _) :: rest, s => run_sendPublic rest s
  | (.scalar, .root _) :: rest, s => run_sendPublic rest s
  | (.scalar, .scalar x) :: rest, s => by
    obtain ⟨s', h, ha, hs⟩ := run_sendPublic rest
      { s with stream := s.stream ++ (UniComplete.scalarWire x).toArray }
    refine ⟨s', ?_, ha, ?_⟩
    · show (UniComplete.sendScalar x >>= fun _ ↦ sendPublic rest).run s = _
      rw [StateT.run_bind]
      exact h
    · rw [hs]
      simp [Pi2S.publicWire]
      omega

/-- The public values' bytes: at most `32` a value, when no read is an integer. -/
theorem length_publicWire_le : ∀ (l : List (Read × PublicValue)), (∀ p ∈ l, ∀ b, p.1 ≠ .integer b) →
    (Pi2S.publicWire l).length ≤ 32 * l.length
  | [], _ => by simp [Pi2S.publicWire]
  | (.integer b, _) :: _, h => absurd rfl (h _ List.mem_cons_self b)
  | (.root, .integer _) :: rest, h => by
    have := length_publicWire_le rest fun p hp ↦ h p (List.mem_cons_of_mem _ hp)
    simp only [Pi2S.publicWire, List.length_cons]
    omega
  | (.root, .root _) :: rest, h => by
    have := length_publicWire_le rest fun p hp ↦ h p (List.mem_cons_of_mem _ hp)
    simp only [Pi2S.publicWire, List.length_append, UniComplete.Cost.length_rootWord, List.length_cons]
    omega
  | (.root, .scalar _) :: rest, h => by
    have := length_publicWire_le rest fun p hp ↦ h p (List.mem_cons_of_mem _ hp)
    simp only [Pi2S.publicWire, List.length_cons]
    omega
  | (.scalar, .integer _) :: rest, h => by
    have := length_publicWire_le rest fun p hp ↦ h p (List.mem_cons_of_mem _ hp)
    simp only [Pi2S.publicWire, List.length_cons]
    omega
  | (.scalar, .root _) :: rest, h => by
    have := length_publicWire_le rest fun p hp ↦ h p (List.mem_cons_of_mem _ hp)
    simp only [Pi2S.publicWire, List.length_cons]
    omega
  | (.scalar, .scalar _) :: rest, h => by
    have := length_publicWire_le rest fun p hp ↦ h p (List.mem_cons_of_mem _ hp)
    simp only [Pi2S.publicWire, List.length_append, UniComplete.Cost.length_scalarWire, List.length_cons]
    omega

theorem data_reads_length : Data.reads.length = 19 := by decide +kernel

/-- A read is an integer. -/
def isInteger : Read → Bool
  | .integer _ => true
  | _ => false

theorem data_reads_isInteger : ∀ r ∈ Data.reads, isInteger r = false := by decide +kernel

theorem data_reads_integer : ∀ r ∈ Data.reads, ∀ b, r ≠ .integer b := by
  intro r hr b hb
  have := data_reads_isInteger r hr
  rw [hb] at this
  cases this

/-- **The public values' bytes on the real circuit**: at most `19 · 32`. -/
theorem length_publicWire_data (values : List PublicValue) : (Pi2S.publicWire (Data.reads.zip values)).length ≤ 608 := by
  refine (length_publicWire_le _ fun p hp b ↦ data_reads_integer _ (List.of_mem_zip hp).1 b).trans ?_
  rw [List.length_zip, data_reads_length]
  have : min 19 values.length ≤ 19 := min_le_left _ _
  omega

/-- **Before `α`**: `W`'s tree; the public values and the root written. -/
theorem cp_pre2 (G : RecPiop.Circuit E) (hG : G.logN = 24) (reads : List Read) (values : List PublicValue)
    (w : ℕ → K) (s : UniComplete.Wr) :
    CP ((pre2 callKeccak256 G reads values w).run s) (treeCost 24) fun z ↦
      z.2.absorbed = s.absorbed ∧ z.2.stream.size = s.stream.size + (Pi2S.publicWire (reads.zip values)).length + 32 := by
  obtain ⟨s', h, ha, hs⟩ := run_sendPublic (reads.zip values) s
  unfold pre2
  simp only [StateT.run_bind, h, pure_bind, StateT.run_lift, bind_assoc, run_sendRoot2, StateT.run_pure]
  refine CP.bind_le (cp_of_qc (qc_commitWithH _ _)) (fun t _ ↦ cp_pure _ ⟨ha, ?_⟩) ?_
  · simp [hs]
  · rw [hG]
    decide

/-- **From `γ` to `t`**: `Q`'s tree; its root written. -/
theorem cp_mid2 (G : RecPiop.Circuit E) (hG : G.logN = 24) (w : ℕ → K) (α β γ : E) (s : UniComplete.Wr) :
    CP ((mid2 callKeccak256 G w α β γ).run s) (treeCost 28) fun z ↦
      z.2.absorbed = s.absorbed ∧ z.2.stream.size = s.stream.size + 32 := by
  unfold mid2
  simp only [StateT.run_bind, pure_bind, StateT.run_lift, bind_assoc, run_sendRoot2, StateT.run_pure]
  refine CP.bind_le (cp_of_qc (qc_commitWithH _ _)) (fun t _ ↦ cp_pure _ ⟨rfl, ?_⟩) ?_
  · simp
  · rw [hG]
    decide

theorem length_foldValues (m r : ℕ) (T : Array K) (t : E) : (foldValues m r T t).length = 2 ^ r := by
  simp [foldValues]

/-- **After `t`**: the values at `t` written, `ρ` (`440` bytes, `4` blocks). -/
theorem cp_post2 (G : RecPiop.Circuit E) (hW : G.logW = 4) (setupStack : Array K) (input : List UInt8)
    (values : List PublicValue) (w : ℕ → K) (wS : Array K) (wT : LeanVM.Prover.Tree) (qS : Array K)
    (qT : LeanVM.Prover.Tree) (α β γ t : E) (s : UniComplete.Wr) (hs : s.absorbed = s.stream.size) :
    CP ((post2 callKeccak256 G setupStack input values w wS wT qS qT α β γ t).run s) 4 fun z ↦
      z.1.stream.size = s.stream.size + 408 := by
  unfold post2
  simp only [StateT.run_bind, pure_bind, bind_assoc, run_sendScalars2, UniComplete.sampleW, StateT.run_get,
    StateT.run_lift, StateT.run_set, StateT.run_pure]
  refine CP.bind_le (cp_H_le (k := 4) ?_) (fun _ _ ↦ cp_pure _ ?_) le_rfl
  · simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, Array.size_append,
      List.size_toArray, UniComplete.Cost.length_flatMap_scalarWire, length_foldValues, hW, hs,
      List.length_singleton, Nat.min_self]
    omega
  · simp [length_foldValues, hW]

/-! ## The graph's three `PCS_OPEN`s -/

theorem mapM_option_length {γ δ : Type} {f : γ → Option δ} :
    ∀ {l : List γ} {l' : List δ}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        simp [mapM_option_length hl]

theorem mem_of_mapM_some {γ δ : Type} {f : γ → Option δ} :
    ∀ {l : List γ} {l' : List δ}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by
    simp only [List.mapM_nil] at h
    cases h
    simp at hy
  | a :: l, l', h, y, hy => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨x, hx, hfx⟩ := mem_of_mapM_some hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem claimsOfWords_length {words : List (List UInt8)} {k v : ℕ} {cl : List PcsQuotient.Claim}
    (h : claimsOfWords words k v = some cl) : cl.length = k := by
  unfold claimsOfWords at h
  rw [mapM_option_length h, List.length_range]

/-- **A decoded π1 call's claims**: `k` claims of `v + 1` words each, after the three head words. -/
theorem decodePi1Call_claims {call : List UInt8} {o : Pi1Opening} (h : decodePi1Call call = some o) :
    o.2.2.length * (UniStatement.layoutWordVars o.2.1 + 1) + 3 ≤ call.length / 32 := by
  unfold decodePi1Call at h
  generalize hw : List.map (fun j ↦ List.take 32 (List.drop (32 * j) call)) (List.range (call.length / 32)) =
    words at h
  have hwl : words.length = call.length / 32 := by simp [← hw]
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨root, -, layout, hlay, w2, -, k, hk, h⟩ := h
    split at h
    · simp at h
    · rename_i hc
      simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨cl, hcl, rfl⟩ := h
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not] at hc
      simp only
      rw [claimsOfWords_length hcl]
      have := hc.2
      omega

theorem length_wordBytes_le (s : Array UInt8) (vals : Array RecGraph.Value) (w : RecGraph.Word) :
    (RecGraph.wordBytes s vals w).length ≤ 32 := by
  cases w with
  | node id => simp [RecGraph.wordBytes]
  | const w => simp [RecGraph.wordBytes, RecGraph.beBytes32]
  | stream a => simp [RecGraph.wordBytes]

theorem length_flatMap_le {γ δ : Type} (f : γ → List δ) (k : ℕ) (hf : ∀ x, (f x).length ≤ k) :
    ∀ l : List γ, (l.flatMap f).length ≤ k * l.length
  | [] => by simp
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := hf x
    have := length_flatMap_le f k hf l
    rw [Nat.mul_succ]
    omega

theorem emitted_calls_le : ∀ ws ∈ RecGraph.Emitted.calls, ws.length ≤ 31 := by decide +kernel

/-- A graph's outputs' calls: each call's words' bytes. -/
theorem evalGraphDeployed_calls {g : RecGraph.Graph} {iv pub : List UInt8} {s : Array UInt8} {out : RecGraph.Outputs}
    (h : RecGraph.evalGraphDeployed g iv pub s = some out) :
    ∃ vals, out.calls = g.calls.map (·.flatMap (RecGraph.wordBytes s vals)) := by
  unfold RecGraph.evalGraphDeployed RecGraph.evalGraph at h
  split at h
  · have h' : some (RecGraph.outputsOf g s
        (Id.run (RecGraph.evalNodes (m := Id) (fun x ↦ pure (keccakF1600 x)) g iv pub s))) = some out := h
    exact ⟨_, by rw [← Option.some.inj h']; rfl⟩
  · cases h

/-- The graph's calls: at most `31` words of `32` bytes. -/
theorem graph_calls_le (hg : GraphsAgree) {iv pub : List UInt8} {s : Array UInt8} {out : RecGraph.Outputs}
    (h : RecGraph.evalGraphDeployed RecGraph.Pi1.pi1Graph iv pub s = some out) :
    ∀ call ∈ out.calls, call.length ≤ 32 * 31 := by
  obtain ⟨vals, hv⟩ := evalGraphDeployed_calls h
  intro call hc
  rw [hv, List.mem_map] at hc
  obtain ⟨ws, hws, rfl⟩ := hc
  have hws' : ws ∈ RecGraph.Emitted.calls := by
    unfold GraphsAgree at hg
    rw [hg] at hws
    exact hws
  exact (length_flatMap_le _ 32 (length_wordBytes_le _ _) ws).trans
    (Nat.mul_le_mul_left _ (emitted_calls_le ws hws'))

/-- `PCS_OPEN`'s cost on a claim count and variables of at most `X` words. -/
theorem qc_openingW (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim)
    (p : LeanVM.Protocol.Compile.Proof) (X : ℕ) (hX : claims.length * (L.vars + 1) ≤ X)
    (hL : L.logN - PcsQuotient.laneFold + PcsQuotient.logInvRate ≤ 12 * costHeight) :
    QC (E2ECompleteness.openingWithH callKeccak256 callKeccakF1600 L root claims p) ((76 + 24 * X) / 136 + 1 + vOpen) :=
  E2ECompleteness.Cost.cost_openingWithH L root claims p hL _ (by omega)

theorem plain_ok (v : ℕ) (hv : v ≤ 255) :
    (UniStatement.plainLayout v).logN - PcsQuotient.laneFold + PcsQuotient.logInvRate ≤ 12 * costHeight := by
  show v - PcsQuotient.laneFold + PcsQuotient.logInvRate ≤ 12 * costHeight
  simp only [PcsQuotient.laneFold, PcsQuotient.logInvRate, costHeight]
  omega

theorem plain_vars (v : ℕ) : (UniStatement.plainLayout v).vars = v := rfl

/-- The graph's opening: a call of at most `31` words. -/
noncomputable def gOpen : ℕ := (76 + 24 * 31) / 136 + 1 + vOpen

theorem mem_modify_snd {γ δ : Type} {g : γ × δ → γ × δ} (hg : ∀ x, (g x).2 = x.2) :
    ∀ {l : List (γ × δ)} {i : ℕ} {x : γ × δ}, x ∈ l.modify i g → ∃ y ∈ l, x.2 = y.2
  | [], i, x, h => by simp at h
  | a :: l, 0, x, h => by
    rw [List.modify_zero_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨a, List.mem_cons_self, hg a⟩
    · exact ⟨x, List.mem_cons_of_mem _ h, rfl⟩
  | a :: l, i + 1, x, h => by
    rw [List.modify_succ_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨x, List.mem_cons_self, rfl⟩
    · obtain ⟨y, hy, he⟩ := mem_modify_snd hg h
      exact ⟨y, List.mem_cons_of_mem _ hy, he⟩

/-- **π1-rec3's graph with its three `PCS_OPEN`s**: at most `3 · gOpen` blocks. -/
theorem qc_pi1GraphVerifierWithH (hg : GraphsAgree) (D : RecDeployment) (roots : UniStatement.SetupRoots)
    (input : Vector UInt8 32) (p : UniStatement.UniProof) :
    QC (Pi2H.pi1GraphVerifierWithH callKeccak256 callKeccakF1600 D roots input p) (3 * gOpen) := by
  unfold Pi2H.pi1GraphVerifierWithH
  split
  · exact qc_pure _ _
  · rename_i out hout
    split
    · exact qc_pure _ _
    · split
      · exact qc_pure _ _
      · rename_i ops hops
        split
        · exact qc_pure _ _
        · refine (qc_forIn_mem _ _ _ (c := gOpen) fun x hx s ↦ ?_).bind_le (fun _ ↦ qc_pure _ 0) ?_
          · obtain ⟨o, pp⟩ := x
            obtain ⟨ho, -⟩ := List.of_mem_zip hx
            obtain ⟨o', ho', he⟩ := mem_modify_snd (g := fun o ↦ (roots.bytecode, o.2)) (fun _ ↦ rfl) ho
            obtain ⟨call, hcall, hdec⟩ := mem_of_mapM_some hops o' ho'
            have hc := decodePi1Call_claims hdec
            have hlen := graph_calls_le hg hout call hcall
            rw [← he] at hc
            refine (qc_openingW (UniStatement.plainLayout (UniStatement.layoutWordVars o.2.1)) _ _ _ 31 ?_
              (plain_ok _ (UniComplete.Cost.layoutWordVars_le _))).bind_le (fun _ ↦ qc_pure _ 0)
              (by unfold gOpen; omega)
            rw [plain_vars]
            omega
          · rw [List.length_zip, Nat.add_zero]
            exact Nat.mul_le_mul_right _ (min_le_right _ _)

/-! ## The contract -/

/-- A call's third word is a count of at most two. -/
def CountOK (words : List (List UInt8)) : Prop := ∀ k, countOfWord (words.getD 2 []) = some k → k ≤ 2

/-- **A decoded call's claims**: as many as its count word says; its layout registered. -/
theorem decodeWith_claims {reg : List (List UInt8 × Opener)} {words : List (List UInt8)}
    {x : Digest × Opener × List PcsQuotient.Claim} (h : decodeWith reg words = some x) :
    (∃ k, countOfWord (words.getD 2 []) = some k ∧ x.2.2.length = k) ∧ reg.lookup (words.getD 1 []) = some x.2.1 := by
  unfold decodeWith at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨root, -, layout, hlay, op, hop, w2, hw2, k, hk, h⟩ := h
  split at h
  · simp at h
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cl, hcl, rfl⟩ := h
    have h1 : words.getD 1 [] = layout := by rw [List.getD_eq_getElem?_getD, hlay]; rfl
    have h2 : words.getD 2 [] = w2 := by rw [List.getD_eq_getElem?_getD, hw2]; rfl
    exact ⟨⟨k, by rw [h2]; exact hk, claimsOfWords_length hcl⟩, by rw [h1]; exact hop⟩

/-- **The registry's openers**: at most `255` variables, π2's layouts within the verifier's height. -/
theorem registry_ok (shape : UniStatement.Shape) {w : List UInt8} {op : Opener}
    (h : (registryOf shape 24).lookup w = some op) :
    op.vars ≤ 255 ∧ ∀ L, op = .pi2 L → L.logN - PcsQuotient.laneFold + PcsQuotient.logInvRate ≤ 12 * costHeight := by
  obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp h
  have hmem : (w, op) ∈ registryOf shape 24 := by rw [hl]; simp
  unfold registryOf at hmem
  simp only [List.mem_append, List.mem_cons, List.mem_map, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ((⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩)) | ⟨word, -, -, rfl⟩
  · refine ⟨by decide, fun L hL ↦ ?_⟩
    cases hL
    decide
  · refine ⟨by decide, fun L hL ↦ ?_⟩
    cases hL
    decide
  · refine ⟨by decide, fun L hL ↦ ?_⟩
    cases hL
    decide
  · exact ⟨UniComplete.Cost.layoutWordVars_le _, fun L hL ↦ by cases hL⟩

/-- The contract's opening: a count of at most `2`, at most `255` variables. -/
noncomputable def cOpen : ℕ := (76 + 24 * 512) / 136 + 1 + vOpen

/-- **`PCS_OPEN` on a call whose count is at most two**: at most `cOpen` blocks. -/
theorem qc_pcsOpenAtH (shape : UniStatement.Shape) (words : List (List UInt8)) (p : Compile.Proof)
    (hk : CountOK words) : QC (Pi2H.pcsOpenAtH callKeccak256 callKeccakF1600 (registryOf shape 24) words p) cOpen := by
  unfold Pi2H.pcsOpenAtH
  split
  · exact qc_pure _ _
  · rename_i root vars claims hd
    obtain ⟨⟨k, hck, hcl⟩, hlook⟩ := decodeWith_claims hd
    obtain ⟨hv, -⟩ := registry_ok shape hlook
    have hk2 := hk k hck
    dsimp only at hcl hv
    unfold UniComplete.pcsOpenWithH
    refine qc_openingW (UniStatement.plainLayout vars) root claims p 512 ?_ (plain_ok vars hv)
    rw [plain_vars, hcl]
    have : k * (vars + 1) ≤ 2 * 256 := Nat.mul_le_mul hk2 (by simp only [Opener.vars] at hv; omega)
    omega
  · rename_i root L claims hd
    obtain ⟨⟨k, hck, hcl⟩, hlook⟩ := decodeWith_claims hd
    obtain ⟨hv, hL⟩ := registry_ok shape hlook
    have hk2 := hk k hck
    dsimp only at hcl hv
    refine qc_openingW L root claims p 512 ?_ (hL L rfl)
    rw [hcl]
    have : k * (L.vars + 1) ≤ 2 * 256 := Nat.mul_le_mul hk2 (by simp only [Opener.vars] at hv; omega)
    omega

theorem countOfWord_numberWord_two : countOfWord (UniStatement.numberWord 2) = some 2 := by decide

theorem data_calls_third : ∀ call ∈ Data.pi1Calls, call[2]? = some (CallWord.const (UniStatement.numberWord 1)) := by
  decide +kernel

theorem pi1CallsWith_third (calls : List (List CallWord)) (f : Digest)
    (h : ∀ call ∈ calls, call[2]? = some (CallWord.const (UniStatement.numberWord 1))) :
    ∀ call ∈ pi1CallsWith calls f, call[2]? = some (CallWord.const (UniStatement.numberWord 1)) := by
  intro call hc
  unfold pi1CallsWith at hc
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
  have := h c0 hc0
  split
  · rename_i w rest
    simpa using this
  · exact this

theorem pcsCalls_shape (c : Circuit) (pi1 : List (List CallWord)) (sr : List UInt8) (stream : Array UInt8)
    (r : Reduced) : ∃ a b d, pcsCalls c pi1 sr stream r = pi1.map (·.map (callWord c.reads stream r)) ++ [a, b, d] ∧
      a.getD 2 [] = UniStatement.numberWord 1 ∧ b.getD 2 [] = UniStatement.numberWord 1 ∧
      d.getD 2 [] = UniStatement.numberWord 2 :=
  ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- **Every call of the contract has a count of at most two** (`numberWord 1`, `numberWord 2`). -/
theorem countOK_pcsCalls {D : RecDeployment} (hD : D.Real) (c : Circuit) (f : Digest) (sr : List UInt8)
    (stream : Array UInt8) (r : Reduced) :
    ∀ words ∈ pcsCalls c (pi1CallsWith D.pi1Calls f) sr stream r, CountOK words := by
  intro words hw k hk
  obtain ⟨a, b, d, he, ha, hb, hd⟩ := pcsCalls_shape c (pi1CallsWith D.pi1Calls f) sr stream r
  rw [he] at hw
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with ⟨call, hcall, rfl⟩ | rfl | rfl | rfl
  · have h3 := pi1CallsWith_third _ f (by rw [hD.2.1]; exact data_calls_third) call hcall
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, h3] at hk
    simp only [Option.map_some, Option.getD_some, callWord, RecCompose.Pi1Decode.countOfWord_numberWord_one,
      Option.some.injEq] at hk
    omega
  · rw [ha, RecCompose.Pi1Decode.countOfWord_numberWord_one] at hk
    cases hk
    omega
  · rw [hb, RecCompose.Pi1Decode.countOfWord_numberWord_one] at hk
    cases hk
    omega
  · rw [hd, countOfWord_numberWord_two] at hk
    cases hk
    omega

/-- **π2's walk on the calldata**: `10` blocks beyond the channel's potential (five challenges). -/
theorem cc_reduceWithH2 (s : Spec) (stmt : List E) : CC (Pi2H.reduceWithH callKeccak256 s stmt) 10 0 fun _ ↦ True := by
  unfold Pi2H.reduceWithH
  refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun rd pubs ↦ ?_) (by simp) le_rfl fun _ h ↦ h)
    fun pubs _ ↦ ?_
  · rcases rd with b | _ | _
    · exact cc_free (cc_nextInteger b) fun _ _ ↦ cc_pure trivial 0
    · exact cc_free cc_nextRoot fun _ _ ↦ cc_pure trivial 0
    · exact cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ cc_pure trivial 0
  · refine cc_free cc_nextRoot fun _ _ ↦ cc_seq cc_sampleH (fun _ _ ↦ cc_seq cc_sampleH (fun _ _ ↦
      cc_seq cc_sampleH (fun _ _ ↦ cc_free cc_nextRoot fun _ _ ↦ cc_seq cc_sampleH (fun _ _ ↦
      cc_free (cc_nextScalars _) fun _ _ ↦ cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h)
      fun _ _ ↦ cc_seq cc_sampleH (fun _ _ ↦ cc_pure trivial _) (by omega)) (by omega)) (by omega)) (by omega))
      (by omega)

/-- **The contract's run on the calldata**: the seed (`80` bytes), the walk; `m` blocks left on success. -/
theorem costP_runWithH2 (s : Spec) (iv input : List UInt8) (stream : Array UInt8) (hiv : iv.length = 32)
    (hin : input.length = 32) (m : ℕ) :
    CostP (Pi2H.runWithH callKeccak256 s iv input stream) (1 + (10 + 3 * stream.size + m))
      fun o rem ↦ ∀ r, o.result = .ok r → m ≤ rem := by
  unfold Pi2H.runWithH callKeccak256
  rw [costP_query_bind]
  refine ⟨?_, fun seed ↦ ?_⟩
  · show (RecStatement.name ++ iv ++ input).length / 136 + 1 ≤ _
    simp only [List.length_append, name_length, hiv, hin]
    omega
  · rw [show 1 + (10 + 3 * stream.size + m) - hashBlocks (Sum.inl (RecStatement.name ++ iv ++ input)) =
        10 + pot (Chan.start seed stream) + m by
      show _ - ((RecStatement.name ++ iv ++ input).length / 136 + 1) = _
      simp only [List.length_append, name_length, hiv, hin, pot, Chan.start]
      omega]
    have hw : CC (do
        let r ← Pi2H.reduceWithH callKeccak256 s (UniStatement.publicWordsOf input)
        UniStatement.finish (m := OracleComp KeccakCalls)
        return r : UniComplete.Cost.CM Reduced) 10 0 fun _ ↦ True :=
      cc_mono (cc_bind (k₂ := 0) (g₂ := 0) (cc_reduceWithH2 s _) fun _ _ ↦ cc_free cc_finish fun _ _ ↦
        cc_pure (P := fun _ : Reduced ↦ True) trivial 0) (by omega) le_rfl fun _ h ↦ h
    refine UniComplete.Cost.CostP.bind (hw (Chan.start seed stream) ⟨le_rfl, Nat.zero_le _⟩ m) fun z rem hz ↦ ?_
    obtain ⟨res, ch⟩ := z
    show ∀ r, res = .ok r → m ≤ rem
    intro r hr
    have := (hz r hr).2.2
    omega

/-- The contract's run and six openings, on a stream of at most `S` bytes. -/
noncomputable def contractC (S : ℕ) : ℕ := ivC + (1 + (10 + 3 * S + 6 * cOpen))

/-- **The contract**: π2's IV, the run on the calldata, its six openings. -/
theorem qc_contractWithH {D : RecDeployment} (hD : D.Real) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) {S : ℕ} (hS : proof.stream.size ≤ S) :
    QC (Pi2H.contractWithH callKeccak256 callKeccakF1600 D roots input proof) (contractC S) := by
  refine UniComplete.Cost.CostP.toQC (Q := fun _ _ ↦ True) ?_
  unfold Pi2H.contractWithH contractC
  refine UniComplete.Cost.CostP.bind (cp_ivOfH hD roots _) fun iv rem hiv ↦ ?_
  refine UniComplete.Cost.CostP.weaken (n := 1 + (10 + 3 * proof.stream.size + 6 * cOpen)) ?_
    (by have := hiv.2; omega)
  refine UniComplete.Cost.CostP.bind (costP_runWithH2 _ iv input.toList proof.stream hiv.1 (by simp) (6 * cOpen))
    fun o rem' ho ↦ ?_
  split
  · trivial
  · rename_i r hr
    have hm := ho r hr
    split
    · trivial
    · dsimp only
      split
      · trivial
      · rename_i hl
        refine UniComplete.Cost.CostP.weaken (UniComplete.Cost.CostP.mono (costP_of_qc ?_ 0) fun _ _ _ ↦ trivial)
          (by omega)
        refine (qc_forIn_mem _ _ _ (c := cOpen) fun x hx s ↦ ?_).bind_le (fun _ ↦ qc_pure _ 0) ?_
        · obtain ⟨words, pp⟩ := x
          have hw := (List.of_mem_zip hx).1
          rw [circuit_logN hD]
          exact (qc_pcsOpenAtH _ words pp (countOK_pcsCalls hD _ _ _ _ _ words hw)).bind_le
            (fun _ ↦ qc_pure _ 0) le_rfl
        · rw [List.length_zip, Nat.add_zero]
          refine Nat.mul_le_mul_right _ ?_
          simp only [ne_eq, not_not] at hl
          exact (min_le_left _ _).trans (le_of_eq hl)

theorem qc_verifierWithH {D : RecDeployment} (hD : D.Real) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) {S : ℕ} (hS : proof.stream.size ≤ S) :
    QC (Pi2H.verifierWithH callKeccak256 callKeccakF1600 D roots input proof) (contractC S + 0) := by
  unfold Pi2H.verifierWithH
  exact (qc_contractWithH hD roots input proof hS).bind (fun _ ↦ qc_pure _ 0)

/-! ## The stages -/

/-- The prover's openings' common part: WHIR's prover at height `26`, `nonceFuel` nonces a proof of work. -/
noncomputable def openP2 : ℕ := 3 + (4 + (2 + whirBound)) * blockFactor costHeight PcsQuotient.nonceFuel

/-- Stage C: `ρ`, the three openings (IVs of `5`, `6`, `12` blocks), the contract on `1080` bytes. -/
noncomputable def costC : ℕ := 4 + ((5 + openP2) + ((6 + openP2) + ((12 + openP2) + (contractC 1080 + 0))))

theorem qc_stageC {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (input : Vector UInt8 32)
    (b : StB) (st : Digest) (hb : b.wr.stream.size ≤ 672) :
    QC (stageC callKeccak256 callKeccakF1600 D C input b st) costC := by
  unfold stageC
  split
  · exact qc_pure _ _
  · refine CP.toQC (P := fun _ ↦ True) (CP.bind_le
      (c₂ := (5 + openP2) + ((6 + openP2) + ((12 + openP2) + (contractC 1080 + 0)))) (cp_post2 (C.G b.a.roots) (Fa.logW b.a.roots) _ _ _ _ _ _ _ _
      _ _ _ _ _ rfl) (fun z hz ↦ cp_of_qc ?_) (by unfold costC; omega))
    obtain ⟨out, _⟩ := z
    dsimp only at hz ⊢
    have hc : (D.circuitAt b.a.roots.pi1).circuit = Data.circuit := by rw [RecDeployment.circuitAt, hD.1]
    obtain ⟨lW, lS, lQ, lSum⟩ := Pi2K.run_points_length (Spec.of (D.circuitAt b.a.roots.pi1).circuit).core
      (by rw [hc]; rfl) (by rw [hc]; rfl) out.inputs
    refine E2ECompleteness.Cost.QC.bind_le (b := (6 + openP2) + ((12 + openP2) + (contractC 1080 + 0)))
      (E2ECompleteness.Cost.cost_proveOpeningWithH _ _ _ _ _ 24 5 (by simp [lW]) (by simp)) (fun pW ↦ ?_)
      (by unfold openP2; omega)
    refine E2ECompleteness.Cost.QC.bind_le (b := (12 + openP2) + (contractC 1080 + 0))
      (E2ECompleteness.Cost.cost_proveOpeningWithH _ _ _ _ _ 25 6 (by simp [lS]) (by simp)) (fun pS ↦ ?_)
      (by unfold openP2; omega)
    refine E2ECompleteness.Cost.QC.bind_le (b := contractC 1080 + 0)
      (E2ECompleteness.Cost.cost_proveOpeningWithH _ _ _ _ _ 29 12 (by simp [lQ, lSum]) (by simp)) (fun pQ ↦ ?_)
      (by unfold openP2; omega)
    split
    · refine (qc_verifierWithH hD _ input _ (S := 1080) ?_).bind_le (fun _ ↦ qc_pure _ 0) (by omega)
      show out.stream.size ≤ 1080
      rw [hz]
      show b.wr.stream.size + 408 ≤ 1080
      omega
    · exact qc_pure _ _

theorem cp_stageB {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C) (a : StA) (s₁ s₂ s₃ : Digest)
    (ha : a.wr.stream.size ≤ 640) :
    CP (stageB callKeccak256 D C a s₁ s₂ s₃) (treeCost 28) fun b ↦
      b.wr.absorbed + 32 = b.wr.stream.size ∧ b.wr.stream.size ≤ 672 := by
  unfold stageB
  dsimp only
  refine CP.bind_le (c₂ := 0) (cp_mid2 _ (Fa.logN a.roots) _ _ _ _ _) (fun z hz ↦ ?_) (by simp)
  obtain ⟨qs, wr⟩ := z
  refine cp_pure _ ⟨?_, ?_⟩
  · show wr.absorbed + 32 = wr.stream.size
    rw [hz.1, hz.2]
    rfl
  · show wr.stream.size ≤ 672
    rw [hz.2]
    show a.wr.stream.size + 32 ≤ 672
    omega

/-- Stage A: the setup twice, π1-rec3's prover, the graph, π2's IV, the seed, `W`'s tree. -/
noncomputable def costA (S : ℕ) : ℕ := S + (2 ^ 47 + (3 * gOpen + (S + (ivC + (1 + (treeCost 24 + 0))))))

theorem cp_stageA {D : RecDeployment} (hD : D.Real) (hg : GraphsAgree) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (hP : QC P1k (2 ^ 47)) (input : Vector UInt8 32) :
    CP (stageA callKeccak256 callKeccakF1600 D C Fa P1k input) (costA (setup2 D)) fun a ↦ a.wr.stream.size ≤ 640 := by
  unfold stageA costA
  refine CP.bind (cp_of_qc (qc_setupTreesWithH2 hD)) fun trees _ ↦ CP.bind (cp_of_qc hP) fun o _ ↦ ?_
  cases o with
  | none => exact (cp_pure _ (by simp [UniComplete.Wr.start])).mono (Nat.zero_le _) fun _ h ↦ h
  | some p1 =>
    dsimp only
    refine CP.bind (cp_of_qc (qc_pi1GraphVerifierWithH hg D _ input p1)) fun a1 _ ↦
      CP.bind (cp_of_qc (qc_setupTreesWithH2 hD)) fun tr _ ↦ CP.bind (cp_ivOfH hD tr.roots) fun iv hiv ↦
      CP.bind (cp_H_le (k := 1) ?_) fun seed _ ↦ ?_
    · simp only [List.length_append, name_length, hiv, Vector.length_toList]
      omega
    · have hr : (D.circuitAt tr.roots.pi1).circuit.reads = Data.reads := by
        rw [RecDeployment.circuitAt, hD.1]
        rfl
      refine CP.bind (cp_pre2 _ (Fa.logN tr.roots) _ _ _ _) fun z hz ↦ ?_
      obtain ⟨ws, wr⟩ := z
      refine cp_pure _ ?_
      show wr.stream.size ≤ 640
      rw [hz.2, hr]
      have := length_publicWire_data (Pi2E.pi2Choice D C Fa tr.roots input p1.stream).1
      show 0 + _ + 32 ≤ 640
      omega

/-! ## The staged run -/

/-- The setup's blocks at the reference shape: at most `2^27` for π1's, π2's setup tree. -/
noncomputable def setupR : ℕ := 2 ^ 27 + treeCost 25

theorem setup2_le {D : RecDeployment} (hD : D.Real) : setup2 D ≤ setupR := by
  unfold setup2 setupR UniComplete.Cost.setupCost
  rw [hD.2.2.1]
  obtain ⟨-, -, h3, -⟩ := UniComplete.Cost.reference_vars
  have h19 : 2 ^ ((UniStatement.setupLayout UniStatement.reference).vars - 6 + 1) ≤ 2 ^ 19 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : UniStatement.matrixVars ≤ 28 := by decide
  have h23 : 2 ^ (UniStatement.matrixVars - 6 + 1) ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ ((UniStatement.setupLayout UniStatement.reference).vars - 6 + 1) = x at h19 ⊢
  generalize 2 ^ (UniStatement.matrixVars - 6 + 1) = y at h23 ⊢
  have e19 : (2 : ℕ) ^ 19 = 524288 := by norm_num
  have e23 : (2 : ℕ) ^ 23 = 8388608 := by norm_num
  have e27 : (2 : ℕ) ^ 27 = 134217728 := by norm_num
  omega

/-- **The staged run's block count.** -/
noncomputable def pi2RunN : ℕ := costA setupR + (4 + (1 + (1 + ((treeCost 28 + (1 + (costC + 0))) + 0))))

theorem qc_pi2Staged {D : RecDeployment} (hD : D.Real) (hg : GraphsAgree) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (hP : QC P1k (2 ^ 47)) (input : Vector UInt8 32) :
    QC (pi2Staged D C Fa P1k input).run pi2RunN := by
  have h : CP (pi2Staged D C Fa P1k input).run
      (costA (setup2 D) + (4 + (1 + (1 + ((treeCost 28 + (1 + (costC + 0))) + 0))))) fun _ ↦ True := by
    unfold Pi2P.Pi2Staged.run Pi2P.staged3 Pi2P.Pi2Staged.tail
    refine CP.bind (cp_stageA hD hg C Fa P1k hP input) fun a ha ↦ CP.bind (cp_H_le (k := 4) ?_) fun s₁ _ ↦
      CP.bind (cp_H_le (k := 1) ?_) fun s₂ _ ↦ CP.bind (cp_H_le (k := 1) ?_) fun s₃ _ ↦
      CP.bind (CP.bind (cp_stageB C Fa a s₁ s₂ s₃ ha) fun b hb ↦ CP.bind (cp_H_le (k := 1) ?_) fun st _ ↦
        CP.bind (cp_of_qc (qc_stageC hD C Fa input b st hb.2)) fun _ _ ↦ cp_pure (P := fun _ ↦ True) _ trivial)
        fun _ _ ↦ cp_pure (P := fun _ ↦ True) _ trivial
    · show (fixLen 536 _).length < 136 * 4
      rw [fixLen_length]
      norm_num
    · rw [len_digestBytes]
      norm_num
    · rw [len_digestBytes]
      norm_num
    · show (UniComplete.Prob.tInput b.wr).length < 136 * 1
      simp only [UniComplete.Prob.tInput, List.length_append, len_digestBytes, Array.length_toList,
        Array.size_extract]
      have := hb.1
      omega
  refine (h.mono ?_ fun _ _ ↦ trivial).toQC
  unfold pi2RunN costA
  have := setup2_le hD
  omega

theorem pi2RunN_le : pi2RunN ≤ 2 ^ 50 := by
  unfold pi2RunN costA setupR costC openP2 contractC cOpen gOpen ivC
  norm_num [treeCost, vOpen, whirBound, costHeight, blockFactor, PcsQuotient.nonceFuel]

end Cost2

open Cost2 in
/-- **`Pi2RunCost` for π1-rec3's honest prover**: at most `pi2RunN ≤ 2^50` block calls (`pi2RunN_le`), at the real
deployment and the graphs' agreement. -/
theorem pi2RunCost_p1k {D : RecDeployment} (hD : D.Real) (hg : GraphsAgree) (C : Pi2Circuits D) (Fa : Pi2Facts D C) :
    Pi2RunCost D C Fa (p1k D) pi2RunN := fun input rows q hfit hrel ↦
  qc_pi2Staged hD hg C Fa _ (UniComplete.Rec3.proverCost3_flockProve3H D.pi1 hD.2.2.1
    (by rw [hD.2.2.2.1, programIv_length]; norm_num) input rows q hfit hrel) input

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2G.pi2RunCost_p1k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.pi2RunCost_p1k

/-- info: 'RecCompose.Pi2G.Cost2.pi2RunN_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.Cost2.pi2RunN_le
