-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The walks of `formal/UniComplete/UniComplete/
-- Rec3ProverCost.lean` (`wc_proveStreamRec3With`, `costP_proveRec3With`) and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean` (`cost_runFromWithHash`, `cost_proveOpeningWithH`,
-- `qc_findNonceM`), redone for the lengths of the hashed inputs; uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, the block cost `hashBlocks`, the weight calculus `Common.QueryCostAtMost`, VCVio's `IsQueryBound`.
import RecCompose.Pi2RunCost

/-!
# Before π2's IV, nothing of `2^26` bytes is hashed

π2's IV starts with a hash of `σ`'s `4 · 2^24 = 2^26` bytes (`Pi2H.digestWithH`). Every Keccak-256 query before it,
in `pi2Staged`'s stage A, is shorter (`Short`):

* **`hashOK_setupTreesWithH2`**: the setup's four trees (`512`-byte leaves, `64`-byte nodes);
* **`hashOK_graph`**: π1-rec3's graph with its three `PCS_OPEN`s, from its block count (`3 · gOpen` blocks, so no
  query of `136 · 3 · gOpen < 2^26` bytes or more; **`hashOK_of_qc`**);
* **`hashOK_p1k`**: π1-rec3's honest prover: its setup's trees, its IV (`321` bytes), its seed (`80`), its stream (a
  sample hashes the state and the bytes written since the last one, at most `9328`; Flock's prover from its block
  count, `46` blocks beyond its `3552` bytes), its three WHIR openings (the seed of `76 + 24 · 29` bytes at most, the
  trees of rows of at most `192` words, the sponge and the proof-of-work search through the permutation only).

The stream's walk is `Rec3.wc_proveStreamRec3With`'s, in a calculus `WS` (every query short, the stream at most
`2^14` bytes), each piece of few blocks converted from its `Cost.WC` (`ws_of_wc`: with no extra budget a query costs
at most the blocks left, `lenP_of_costP`), the two trees lifted (`ws_lift`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open LeanVM.Prover (Tree Script)
open RecStatement
open UniStatement
open E2ECompleteness (HashOK hashOK_callKeccak256 hashOK_callKeccakF1600)
open E2ECompleteness.Cost (qc_absorb qc_squeeze qc_powStepM qc_openingSpongeWithH OWordsLE
  oWordsLE_afterSend oWordsLE_afterSample oWordsLE_afterGrind oWordsLE_afterCommit oWordsLE_afterQuery
  length_wordOf_le wordsLE_openingScript)
open UniComplete.Cost (CostP costP_query_bind WC WInv wpot)

namespace RecCompose.Pi2A

/-- Shorter than π2's σ hash input (`4 · 2^24 = 2^26` bytes). -/
def Short (m : List UInt8) : Prop := m.length < 2 ^ 26

theorem two26 : (2 : ℕ) ^ 26 = 67108864 := by norm_num

/-- A short query: a hash of a short input, or a permutation. -/
def ShortQ : List UInt8 ⊕ KeccakState → Prop
  | .inl x => Short x
  | .inr _ => True

/-! ## From a block count -/

/-- **A computation of at most `n` block calls, `136 · n ≤ 2^26`, hashes only short inputs.** -/
theorem hashOK_of_qc {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ}
    (h : Common.QueryCostAtMost X LeanVM.Rpm.hashBlocks n) (hn : 136 * n ≤ 2 ^ 26) : HashOK Short X := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨?_, fun u ↦ ih u (h.2 u)
      ((Nat.mul_le_mul_left 136 (Nat.sub_le _ _)).trans hn)⟩
    rcases t with x | s
    · have h1 := h.1
      simp only [LeanVM.Rpm.hashBlocks] at h1
      show x.length < 2 ^ 26
      rw [two26] at hn ⊢
      omega
    · trivial

/-! ## Short queries with a postcondition -/

/-- **Every query short on every path**, each outcome satisfying `Q`. -/
def LenP {α : Type} : OracleComp KeccakCalls α → (α → Prop) → Prop
  | .pure a, Q => Q a
  | .liftBind t k, Q => ShortQ t ∧ ∀ u, LenP (k u) Q

section LenP

variable {α β : Type}

theorem lenP_query_bind (t : List UInt8 ⊕ KeccakState) (k : KeccakCalls.Range t → OracleComp KeccakCalls α)
    (Q : α → Prop) : LenP (liftM (KeccakCalls.query t) >>= k) Q ↔ ShortQ t ∧ ∀ u, LenP (k u) Q :=
  Iff.rfl

theorem LenP.bind {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} {Q : α → Prop}
    {R : β → Prop} (hX : LenP X Q) (hf : ∀ a, Q a → LenP (f a) R) : LenP (X >>= f) R := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a hX
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [lenP_query_bind] at hX ⊢
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem LenP.mono {X : OracleComp KeccakCalls α} {Q R : α → Prop} (hX : LenP X Q) (h : ∀ a, Q a → R a) :
    LenP X R := by
  induction X using OracleComp.inductionOn with
  | pure a => exact h a hX
  | query_bind t k ih =>
    rw [lenP_query_bind] at hX ⊢
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem LenP.toHashOK {X : OracleComp KeccakCalls α} {Q : α → Prop} (h : LenP X Q) : HashOK Short X := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [lenP_query_bind] at h
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨?_, fun u ↦ ih u (h.2 u)⟩
    rcases t with x | s
    · exact h.1
    · trivial

theorem lenP_of_hashOK {X : OracleComp KeccakCalls α} (h : HashOK Short X) : LenP X fun _ ↦ True := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    rw [lenP_query_bind]
    refine ⟨?_, fun u ↦ ih u (hk u)⟩
    rcases t with x | s
    · exact ht
    · trivial

/-- **A cost with no extra budget**: a query costs at most the blocks left. -/
theorem lenP_of_costP {X : OracleComp KeccakCalls α} {n : ℕ} {Q : α → ℕ → Prop} (h : CostP X n Q)
    (hn : 136 * n ≤ 2 ^ 26) : LenP X fun a ↦ ∃ r, Q a r := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => exact ⟨n, h⟩
  | query_bind t k ih =>
    rw [costP_query_bind] at h
    rw [lenP_query_bind]
    refine ⟨?_, fun u ↦ ih u (h.2 u) ((Nat.mul_le_mul_left 136 (Nat.sub_le _ _)).trans hn)⟩
    rcases t with x | s
    · have h1 := h.1
      simp only [LeanVM.Rpm.hashBlocks] at h1
      show x.length < 2 ^ 26
      rw [two26] at hn ⊢
      omega
    · trivial

end LenP

/-! ## The writer's calculus -/

/-- **`x` hashes only short inputs and writes at most `w` bytes**, from any state of at most `2^14 − w` bytes. -/
def WS {α : Type} (x : UniComplete.PM α) (w : ℕ) (P : α → UniComplete.Wr → Prop) : Prop :=
  ∀ c, WInv c → c.stream.size + w ≤ 16384 → LenP (x.run c) fun z ↦
    P z.1 z.2 ∧ WInv z.2 ∧ c.stream.size ≤ z.2.stream.size ∧ z.2.stream.size ≤ c.stream.size + w

section WS

variable {α β : Type}

/-- **A piece of at most `2^14` blocks beyond its bytes.** -/
theorem ws_of_wc {x : UniComplete.PM α} {k w : ℕ} {P : α → UniComplete.Wr → Prop} (h : WC x k w P)
    (hk : k ≤ 16384) : WS x w P := by
  intro c hc hs
  refine (lenP_of_costP (h c hc 0) ?_).mono fun z ⟨_, hz⟩ ↦ ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩
  have : wpot c ≤ c.stream.size := Nat.sub_le _ _
  rw [two26]
  omega

theorem ws_seq {x : UniComplete.PM α} {f : α → UniComplete.PM β} {w₁ w : ℕ} {P : α → UniComplete.Wr → Prop}
    {Q : β → UniComplete.Wr → Prop} (hx : WS x w₁ P) (hf : ∀ a s, P a s → WS (f a) (w - w₁) Q) (hw : w₁ ≤ w) :
    WS (x >>= f) w Q := by
  intro c hc hs
  rw [StateT.run_bind]
  refine (hx c hc (by omega)).bind fun z hz ↦ ?_
  obtain ⟨hP, hI, h1, h2⟩ := hz
  exact (hf z.1 z.2 hP z.2 hI (by omega)).mono fun z' h ↦ ⟨h.1, h.2.1, by omega, by omega⟩

/-- **A lifted computation** of short queries writes nothing. -/
theorem ws_lift {X : OracleComp KeccakCalls α} (hX : HashOK Short X) :
    WS (StateT.lift X : UniComplete.PM α) 0 fun _ _ ↦ True := by
  intro c hc _
  rw [StateT.run_lift]
  exact (lenP_of_hashOK hX).bind fun a _ ↦ ⟨trivial, hc, le_rfl, Nat.le_add_right _ _⟩

end WS

/-! ## Merkle trees -/

theorem hashOK_buildTree (height : ℕ) (word : Word) (hw : ∀ p, (word p).length ≤ 192) :
    HashOK Short (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash
  refine E2ECompleteness.HashOK.bind ?_ fun leaves ↦ E2ECompleteness.HashOK.bind ?_ fun _ ↦
    E2ECompleteness.HashOK.pure _ _
  · unfold LeanVM.Prover.leafDigestsWithHash
    refine E2ECompleteness.HashOK.arrayMapM _ (fun i ↦ hashOK_callKeccak256 ?_) _
    show _ < 2 ^ 26
    rw [E2ECompleteness.length_flatMap_kBytes, two26]
    have := hw i
    omega
  · suffices h : ∀ k (level : Array Digest),
        HashOK Short (LeanVM.Prover.levelsWithHash callKeccak256 k level) from h _ _
    intro k
    induction k with
    | zero => intro level; exact E2ECompleteness.HashOK.pure _ _
    | succ k ih =>
      intro level
      unfold LeanVM.Prover.levelsWithHash
      refine E2ECompleteness.HashOK.bind ?_ fun up ↦ E2ECompleteness.HashOK.bind (ih up) fun _ ↦
        E2ECompleteness.HashOK.pure _ _
      unfold LeanVM.Prover.parentsWithHash
      refine E2ECompleteness.HashOK.arrayMapM _ (fun j ↦ hashOK_callKeccak256 ?_) _
      show _ < 2 ^ 26
      rw [List.length_append, E2ECompleteness.length_digestBytes, E2ECompleteness.length_digestBytes, two26]
      omega

theorem hashOK_commitWithH (μ : ℕ) (stack : Array K) :
    HashOK Short (E2ECompleteness.commitWithH callKeccak256 μ stack) :=
  hashOK_buildTree _ _ fun p ↦ by rw [E2ECompleteness.length_stackWordFast]; norm_num

theorem hashOK_commitReal (c : Commitment) (vars : ℕ) (stack : Array K) :
    HashOK Short (UniComplete.commitReal callKeccak256 c vars stack) := by
  unfold UniComplete.commitReal
  exact E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ E2ECompleteness.HashOK.pure _ _

/-- **The setup's four trees.** -/
theorem hashOK_setupTreesWithH2 (D : RecDeployment) :
    HashOK Short (Pi2H.setupTreesWithH callKeccak256 callKeccakF1600 D) := by
  unfold Pi2H.setupTreesWithH UniComplete.setupTreesWithH Pi2H.setupTreeWithH
  refine E2ECompleteness.HashOK.bind ?_ fun _ ↦ E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.pure _ _
  exact E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ E2ECompleteness.HashOK.pure _ _

/-! ## π1-rec3's graph -/

/-- **π1-rec3's graph with its three `PCS_OPEN`s** (`3 · gOpen` blocks). -/
theorem hashOK_graph (hg : GraphsAgree) (D : RecDeployment) (roots : UniStatement.SetupRoots)
    (input : Vector UInt8 32) (p : UniStatement.UniProof) :
    HashOK Short (Pi2H.pi1GraphVerifierWithH callKeccak256 callKeccakF1600 D roots input p) :=
  hashOK_of_qc (Pi2G.Cost2.qc_pi1GraphVerifierWithH hg D roots input p) (by
    unfold Pi2G.Cost2.gOpen E2ECompleteness.Cost.vOpen
    norm_num [LeanVM.Protocol.Verifier.whirBound])

/-! ## The WHIR openings -/

theorem hashOK_searchM (bits : ℕ) (sp : Sponge) :
    ∀ (count n : ℕ), HashOK Short (LeanVM.Prover.searchM callKeccakF1600 bits sp n count)
  | 0, _ => trivial
  | count + 1, n => by
    simp only [LeanVM.Prover.searchM]
    refine E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_powStepM _ _) (by norm_num)) fun r ↦ ?_
    split
    · exact E2ECompleteness.HashOK.pure _ _
    · exact hashOK_searchM bits sp count (n + 1)

theorem hashOK_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    HashOK Short (LeanVM.Prover.findNonceM callKeccakF1600 bits sp fuel) := by
  unfold LeanVM.Prover.findNonceM
  split
  · exact E2ECompleteness.HashOK.pure _ _
  · exact hashOK_searchM _ _ _ _

/-- **The prover's runner** hashes only its trees' rows (at most `192` words) and nodes. -/
theorem hashOK_runFromWithHash (fuel : ℕ) {α β : Type} :
    ∀ (P : Prog α) (S : Option (Script β)) (sp : Sponge) (cs : List Tree), OWordsLE 192 S →
      HashOK Short (LeanVM.Prover.runFromWithHash callKeccak256 callKeccakF1600 fuel P S sp cs) := by
  intro P
  induction P with
  | ret a => intros; exact E2ECompleteness.HashOK.pure _ _
  | fail => intros; exact E2ECompleteness.HashOK.pure _ _
  | read k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    exact E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
      E2ECompleteness.HashOK.bind (ih _ _ _ cs (oWordsLE_afterSend hS)) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  | sample k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    exact E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_squeeze _) (by norm_num)) fun r ↦
      ih _ _ _ cs (oWordsLE_afterSample _ hS)
  | grind bits k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine E2ECompleteness.HashOK.bind (hashOK_findNonceM _ _ _) fun o ↦ ?_
    split
    · exact E2ECompleteness.HashOK.pure _ _
    · exact E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_powStepM _ _) (by norm_num)) fun _ ↦
        E2ECompleteness.HashOK.bind (ih _ _ cs (oWordsLE_afterGrind hS)) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  | commit ht w k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    exact E2ECompleteness.HashOK.bind (hashOK_buildTree ht _ (length_wordOf_le hS)) fun _ ↦
      E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
      E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
      E2ECompleteness.HashOK.bind (ih _ _ _ (oWordsLE_afterCommit hS)) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  | query i ps k ih =>
    intro S sp cs hS
    simp only [LeanVM.Prover.runFromWithHash]
    split
    · exact E2ECompleteness.HashOK.pure _ _
    · exact E2ECompleteness.HashOK.bind (ih _ _ _ cs (oWordsLE_afterQuery _ hS)) fun _ ↦
        E2ECompleteness.HashOK.pure _ _

/-- **A WHIR opening** of claims of at most `v` coordinates, its seed's input of at most `2^20` bytes. -/
theorem hashOK_proveOpeningWithH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree) (stack : Array K)
    (claims : List PcsQuotient.Claim) (v : ℕ) (hv : ∀ c ∈ claims, c.point.length ≤ v)
    (hB : 76 + 24 * (claims.length * (v + 1)) ≤ 1048576) :
    HashOK Short (E2ECompleteness.proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack claims) := by
  unfold E2ECompleteness.proveOpeningWithH
  split
  exact E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_openingSpongeWithH L claims v 7712 hv
      (lt_of_le_of_lt hB (by norm_num))) (by norm_num)) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_of_qc (qc_absorb _ _ _) (by norm_num)) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_runFromWithHash _ _ _ _ _ (wordsLE_openingScript L stack claims)) fun _ ↦
      E2ECompleteness.HashOK.pure _ _

/-- One point claim of at most `v ≤ 2^14` coordinates. -/
theorem hashOK_proveOpening1 (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree) (stack : Array K)
    (pt : List E) (value : E) {v : ℕ} (hv : pt.length ≤ v) (hv' : v ≤ 16384) :
    HashOK Short (E2ECompleteness.proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack [⟨pt, value⟩]) :=
  hashOK_proveOpeningWithH fuel L tree stack _ v
    (fun c hc ↦ by
      simp only [List.mem_singleton] at hc
      subst hc
      exact hv)
    (by simp only [List.length_singleton, Nat.one_mul]; omega)

/-! ## π1-rec3's stream -/

section Stream

open UniComplete UniComplete.Rec3 UniComplete.Cost
open UniComplete.Bounds (batchVarsBound valuesBound)

/-- **π1-rec3's stream hashes only short inputs** (`wc_proveStreamRec3With`'s walk), given Flock's prover's cost
with at most `2^14` blocks beyond its bytes and a batch of at most `2^14` variables. -/
theorem ws_proveStreamRec3With (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ) (tr : Trace)
    (hF : WC (flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock) kF wF
      fun _ _ ↦ True) (hkF : kF ≤ 16384) (hV : batchVarsBound tr.shape ≤ 16384) :
    WS (proveStreamRec3With callKeccak256 (commitReal callKeccak256) flock tr)
      (streamBytes3 tr.shape tr.rows.length wF) (StreamOK3 (batchVarsBound tr.shape)) := by
  unfold proveStreamRec3With streamBytes3
  refine ws_seq (ws_of_wc (wc_forIn_list (k := 0) (w := 4) _ _ _ fun _ _ ↦ wc_seq (wc_sendInteger _ 4)
    (fun _ _ _ ↦ wc_mono (wc_pure _) le_rfl le_rfl fun _ _ _ ↦ trivial) le_rfl le_rfl) (by simp))
    (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_lift (hashOK_commitReal _ _ _)) (fun committed1 _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendRoot _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_drawRunW 4) (by norm_num)) (fun alphas _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun beta _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun gamma _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_map some hF) hkF) (fun flockOut _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_lift (hashOK_commitReal _ _ _)) (fun committed2 _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_sendRoot _) (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun t _ _ ↦ ?_) (by omega)
  have ha := Bounds.atT_facts tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  have hvars := Bounds.batchVars_atT tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t flockOut
  refine ws_seq (ws_of_wc (wc_mono (wc_sendScalars _) le_rfl (Nat.mul_le_mul_left 24 ha.values) fun _ _ h ↦ h)
    (by norm_num)) (fun _ _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun rho _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc wc_sampleW (by norm_num)) (fun lambda _ _ ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_mono (wc_batchRounds3 _ _ _) hvars (Nat.mul_le_mul_left 96 hvars) fun r _ h ↦ h)
    hV) (fun r _ hr ↦ ?_) (by omega)
  refine ws_seq (ws_of_wc (wc_mono (wc_sendScalars _) le_rfl (length_claims _ _ _) fun _ _ h ↦ h) (by norm_num))
    (fun _ _ _ ↦ ?_) (by omega)
  simp only [List.length_nil, Nat.zero_add] at hr
  refine ws_of_wc (k := 0) (wc_mono (wc_get_pure _ _ fun s ↦ ⟨rfl, ?_⟩) (Nat.zero_le _) (Nat.zero_le _) fun _ _ h ↦ h)
    (by norm_num)
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨⟨c, cl⟩, _, rfl⟩ := hx
  dsimp only
  rw [List.length_take]
  omega

end Stream

/-! ## π1-rec3's prover -/

section Prover

open UniComplete UniComplete.Rec3 UniComplete.Cost
open UniComplete.Bounds (batchVarsBound valuesBound)

theorem hashOK_setupTreesOf (tr : Trace) : HashOK Short (setupTreesOf callKeccak256 tr) := by
  unfold setupTreesOf
  exact E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ E2ECompleteness.HashOK.pure _ _

set_option hygiene false in
/-- One step of the three openings' walk (`hc`, `h1` … `h3` the local facts on the claims). -/
macro "hop3_step" : tactic => `(tactic| first
  | exact E2ECompleteness.HashOK.pure _ _
  | refine E2ECompleteness.HashOK.bind (hashOK_proveOpening1 _ _ _ _ _ _ (v := batchVarsBound tr.shape) (by first
      | exact hc _ _ _ (List.mem_of_find?_eq_some h1)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h2)
      | exact hc _ _ _ (List.mem_of_find?_eq_some h3)) hV) fun _ ↦ ?_)

/-- **π1-rec3's honest prover hashes only short inputs** (`costP_proveRec3With`'s walk). -/
theorem hashOK_proveRec3With (flock : FlockProver (OracleComp KeccakCalls)) (kF wF : ℕ) (programIv : List UInt8)
    (tr : Trace) (hpub : tr.publicInput.length = 32)
    (hF : WC (flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock) kF wF
      fun _ _ ↦ True) (hkF : kF ≤ 16384) (hV : batchVarsBound tr.shape ≤ 16384)
    (hS : streamBytes3 tr.shape tr.rows.length wF ≤ 16384) (hIv : programIv.length ≤ 2 ^ 16) :
    HashOK Short (proveRec3With callKeccak256 callKeccakF1600 PcsQuotient.nonceFuel flock programIv tr) := by
  unfold proveRec3With contractIvRec3Of seedOf
  simp only [bind_assoc, pure_bind]
  refine E2ECompleteness.HashOK.bind (hashOK_setupTreesOf tr) fun trees ↦ ?_
  refine E2ECompleteness.HashOK.bind (hashOK_callKeccak256 ?_) fun d ↦ ?_
  · show _ < 2 ^ 26
    rw [List.length_append, ivInput_length', variantBytes_rec3_length, two26]
    have : (2 : ℕ) ^ 16 = 65536 := by norm_num
    omega
  refine E2ECompleteness.HashOK.bind (hashOK_callKeccak256 ?_) fun seed ↦ ?_
  · show _ < 2 ^ 26
    simp only [List.length_append, name_length, len_digestBytes, hpub, two26]
    omega
  refine (LenP.bind (ws_proveStreamRec3With flock kF wF tr hF hkF hV (Wr.start seed)
    (by simp [WInv, Wr.start]) (by simpa [Wr.start] using hS)) fun z hz ↦ lenP_of_hashOK ?_).toHashOK
  obtain ⟨⟨_, hc0⟩, -, -, -⟩ := hz
  have hc : ∀ c pt v, (c, pt, v) ∈ z.1.claims → pt.length ≤ batchVarsBound tr.shape :=
    fun c pt v h ↦ hc0 _ h
  obtain ⟨out, _⟩ := z
  dsimp only at hc ⊢
  generalize h1 : List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize h2 : List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize h3 : List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    repeat hop3_step

/-- **π1-rec3's honest prover over the two calls hashes only short inputs** (`p1k`), at the real deployment and
an honest statement of the shape's row counts. -/
theorem hashOK_p1k {D : RecDeployment} (hD : D.Real) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows) (_hrel : D.pi1.HonestRelation rows input q) :
    HashOK Short (Pi2G.p1k D input rows q) := by
  have hsh : D.pi1.shape = reference := hD.2.2.1
  have hlen : rows.length = 6 := hfit.1
  obtain ⟨-, -, -, h4⟩ := UniComplete.Cost.reference_vars
  have e : blake2sR1csLogSize + D.pi1.shape.heights.getD opBlake2s 0 = 32 := by
    rw [hsh]
    exact reference_flockLogN
  have hs := proverStream3_reference D.pi1 hsh fun _ _ ↦ 3552
  unfold proverStream3 at hs
  beta_reduce at hs
  have hF : WC (flockProve3H callKeccak256 32 flockMain (honestTrace D.pi1 input rows q).qflock) 46 3552
      fun _ _ ↦ True := by
    have h := flockCost_flockProve3H 32 flockMain (honestTrace D.pi1 input rows q).qflock
    rw [flockBlocks3_reference, flockBytes_reference] at h
    exact wc_mono h le_rfl le_rfl fun _ _ _ ↦ trivial
  unfold Pi2G.p1k uniProverRec3With
  refine hashOK_proveRec3With (flockProve3H callKeccak256) 46 3552 D.pi1.programIv
    (honestTrace D.pi1 input rows q) (by simp [honestTrace]) ?_ (by norm_num) ?_ ?_ ?_
  · rw [UniComplete.Mapping.honestTrace_shape, e]
    exact hF
  · rw [UniComplete.Mapping.honestTrace_shape, hsh]
    omega
  · rw [UniComplete.Mapping.honestTrace_shape, UniComplete.Mapping.honestTrace_rows, hlen]
    omega
  · rw [hD.2.2.2.1, Pi2G.Cost2.programIv_length]
    norm_num

end Prover

end RecCompose.Pi2A

/-- info: 'RecCompose.Pi2A.hashOK_setupTreesWithH2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2A.hashOK_setupTreesWithH2

/-- info: 'RecCompose.Pi2A.hashOK_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2A.hashOK_graph

/-- info: 'RecCompose.Pi2A.hashOK_p1k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2A.hashOK_p1k
