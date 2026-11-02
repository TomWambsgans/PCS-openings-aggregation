-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the duplex discipline (`LeanVM.Rpm.DuplexVm`, `DuplexP`, `HOnly`) and its
-- rules for the sponge, the runners and the Merkle trees (`duplexP_absorb`, `duplexP_run`,
-- `duplexP_findNonceM`, `duplexP_powStepM`, `hOnly_buildTreeM`, `admissibleVm_seedInput`).
import E2ECompleteness.Assemble
import LeanVM.Protocol.Rpm.Duplex

/-!
# The duplex discipline of the deployed staged run

Every Keccak-f[1600] call of the honest run either continues a duplex (its capacity, lanes
`16 … 24`, an earlier answer's) or starts one at a zero capacity (an opening's seed,
`F(seedInput iv 0)`): mumbai's `DuplexVm`. Each opening, prover's and verifier's, starts its own
duplex, so every piece is disciplined from any earlier answers (`Disc`), and so is their sequence.
**`duplexVm_stagedRun`**.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover (Tree)
open scoped ENNReal
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness

/-- Disciplined from any earlier answers. -/
def Disc {α : Type} (X : OracleComp KeccakCalls α) : Prop :=
  ∀ h : List KeccakState, DuplexP X h fun _ _ ↦ True

theorem Disc.bind {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    (hX : Disc X) (hf : ∀ a, Disc (f a)) : Disc (X >>= f) :=
  fun h ↦ (hX h).bind fun a h' _ ↦ hf a h'

theorem disc_pure {α : Type} (a : α) : Disc (pure a : OracleComp KeccakCalls α) := fun _ ↦ trivial

theorem disc_of_hOnly {α : Type} {X : OracleComp KeccakCalls α} (hX : HOnly X) : Disc X :=
  fun h ↦ (hX.duplexP h).mono fun _ _ _ ↦ trivial

theorem Disc.map {α β : Type} {X : OracleComp KeccakCalls α} (f : α → β) (hX : Disc X) :
    Disc (f <$> X) := by
  rw [map_eq_bind_pure_comp]
  exact hX.bind fun _ ↦ disc_pure _

/-! ## The hash-only pieces -/

theorem hOnly_startWithH (label : List UInt8) : HOnly (startWithH callKeccak256 label) :=
  (hOnly_queryH _).bind fun _ ↦ hOnly_pure _

theorem hOnly_squeezeWithH (c : Chain) : HOnly (squeezeWithH callKeccak256 c) :=
  (hOnly_queryH _).bind fun _ ↦ hOnly_pure _

theorem hOnly_reduceWithH (logRows : ℕ) (indexRoot : Digest) (stmt : Statement)
    (p : ReductionProof) : HOnly (reduceWithH callKeccak256 logRows indexRoot stmt p) := by
  unfold reduceWithH
  split
  · exact hOnly_pure _
  · refine (hOnly_startWithH _).bind fun c ↦ ?_
    split
    · exact hOnly_pure _
    · refine (hOnly_squeezeWithH _).bind fun ⟨α, c₁⟩ ↦ ?_
      refine (hOnly_squeezeWithH _).bind fun ⟨β, c₂⟩ ↦ ?_
      refine (hOnly_squeezeWithH _).bind fun ⟨γ, c₃⟩ ↦ ?_
      dsimp only
      split
      · exact hOnly_pure _
      · refine (hOnly_squeezeWithH _).bind fun ⟨t, c₄⟩ ↦ ?_
        dsimp only
        exact (hOnly_squeezeWithH _).bind fun ⟨ρ, _⟩ ↦ hOnly_pure _

theorem hOnly_commitWithH (μ : ℕ) (stack : Array K) : HOnly (commitWithH callKeccak256 μ stack) :=
  hOnly_buildTreeM _ _

theorem hOnly_setupWithH : HOnly (setupWithH callKeccak256) :=
  (hOnly_commitWithH _ _).bind fun _ ↦ hOnly_pure _

/-! ## The openings -/

theorem duplexP_openingSpongeWithH (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim)
    (h : List KeccakState) :
    DuplexP (openingSpongeWithH callKeccak256 callKeccakF1600 L claims) h
      fun sp h' ↦ sp.state ∈ h' := by
  unfold openingSpongeWithH
  refine (((hOnly_queryH _).duplexP h)).bind fun iv h' hh ↦ ?_
  subst hh
  exact (duplexP_queryF_bind _ _ _ _).mpr
    ⟨admissibleVm_seedInput _ _ _, fun y ↦ List.mem_cons_self⟩

/-- **The verifier's opening is disciplined.** -/
theorem disc_openingWithH (L : PcsQuotient.Layout) (root : Digest)
    (claims : List PcsQuotient.Claim) (proof : Compile.Proof) :
    Disc (openingWithH callKeccak256 callKeccakF1600 L root claims proof) := by
  intro h
  unfold openingWithH
  split
  · split
    · refine (duplexP_openingSpongeWithH L claims h).bind fun sp h₁ hs ↦ ?_
      refine (duplexP_absorb hs _ _).bind fun sp h₂ hs ↦ ?_
      refine (duplexP_absorb hs _ _).bind fun sp h₃ hs ↦ ?_
      split
      · split
        · exact (duplexP_run _ _ _ hs).bind fun z _ _ ↦ by split <;> trivial
        · trivial
      · trivial
    · trivial
  · trivial

/-- **The verifier is disciplined.** -/
theorem disc_verifyWithH (logRows : ℕ) (indexRoot : Digest) (stmt : Statement)
    (proof : PcsQuotient.Proof) :
    Disc (verifyWithH callKeccak256 callKeccakF1600 logRows indexRoot stmt proof) := by
  unfold verifyWithH
  refine (disc_of_hOnly (hOnly_reduceWithH _ _ _ _)).bind fun o ↦ ?_
  split
  · exact disc_pure _
  · refine (disc_openingWithH _ _ _ _).bind fun b₁ ↦ ?_
    split
    · exact disc_pure _
    · refine (disc_openingWithH _ _ _ _).bind fun b₂ ↦ ?_
      split
      · exact disc_pure _
      · exact disc_openingWithH _ _ _ _

/-- **The prover's script runner keeps the discipline**, from a sponge whose state is an earlier
answer (mumbai's `duplexP_proveFromM`, for `runFromWithHash`). -/
theorem duplexP_runFromWithHash (fuel : ℕ) {α β : Type} (P : Prog α) :
    ∀ (S : Option (LeanVM.Prover.Script β)) (sp : Sponge) (cs : List Tree) (h : List KeccakState),
      sp.state ∈ h →
      DuplexP (LeanVM.Prover.runFromWithHash callKeccak256 callKeccakF1600 fuel P S sp cs) h
        fun _ _ ↦ True := by
  induction P with
  | ret a => intro S sp cs h _; trivial
  | fail => intro S sp cs h _; trivial
  | read k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    exact (duplexP_absorb hs _ _).bind fun sp' h' hsp ↦
      (ih _ _ _ _ _ hsp).bind fun _ _ _ ↦ trivial
  | sample k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    exact (duplexP_squeeze hs).bind fun r h' hr ↦ ih _ _ _ _ _ hr
  | grind bits k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    refine (duplexP_findNonceM bits hs fuel).bind fun r h' hr ↦ ?_
    split
    · trivial
    · exact (duplexP_powStepM hr _).bind fun r' h'' hr' ↦
        (ih _ _ _ _ hr').bind fun _ _ _ ↦ trivial
  | commit ht w k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    refine ((hOnly_buildTreeM _ _).duplexP h).bind fun tree h' hh ↦ ?_
    subst hh
    exact (duplexP_absorb hs _ _).bind fun sp0 h0 hs0 ↦ (duplexP_absorb hs0 _ _).bind
      fun sp1 h1 hs1 ↦ (ih _ _ _ _ hs1).bind fun _ _ _ ↦ trivial
  | query i ps k ih =>
    intro S sp cs h hs
    simp only [LeanVM.Prover.runFromWithHash]
    split
    · trivial
    · exact (ih _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial

/-- **The prover's opening is disciplined.** -/
theorem disc_proveOpeningWithH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree)
    (stack : Array K) (claims : List PcsQuotient.Claim) :
    Disc (proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack claims) := by
  intro h
  unfold proveOpeningWithH
  refine (duplexP_openingSpongeWithH L claims h).bind fun sp h₁ hs ↦ ?_
  refine (duplexP_absorb hs _ _).bind fun sp h₂ hs ↦ ?_
  refine (duplexP_absorb hs _ _).bind fun sp h₃ hs ↦ ?_
  exact (duplexP_runFromWithHash _ _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial

/-! ## The stages -/

theorem disc_proverTail (circuit : Circuit) (fuel : ℕ) (stmt : Statement) (a : AuxA)
    (bq : Tree × Array K) (t : E) : Disc (proverTail circuit fuel stmt a bq t) := by
  unfold proverTail
  refine (disc_of_hOnly (hOnly_reduceWithH _ _ _ _)).bind fun o ↦ ?_
  split
  · exact disc_pure _
  · refine (disc_proveOpeningWithH _ _ _ _ _).bind fun o₁ ↦ ?_
    split
    · refine (disc_proveOpeningWithH _ _ _ _ _).bind fun o₂ ↦ ?_
      split
      · refine (disc_proveOpeningWithH _ _ _ _ _).bind fun o₃ ↦ ?_
        split
        · exact disc_pure _
        · exact disc_pure _
      · exact disc_pure _
    · exact disc_pure _

theorem hOnly_stageAG (setup : OracleComp KeccakCalls Digest) (hs : HOnly setup)
    (circuit : Circuit) (cells : Array K) (masks : Masks) (witnessPad : Padding)
    (stmt : Statement) : HOnly (stageAG setup circuit cells masks witnessPad stmt) := by
  unfold stageAG
  exact hs.bind fun _ ↦ (hOnly_commitWithH _ _).bind fun _ ↦ (hOnly_commitWithH _ _).bind fun _ ↦
    (hOnly_queryH _).bind fun _ ↦ hOnly_pure _

theorem hOnly_stageBG (circuit : Circuit) (cells : Array K) (quotientPad : Padding) (a : AuxA)
    (s₁ s₂ s₃ : Digest) : HOnly (stageBG circuit cells quotientPad a s₁ s₂ s₃) := by
  unfold stageBG
  exact (hOnly_commitWithH _ _).bind fun _ ↦ hOnly_pure _

theorem disc_stageCG (circuit : Circuit) (fuel vLogRows : ℕ) (stmt : Statement) (a : AuxA)
    (bq : Tree × Array K) (s₁ s₂ s₃ s₄ : Digest) :
    Disc (stageCG circuit fuel vLogRows stmt a bq s₁ s₂ s₃ s₄) := by
  unfold stageCG
  refine (disc_proverTail _ _ _ _ _ _).bind fun o ↦ ?_
  split
  · exact disc_pure _
  · exact disc_verifyWithH _ _ _ _

/-- A computation of the chain's shape is disciplined when its stages are. -/
theorem disc_staged {α β γ : Type} (chal : Digest → E)
    (A : OracleComp KeccakCalls (α × Digest × (E × E)))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × (E × E)))
    (C : α → β → Digest → Digest → Digest → Digest → OracleComp KeccakCalls γ)
    (hA : Disc A) (hB : ∀ a s₁ s₂ s₃, Disc (B a s₁ s₂ s₃))
    (hC : ∀ a b s₁ s₂ s₃ s₄, Disc (C a b s₁ s₂ s₃ s₄)) : Disc (staged chal A B C) := by
  unfold staged
  exact hA.bind fun x ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun s₁ ↦
    (disc_of_hOnly (hOnly_queryH _)).bind fun s₂ ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun s₃ ↦
      (hB _ _ _ _).bind fun y ↦ (disc_of_hOnly (hOnly_queryH _)).bind fun s₄ ↦
        (hC _ _ _ _ _ _).bind fun _ ↦ disc_pure _

theorem disc_stagedRunG (setup : OracleComp KeccakCalls Digest) (hs : HOnly setup)
    (circuit : Circuit) (cells : Array K) (masks : Masks) (witnessPad quotientPad : Padding)
    (fuel vLogRows : ℕ) (stmt : Statement) :
    Disc (stagedRunG setup circuit cells masks witnessPad quotientPad fuel vLogRows stmt) :=
  disc_staged _ _ _ _ (disc_of_hOnly (hOnly_stageAG setup hs _ _ _ _ _))
    (fun _ _ _ _ ↦ disc_of_hOnly (hOnly_stageBG _ _ _ _ _ _ _))
    (fun _ _ _ _ _ _ ↦ disc_stageCG _ _ _ _ _ _ _ _ _ _)

/-- **The deployed staged run follows the duplex discipline.** -/
theorem duplexVm_stagedRun (stmt : Statement) (w : Secret) (coins : Masks × Padding × Padding) :
    DuplexVm (stagedRun stmt w coins) [] :=
  (duplexVm_iff_duplexP _ _).mpr
    (disc_stagedRunG _ hOnly_setupWithH _ _ _ _ _ _ _ _ [])

/-- **`PcsQuotient.Completeness deltaDeployed`** from the block count `2^48` of the deployed staged
run and the grinding bound `3 · 2^-277` at non-degenerate challenges (the duplex discipline
proved, `duplexVm_stagedRun`). -/
theorem completeness_deployed_cost_rej
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48))
    (hrej : RejectGood (3 * (2 : ℝ≥0∞)⁻¹ ^ 277)) :
    PcsQuotient.Completeness deltaDeployed :=
  completeness_deployed_staged duplexVm_stagedRun hcost hrej

end E2ECompleteness
