-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0), `lean_vm/LeanVM/Protocol/Compile/Rom/Complete.lean`: the honest
-- prover fails only at a proof of work (`proveFromM_eq_some_none`, here for the script runner
-- `runFromWithHash`), and a failed search puts the potential at `1` (the end of `one_le_powPot`,
-- here `one_le_powPot_of_findNonceM`). Uses, from the same commit: the proof-of-work potential
-- `powPot` and its step (`powPot_stepF`, `powPot_append_inl`, `Compile/Rom/Complete.lean`), the logged
-- random oracle and its potential engine (`ToVCVio/Rom/LoggedOracle.lean`,
-- `prEvent_run_loggedRO_le_of_freshStepBound`, `prEvent_run_randomOracle_eq_loggedRO`), the bridge
-- from a logged run to the run at the log's answers (`simulateQ_look_of_mem_support`,
-- `Compile/Rom/Bridge.lean`; `simulateQ_id_of_look`, `Compile/Rom/Prover.lean`), and WHIR's proofs
-- of work (`movesOK_verifyStackedOpening`, `EndToEnd/Sound/Moves.lean`).
import E2ECompleteness.Duplex
import E2ECompleteness.ProverBridge
import LeanVM.Protocol.Compile.Rom.Complete
import LeanVM.Protocol.EndToEnd.Sound.Moves

/-!
# The grinding at non-degenerate challenges

`RejectGood (3 · 2^-277)` (`Assemble.lean`): in the two-call random-oracle model the deployed staged
run (`stagedRun`) is rejected while its challenges `(α, β, t)` avoid `badSet` with probability at
most `3 · 2^-277`. **`rejectGood_of_tail`**, from the block count (`2^48`, the field `cost` of
`Staged.Holds`) and two facts about the pure run (`runAt`) at every hash function `H` and
permutation `F`, given the stages' run there (`StagesAt`):

* **`TailAccepts`** (Acc): when the prover's tail (`proverTail`) returns a proof `π` and the
  challenges avoid `badSet`, the verifier accepts `π`;
* **`TailReduces`** (Red): when the challenges avoid `badSet`, the reduction returns claims on the
  prover's reduction proof (`tailProof`).

Both are the Prover bridge's (`acc_staged`, `red_staged`, `ProverBridge.lean`: `tailAccepts`,
`tailReduces`), so **`rejectGood_deployed`** holds from the block count and the bridge's remaining
hypotheses (`Constants`, `Bridge.ClaimsMatch stmtConsts`, `CircuitMatch`, `TablesMatch`).

## The proof

The run against the random oracles is the run against the logged random oracle (`loggedRO`, mumbai's
`prEvent_run_randomOracle_eq_loggedRO`). On every outcome the run is the run with every query
answered by the final log `ℓ` (`simulateQ_look_of_mem_support`), and so the pure run at any
`(H, F)` extending it (`simulateQ_id_of_look`). On an outcome rejected at non-degenerate
challenges, (Acc) at such an `(H, F)` says the prover's tail returned no proof, (Red) that its
reduction returned claims, so one of its three openings returned none
(`opening_fails_of_proverTail`): its script runner failed at a `17`-bit proof of work
(`runFromWithHash_eq_some_none`, along WHIR's program `movesOK_verifyStackedOpening`), at a sponge
the prover keeps, every nonce below `2^25` failing in the log. So mumbai's potential `powPot` of
the final log is at least `1` (`one_le_powPot_of_findNonceM`). The potential starts at `0` and a
fresh query raises it by at most `(1 - 2^-17)^(2^25)` in expectation (`powPot_stepF`), so the
event has probability at most `Q · (1 - 2^-17)^(2^25)`, `Q ≤ 2^48` the queries (each at least one
block, `isTotalQueryBound_of_queryCostAtMost`): below `2^-304` (`grinding_le`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open LeanVM.Prover (Tree findNonceM powStepM Script)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Runs at a log and at a hash function and a permutation -/

/-- **The pure run** of a two-call computation at a hash function `H` and a permutation `F`. -/
abbrev runAt {α : Type} (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (oa : OracleComp KeccakCalls α) : α :=
  simulateQ (totalImpl H F) oa

theorem look_bind {α β : Type} {ℓ : Log} {oa : OracleComp KeccakCalls α}
    {f : α → OracleComp KeccakCalls β} {b : β}
    (h : simulateQ (lookImpl ℓ) (oa >>= f) = some b) :
    ∃ a, simulateQ (lookImpl ℓ) oa = some a ∧ simulateQ (lookImpl ℓ) (f a) = some b := by
  rw [simulateQ_bind] at h
  exact Option.bind_eq_some_iff.mp h

theorem look_pure {α : Type} {ℓ : Log} {a b : α}
    (h : simulateQ (lookImpl ℓ) (pure a : OracleComp KeccakCalls α) = some b) : a = b := by
  rw [simulateQ_pure] at h
  exact Option.some.inj h

theorem look_callKeccak256 {ℓ : Log} {x : Bytes} {u : Digest}
    (h : simulateQ (lookImpl ℓ) (callKeccak256 x) = some u) : lookH ℓ x = some u := by
  rw [simulateQ_queryH] at h
  exact h

/-! ## The prover fails only at a proof of work -/

section Failure

variable {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState}

/-- **The script runner fails only at a proof of work** (mumbai's `proveFromM_eq_some_none`, for
`runFromWithHash`): if it fails, with the queries answered in `Option`, along a program whose proofs
of work all have `b` bits, then a `b`-bit search fails at a sponge the honest prover keeps. -/
theorem runFromWithHash_eq_some_none (b fuel : ℕ) {α β : Type} (P : Prog α) :
    ∀ (S : Option (Script β)) (sp : Sponge) (cs : List Tree),
      EndToEnd.Sound.MovesOK (· = b) True P → ProverSp sp →
      LeanVM.Prover.runFromWithHash H F fuel P S sp cs = some none →
      ∃ sp', ProverSp sp' ∧ findNonceM F b sp' fuel = some none := by
  induction P with
  | ret a => intro S sp cs _ _ hp; cases hp
  | fail => intro S sp cs _ _ hp; cases hp
  | read k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨sp', hsp', hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact ih _ _ _ _ (hm _) (proverSp_absorb hsp hsp') hr
    · cases hp
  | sample k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨u, -, rfl⟩ := (squeeze_option _ _ _).mp hr
    exact ih _ _ _ _ (hm _) ⟨by simp, by simp⟩ hp
  | grind bits k ih =>
    intro S sp cs hm hsp hp
    have hb : bits = b := hm.1
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨o, ho, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases o with _ | n
    · subst hb
      exact ⟨sp, hsp, ho⟩
    · obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨t, ht, hp⟩ := Option.bind_eq_some_iff.mp hp
      have hsp' : ProverSp r.2 := by
        simp only [powStepM, bind, Option.bind_eq_some_iff] at hr
        obtain ⟨sp', -, hs⟩ := hr
        obtain ⟨u, -, rfl⟩ := (squeeze_option _ _ _).mp hs
        exact ⟨by simp, by simp⟩
      rcases t with _ | _
      · exact ih _ _ _ hm.2 hsp' ht
      · cases hp
  | commit ht w k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    obtain ⟨tree, -, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨sp0, h0, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨sp1, h1, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact ih _ _ _ hm.2 (proverSp_absorb (proverSp_absorb hsp h0) h1) hr
    · cases hp
  | query i ps k ih =>
    intro S sp cs hm hsp hp
    simp only [LeanVM.Prover.runFromWithHash] at hp
    split at hp
    · cases hp
    · obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      rcases r with _ | _
      · exact ih _ _ _ _ (hm _) hsp hr
      · cases hp

/-- The opening's sponge waits for nothing. -/
theorem proverSp_openingSpongeWithH {L : PcsQuotient.Layout} {claims : List PcsQuotient.Claim}
    {sp : Sponge} (h : openingSpongeWithH H F L claims = some sp) : ProverSp sp := by
  simp only [openingSpongeWithH] at h
  obtain ⟨iv, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨by simp, by simp⟩

/-- **An opening fails only at a `17`-bit proof of work.** -/
theorem proveOpeningWithH_eq_some_none {fuel : ℕ} {L : PcsQuotient.Layout} {tree : Tree}
    {stack : Array K} {claims : List PcsQuotient.Claim}
    (h : proveOpeningWithH H F fuel L tree stack claims = some none) :
    ∃ sp', ProverSp sp' ∧ findNonceM F Whir.queryGrindingBits sp' fuel = some none := by
  simp only [proveOpeningWithH] at h
  obtain ⟨sp₀, h₀, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sp₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sp₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  rcases r with _ | _
  · exact runFromWithHash_eq_some_none _ fuel _ _ _ _
      (EndToEnd.Sound.movesOK_verifyStackedOpening _ _ _)
      (proverSp_absorb (proverSp_absorb (proverSp_openingSpongeWithH h₀) h₁) h₂) hr
  · cases h

end Failure

/-! ## A failed search puts the potential at one -/

/-- **A failed proof-of-work search in the log** puts the potential at least at `1` (the end of
mumbai's `one_le_powPot`): every nonce below `fuel` at the search's position is in the log, and
fails. -/
theorem one_le_powPot_of_findNonceM {ℓ : Log} {bits fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64)
    (hfuel0 : fuel ≠ 0) {sp : Sponge} (hsp : ProverSp sp)
    (hf : findNonceM (lookF ℓ) bits sp fuel = some none) : 1 ≤ powPot bits fuel ℓ := by
  obtain ⟨-, hall⟩ := findNonceM_eq_some_none hf
  -- The position of the search, the same for every nonce.
  obtain ⟨κ, hκ, hnon⟩ : ∃ κ : PowKey, KeyOk κ ∧ ∀ n < fuel, ∃ u,
      lookF ℓ (nonceInput κ.1 κ.2 n) = some u ∧ powOk bits (nonceOf n) (challengeOf u) = false := by
    by_cases h4 : sp.pending.length = 4
    · obtain ⟨r0, hr0, -⟩ := hall 0 (Nat.pos_of_ne_zero hfuel0)
      obtain ⟨c0, ps0, u0, -, -, hif⟩ := powStepM_option hr0
      simp only [h4, ↓reduceIte] at hif
      obtain ⟨-, v, hv, -⟩ := hif
      refine ⟨(capOf v, []), ⟨by simp, by simp⟩, fun n hn ↦ ?_⟩
      obtain ⟨r, hr, hp⟩ := hall n hn
      obtain ⟨c, ps, u, hu, hru, hif⟩ := powStepM_option hr
      simp only [h4, ↓reduceIte] at hif
      obtain ⟨rfl, v', hv', rfl⟩ := hif
      rw [hv] at hv'
      cases hv'
      exact ⟨u, hu, by rw [← hru]; exact hp⟩
    · refine ⟨(capOf sp.state, sp.pending), ⟨by dsimp only; have := hsp.1; omega, hsp.2⟩,
        fun n hn ↦ ?_⟩
      obtain ⟨r, hr, hp⟩ := hall n hn
      obtain ⟨c, ps, u, hu, hru, hif⟩ := powStepM_option hr
      simp only [h4, ↓reduceIte] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact ⟨u, hu, by rw [← hru]; exact hp⟩
  -- Its term is `1`.
  have hS : ¬ Solved bits fuel ℓ κ := by
    rintro ⟨n, hn, d, hd, hp⟩
    obtain ⟨d', hd', hp'⟩ := hnon n hn
    rw [hd'] at hd
    cases hd
    rw [hp'] at hp
    cases hp
  have hT : (tried fuel ℓ κ).card = fuel := by
    have : tried fuel ℓ κ = Finset.range fuel := by
      refine Finset.filter_true_of_mem fun n hn ↦ ?_
      obtain ⟨d, hd, -⟩ := hnon n (Finset.mem_range.mp hn)
      simp [hd]
    rw [this, Finset.card_range]
  have hterm : powTerm bits fuel ℓ κ = 1 := by
    simp [powTerm, hS, hT]
  have hmem : κ ∈ keys fuel ℓ := by
    obtain ⟨u, hu, -⟩ := hnon 0 (Nat.pos_of_ne_zero hfuel0)
    obtain ⟨i, hi, hei, -⟩ := (lookF_eq_some_iff ℓ _ u).mp hu
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, mem_fIns_of_getElem hi hei,
      keyOf_nonceInput hfuel hκ (Nat.pos_of_ne_zero hfuel0)⟩)
  rw [← hterm]
  exact Finset.single_le_sum (fun _ _ ↦ bot_le) hmem

/-- **A failed opening in the log** puts the potential at least at `1`. -/
theorem one_le_powPot_of_proveOpening {ℓ : Log} {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64)
    (hfuel0 : fuel ≠ 0) {L : PcsQuotient.Layout} {tree : Tree} {stack : Array K}
    {claims : List PcsQuotient.Claim}
    (h : simulateQ (lookImpl ℓ) (proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack
      claims) = some none) :
    1 ≤ powPot Whir.queryGrindingBits fuel ℓ := by
  rw [simulateQ_proveOpeningWithH] at h
  obtain ⟨sp, hsp, hf⟩ := proveOpeningWithH_eq_some_none h
  exact one_le_powPot_of_findNonceM hfuel hfuel0 hsp hf

/-! ## The prover's tail -/

/-- **The prover's tail fails only at an opening**, when its reduction returns claims on its
reduction proof (`tailProof`, `ProverStaged.lean`). -/
theorem opening_fails_of_proverTail {ℓ : Log} (circuit : Circuit) (fuel : ℕ) (stmt : Statement)
    (a : AuxA) (bq : Tree × Array K) (t : E)
    (h : simulateQ (lookImpl ℓ) (proverTail circuit fuel stmt a bq t) = some none)
    (hred : simulateQ (lookImpl ℓ) (reduceWithH callKeccak256 circuit.logRows a.2.1.root stmt
      (tailProof circuit a bq t)) ≠ some none) :
    ∃ (L : PcsQuotient.Layout) (tree : Tree) (stack : Array K) (claims : List PcsQuotient.Claim),
      simulateQ (lookImpl ℓ) (proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack
        claims) = some none := by
  unfold proverTail at h
  obtain ⟨red, hr, h⟩ := look_bind h
  rcases red with _ | r
  · exact absurd hr hred
  obtain ⟨o₁, h₁, h⟩ := look_bind h
  rcases o₁ with _ | p₁
  · exact ⟨_, _, _, _, h₁⟩
  obtain ⟨o₂, h₂, h⟩ := look_bind h
  rcases o₂ with _ | p₂
  · exact ⟨_, _, _, _, h₂⟩
  obtain ⟨o₃, h₃, h⟩ := look_bind h
  rcases o₃ with _ | p₃
  · exact ⟨_, _, _, _, h₃⟩
  cases look_pure h

/-! ## The staged run -/

section Generic

variable (setup : OracleComp KeccakCalls Digest) (circuit : Circuit) (cells : Array K)
  (masks : Masks) (witnessPad quotientPad : Padding) (fuel vLogRows : ℕ) (stmt : Statement)

/-- **The stages at a hash function and a permutation**: the pure run of stage A gives `x`, the
chain's states are `s₁, s₂, s₃`, the pure run of stage B gives `y`, and the next state is `s₄`. -/
structure StagesAt (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (x : AuxA × Digest × (E × E)) (s₁ s₂ s₃ : Digest) (y : (Tree × Array K) × (E × E))
    (s₄ : Digest) : Prop where
  hA : runAt H F (stageAG setup circuit cells masks witnessPad stmt) = x
  h₁ : H (chainIn x.2.1 x.2.2) = s₁
  h₂ : H (digestBytes s₁) = s₂
  h₃ : H (digestBytes s₂) = s₃
  hB : runAt H F (stageBG circuit cells quotientPad x.1 s₁ s₂ s₃) = y
  h₄ : H (chainIn s₃ y.2) = s₄

/-- **(Acc), for any setup, circuit and cells**: at every hash function and permutation, when the
prover's tail returns a proof and the challenges `(α, β, t)` avoid `bad`, the verifier accepts it. -/
def TailAcceptsG (bad : Finset (E × E × E)) : Prop :=
  ∀ (H : Bytes → Digest) (F : KeccakState → KeccakState) (x : AuxA × Digest × (E × E))
    (s₁ s₂ s₃ : Digest) (y : (Tree × Array K) × (E × E)) (s₄ : Digest),
    StagesAt setup circuit cells masks witnessPad quotientPad stmt H F x s₁ s₂ s₃ y s₄ →
    (challengeOf s₁, challengeOf s₂, challengeOf s₄) ∉ bad →
    ∀ π : PcsQuotient.Proof,
      runAt H F (proverTail circuit fuel stmt x.1 y.1 (challengeOf s₄)) = some π →
      verifyWithH (m := Id) H F vLogRows x.1.1 stmt π = true

/-- **(Red), for any setup, circuit and cells**: at every hash function and permutation, when the
challenges `(α, β, t)` avoid `bad`, the reduction returns claims on the prover's reduction proof. -/
def TailReducesG (bad : Finset (E × E × E)) : Prop :=
  ∀ (H : Bytes → Digest) (F : KeccakState → KeccakState) (x : AuxA × Digest × (E × E))
    (s₁ s₂ s₃ : Digest) (y : (Tree × Array K) × (E × E)) (s₄ : Digest),
    StagesAt setup circuit cells masks witnessPad quotientPad stmt H F x s₁ s₂ s₃ y s₄ →
    (challengeOf s₁, challengeOf s₂, challengeOf s₄) ∉ bad →
    reduceWithH (m := Id) H circuit.logRows x.1.2.1.root stmt
      (tailProof circuit x.1 y.1 (challengeOf s₄)) ≠ none

/-- **A run rejected at non-degenerate challenges puts the potential at one.** On a log at which the
staged run is rejected while its challenges avoid `bad`, given (Acc) and (Red), one of the prover's
openings failed at a `17`-bit proof of work whose nonces below `fuel` all fail in the log. -/
theorem one_le_powPot_of_rejected {bad : Finset (E × E × E)} (hfuel : fuel ≤ 2 ^ 64)
    (hfuel0 : fuel ≠ 0)
    (hacc : TailAcceptsG setup circuit cells masks witnessPad quotientPad fuel vLogRows stmt bad)
    (hred : TailReducesG setup circuit cells masks witnessPad quotientPad stmt bad)
    {ℓ : Log} {z : Bool × (E × E × E)}
    (hz : simulateQ (lookImpl ℓ)
      (stagedRunG setup circuit cells masks witnessPad quotientPad fuel vLogRows stmt) = some z)
    (hrej : z.1 = false) (hgood : z.2 ∉ bad) :
    1 ≤ powPot Whir.queryGrindingBits fuel ℓ := by
  -- A hash function and a permutation extending the log.
  let Ht : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default
  let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD default
  have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
  have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
  have hid : ∀ {β : Type} (oa : OracleComp KeccakCalls β) (r : β),
      simulateQ (lookImpl ℓ) oa = some r → runAt Ht Ft oa = r :=
    fun oa r h ↦ simulateQ_id_of_look ℓ Ht Ft hH hF oa r h
  -- The staged run at the log.
  unfold stagedRunG staged at hz
  obtain ⟨x, hx, hz⟩ := look_bind hz
  obtain ⟨s₁, hs₁, hz⟩ := look_bind hz
  obtain ⟨s₂, hs₂, hz⟩ := look_bind hz
  obtain ⟨s₃, hs₃, hz⟩ := look_bind hz
  obtain ⟨y, hy, hz⟩ := look_bind hz
  obtain ⟨s₄, hs₄, hz⟩ := look_bind hz
  obtain ⟨v, hv, hz⟩ := look_bind hz
  obtain rfl := look_pure hz
  have hst : StagesAt setup circuit cells masks witnessPad quotientPad stmt Ht Ft x s₁ s₂ s₃ y s₄ :=
    ⟨hid _ _ hx, hH _ _ (look_callKeccak256 hs₁), hH _ _ (look_callKeccak256 hs₂),
      hH _ _ (look_callKeccak256 hs₃), hid _ _ hy, hH _ _ (look_callKeccak256 hs₄)⟩
  -- The verdict.
  unfold stageCG at hv
  obtain ⟨o, ho, hv⟩ := look_bind hv
  rcases o with _ | π
  · -- The prover's tail returned no proof: an opening failed.
    obtain ⟨L, tree, stack, claims, hfail⟩ :=
      opening_fails_of_proverTail circuit fuel stmt x.1 y.1 _ ho fun hr ↦
        hred Ht Ft x s₁ s₂ s₃ y s₄ hst hgood (by
          have h := hid _ _ hr
          rw [runAt, simulateQ_reduceWithH] at h
          exact h)
    exact one_le_powPot_of_proveOpening hfuel hfuel0 hfail
  · -- The prover's tail returned a proof: the verifier accepts it, a contradiction.
    exfalso
    have hver := hid _ _ hv
    rw [runAt, simulateQ_verifyWithH] at hver
    have hacc' := hacc Ht Ft x s₁ s₂ s₃ y s₄ hst hgood π (hid _ _ ho)
    have hvt : v = true := hver.symm.trans hacc'
    simp only at hrej
    rw [hvt] at hrej
    cases hrej

end Generic

/-! ## The deployed instance -/

/-- **(Acc) on the deployed instance** (the Prover bridge's): for a witness, at every hash function
and permutation, the honest proof the prover's tail returns is accepted when the challenges avoid
`badSet`. -/
def TailAccepts : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w → ∀ coins : Masks × Padding × Padding,
    TailAcceptsG (setupWithH callKeccak256) (membership logRows) (cellsOf w) coins.1 coins.2.1
      coins.2.2 nonceFuel logRows stmt (badSet w coins.1)

/-- **(Red) on the deployed instance** (the Prover bridge's): for a witness, at every hash function
and permutation, the reduction returns claims on the prover's reduction proof when the challenges
avoid `badSet`. -/
def TailReduces : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w → ∀ coins : Masks × Padding × Padding,
    TailReducesG (setupWithH callKeccak256) (membership logRows) (cellsOf w) coins.1 coins.2.1
      coins.2.2 stmt (badSet w coins.1)

/-- **At most `N` blocks is at most `N` queries**: every query costs at least one block. -/
theorem isTotalQueryBound_of_queryCostAtMost {α : Type} {oa : OracleComp KeccakCalls α} {N : ℕ}
    (h : Common.QueryCostAtMost oa hashBlocks N) : IsTotalQueryBound oa N := by
  induction oa using OracleComp.inductionOn generalizing N with
  | pure x => trivial
  | query_bind t mx ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    have ht' : hashBlocks t ≤ N := ht
    have h1 : 1 ≤ hashBlocks t := by rcases t with x | s <;> simp [hashBlocks]
    exact isTotalQueryBound_query_bind_iff.2 ⟨by omega, fun u ↦ (ih u (hk u)).mono (by omega)⟩

/-- **The numbers**: `2^48` queries, each completing a `17`-bit proof of work whose `2^25` nonces all
failed with probability `(1 - 2^-17)^(2^25) ≤ (3/8)^(2^8)` (mumbai's
`one_sub_pow_le_three_eighths`): below `2^-304`. -/
theorem grinding_le : ((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ nonceFuel ≤
    (2 : ℝ≥0∞)⁻¹ ^ 304 := by
  have hb : Whir.queryGrindingBits = 17 := rfl
  have hf : nonceFuel = 2 ^ 17 * 2 ^ 8 := by norm_num [nonceFuel]
  have hy : (0 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 17 := by norm_num
  have h38 : (1 - (1 / 2 : ℝ) ^ 17) ^ (2 ^ 17) ≤ 3 / 8 := one_sub_pow_le_three_eighths 17
  have hreal : (2 : ℝ) ^ 48 * ((1 - (1 / 2 : ℝ) ^ 17) ^ (2 ^ 17)) ^ (2 ^ 8) ≤ (1 / 2) ^ 304 := by
    calc (2 : ℝ) ^ 48 * ((1 - (1 / 2 : ℝ) ^ 17) ^ (2 ^ 17)) ^ (2 ^ 8)
        ≤ (2 : ℝ) ^ 48 * (3 / 8) ^ (2 ^ 8) := by gcongr
      _ ≤ ((1 / 2) ^ 152) ^ 2 := by norm_num
      _ = (1 / 2) ^ 304 := by rw [← pow_mul]
  rw [hb, hf, pow_mul, missProb_eq_ofReal, ← ENNReal.ofReal_pow hy,
    ← ENNReal.ofReal_pow (pow_nonneg hy _)]
  calc ((2 ^ 48 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (((1 - (1 / 2 : ℝ) ^ 17) ^ 2 ^ 17) ^ 2 ^ 8)
      = ENNReal.ofReal ((2 : ℝ) ^ 48 * ((1 - (1 / 2 : ℝ) ^ 17) ^ 2 ^ 17) ^ 2 ^ 8) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        norm_num
    _ ≤ ENNReal.ofReal ((1 / 2) ^ 304) := ENNReal.ofReal_le_ofReal hreal
    _ = (2 : ℝ≥0∞)⁻¹ ^ 304 := by
        rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num

/-- **`RejectGood (3 · 2^-277)`**, from the block count `2^48` of the deployed staged run, (Acc) and
(Red): the deployed staged run is rejected at non-degenerate challenges with probability below
`2^-304`. -/
theorem rejectGood_of_tail
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48))
    (hacc : TailAccepts) (hred : TailReduces) : RejectGood (3 * (2 : ℝ≥0∞)⁻¹ ^ 277) := by
  intro stmt w hrel c
  have hfuel : nonceFuel ≤ 2 ^ 64 := by norm_num [nonceFuel]
  have hfuel0 : nonceFuel ≠ 0 := by norm_num [nonceFuel]
  have hstep : LogFreshStepBound (powPot Whir.queryGrindingBits nonceFuel)
      (missProb Whir.queryGrindingBits ^ nonceFuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF (by decide) (by decide) hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have e : Pr{let z ← (simulateQ ro (stagedRun stmt w (coinsOf c))).run' ∅}[
      z.1 = false ∧ z.2 ∉ badSet w (coinsOf c).1] =
      Pr{let z ← (simulateQ loggedRO (stagedRun stmt w (coinsOf c))).run []}[
        z.1.1 = false ∧ z.1.2 ∉ badSet w (coinsOf c).1] := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_run_randomOracle_eq_loggedRO _
      (fun (z : Bool × (E × E × E)) _ ↦ z.1 = false ∧ z.2 ∉ badSet w (coinsOf c).1)
  rw [e]
  refine (prEvent_run_loggedRO_le_of_freshStepBound hstep _ (2 ^ 48)
    (isTotalQueryBound_of_queryCostAtMost (hcost stmt w (coinsOf c))) []
    (fun (z : Bool × (E × E × E)) _ ↦ z.1 = false ∧ z.2 ∉ badSet w (coinsOf c).1)
    fun z hz hev ↦ ?_).trans ?_
  · have hlook := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
    exact one_le_powPot_of_rejected _ _ _ _ _ _ _ _ _ hfuel hfuel0
      (hacc stmt w hrel (coinsOf c)) (hred stmt w hrel (coinsOf c)) hlook hev.1 hev.2
  · rw [powPot_nil, zero_add]
    calc ((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ nonceFuel
        ≤ (2 : ℝ≥0∞)⁻¹ ^ 304 := grinding_le
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 277 := inv_pow_le_inv_pow (by norm_num)
      _ ≤ 3 * (2 : ℝ≥0∞)⁻¹ ^ 277 := le_mul_of_one_le_left bot_le (by norm_num)

/-! ## (Acc) and (Red) from the Prover bridge -/

/-- The Prover bridge's functions answering the two calls are mumbai's `totalImpl`. -/
theorem implHF_eq_totalImpl (H : Bytes → Digest) (F : KeccakState → KeccakState) :
    implHF H F = totalImpl H F := by
  funext t
  rcases t with x | s <;> rfl

section Bridge

variable (hK : Constants) (hcl : Bridge.ClaimsMatch stmtConsts) (hcirc : CircuitMatch)
  (hT : TablesMatch)

include hK hcl hcirc hT

/-- **(Acc)**, the Prover bridge's `acc_staged`. -/
theorem tailAccepts : TailAccepts := by
  intro stmt w hrel coins H F x s₁ s₂ s₃ y s₄ hst hgood π hπ
  have hA : simulateQ (implHF H F) (stageAG (setupWithH callKeccak256) (membership logRows)
      (cellsOf w) coins.1 coins.2.1 stmt) = x := by
    rw [implHF_eq_totalImpl]; exact hst.hA
  have hB : simulateQ (implHF H F) (stageBG (membership logRows) (cellsOf w) coins.2.2 x.1 s₁ s₂
      s₃) = y := by
    rw [implHF_eq_totalImpl]; exact hst.hB
  have hπ' : simulateQ (implHF H F) (proverTail (membership logRows) nonceFuel stmt x.1 y.1
      (challengeOf s₄)) = some π := by
    rw [implHF_eq_totalImpl]; exact hπ
  exact acc_staged hK hcl hcirc hT H F stmt w hrel coins.1 coins.2.1 coins.2.2 x hA s₁ s₂ s₃
    hst.h₁ hst.h₂ hst.h₃ y hB s₄ hst.h₄ hgood π hπ'

/-- **(Red)**, the Prover bridge's `red_staged`. -/
theorem tailReduces : TailReduces := by
  intro stmt w hrel coins H F x s₁ s₂ s₃ y s₄ hst hgood
  have hA : simulateQ (implHF H F) (stageAG (setupWithH callKeccak256) (membership logRows)
      (cellsOf w) coins.1 coins.2.1 stmt) = x := by
    rw [implHF_eq_totalImpl]; exact hst.hA
  have hB : simulateQ (implHF H F) (stageBG (membership logRows) (cellsOf w) coins.2.2 x.1 s₁ s₂
      s₃) = y := by
    rw [implHF_eq_totalImpl]; exact hst.hB
  rw [membership_logRows]
  exact red_staged hK hcl hcirc hT H F stmt w hrel coins.1 coins.2.1 coins.2.2 x hA s₁ s₂ s₃
    hst.h₁ hst.h₂ hst.h₃ y hB s₄ hst.h₄ hgood

/-- **`RejectGood (3 · 2^-277)`**, from the block count `2^48` of the deployed staged run and the
Prover bridge's remaining hypotheses (the Statement's constants, its claims being Compose's, the
membership circuit being F0b's, the prover's tables being Completeness's). -/
theorem rejectGood_deployed
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48)) :
    RejectGood (3 * (2 : ℝ≥0∞)⁻¹ ^ 277) :=
  rejectGood_of_tail hcost (tailAccepts hK hcl hcirc hT) (tailReduces hK hcl hcirc hT)

end Bridge

end E2ECompleteness
