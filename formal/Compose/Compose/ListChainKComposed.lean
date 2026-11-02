-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Generalises `formal/Compose/Compose/Openings.lean` (`breaks_imp`, `knowledgeSoundness_composed`)
-- and `AdversaryLog.lean` (`knowledgeSoundness_composed_adv`) of this repository to the `k`-round
-- chain of `ListChainK.lean`, with the setup's commitment as `DeployedWired.lean` and
-- `WiringSetup.lean` treat the circuit's; the random-permutation step is `ListChainKRpm.lean`'s
-- transfer (`rpm_le_kcG`, adapted from `Rpm.lean`).
import Compose.ListChainKAdv
import Compose.ListChainKRpm

/-!
# The `k`-round chain composed with the openings, and with the setup's commitment

The verifier runs the chain, its own check, and the openings: one per round with a root (round
`i`'s root, its claims a function of the proof and the challenges), and the **setup's**: the
fixed commitment the label holds, computed with the oracle before the adversary runs (the
circuit's fixed columns). The openings are parameters (`OpeningsK`): what each accepts and what a
candidate must satisfy (`acc i`, `good i`), the setup's (`accS`, `goodS`: the honest table
satisfies its claims), and the verifier's own check (`check`, which rejects messages that do not
fit the rounds, `hfit`). The protocol's last state follows from its claims (`hlink`: candidates
satisfying every opening's claims, with the honest fixed table, make the opened transcript won
at the end).

**The setup's commitment is a fixed root whose only candidate is the honest table**: it adds
**no list** to the union bound (round `j`'s factor is the product over the proof's roots only),
and its opening's term is that the opening accepts while the honest table violates its claims
(`DoomSK`). For WHIR's openings and a setup computing the Merkle tree of an honest codeword,
this is `DeployedWired.lean`'s and `WiringSetup.lean`'s argument (`extract_wiringSetup`,
`candidates_honest`: the setup's queries make the extracted word the honest word, whose only
candidate is the honest table).

**The extractor** (`extractorK`) is round `0`'s root's candidate list read off the adversary's
log: an explicit function of the adversary's Keccak-256 queries and the proof
(`adversaryExtractor` for a Merkle list commitment). Knowledge soundness is broken (`BreaksK`) when
the verifier accepts while no extracted candidate's state before round `0`'s challenges holds
(`¬ pre s [] (c, values)`: the relation fails for the candidate's witness).

`breaksK_imp`: a broken run has a doomed opening, or wins the list game.
**`knowledgeSoundness_listChainK`**: in mumbai's two-oracle model, at most the openings' terms
plus `N (maxErrK + 5 N / 2^256)`; **`knowledgeSoundness_listChainK_setup`** with the setup;
**`knowledgeSoundness_listChainK_rpm`**: in the random-permutation model, through `rpm_le_kcG`,
plus `(QSπ + Q + QVπ)² / 2^508`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Rpm (HOnly DuplexVm hashBlocks)

/-! ## The openings and the events -/

/-- **What the openings check**, a parameter: the verifier's own check, whether round `i`'s
opening accepts and whether a candidate of its root satisfies its claims, whether the setup's
opening accepts and whether the setup's honest table satisfies its claims; each a function of the
proof, the challenges and what the openings returned. -/
structure OpeningsK (Pf F β M : Type) where
  check : Pf → List (List F) → β → Prop
  acc : ℕ → Pf → List (List F) → β → Prop
  good : ℕ → Pf → List (List F) → Option M → Prop
  accS : Pf → List (List F) → β → Prop
  goodS : Pf → List (List F) → Prop

variable {F St M Pf β : Type} [SampleableType F]
variable (K : ChainSpec F St) (C : ℕ → ListCommit M) (R : Piop K M)
  (view : Pf → St × List (RMsg F)) (Op : OpeningsK Pf F β M)

/-- Round `i`'s message. -/
def msgK (π : Pf) (i : ℕ) : RMsg F := (view π).2.getD i (none, [])

/-- **The verifier accepts**: its own check, every root's opening, the setup's opening. -/
def AcceptedK (z : OutK Pf F β) : Prop :=
  Op.check z.1.1 z.1.2.1 z.1.2.2 ∧
    (∀ i < K.rounds.length, (K.spec i).root → Op.acc i z.1.1 z.1.2.1 z.1.2.2) ∧
    Op.accS z.1.1 z.1.2.1 z.1.2.2

/-- **The extractor**: round `0`'s root's candidates, read off the adversary's transcript. -/
def extractorK (z : OutK Pf F β) : List (Option M) :=
  optC (C 0) (histOfTr z.2) (tableOfTr z.2) (msgK view z.1.1 0)

/-- **Knowledge soundness is broken**: the verifier accepts while no extracted candidate's state
before round `0`'s challenges holds. -/
def BreaksK (z : OutK Pf F β) : Prop :=
  AcceptedK K Op z ∧
    ∀ c ∈ extractorK C view z, ¬ R.pre (view z.1.1).1 [] (c, (msgK view z.1.1 0).2)

/-- **Round `i`'s opening is doomed**: it accepts while every candidate of its root violates its
claims. -/
def DoomK (i : ℕ) (z : OutK Pf F β) : Prop :=
  Op.acc i z.1.1 z.1.2.1 z.1.2.2 ∧
    ∀ c ∈ optC (C i) (histOfTr z.2) (tableOfTr z.2) (msgK view z.1.1 i), ¬ Op.good i z.1.1 z.1.2.1 c

/-- **The setup's opening is doomed**: it accepts while the honest table violates its claims. -/
def DoomSK (z : OutK Pf F β) : Prop := Op.accS z.1.1 z.1.2.1 z.1.2.2 ∧ ¬ Op.goodS z.1.1 z.1.2.1

/-! ## A broken run has a doomed opening or wins the list game -/

section Imp

theorem getElem_candLists (C : ℕ → ListCommit M) (H : Hist) (T : Table) :
    ∀ (i₀ : ℕ) (ms : List (RMsg F)) (i : ℕ) (h : i < (candLists C H T i₀ ms).length),
      (candLists C H T i₀ ms)[i] = optC (C (i₀ + i)) H T (ms.getD i (none, []))
  | _, [], _, h => by simp [candLists] at h
  | i₀, m :: ms, 0, _ => by simp [candLists]
  | i₀, m :: ms, i + 1, h => by
    simp only [candLists, List.getElem_cons_succ, List.getD_cons_succ]
    rw [getElem_candLists C H T (i₀ + 1) ms i (by simpa [candLists] using h)]
    rw [show i₀ + 1 + i = i₀ + (i + 1) by omega]

/-- **A member in each list gives a tuple**: if each list has a member satisfying its round's
predicate, some tuple of members satisfies them all. -/
theorem exists_forall₂_of_forall {α : Type} (P : ℕ → α → Prop) :
    ∀ (Ls : List (List α)), (∀ i (h : i < Ls.length), ∃ c ∈ Ls[i], P i c) →
      ∃ cs, List.Forall₂ (· ∈ ·) cs Ls ∧ ∀ i (h : i < cs.length), P i cs[i]
  | [], _ => ⟨[], List.Forall₂.nil, fun i h => by simp at h⟩
  | l :: Ls, h => by
    obtain ⟨c, hc, hP⟩ := h 0 (by simp)
    obtain ⟨cs, hcs, hcsP⟩ := exists_forall₂_of_forall (fun i a => P (i + 1) a) Ls
      fun i hi => h (i + 1) (by simpa using hi)
    refine ⟨c :: cs, List.Forall₂.cons hc hcs, fun i hi => ?_⟩
    cases i with
    | zero => exact hP
    | succ i => exact hcsP i (by simpa using hi)

end Imp

theorem fitsAll_getD : ∀ {rs : List RoundSpec} {ms : List (RMsg F)}, FitsAll rs ms →
    ∀ i < rs.length, (ms.getD i (none, [])).Fits (rs.getD i ⟨false, 0, 0⟩)
  | [], [], _, _, h => by simp at h
  | s :: rs, m :: ms, h, 0, _ => by simpa using h.1
  | s :: rs, m :: ms, h, i + 1, hi => by
    simpa using fitsAll_getD h.2 i (by simpa using hi)
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- The first round's state is lost when every extracted candidate's is. -/
theorem lostWon_of_extract {St' : Type} {K' : ChainSpec F St'} (R' : Piop K' M)
    (C : ℕ → ListCommit M) (H : Hist) (T : Table) (s : St') :
    ∀ (cs : List (Option M)) (ms : List (RMsg F)) (ch : List (List F)) (p : Opened M F)
      (m : Option M × List F) (c : List F),
      List.Forall₂ (· ∈ ·) cs (candLists C H T 0 ms) →
      (∀ c₀ ∈ optC (C 0) H T (ms.getD 0 (none, [])),
        ¬ R'.pre s [] (c₀, (ms.getD 0 (none, [])).2)) →
      opened cs ms ch = p ++ [(m, c)] → R'.post s p m c → R'.LostWon s (opened cs ms ch)
  | c₀ :: cs, m₀ :: ms, ch₀ :: chs, p, m, c, hcs, hext, hpe, hpost => by
    cases hcs with
    | cons h0 _ => exact ⟨hext c₀ h0, p, m, c, hpe, hpost⟩
  | [], _, _, p, m, c, _, _, hpe, _ => by simp [opened] at hpe
  | _ :: _, [], _, p, m, c, _, _, hpe, _ => by simp [opened] at hpe
  | _ :: _, _ :: _, [], p, m, c, _, _, hpe, _ => by simp [opened] at hpe

/-- **A broken run has a doomed opening, or wins the list game.** -/
theorem breaksK_imp
    (hfit : ∀ π ch b, Op.check π ch b → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch b (cs : List (Option M)), Op.check π ch b →
      cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → Op.good i π ch cs[i]) → Op.goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (z : OutK Pf F β) (h : BreaksK K C R view Op z) :
    (∃ i < K.rounds.length, (K.spec i).root ∧ DoomK C view Op i z) ∨ DoomSK Op z ∨
      ListWinsK K C R view z := by
  obtain ⟨⟨hchk, hacc, haccS⟩, hext⟩ := h
  by_contra hno
  simp only [not_or, not_exists, not_and] at hno
  obtain ⟨hD, hS, hL⟩ := hno
  have hgS : Op.goodS z.1.1 z.1.2.1 := by
    by_contra hc
    exact hS ⟨haccS, hc⟩
  have hf := hfit _ _ _ hchk
  have hlen := hf.length_eq
  set H := histOfTr z.2
  set T := tableOfTr z.2
  set ms := (view z.1.1).2
  -- A candidate satisfying each root's opening's claims.
  have hex : ∀ i (hi : i < (candLists C H T 0 ms).length),
      ∃ c ∈ (candLists C H T 0 ms)[i], (K.spec i).root → Op.good i z.1.1 z.1.2.1 c := by
    intro i hi
    rw [getElem_candLists, Nat.zero_add]
    have hik : i < K.rounds.length := by rw [length_candLists, hlen] at hi; exact hi
    by_cases hr : (K.spec i).root
    · by_contra hc
      push Not at hc
      exact hD i hik hr ⟨hacc i hik hr, fun c hc' => (hc c hc').2⟩
    · have hfi := fitsAll_getD hf i hik
      have hnone : (ms.getD i (none, [])).1 = none := by
        rw [ChainSpec.spec] at hr
        obtain ⟨hfi1, -⟩ := hfi
        cases h1 : (ms.getD i (none, [])).1 with
        | none => rfl
        | some _ =>
          rw [h1] at hfi1
          exact absurd hfi1.symm (by simpa using hr)
      refine ⟨none, ?_, fun h' => absurd h' hr⟩
      unfold optC
      rw [hnone]
      simp
  obtain ⟨cs, hcs, hcsP⟩ := exists_forall₂_of_forall _ _ hex
  have hcl : cs.length = K.rounds.length := by
    rw [hcs.length_eq, length_candLists, hlen]
  obtain ⟨p, m, c, hpe, hpost⟩ := hlink z.1.1 z.1.2.1 z.1.2.2 cs hchk hcl
    (fun i h hr => hcsP i h hr) hgS
  exact hL ⟨hf, cs, hcs, lostWon_of_extract R C H T _ cs ms _ p m c hcs
    (fun c₀ hc₀ => hext c₀ hc₀) hpe hpost⟩

/-! ## Knowledge soundness in mumbai's two-oracle model -/

theorem prEvent_exists_range_le {α : Type} (mx : ProbComp α) (E : ℕ → α → Prop)
    (ε : ℕ → ℝ≥0∞) : ∀ n : ℕ, (∀ i < n, Pr{let a ← mx}[E i a] ≤ ε i) →
      Pr{let a ← mx}[∃ i < n, E i a] ≤ ∑ i ∈ Finset.range n, ε i
  | 0, _ => by
    rw [prEvent_eq_zero_of_forall_not _ _ fun a h => by obtain ⟨i, hi, -⟩ := h; omega]
    exact bot_le
  | n + 1, h => by
    refine (prEvent_mono _ _ (fun a => (∃ i < n, E i a) ∨ E n a) fun a ha => ?_).trans
      ((prEvent_or_le _ _ _).trans ?_)
    · obtain ⟨i, hi, he⟩ := ha
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, he⟩
      · exact Or.inr he
    · rw [Finset.sum_range_succ]
      exact add_le_add (prEvent_exists_range_le mx E ε n fun i hi => h i (by omega))
        (h n (by omega))

variable [Fintype F] [DecidableEq F]

/-- **Knowledge soundness of the `k`-round chain composed with the openings, the extractor reading
the adversary's queries only**, in mumbai's two-oracle model. If round `i`'s opening (a round with
a root) is doomed with probability at most `εD i` and the setup's with probability at most `εS`,
the verifier accepts while the extracted list holds no candidate whose state before round `0`
holds with probability at most `Σ_i εD i + εS + N (maxErrK + 5 N / 2^256)`, `N = Q + nQ + QV`. -/
theorem knowledgeSoundness_listChainK (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV)
    (hfit : ∀ π ch b, Op.check π ch b → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch b (cs : List (Option M)), Op.check π ch b →
      cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → Op.good i π ch cs[i]) → Op.goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (εD : ℕ → ℝ≥0∞) (εS : ℝ≥0∞)
    (hD : ∀ i < K.rounds.length, (K.spec i).root →
      Pr{let z ← (simulateQ randomOracle (expK K view A post)).run' ∅}[DoomK C view Op i z] ≤ εD i)
    (hS : Pr{let z ← (simulateQ randomOracle (expK K view A post)).run' ∅}[DoomSK Op z] ≤ εS) :
    Pr{let z ← (simulateQ randomOracle (expK K view A post)).run' ∅}[BreaksK K C R view Op z] ≤
      (∑ i ∈ Finset.range K.rounds.length, εD i) + εS +
        ((Q + K.nQ + QV : ℕ) : ℝ≥0∞) * (maxErrK K C R +
          5 * ((Q + K.nQ + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set mx := (simulateQ randomOracle (expK K view A post)).run' ∅
  have hL := knowledgeSoundness_listK_adv K C R view A post Q QV hQ hV
  refine (prEvent_mono mx _ _ (breaksK_imp K C R view Op hfit hlink)).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine add_le_add ?_ ((prEvent_or_le _ _ _).trans ?_) |>.trans (le_of_eq (add_assoc _ _ _).symm)
  · refine (prEvent_mono mx _ (fun z => ∃ i < K.rounds.length, (K.spec i).root ∧
      DoomK C view Op i z) fun z h => h).trans ?_
    refine prEvent_exists_range_le mx (fun i z => (K.spec i).root ∧ DoomK C view Op i z) εD _
      fun i hi => ?_
    by_cases hr : (K.spec i).root
    · exact (prEvent_mono mx _ _ fun z h => h.2).trans (hD i hi hr)
    · rw [prEvent_eq_zero_of_forall_not _ _ fun z h => hr h.1]
      exact bot_le
  · exact add_le_add hS hL

/-- **With the setup**: the setup computes the fixed commitment with the oracle before the
adversary, which is given it (`setup >>= fun ir => fix ir <$> A' ir`: `fix` puts the setup's root
in the proof the verifier reads, whatever the adversary put there). This is
`ListChainKRpm.lean`'s two-oracle game `kcGameG`; the adversary's log holds the setup's queries
(public), so the extractor reads them too. -/
theorem knowledgeSoundness_listChainK_setup (setup : OracleComp KeccakCalls Bytes32)
    (fix : Bytes32 → Pf → Pf) (A' : Bytes32 → OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (QS Q QV : ℕ)
    (hSq : IsTotalQueryBound setup QS) (hQ : ∀ ir, IsTotalQueryBound (A' ir) Q)
    (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV)
    (hfit : ∀ π ch b, Op.check π ch b → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch b (cs : List (Option M)), Op.check π ch b →
      cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → Op.good i π ch cs[i]) → Op.goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (εD : ℕ → ℝ≥0∞) (εS : ℝ≥0∞)
    (hD : ∀ i < K.rounds.length, (K.spec i).root →
      Pr{let z ← (simulateQ randomOracle (kcGameG setup fix A' (verK K view post))).run' ∅}[
        DoomK C view Op i z] ≤ εD i)
    (hS : Pr{let z ← (simulateQ randomOracle (kcGameG setup fix A' (verK K view post))).run' ∅}[
      DoomSK Op z] ≤ εS) :
    Pr{let z ← (simulateQ randomOracle (kcGameG setup fix A' (verK K view post))).run' ∅}[
        BreaksK K C R view Op z] ≤
      (∑ i ∈ Finset.range K.rounds.length, εD i) + εS +
        ((QS + Q + K.nQ + QV : ℕ) : ℝ≥0∞) * (maxErrK K C R +
          5 * ((QS + Q + K.nQ + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have hA : IsTotalQueryBound (setup >>= fun ir => fix ir <$> A' ir) (QS + Q) :=
    isTotalQueryBound_bind hSq fun ir => by
      have h := isTotalQueryBound_bind
        (ob := fun x => (pure (fix ir x) : OracleComp KeccakCalls Pf)) (n₂ := 0) (hQ ir)
        fun _ => trivial
      rw [Nat.add_zero] at h
      rwa [map_eq_bind_pure_comp]
  exact knowledgeSoundness_listChainK K C R view Op _ post (QS + Q) QV hA hV hfit hlink εD εS hD hS

/-! ## In the random-permutation model -/

/-- Two transcripts recording the same answers have the same history and table. -/
theorem histOfTr_tableOfTr_congr {tr tr' : Transcript} (h : ∀ x, lookTr tr x = lookTr tr' x) :
    histOfTr tr = histOfTr tr' ∧ tableOfTr tr = tableOfTr tr' := by
  have hs : ∀ x, (tr.find? fun e => decide (e.1 = x)).map Prod.snd =
      (tr'.find? fun e => decide (e.1 = x)).map Prod.snd := fun x => by
    have := h x
    rw [lookTr_eq_map, lookTr_eq_map] at this
    exact Option.map_injective (LeanVM.Rpm.digestEquiv.symm.injective) this
  refine ⟨?_, ?_⟩
  · ext x
    rw [mem_histOfTr_iff, mem_histOfTr_iff, hs x]
  · funext x
    simp only [tableOfTr, hs x]

/-- `BreaksK` reads the transcript through its answers only. -/
theorem breaksK_congr (z : Pf × (List (List F) × β)) (tr tr' : Transcript)
    (h : ∀ x, lookTr tr x = lookTr tr' x) (hz : BreaksK K C R view Op (z, tr)) :
    BreaksK K C R view Op (z, tr') := by
  obtain ⟨hH, hT⟩ := histOfTr_tableOfTr_congr h
  refine ⟨hz.1, fun c hc => hz.2 c ?_⟩
  unfold extractorK at hc ⊢
  simp only at hc ⊢
  rwa [hH, hT]

/-- **The chain over Keccak-256 calls Keccak-256 only.** -/
theorem hOnly_runM : ∀ (y : List UInt8) (es : List (List UInt8)), HOnly (runM hash256 y es)
  | y, [] => (hOnly_hash256 y).bind fun _ => trivial
  | y, e :: es => (hOnly_hash256 y).bind fun st => (hOnly_runM (stepIn st e) es).bind fun _ => trivial

/-- **The verifier follows the duplex discipline** when the openings do. -/
theorem duplexVm_verK (post : Pf → List (List F) → OracleComp KeccakCalls β)
    (hpost : ∀ π ch, DuplexVm (post π ch) []) (π : Pf) : DuplexVm (verK K view post π) [] := by
  have e : verK K view post π = runM hash256 (K.label (view π).1)
      (absorbs K.lim K.rounds (view π).2) >>= fun sts => post π (K.chalsOf sts) >>= fun b =>
        pure (K.chalsOf sts, b) := by
    simp [verK, ChainSpec.chain, bind_map_left]
  rw [e]
  refine LeanVM.Rpm.DuplexVm.bind ?_ fun sts => LeanVM.Rpm.DuplexVm.bind (hpost π _) fun _ => trivial
  rw [LeanVM.Rpm.duplexVm_iff_duplexP]
  exact ((hOnly_runM _ _).duplexP []).mono fun _ _ _ => trivial

/-- **Knowledge soundness of the `k`-round chain in the random-permutation model** (leanerVM's
model: one uniformly random permutation of Keccak-f[1600]'s state, queried forward and inverse;
Keccak-256 the sponge over it). The setup computes the fixed commitment with Keccak-256 over `π`
(at most `QS` Keccak-256 calls, `QSπ` calls of `π`); the adversary, with coins, `π` and `π⁻¹`,
makes at most `Q` calls given it; the verifier (the chain and the openings, `QVπ` calls of `π`)
accepts while the extracted list, read off the setup's log and the Keccak-256 evaluations of the
adversary's permutation transcript, holds no candidate whose state before round `0` holds, with
probability at most the two-oracle bound for an adversary of `QS + Q` queries, plus
`(QSπ + Q + QVπ)² / 2^508`. The openings' terms are bounded for every such adversary (`hD`,
`hS`). -/
theorem knowledgeSoundness_listChainK_rpm (setup : OracleComp KeccakCalls Bytes32)
    (hSH : HOnly setup) (QS QSπ : ℕ) (hSq : IsTotalQueryBound setup QS)
    (hSπ : Common.QueryCostAtMost setup hashBlocks QSπ) (fix : Bytes32 → Pf → Pf)
    (A : Bytes32 → OracleComp Common.RandomPermutationOracles Pf) (Q : ℕ)
    (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (QV QVπ : ℕ)
    (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) (hpost : ∀ π ch, DuplexVm (post π ch) [])
    (hVπ : ∀ π, Common.QueryCostAtMost (verK K view post π) hashBlocks QVπ)
    (hfit : ∀ π ch b, Op.check π ch b → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch b (cs : List (Option M)), Op.check π ch b →
      cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → Op.good i π ch cs[i]) → Op.goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (εD : ℕ → ℝ≥0∞) (εS : ℝ≥0∞)
    (hD : ∀ A' : Bytes32 → OracleComp KeccakCalls Pf, (∀ ir, IsTotalQueryBound (A' ir) (QS + Q)) →
      ∀ i < K.rounds.length, (K.spec i).root →
        Pr{let z ← (simulateQ randomOracle (kcGameG setup fix A' (verK K view post))).run' ∅}[
          DoomK C view Op i z] ≤ εD i)
    (hS : ∀ A' : Bytes32 → OracleComp KeccakCalls Pf, (∀ ir, IsTotalQueryBound (A' ir) (QS + Q)) →
      Pr{let z ← (simulateQ randomOracle (kcGameG setup fix A' (verK K view post))).run' ∅}[
        DoomSK Op z] ≤ εS) :
    Pr{let z ← Common.runWithRandomPermutation (rpmGameG setup fix A (verK K view post))}[
        BreaksK K C R view Op (z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))] ≤
      (∑ i ∈ Finset.range K.rounds.length, εD i) + εS +
        ((QS + (QS + Q) + K.nQ + QV : ℕ) : ℝ≥0∞) * (maxErrK K C R +
          5 * ((QS + (QS + Q) + K.nQ + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        ((QSπ + Q + QVπ : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 := by
  obtain ⟨A', hA', hle⟩ := rpm_le_kcG setup hSH QS QSπ hSq hSπ fix A Q hA (verK K view post)
    (duplexVm_verK K view post hpost) QVπ hVπ (fun z tr => BreaksK K C R view Op (z, tr))
    (fun z tr tr' h hz => breaksK_congr K C R view Op z tr tr' h hz)
  exact hle.trans (add_le_add (knowledgeSoundness_listChainK_setup K C R view Op setup fix A' post
    QS (QS + Q) QV hSq hA' hV hfit hlink εD εS (hD A' hA') (hS A' hA')) le_rfl)

end Compose
