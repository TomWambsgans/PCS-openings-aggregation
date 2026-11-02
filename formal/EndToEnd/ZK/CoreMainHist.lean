-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The sponge, the proof-of-work search and the trees (`buildTreeM`, `Tree.opening`) are leanerVM's
-- (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Run.lean`,
-- `Statement/LeanVmVerifier.lean`).
import ZK.CoreOpen
import ZK.Budget

/-!
# The skeleton's history through an opening, and the sizes of the statement's multiproofs

Two facts the assembly of the deployed core (`CoreMain.lean`) needs besides `opening_eq`:

* **the history** (`NC`, `nc_opening`): against any oracle, an opening of the skeleton
  (`Deployed.opening`) appends to the recorded challenges exactly one answer per draw of its events
  (`drawsIn (openingEv sh)`), while that many remain below `P.n`; every other operation (hashes,
  permutations, messages, leaves) leaves them alone. So the wiring opening starts after `5 + 123`
  answers, the quotient opening after `128 + 114`, the first five always the reduction's chain's;
* **the multiproofs** (`runEvS_small`): the statement's event-driven run (`runEvS`) of a script
  committing rows of at most `192` words, from trees of such rows, makes one multiproof per opened
  event, each of at most `q` positions (`q` the event's query count) and rows of at most `192` words:
  `FmtSmall`'s bounds (`CoreBudget.lean`) for the deployed openings (at most `6` query phases, at most
  `225` queries).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open QuotientZk.Deployed (OSt Dx drawO sendK commitNext takeOpened takeScalars takeRows sortedUnique
  prune grind tryNonce rounds drawMany ood queryPhase DSpec Out Inp Msg Item)

namespace PcsQuotient.EndToEnd.Core

open Render (OWordsLE oWordsLE_afterSend oWordsLE_afterSample oWordsLE_afterGrind
  oWordsLE_afterCommit oWordsLE_afterQuery length_wordOf_le)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## The history -/

section Hist

variable {S₀ : Type} (P : QuotientZk.Proto S₀ Inp Out Msg QuotientZk.Deployed.Tbl
  QuotientZk.Deployed.Pos) (G : Inp → Out) (s : S₀)

open Merkle (runDet_bind runDet_pure)

/-- **`X` appends exactly `k` answers to the recorded challenges**, from every history with `k`
remaining below `P.n`. -/
def NC {α : Type} (X : OracleComp DSpec α) (k : ℕ) : Prop :=
  ∀ hist : List Out, hist.length + k ≤ P.n →
    ∃ l : List Out, (runDet P G s X hist).2 = hist ++ l ∧ l.length = k

theorem nc_pure {α : Type} (a : α) : NC P G s (pure a) 0 := fun hist _ ↦
  ⟨[], by rw [runDet_pure, List.append_nil], rfl⟩

theorem NC.bind {α β : Type} {X : OracleComp DSpec α} {f : α → OracleComp DSpec β} {k₁ k₂ k : ℕ}
    (hX : NC P G s X k₁) (hf : ∀ a, NC P G s (f a) k₂) (hk : k₁ + k₂ = k) :
    NC P G s (X >>= f) k := by
  intro hist hn
  obtain ⟨l₁, h1, hl₁⟩ := hX hist (by omega)
  obtain ⟨l₂, h2, hl₂⟩ := hf (runDet P G s X hist).1 (runDet P G s X hist).2
    (by rw [h1, List.length_append]; omega)
  refine ⟨l₁ ++ l₂, ?_, by rw [List.length_append]; omega⟩
  rw [runDet_bind, h2, h1, List.append_assoc]

theorem NC.congr {α : Type} {X Y : OracleComp DSpec α} {k : ℕ}
    (h : ∀ hist, runDet P G s X hist = runDet P G s Y hist) (hY : NC P G s Y k) : NC P G s X k :=
  fun hist hn ↦ by rw [h]; exact hY hist hn

theorem nc_hashH (m : List UInt8) : NC P G s (QuotientZk.Deployed.hashH m) 0 := fun hist _ ↦
  ⟨[], by rw [Merkle.runDet_hashH, List.append_nil], rfl⟩

theorem nc_perm (x : QuotientZk.Deployed.KSt) : NC P G s (QuotientZk.Deployed.perm x) 0 :=
  fun hist _ ↦ ⟨[], by rw [List.append_nil]; rfl, rfl⟩

theorem nc_chalF (x : QuotientZk.Deployed.KSt) : NC P G s (QuotientZk.Deployed.chalF x) 1 := by
  intro hist hn
  refine ⟨[G (.inr x)], ?_, rfl⟩
  show (if hist.length < P.n then hist ++ [G (.inr x)] else hist) = _
  simp only [show hist.length < P.n from by omega, ↓reduceIte]

theorem nc_getMsg : NC P G s QuotientZk.Deployed.getMsg 0 := fun hist _ ↦
  ⟨[], by rw [List.append_nil]; rfl, rfl⟩

theorem nc_absorb (d : Dx) (x : QuotientRpm.Limbs) (tag : UInt64) : NC P G s (d.absorb x tag) 0 := by
  unfold Dx.absorb
  split
  · exact (nc_perm P G s _).bind P G s (fun _ ↦ nc_pure P G s _) rfl
  · exact nc_pure P G s _

theorem nc_absorbAll : ∀ (d : Dx) (xs : List QuotientRpm.Limbs), NC P G s (d.absorbAll xs) 0
  | _, [] => nc_pure P G s _
  | d, x :: xs => (nc_absorb P G s d x _).bind P G s (fun d' ↦ nc_absorbAll d' xs) rfl

theorem nc_draw (d : Dx) : NC P G s d.draw 1 :=
  (nc_chalF P G s _).bind P G s (fun _ ↦ nc_pure P G s _) rfl

theorem nc_seed (iv : QuotientRpm.Bytes32) : NC P G s (QuotientZk.Deployed.seed iv) 0 :=
  (nc_perm P G s _).bind P G s (fun _ ↦ nc_pure P G s _) rfl

theorem nc_tryNonce (d : Dx) (n : UInt64) : NC P G s (tryNonce d n) 0 :=
  (nc_absorb P G s _ _ _).bind P G s (fun _ ↦ (nc_perm P G s _).bind P G s
    (fun _ ↦ nc_pure P G s _) rfl) rfl

theorem nc_grind : ∀ (fuel : ℕ) (d : Dx) (n : UInt64), NC P G s (grind d fuel n) 0
  | 0, d, n => nc_pure P G s _
  | fuel + 1, d, n => by
    unfold grind
    refine (nc_tryNonce P G s d n).bind P G s (k₂ := 0) (fun r ↦ ?_) rfl
    obtain ⟨ok, d'⟩ := r
    dsimp only
    split
    · exact nc_pure P G s _
    · exact nc_grind fuel d (n + 1)

theorem nc_mapM_hashH (f : ℕ → List UInt8) :
    ∀ l : List ℕ, NC P G s (l.mapM fun i ↦ QuotientZk.Deployed.hashH (f i)) 0
  | [] => nc_pure P G s _
  | x :: l => by
    rw [List.mapM_cons]
    exact (nc_hashH P G s _).bind P G s (fun _ ↦ (nc_mapM_hashH f l).bind P G s
      (fun _ ↦ nc_pure P G s _) rfl) rfl

theorem nc_levelUp : ∀ l : List QuotientRpm.Bytes32, NC P G s (QuotientZk.Deployed.levelUp l) 0
  | a :: b :: rest => by
    rw [QuotientZk.Deployed.levelUp]
    exact (nc_hashH P G s _).bind P G s (fun _ ↦ (nc_levelUp rest).bind P G s
      (fun _ ↦ nc_pure P G s _) rfl) rfl
  | [] => nc_pure P G s _
  | [_] => nc_pure P G s _

theorem nc_levels : ∀ (d : ℕ) (l : List QuotientRpm.Bytes32),
    NC P G s (QuotientZk.Deployed.levels d l) 0
  | 0, l => nc_pure P G s _
  | d + 1, l => by
    rw [QuotientZk.Deployed.levels]
    exact (nc_levelUp P G s l).bind P G s (fun _ ↦ (nc_levels d _).bind P G s
      (fun _ ↦ nc_pure P G s _) rfl) rfl

theorem nc_sendK (o : OSt) (k : ℕ) : NC P G s (sendK o k) 0 := by
  unfold sendK
  exact (nc_absorbAll P G s _ _).bind P G s (fun _ ↦ nc_pure P G s _) rfl

theorem nc_drawO (o : OSt) : NC P G s (drawO o) 1 := by
  unfold drawO
  refine (nc_draw P G s _).bind P G s (k₂ := 0) (fun r ↦ ?_) rfl
  obtain ⟨c, dx⟩ := r
  exact nc_getMsg P G s |>.bind P G s (fun _ ↦ nc_pure P G s _) rfl

theorem nc_commitNext (o : OSt) (d : ℕ) : NC P G s (commitNext o d) 0 := by
  unfold commitNext
  exact (nc_mapM_hashH P G s _ _).bind P G s (fun _ ↦ (nc_levels P G s _ _).bind P G s
    (fun _ ↦ (nc_absorbAll P G s _ _).bind P G s (fun _ ↦ nc_pure P G s _) rfl) rfl) rfl

/-- **The skeleton on events appends one answer per draw.** -/
theorem nc_skelEv : ∀ (evs : List Render.Ev) (o : OSt) (pl : List QuotientRpm.Limbs),
    NC P G s (skelEv evs o pl) (drawsIn evs)
  | [], o, _ => nc_pure P G s o
  | .draw :: evs, o, pl => by
    refine (nc_drawO P G s o).bind P G s (k₂ := drawsIn evs) (fun r ↦ ?_)
      (by simp only [drawsIn]; omega)
    obtain ⟨_, o'⟩ := r
    exact nc_skelEv evs o' pl
  | .posDraw :: evs, o, pl => by
    refine (nc_drawO P G s o).bind P G s (k₂ := drawsIn evs) (fun r ↦ ?_)
      (by simp only [drawsIn]; omega)
    obtain ⟨c, o'⟩ := r
    exact nc_skelEv evs o' (pl ++ [c])
  | .send k :: evs, o, pl =>
    (nc_sendK P G s o k).bind P G s (fun o' ↦ nc_skelEv evs o' pl) (by simp only [drawsIn]; omega)
  | .commit d :: evs, o, pl =>
    (nc_commitNext P G s o d).bind P G s (fun o' ↦ nc_skelEv evs o' pl)
      (by simp only [drawsIn]; omega)
  | .grind :: evs, o, pl => by
    refine (nc_grind P G s _ o.dx 0).bind P G s (k₂ := drawsIn evs) (fun r ↦ ?_)
      (by simp only [drawsIn]; omega)
    obtain ⟨nonce, dx⟩ := r
    exact nc_skelEv evs _ pl
  | .opened lvl q b :: evs, o, pl => nc_skelEv evs _ []

/-- **An opening appends one answer per draw of its events**, its level-0 tree of depth `depth₀`. -/
theorem nc_opening (sh : QuotientZk.Deployed.OpenShape) (lv₀ : List (List QuotientRpm.Bytes32))
    (hlv : lv₀.length = sh.depth₀ + 1) (hq : sh.levels.length ≤ (sh.queries.drop 1).length) :
    NC P G s (QuotientZk.Deployed.opening sh lv₀) (drawsIn (Render.openingEv sh)) := by
  unfold QuotientZk.Deployed.opening
  refine (nc_getMsg P G s).bind P G s (fun m ↦ ?_) (Nat.zero_add _)
  split
  all_goals
    refine (nc_hashH P G s _).bind P G s (fun iv ↦ ?_) (Nat.zero_add _)
    refine (nc_seed P G s iv).bind P G s (fun dx ↦ ?_) (Nat.zero_add _)
    refine (nc_absorbAll P G s _ _).bind P G s (fun dx' ↦ ?_) (Nat.zero_add _)
    refine NC.congr P G s (Y := skelEv (Render.openingEv sh) _ [] >>= fun o ↦ pure (o.stream, o.merkle))
      (fun hist ↦ openTail_run P G s sh _ lv₀ rfl hlv hq hist) ?_
    exact (nc_skelEv P G s _ _ _).bind P G s (fun _ ↦ nc_pure P G s _) (Nat.add_zero _)

end Hist

/-! ## The multiproofs' sizes -/

section Small

variable (π : Equiv.Perm Eager.St) (fuel : ℕ)

/-- The opened events. -/
def openedIn : List Render.Ev → ℕ
  | [] => 0
  | .opened _ _ _ :: evs => openedIn evs + 1
  | _ :: evs => openedIn evs

/-- Every opened event has at most `2^10` queries. -/
def queriesOK : List Render.Ev → Bool
  | [] => true
  | .opened _ q _ :: evs => decide (q ≤ 2 ^ 10) && queriesOK evs
  | _ :: evs => queriesOK evs

theorem length_dedup_le {α : Type} [DecidableEq α] : ∀ l : List α, l.dedup.length ≤ l.length :=
  fun l ↦ (List.dedup_sublist l).length_le

theorem length_sortedUnique_le (ps : List ℕ) : (sortedUnique ps).length ≤ ps.length := by
  unfold sortedUnique
  exact (length_dedup_le _).trans (List.length_mergeSort _).le

theorem length_posOf_le (pl : List QuotientRpm.Limbs) (b q : ℕ) : (posOf pl b q).length ≤ q := by
  unfold posOf
  exact List.length_take_le _ _

theorem oWordsLE_sendsS : ∀ (k : ℕ) (S : Option (Script Unit)) (sp : Sponge), OWordsLE 192 S →
    OWordsLE 192 (sendsS π k S sp).2.1
  | 0, _, _, h => h
  | k + 1, _, _, h => oWordsLE_sendsS k _ _ (oWordsLE_afterSend h)

/-- A multiproof within `FmtSmall`'s bounds. -/
def MSmall (mp : Multi) : Prop := mp.1.length ≤ 2 ^ 10 ∧ ∀ r ∈ mp.2.1, r.length ≤ 2 ^ 10

/-- **The statement's run makes small multiproofs**: from a script committing rows of at most `192`
words and trees of such rows, one multiproof per opened event, each within `MSmall`. -/
theorem runEvS_small : ∀ (evs : List Render.Ev) (S : Option (Script Unit)) (sp : Sponge)
    (cs : List Tree) (pl : List QuotientRpm.Limbs) (str : List E) (ops : List Opening)
    (ms : List Multi), OWordsLE 192 S → (∀ t ∈ cs, ∀ p, (t.word p).length ≤ 192) →
    queriesOK evs = true → runEvS π fuel evs S sp cs pl = some (str, ops, ms) →
    ms.length ≤ openedIn evs ∧ ∀ mp ∈ ms, MSmall mp
  | [], _, _, _, _, str, ops, ms, _, _, _, hr => by
    simp only [runEvS, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    simp
  | .draw :: evs, _, _, cs, pl, str, ops, ms, hS, hc, hq, hr =>
    runEvS_small evs _ _ cs pl str ops ms (oWordsLE_afterSample _ hS) hc hq hr
  | .posDraw :: evs, _, _, cs, _, str, ops, ms, hS, hc, hq, hr =>
    runEvS_small evs _ _ cs _ str ops ms (oWordsLE_afterSample _ hS) hc hq hr
  | .send k :: evs, S, sp, cs, pl, str, ops, ms, hS, hc, hq, hr => by
    change (runEvS π fuel evs (sendsS π k S sp).2.1 (sendsS π k S sp).2.2 cs pl).map
      (fun t ↦ ((sendsS π k S sp).1 ++ t.1, t.2)) = some (str, ops, ms) at hr
    obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hte
    obtain ⟨-, -, rfl⟩ := hte
    exact runEvS_small evs _ _ cs pl _ _ _ (oWordsLE_sendsS π k S sp hS) hc hq ht
  | .commit d :: evs, S, sp, cs, pl, str, ops, ms, hS, hc, hq, hr => by
    change (runEvS π fuel evs (Script.afterCommit S) _
      (cs ++ [(buildTreeM (permId π) d (Script.wordOf S)).run]) pl).map _ = some (str, ops, ms) at hr
    obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hte
    obtain ⟨-, -, rfl⟩ := hte
    refine runEvS_small evs _ _ _ pl _ _ _ (oWordsLE_afterCommit hS) ?_ hq ht
    intro t htm p
    rcases List.mem_append.mp htm with htm | htm
    · exact hc t htm p
    · rw [List.mem_singleton.mp htm, Merkle.buildTree_run]
      exact length_wordOf_le hS p
  | .grind :: evs, S, sp, cs, pl, str, ops, ms, hS, hc, hq, hr => by
    rw [runEvS_grind] at hr
    rcases hfn : (findNonceM (permId π) 17 sp fuel).run with _ | n
    · rw [hfn] at hr
      cases hr
    rw [hfn] at hr
    obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hte
    obtain ⟨-, -, rfl⟩ := hte
    exact runEvS_small evs _ _ cs pl _ _ _ (oWordsLE_afterGrind hS) hc hq ht
  | .opened lvl q b :: evs, S, sp, cs, pl, str, ops, ms, hS, hc, hq, hr => by
    simp only [queriesOK, Bool.and_eq_true, decide_eq_true_eq] at hq
    rw [runEvS_opened] at hr
    rcases hcs : cs[lvl]? with _ | tree
    · rw [hcs] at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, -, rfl⟩ := hr
      simp
    rw [hcs] at hr
    obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hte
    obtain ⟨-, -, rfl⟩ := hte
    obtain ⟨ih1, ih2⟩ := runEvS_small evs _ _ cs [] _ _ _ (oWordsLE_afterQuery _ hS) hc hq.2 ht
    have htree : tree ∈ cs := List.mem_of_getElem? hcs
    refine ⟨by simp only [List.length_cons, openedIn]; omega, fun mp hmp ↦ ?_⟩
    rcases List.mem_cons.mp hmp with rfl | hmp
    · refine ⟨(length_sortedUnique_le _).trans ((length_posOf_le _ _ _).trans hq.1), fun r hr ↦ ?_⟩
      simp only [multiOf, List.mem_map] at hr
      obtain ⟨p, -, rfl⟩ := hr
      rw [List.length_map]
      exact (hc tree htree p).trans (by norm_num)
    · exact ih2 mp hmp

end Small

end PcsQuotient.EndToEnd.Core
