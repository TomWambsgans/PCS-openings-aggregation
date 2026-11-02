-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The sponge (`absorb`, `squeeze`), the proof-of-work step (`powStepM`), the trees (`buildTreeM`,
-- `Tree.opening`) and `digestOfScalars_digestScalars` are leanerVM's (branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0: `Statement/LeanVmVerifier.lean`, `Statement/Prover/Run.lean`,
-- `lean_vm/LeanVM/Protocol/KeccakHash.lean`).
import ZK.CoreEv

/-!
# `fmt`'s production replays the statement's run

`fillRun` (`ZK/Format.lean`) runs the verifier's program on a stream and produces the Merkle openings
from the multiproofs. **`fill_runEvS`**: on a program following an opening's events, from the sponge the
statement's run starts at, fed the run's stream and multiproofs (`runEvS`), it outputs the run's
openings: each query's multiproof expands to the statement's tree's openings (`expandMulti_eq`), the
roots read are the trees' (`digestOfScalars_digestScalars`), and every absorb and squeeze is the run's.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open QuotientZk.Deployed (sortedUnique prune positionsOf)

namespace PcsQuotient.EndToEnd.Core

open Render (limbsOf)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

variable (π : Equiv.Perm Eager.St) (fuel : ℕ)

/-! ## Against `π` -/

theorem sim_absorbF (sp : Sponge) (x : E) (t : ℕ) :
    simulateQ (permOnly π) (absorb permF sp x t) = absorb (permId π) sp x t := by
  have h := Param.absorb_hom (simHom (permOnly π)) permF sp x t
  simp only [simHom_app, Merkle.sim_permF] at h
  exact h

theorem sim_squeezeF (sp : Sponge) :
    simulateQ (permOnly π) (squeeze permF sp) = squeeze (permId π) sp := by
  have h := Param.squeeze_hom (simHom (permOnly π)) permF sp
  simp only [simHom_app, Merkle.sim_permF] at h
  exact h

/-- **`fillRun` against `π`.** -/
def fillD {α : Type} (P : Prog α) (st : FillState) : Option FillState :=
  (simulateQ (permOnly π) (fillRun P st)).run

theorem fillD_ret {α : Type} (a : α) (st : FillState) : fillD π (.ret a) st = some st := rfl

theorem fillD_fail {α : Type} (st : FillState) : fillD π (.fail : Prog α) st = some st := rfl

theorem fillD_read {α : Type} (k : E → Prog α) (st : FillState) (x : E) (xs : List E)
    (h : st.stream = x :: xs) :
    fillD π (.read k) st =
      fillD π (k x) { st with sponge := (absorb (permId π) st.sponge x dsObserve).run, stream := xs } := by
  unfold fillD
  rw [fillRun, h]
  simp only [simulateQ_bind, sim_absorbF]
  rfl

theorem fillD_sample {α : Type} (k : E → Prog α) (st : FillState) :
    fillD π (.sample k) st =
      fillD π (k (squeeze (permId π) st.sponge).run.1)
        { st with sponge := (squeeze (permId π) st.sponge).run.2 } := by
  unfold fillD
  rw [fillRun]
  simp only [simulateQ_bind, sim_squeezeF]
  rfl

theorem fillD_grind {α : Type} (bits : ℕ) (k : Prog α) (st : FillState) (n : E) (xs : List E)
    (h : st.stream = n :: xs) :
    fillD π (.grind bits k) st =
      fillD π k { st with sponge := (powStepM (permId π) st.sponge n).run.2, stream := xs } := by
  unfold fillD
  rw [fillRun, h]
  simp only [simulateQ_bind, sim_absorbF, sim_squeezeF]
  rfl

theorem fillD_commit {α : Type} (height width : ℕ) (k : Prog α) (st : FillState) (x0 x1 : E)
    (xs : List E) (h : st.stream = x0 :: x1 :: xs) (root : Digest)
    (hr : digestOfScalars (x0, x1) = some root) :
    fillD π (.commit height width k) st =
      fillD π k ⟨(absorb (permId π) (absorb (permId π) st.sponge x0 dsObserve).run x1 dsObserve).run,
        xs, st.multis, st.roots ++ [(root, height, width)], st.out⟩ := by
  unfold fillD
  rw [fillRun, h]
  simp only [simulateQ_bind, sim_absorbF, hr]
  rfl

theorem fillD_query {α : Type} (i : ℕ) (ps : List ℕ) (k : List (List K) → Prog α) (st : FillState)
    (r : Digest) (height width : ℕ) (h : st.roots[i]? = some (r, height, width)) (mp : Multi)
    (rest : List Multi) (hm : st.multis = mp :: rest) :
    fillD π (.query i ps k) st =
      fillD π (k (((simulateQ (permOnly π) (expandMulti mp height ps)).run).map (·.leaf)))
        ⟨st.sponge, st.stream, rest, st.roots,
          st.out ++ (simulateQ (permOnly π) (expandMulti mp height ps)).run⟩ := by
  unfold fillD
  rw [fillRun, h, hm]
  simp only [simulateQ_bind]
  rfl

/-! ## The replay -/

/-- The events' commitments' heights, as they are opened: each opened commitment `lvl` has the height
`b ≥ 1` of its event. -/
def HeightsOK : List Render.Ev → List ℕ → Prop
  | [], _ => True
  | .commit d :: evs, hs => HeightsOK evs (hs ++ [d])
  | .opened lvl _ b :: evs, hs => hs[lvl]? = some b ∧ 1 ≤ b ∧ HeightsOK evs hs
  | .draw :: evs, hs => HeightsOK evs hs
  | .posDraw :: evs, hs => HeightsOK evs hs
  | .send _ :: evs, hs => HeightsOK evs hs
  | .grind :: evs, hs => HeightsOK evs hs

theorem positionsOf_lt (b : ℕ) (x : QuotientRpm.Limbs) : ∀ p ∈ positionsOf b x, p < 2 ^ b := by
  intro p hp
  simp only [positionsOf, List.mem_map, List.mem_range] at hp
  obtain ⟨j, -, rfl⟩ := hp
  exact Nat.mod_lt _ (by positivity)

theorem posOf_lt (pl : List QuotientRpm.Limbs) (b q : ℕ) (hb : 1 ≤ b) :
    ∀ p ∈ posOf pl b q, p < 2 ^ b := by
  intro p hp
  have hp' := List.mem_of_mem_take hp
  rw [List.mem_flatMap] at hp'
  obtain ⟨x, -, hx⟩ := hp'
  have := positionsOf_lt (max b 1) x p hx
  rwa [max_eq_left hb] at this

/-- A tree is the tree of its word at its height. -/
def TreeOK (t : Tree) : Prop := t = (buildTreeM (permId π) t.height t.word).run

theorem multiOf_eq (t : Tree) (ht : TreeOK π t) (ps : List ℕ) :
    multiOf t ps = (sortedUnique ps, (sortedUnique ps).map (fun p ↦ (t.word p).map K.lane),
      prune (Merkle.treeBytes π t.height t.word) (sortedUnique ps)) := by
  unfold multiOf treeBytesOf Merkle.treeBytes
  rw [← ht]

theorem fill_reads {α : Type} (K : Prog α → Prop) : ∀ (n : ℕ) (P : Prog α) (S : Option (Script Unit))
    (sp : Sponge) (rest : List E) (ms : List Multi) (roots : List (Digest × ℕ × ℕ))
    (out : List Opening), FollowsReads n P K →
    K (afterReads P (sendsS π n S sp).1) ∧
      fillD π P ⟨sp, (sendsS π n S sp).1 ++ rest, ms, roots, out⟩ =
        fillD π (afterReads P (sendsS π n S sp).1) ⟨(sendsS π n S sp).2.2, rest, ms, roots, out⟩
  | 0, P, S, sp, rest, ms, roots, out, h => by
    refine ⟨?_, ?_⟩
    · rw [sendsS, afterReads_nil]
      exact h
    · simp only [sendsS, afterReads_nil, List.nil_append]
  | n + 1, P, S, sp, rest, ms, roots, out, h => by
    obtain ⟨k, rfl, hk⟩ := h
    obtain ⟨hK, he⟩ := fill_reads K n (k (Script.msgOf S)) (Script.afterSend S)
      (absorb (permId π) sp (Script.msgOf S) dsObserve).run rest ms roots out (hk _)
    refine ⟨hK, ?_⟩
    rw [fillD_read π k _ (Script.msgOf S) _ rfl]
    exact he

/-- **`fillRun` replays the statement's run**: on a program following the events, from the run's
sponge, with the run's stream and multiproofs first, the roots' heights the trees', `fillRun` ends
with the run's openings after `out`, the rest of the stream and of the multiproofs untouched. -/
theorem fill_runEvS : ∀ (evs : List Render.Ev) {α : Type} (P : Prog α) (S : Option (Script Unit))
    (sp : Sponge) (cs : List Tree) (pl : List QuotientRpm.Limbs) (str : List E) (ops : List Opening)
    (ms : List Multi) (rest : List E) (mrest : List Multi) (roots : List (Digest × ℕ × ℕ))
    (out : List Opening),
    Follows evs P pl → HeightsOK evs (cs.map (·.height)) → (∀ t ∈ cs, TreeOK π t) →
    roots.map (·.2.1) = cs.map (·.height) →
    runEvS π fuel evs S sp cs pl = some (str, ops, ms) →
    ∃ st', fillD π P ⟨sp, str ++ rest, ms ++ mrest, roots, out⟩ = some st' ∧ st'.out = out ++ ops
  | [], _, P, S, sp, cs, pl, str, ops, ms, rest, mrest, roots, out, hF, _, _, _, hr => by
    simp only [runEvS, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    rcases hF with ⟨a, rfl⟩ | rfl
    · exact ⟨_, fillD_ret π a _, by simp⟩
    · exact ⟨_, fillD_fail π _, by simp⟩
  | .draw :: evs, _, P, S, sp, cs, pl, str, ops, ms, rest, mrest, roots, out, hF, hH, hT, hR, hr => by
    obtain ⟨k, rfl, hk⟩ := hF
    rw [fillD_sample]
    exact fill_runEvS evs _ _ _ cs pl str ops ms rest mrest roots out (hk _) hH hT hR hr
  | .posDraw :: evs, _, P, S, sp, cs, pl, str, ops, ms, rest, mrest, roots, out, hF, hH, hT, hR,
      hr => by
    obtain ⟨k, rfl, hk⟩ := hF
    rw [fillD_sample]
    exact fill_runEvS evs _ _ _ cs _ str ops ms rest mrest roots out (hk _) hH hT hR hr
  | .send n :: evs, _, P, S, sp, cs, pl, str, ops, ms, rest, mrest, roots, out, hF, hH, hT, hR,
      hr => by
    obtain ⟨hK, he⟩ := fill_reads π _ n P S sp (str.drop (sendsS π n S sp).1.length ++ rest)
      (ms ++ mrest) roots out hF
    change (runEvS π fuel evs (sendsS π n S sp).2.1 (sendsS π n S sp).2.2 cs pl).map
      (fun t ↦ ((sendsS π n S sp).1 ++ t.1, t.2)) = some (str, ops, ms) at hr
    obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hte
    obtain ⟨rfl, rfl, rfl⟩ := hte
    have hd : ((sendsS π n S sp).1 ++ t1).drop (sendsS π n S sp).1.length = t1 := by simp
    rw [hd] at he
    rw [List.append_assoc, he]
    exact fill_runEvS evs _ _ _ cs pl t1 t2 t3 rest mrest roots out hK hH hT hR
      (by rw [ht])
  | .commit d :: evs, _, P, S, sp, cs, pl, str, ops, ms, rest, mrest, roots, out, hF, hH, hT, hR,
      hr => by
    obtain ⟨w, k, rfl, hk⟩ := hF
    change (runEvS π fuel evs (Script.afterCommit S) _ (cs ++ [(buildTreeM (permId π) d
      (Script.wordOf S)).run]) pl).map _ = some (str, ops, ms) at hr
    obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hte
    obtain ⟨rfl, rfl, rfl⟩ := hte
    rw [List.cons_append, List.cons_append,
      fillD_commit π d w k _ _ _ _ rfl _ (digestOfScalars_digestScalars _)]
    have hT' : ∀ u ∈ cs ++ [(buildTreeM (permId π) d (Script.wordOf S)).run], TreeOK π u := by
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hT u hu
      · rw [List.mem_singleton.mp hu]
        rfl
    exact fill_runEvS evs _ _ _ _ pl t1 t2 t3 rest mrest _ out hk
      (by rw [List.map_append]; exact hH) hT' (by rw [List.map_append, List.map_append, hR]; rfl) ht
  | .grind :: evs, _, P, S, sp, cs, pl, str, ops, ms, rest, mrest, roots, out, hF, hH, hT, hR,
      hr => by
    obtain ⟨k, rfl, hk⟩ := hF
    rw [runEvS_grind] at hr
    rcases hn : (findNonceM (permId π) 17 sp fuel).run with _ | n
    · rw [hn] at hr
      cases hr
    · rw [hn] at hr
      obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
      simp only [Prod.mk.injEq] at hte
      obtain ⟨rfl, rfl, rfl⟩ := hte
      rw [List.cons_append, fillD_grind π 17 k _ n _ rfl]
      exact fill_runEvS evs _ _ _ cs pl t1 t2 t3 rest mrest roots out hk hH hT hR ht
  | .opened lvl q b :: evs, _, P, S, sp, cs, pl, str, ops, ms, rest, mrest, roots, out, hF, hH, hT,
      hR, hr => by
    obtain ⟨k, rfl, hk⟩ := hF
    obtain ⟨hb, hb1, hH⟩ := hH
    rw [List.getElem?_map] at hb
    rcases hcs : cs[lvl]? with _ | tree
    · rw [hcs] at hb
      cases hb
    rw [hcs] at hb
    have htb : tree.height = b := Option.some.inj hb
    have htree : TreeOK π tree := hT tree (List.mem_of_getElem? hcs)
    rw [runEvS_opened, hcs] at hr
    obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hte
    obtain ⟨rfl, rfl, rfl⟩ := hte
    have hroot : ∃ r w, roots[lvl]? = some (r, b, w) := by
      have h1 : (roots.map (·.2.1))[lvl]? = some b := by rw [hR, List.getElem?_map, hcs]; exact hb
      rw [List.getElem?_map] at h1
      rcases hr' : roots[lvl]? with _ | ⟨r, hgt, w⟩
      · rw [hr'] at h1
        cases h1
      · rw [hr'] at h1
        have hgt' : hgt = b := Option.some.inj h1
        exact ⟨r, w, by rw [hgt']⟩
    obtain ⟨r, w, hrw⟩ := hroot
    have hexp : (simulateQ (permOnly π) (expandMulti (multiOf tree (posOf pl b q)) b
        (posOf pl b q))).run = (posOf pl b q).map tree.opening := by
      rw [multiOf_eq π tree htree, htb, Merkle.expandMulti_eq π b tree.word (posOf pl b q)
        (posOf_lt pl b q hb1)]
      conv_rhs => rw [htree, htb]
    rw [List.cons_append, fillD_query π lvl _ k _ r b w hrw _ _ rfl, hexp]
    have hrows : ((posOf pl b q).map tree.opening).map (·.leaf) =
        (posOf pl b q).map fun p ↦ tree.word (p % 2 ^ tree.height) := by
      rw [List.map_map]
      rfl
    rw [hrows]
    obtain ⟨st', h1, h2⟩ := fill_runEvS evs _ _ _ cs [] t1 t2 t3 rest mrest roots
      (out ++ (posOf pl b q).map tree.opening) (hk _) hH hT hR ht
    exact ⟨st', h1, by rw [h2, List.append_assoc]⟩

end PcsQuotient.EndToEnd.Core
