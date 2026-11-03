-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.FlockTerminal
import RecGraph.Sim.FlockTower

/-!
# Flock with the walked terminal, simulated: `Pi1.verifyWalked` against `UniStatement.Flock.verifyWalkedFs`

At π1-rec3's shape (`log_n = 32`, `flockMain`: a skip of 3, the slices in tower order; `.rec3`), as `Sim` instances
(`Sim/Chan.lean`):

* `zerocheck_sim`: the seven fixed coordinates, the drawn run (one challenge and its squares), the coset's eight
  values, `z`, the skip's interpolation (`lagrangeInterpolate_ph`), the 29 rounds, `v_a`, `v_b`, `v_c`;
* `front_sim`: `α`, the lincheck's claim, its 8 rounds, the 64 slices;
* `ringEnd_sim`: the map's six challenges, the target (`towerTarget_ph`);
* `verifyWalked_sim`: the front, the walked terminal (`walkedTerminal_ph`) against the lincheck's last claim, a zero,
  the ring switch's end.

The bytes (3552) and the challenges (46) are counted from the definitions. The challenge nodes are tracked
(`Sim.chIds_len`, `sim_sumcheckDrawn_ch`): the 40th challenge of the part (index 39) is the lincheck's last round, the
first coordinate of Flock's point.
-/

-- The judgment's rules are `RecGraph.Sim.Sim.*`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## The challenge nodes -/

theorem chIds_prefix {st st' : RecState} (h : Grows st st') : ∃ L, chIds st' = chIds st ++ L := by
  obtain ⟨⟨ys, hys⟩, _⟩ := h
  unfold chIds
  have hsz : st'.nodes.size = st.nodes.size + ys.length := by
    have := congrArg List.length hys; simpa using this
  rw [hys, hsz, List.range_add, List.zip_append (by simp), List.filter_append, List.map_append]
  exact ⟨_, rfl⟩

theorem chIds_of_nodes {st st' : RecState} (h : st'.nodes = st.nodes) : chIds st' = chIds st := by
  unfold chIds; rw [h]

section Flock

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "RpA'" => RpA π iv publicInput stream
local notation "OptRp'" => OptRp π iv publicInput stream

/-- **The challenge nodes a part draws**: `ch` of them, appended. -/
theorem Sim.chIds_len {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (h : Sim π iv publicInput stream st p u n ch R) :
    Sim π iv publicInput stream st p u n ch
      (fun st' a b ↦ R st' a b ∧ ∃ L, chIds st' = chIds st ++ L ∧ L.length = ch) := by
  intro c hc hle
  obtain ⟨hs, hf⟩ := h c hc hle
  refine ⟨fun hr ↦ ?_, hf⟩
  obtain ⟨b, c', hu, hc', hcur, hch, hgr, hR⟩ := hs hr
  refine ⟨b, c', hu, hc', hcur, hch, hgr, hR, ?_⟩
  obtain ⟨L, hL⟩ := chIds_prefix hgr
  refine ⟨L, hL, ?_⟩
  have h1 := congrArg List.length hc.chal
  have h2 := congrArg List.length hc'.chal
  simp only [Array.length_toList, List.length_map] at h1 h2
  rw [hL, List.length_append] at h2
  omega

theorem sumcheckBytes_some (count : ℕ) (l : List E) :
    sumcheckBytes count (l.map some) = rpBytes count true * l.length := by
  induction l with
  | nil => simp [sumcheckBytes]
  | cons x t ih =>
    simp only [sumcheckBytes, List.map_cons, List.sum_cons, Option.isSome_some] at ih ⊢
    rw [ih]; simp [Nat.mul_succ]; omega

theorem sumcheckBytes_none (count k : ℕ) :
    sumcheckBytes count (List.replicate k none) = rpBytes count false * k := by
  induction k with
  | zero => simp [sumcheckBytes]
  | succ k ih =>
    simp only [sumcheckBytes, List.replicate_succ, List.map_cons, List.sum_cons, Option.isSome_none] at ih ⊢
    rw [ih, Nat.mul_succ]; omega

/-- **`sumcheck_drawn`, its challenge nodes**: those of the point, appended in order. -/
theorem sim_sumcheckDrawn_ch (st : RecState) {claim : Nat} {c : E} (count : Nat) {eqs : List (Option Nat)}
    {eqsE : List (Option E)} (narrow : Bool) (hc : Rp' st claim c)
    (he : List.Forall₂ (OptRp' st) eqs eqsE) :
    Sim π iv publicInput stream st (Pi1.sumcheckDrawn claim count eqs narrow)
      (UniStatement.sumcheckDrawn (Fp π) c count eqsE narrow) (sumcheckBytes count eqsE) eqsE.length
      (fun st' a b ↦ RpL' st' a.1 b.1 ∧ Rp' st' a.2 b.2 ∧ chIds st' = chIds st ++ a.1) := by
  refine Sim.of_good fun hg ↦ ?_
  have hlen := he.length_eq
  unfold Pi1.sumcheckDrawn UniStatement.sumcheckDrawn
  refine Sim.cast ?_ ?_ ((Sim.forIn_list st eqs eqsE
    (fun _ st' (s : Array Nat × Nat) (t : Array E × E) ↦
      RpL' st' s.1.toList t.1.toList ∧ Rp' st' s.2 t.2 ∧ chIds st' = chIds st ++ s.1.toList)
    (fun i ↦ rpBytes count (eqsE.getD i none).isSome) (fun _ ↦ 1) _ _ hlen ?_ st (#[], claim) (#[], c) hg
    (Grows.refl st) ⟨List.Forall₂.nil, hc, by simp⟩).map (f := fun s ↦ (s.1.toList, s.2))
      (g := fun t ↦ (t.1.toList, t.2)) fun _ _ _ _ _ h ↦ h)
  · rw [hlen]; exact sum_range_getD (fun e ↦ rpBytes count e.isSome) none eqsE
  · rw [sum_const_range, hlen, Nat.one_mul]
  · intro i hi hj st' s t hg' hgr' ⟨hpt, hcl, hch⟩
    have heq : OptRp' st' eqs[i] eqsE[i] :=
      (List.forall₂_iff_get.mp he).2 i hi hj |>.grow hg.inv.kinv hgr'
    refine Sim.cast (n := rpBytes count eqsE[i].isSome + (0 + 0)) (ch := 0 + (1 + 0))
      (by rw [List.getD_eq_getElem _ _ hj]; rfl) rfl ?_
    refine Sim.bind (sim_roundPoly st' count hcl heq).chIds_len fun st1 ms xs hg1 hgr1 ⟨hms, L1, hL1, hL1l⟩ ↦ ?_
    rw [List.length_eq_zero_iff.mp hL1l, List.append_nil] at hL1
    refine Sim.bind (sim_sampleDrawn π iv publicInput stream st1 narrow) fun st2 z ze hg2 hgr2 ⟨hz, hzc, _⟩ ↦ ?_
    refine Sim.of_psim (PSim.bind (polyEval_psim st2 hg2 (hms.grow π iv publicInput stream hg1.inv.kinv hgr2) hz)
      fun st3 c' hst3 hc' ↦ PSim.pure hst3.good ⟨_, _, rfl, rfl, ?_, hc', ?_⟩)
    · rw [Array.toList_push, Array.toList_push]
      exact ((hpt.grow π iv publicInput stream hg'.inv.kinv (hgr1.trans hgr2)).snoc hz).pgrow hg2 hst3
    · rw [hst3.chal, hzc, hL1, hch, Array.toList_push, List.append_assoc]

end Flock

end RecGraph.Sim
