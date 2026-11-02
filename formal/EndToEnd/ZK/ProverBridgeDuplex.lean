-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The sponge (`Sponge`, `duplexInput`, `pendingLanes`, `absorb`, `squeeze`, `challengeOf`) is
-- leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/LeanVmVerifier.lean`).
import ZK.ProverBridgeSkel
import ZK.ProverBridgeRender

/-!
# The skeleton's duplex is the statement's sponge

The skeleton's duplex (`Deployed.Dx`: the last permutation's output, the waiting scalars as limbs with
their tags) and the openings' sponge of the statement (mumbai's `Sponge`: the state, the waiting
scalars as elements of `E` with their tags) agree when the capacity lanes `16 .. 24` agree and the
waiting scalars are the same (`Rel`). Then, with the permutation `π` the oracle's (`runDet` against
`Gof h π gH gF`, the statement in `Id` over `π`):

* the permutation's input is the same (`input_eq`);
* absorbing a scalar keeps them related (`absorb_rel`);
* a draw's challenge is the squeeze's, as limbs, and the states after them are related (`draw_rel`).
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open QuotientZk.Deployed (Dx Out Inp KSt DSpec Msg Tbl Pos)
open QuotientRpm (Limbs)

namespace PcsQuotient.EndToEnd.Duplex

open QuotientZk (Proto)
open Render (limbsOf)

set_option linter.unusedSectionVars false

/-- **The duplex and the sponge agree**: the capacity lanes, and the waiting scalars with their tags. -/
def Rel (d : Dx) (sp : Sponge) : Prop :=
  (∀ i : Fin 25, 16 ≤ i.val → d.st[i] = Keccak.lane sp.state i) ∧
    d.pend = sp.pending.map fun p ↦ (limbsOf p.1, p.2.toUInt64)

/-- An entry of a list of blocks of four. -/
theorem getD_flatMap4 {α : Type} (g : α → List UInt64) (hg : ∀ a, (g a).length = 4) :
    ∀ (l : List α) (i : ℕ), (l.flatMap g).getD i 0 =
      match l[i / 4]? with
      | some a => (g a).getD (i % 4) 0
      | none => 0
  | [], i => by simp
  | a :: l, i => by
    rw [List.flatMap_cons]
    by_cases hi : i < 4
    · rw [List.getD_append _ _ _ _ (by rw [hg]; exact hi)]
      have h1 : i / 4 = 0 := Nat.div_eq_of_lt hi
      have h2 : i % 4 = i := Nat.mod_eq_of_lt hi
      rw [h1, h2]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [hg]; omega), hg, getD_flatMap4 g hg l (i - 4)]
      have h1 : i / 4 = (i - 4) / 4 + 1 := by omega
      have h2 : (i - 4) % 4 = i % 4 := by omega
      rw [h1, h2]
      rfl

theorem lane_eq (s : KeccakState) (i : ℕ) (hi : i < 25) : Keccak.lane s i = s[i] := by
  unfold Keccak.lane
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
  rfl

theorem lane_eq_getElem (s : KeccakState) (i : Fin 25) : Keccak.lane s i = s[i] :=
  lane_eq s i i.isLt

/-- **The permutation's input is the same.** -/
theorem input_eq {d : Dx} {sp : Sponge} (h : Rel d sp) : Dx.input d = duplexInput sp := by
  apply Vector.ext
  intro i hi
  simp only [Dx.input, duplexInput, Vector.getElem_ofFn]
  split_ifs with h16
  · rw [h.2, List.getElem?_map]
    unfold pendingLanes
    rw [getD_flatMap4 _ (fun ⟨_, _⟩ ↦ rfl)]
    rcases sp.pending[i / 4]? with _ | ⟨x, tag⟩
    · rfl
    · obtain h0 | h0 | h0 | h0 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
      all_goals simp [h0, limbsOf]
  · rw [h.1 ⟨i, hi⟩ (by simp only; omega)]

section Run

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (h : List UInt8 → Common.DigestBytes)
  (π : KSt → KSt) (gH : List UInt8 → KSt) (gF : KSt → Common.DigestBytes) (s : S)

theorem runDet_perm (x : KSt) (hist : List Out) :
    runDet P (Gof h π gH gF) s (QuotientZk.Deployed.perm x) hist = (π x, hist) := rfl

theorem runDet_chalF (x : KSt) (hist : List Out) :
    runDet P (Gof h π gH gF) s (QuotientZk.Deployed.chalF x) hist =
      (π x, if hist.length < P.n then hist ++ [((gF x, π x) : Out)] else hist) := rfl

/-- **Absorbing keeps the duplex and the sponge related.** -/
theorem absorb_rel {d : Dx} {sp : Sponge} (hr : Rel d sp) (x : E) (tag : ℕ) (hist : List Out) :
    (runDet P (Gof h π gH gF) s (d.absorb (limbsOf x) tag.toUInt64) hist).2 = hist ∧
      Rel (runDet P (Gof h π gH gF) s (d.absorb (limbsOf x) tag.toUInt64) hist).1
        (absorb (m := Id) (fun y ↦ pure (π y)) sp x tag).run := by
  have hlen : d.pend.length = sp.pending.length := by rw [hr.2, List.length_map]
  unfold Dx.absorb
  by_cases h4 : d.pend.length = 4
  · simp only [h4, ↓reduceIte]
    have hs : sp.pending.length = rateScalars := by rw [← hlen, h4]; rfl
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      show (π d.input)[i] = Keccak.lane ((absorb (m := Id) (fun y ↦ pure (π y)) sp x tag).run.state) i
      simp only [absorb, hs, ite_true, duplex]
      rw [lane_eq_getElem, input_eq hr]
      rfl
    · show [(limbsOf x, tag.toUInt64)] =
        ((absorb (m := Id) (fun y ↦ pure (π y)) sp x tag).run.pending).map _
      simp only [absorb, hs, ite_true, duplex]
      rfl
  · simp only [h4, ↓reduceIte]
    have hs : ¬ sp.pending.length = rateScalars := by rw [← hlen]; exact h4
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      show d.st[i] = Keccak.lane ((absorb (m := Id) (fun y ↦ pure (π y)) sp x tag).run.state) i
      simp only [absorb, hs, ite_false]
      exact hr.1 i hi
    · have e : (absorb (m := Id) (fun y ↦ pure (π y)) sp x tag).run =
          ⟨sp.state, sp.pending ++ [(x, tag)]⟩ := by
        simp only [absorb, hs, ite_false]
        rfl
      show d.pend ++ [(limbsOf x, tag.toUInt64)] =
        ((absorb (m := Id) (fun y ↦ pure (π y)) sp x tag).run.pending).map _
      rw [e, hr.2, List.map_append]
      rfl

theorem limbsOf_challengeOf (st : KeccakState) :
    limbsOf (Compile.challengeOf st) = (st[0], st[1], st[2]) := by
  show ((K.ofLane (Keccak.lane st 0)).lane, (K.ofLane (Keccak.lane st 1)).lane,
    (K.ofLane (Keccak.lane st 2)).lane) = _
  rw [lane_eq st 0 (by norm_num), lane_eq st 1 (by norm_num), lane_eq st 2 (by norm_num)]
  rfl

/-- **A draw is a squeeze**: the challenge's limbs, the answer recorded, the states after them related. -/
theorem draw_rel {d : Dx} {sp : Sponge} (hr : Rel d sp) (hist : List Out) :
    let r := runDet P (Gof h π gH gF) s d.draw hist
    let q := (squeeze (m := Id) (fun y ↦ pure (π y)) sp).run
    r.1.1 = limbsOf q.1 ∧ Rel r.1.2 q.2 ∧
      r.2 = (if hist.length < P.n then hist ++ [((gF (duplexInput sp), π (duplexInput sp)) : Out)]
        else hist) := by
  refine ⟨?_, ⟨fun i _ ↦ ?_, rfl⟩, ?_⟩
  · show ((π d.input)[0], (π d.input)[1], (π d.input)[2]) =
      limbsOf (Compile.challengeOf (π (duplexInput sp)))
    rw [limbsOf_challengeOf, input_eq hr]
  · show (π d.input)[i] = Keccak.lane (π (duplexInput sp)) i
    rw [lane_eq_getElem, input_eq hr]
  · show (if hist.length < P.n then hist ++ [((gF d.input, π d.input) : Out)] else hist) = _
    rw [input_eq hr]

end Run

end PcsQuotient.EndToEnd.Duplex

/--
info: 'PcsQuotient.EndToEnd.Duplex.draw_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Duplex.draw_rel
