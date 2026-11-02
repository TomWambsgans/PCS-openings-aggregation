-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.CoreDrive
import ZK.CoreFollows

/-!
# The deployed openings' events

For the three deployed openings (`witnessShape`, `wiringShape`, `quotientShape`): their events end in a
draw, they draw `123`, `114`, `152` times (`openDraws_*`), and every opened commitment has the depth its
event names, from level 0's (`20`, `19`, `23`) on (`HeightsOK`, decided on a Boolean transcription,
`heightsOKb`). These are `drive`'s and `fill_runEvS`'s conditions on the events.
-/

namespace PcsQuotient.EndToEnd.Core

set_option linter.unusedSectionVars false

/-- `HeightsOK` as a Boolean. -/
def heightsOKb : List Render.Ev → List ℕ → Bool
  | [], _ => true
  | .commit d :: evs, hs => heightsOKb evs (hs ++ [d])
  | .opened lvl _ b :: evs, hs => decide (hs[lvl]? = some b) && decide (1 ≤ b) && heightsOKb evs hs
  | .draw :: evs, hs => heightsOKb evs hs
  | .posDraw :: evs, hs => heightsOKb evs hs
  | .send _ :: evs, hs => heightsOKb evs hs
  | .grind :: evs, hs => heightsOKb evs hs

theorem heightsOK_of_b : ∀ (evs : List Render.Ev) (hs : List ℕ), heightsOKb evs hs = true →
    HeightsOK evs hs
  | [], _, _ => trivial
  | .commit d :: evs, hs, h => heightsOK_of_b evs _ h
  | .opened lvl _ b :: evs, hs, h => by
    simp only [heightsOKb, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, heightsOK_of_b evs hs h.2⟩
  | .draw :: evs, hs, h => heightsOK_of_b evs hs h
  | .posDraw :: evs, hs, h => heightsOK_of_b evs hs h
  | .send _ :: evs, hs, h => heightsOK_of_b evs hs h
  | .grind :: evs, hs, h => heightsOK_of_b evs hs h

theorem heights_W (id : QuotientRpm.Bytes32) :
    HeightsOK (Render.openingEv (QuotientZk.Deployed.witnessShape id)) [20] :=
  heightsOK_of_b _ _ (by rw [openingEv_W]; decide +kernel)

theorem heights_σ (id : QuotientRpm.Bytes32) (rows : List (List UInt8)) :
    HeightsOK (Render.openingEv (QuotientZk.Deployed.wiringShape id rows)) [19] :=
  heightsOK_of_b _ _ (by rw [openingEv_σ]; decide +kernel)

theorem heights_Q (id : QuotientRpm.Bytes32) :
    HeightsOK (Render.openingEv (QuotientZk.Deployed.quotientShape id)) [23] :=
  heightsOK_of_b _ _ (by rw [openingEv_Q]; decide +kernel)

theorem draws_W (id : QuotientRpm.Bytes32) :
    drawsIn (Render.openingEv (QuotientZk.Deployed.witnessShape id)) = 123 := by
  rw [openingEv_W]; decide +kernel

theorem draws_σ (id : QuotientRpm.Bytes32) (rows : List (List UInt8)) :
    drawsIn (Render.openingEv (QuotientZk.Deployed.wiringShape id rows)) = 114 := by
  rw [openingEv_σ]; decide +kernel

theorem draws_Q (id : QuotientRpm.Bytes32) :
    drawsIn (Render.openingEv (QuotientZk.Deployed.quotientShape id)) = 152 := by
  rw [openingEv_Q]; decide +kernel

theorem last_W (id : QuotientRpm.Bytes32) :
    (Render.openingEv (QuotientZk.Deployed.witnessShape id)).getLast? = some .draw := by
  rw [openingEv_W]; decide +kernel

theorem last_σ (id : QuotientRpm.Bytes32) (rows : List (List UInt8)) :
    (Render.openingEv (QuotientZk.Deployed.wiringShape id rows)).getLast? = some .draw := by
  rw [openingEv_σ]; decide +kernel

theorem last_Q (id : QuotientRpm.Bytes32) :
    (Render.openingEv (QuotientZk.Deployed.quotientShape id)).getLast? = some .draw := by
  rw [openingEv_Q]; decide +kernel

end PcsQuotient.EndToEnd.Core
