-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The round-by-round form is `UniSound.Piop`'s
-- (`formal/Compose/Compose/ListChainK.lean`'s `Piop`), for π1-rec3's rounds.
import UniSound.Piop
import UniSound.Rec3.FlockInterface3

/-!
# π1-rec3's PIOP, round by round: rounds, identity model, states, errors

π1-rec3's rounds as the chain sees them (`rec3Rounds`):

| round | message | challenges |
|---|---|---|
| `0` | `C1`'s root | `c` (`α = (c, c², c⁴, c⁸)`), `β`, `γ` |
| `1 … nF` | Flock's rounds (`FlockSound3.prog.rounds`: the zerocheck's squares from one challenge, the walk's zero) | Flock's |
| `nF + 1` | `C2`'s root | `t` |
| `nF + 2` | the `nV` values at `t` | `ρ`, `λ` |
| `nF + 3 … nF + 2 + np` | the batch's pair rounds, `8` scalars each | one narrow `z` each |
| `nF + 3 + np` | the batch's last plain round, `c0, c2` | one narrow challenge |

then the three stacks' values at the batch's point (the tail) and three openings.

**The batch's rounds** are given abstractly (`PairBatch np`): a state on their records (the claim is the partial
sum at the point so far), at the start the target being the sum, and each round's error (`errPair` for a pair,
`errLast` for the plain round); `UniSound.Rec3.Pairs` instantiates it (`8 · 2^32 / |E|`, `2 · 2^32 / |E|`: narrow
challenges, a pair's polynomial of degree `8`).

**The identity model** (`UniIds3`) is the main line's (`UniIds`) at π1-rec3's transcripts: round `0`'s three
challenges (`MainOK`, `mainSound` over `3` draws: the bus at `α = (c, c², c⁴, c⁸)`), Flock read through
`FlockSound3.outM` (its end and its pending claim), the batch's products **without** the pending matrices' term
(`prod`, `target`), whose start (`batch_start`) holds when the pending claim is its sum: there the main line's
`λ³` term and its claim cancel.

**The states** (`uniPre3`, `uniPost3`): as the main line's (`uniS`), and from `C2`'s round on **the pending claim is
its sum** (`PendingHolds` of `outM`, a function of Flock's transcript, which the walk's zero gives at the end):
the `ρ, λ` step needs it to start the batch without the `λ³` term.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

/-! ## The rounds -/

/-- **π1-rec3's rounds**: `C1` and `c, β, γ`; Flock's; `C2` and `t`; the `nV` values and `ρ, λ`; `np` pair rounds;
the last plain round. -/
def rec3Rounds (flockRounds : List Compose.RoundSpec) (nV np : ℕ) : List Compose.RoundSpec :=
  [⟨true, 0, 2⟩] ++ flockRounds ++ [⟨true, 0, 0⟩, ⟨false, nV, 1⟩] ++ List.replicate np ⟨false, 8, 0⟩ ++
    [⟨false, 2, 0⟩]

section Rounds

variable (Fr : List Compose.RoundSpec) (nV np : ℕ)

theorem length_rec3Rounds : (rec3Rounds Fr nV np).length = Fr.length + 4 + np := by
  simp [rec3Rounds]
  omega

theorem rec3Rounds_zero : (rec3Rounds Fr nV np).getD 0 ⟨false, 0, 0⟩ = ⟨true, 0, 2⟩ := rfl

theorem rec3Rounds_eq : rec3Rounds Fr nV np =
    [⟨true, 0, 2⟩] ++ (Fr ++ ([⟨true, 0, 0⟩, ⟨false, nV, 1⟩] ++ (List.replicate np ⟨false, 8, 0⟩ ++
      [⟨false, 2, 0⟩]))) := by
  simp [rec3Rounds]

theorem rec3Rounds_flock (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ Fr.length) :
    (rec3Rounds Fr nV np).getD j ⟨false, 0, 0⟩ = Fr.getD (j - 1) ⟨false, 0, 0⟩ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [rec3Rounds_eq]
  simp only [List.getD_eq_getElem?_getD, Nat.add_sub_cancel, List.singleton_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by omega)]

theorem rec3Rounds_c2 : (rec3Rounds Fr nV np).getD (Fr.length + 1) ⟨false, 0, 0⟩ = ⟨true, 0, 0⟩ := by
  rw [rec3Rounds_eq]
  simp only [List.getD_eq_getElem?_getD, List.singleton_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem rec3Rounds_vals : (rec3Rounds Fr nV np).getD (Fr.length + 2) ⟨false, 0, 0⟩ = ⟨false, nV, 1⟩ := by
  rw [rec3Rounds_eq]
  simp only [List.getD_eq_getElem?_getD, List.singleton_append,
    show Fr.length + 2 = (Fr.length + 1) + 1 by omega, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), show Fr.length + 1 - Fr.length = 1 by omega]
  rfl

theorem rec3Rounds_pair (j : ℕ) (h1 : Fr.length + 3 ≤ j) (h2 : j < Fr.length + 3 + np) :
    (rec3Rounds Fr nV np).getD j ⟨false, 0, 0⟩ = ⟨false, 8, 0⟩ := by
  rw [rec3Rounds_eq]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [List.getD_eq_getElem?_getD, List.singleton_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by simp; omega),
    List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
  simp only [List.length_cons, List.length_nil]
  rw [ite_eq_left (by omega)]
  rfl

theorem rec3Rounds_last : (rec3Rounds Fr nV np).getD (Fr.length + 3 + np) ⟨false, 0, 0⟩ = ⟨false, 2, 0⟩ := by
  rw [rec3Rounds_eq]
  simp only [List.getD_eq_getElem?_getD, List.singleton_append,
    show Fr.length + 3 + np = (Fr.length + 2 + np) + 1 by omega, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons, List.length_nil, List.length_replicate]
  rw [show Fr.length + 2 + np - Fr.length - 2 - np = 0 by omega]
  rfl

end Rounds

/-! ## The batch's rounds, abstractly -/

/-- **The batching sumcheck at π1-rec3, round by round**: on a sum of products `P` over `2 np + 1` variables and its
claimed sum `tg`, a state on the rounds' records (each round's scalars and its challenges); before any round the
claim is the sum; a pair round errs with probability at most `errPair`, the last plain round `errLast`. -/
structure PairBatch (np : ℕ) where
  St : ProdSum → E → List (List E × List E) → Prop
  St_nil : ∀ P tg, St P tg [] ↔ tg = P.T []
  errPair : ℝ≥0∞
  errLast : ℝ≥0∞
  step : ∀ (P : ProdSum) (tg : E) (rs : List (List E × List E)) (m : List E), P.vars = 2 * np + 1 →
    rs.length ≤ np → Pr{let c ← Compose.draws E 1}[¬ St P tg rs ∧ St P tg (rs ++ [(m, c)])] ≤
      if rs.length < np then errPair else errLast

/-! ## The identity model -/

/-- **π1-rec3's identity model**: the main line's (`UniIds`) at π1-rec3's transcripts, for its Flock phase `F3`:
round `0`'s three challenges, Flock read through `F3.outM`, the batch over `2 np + 1` variables without the pending
term, its start under the pending claim. -/
structure UniIds3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (np : ℕ) where
  nV : ℕ
  qf : Stk → LeanVM.Protocol.Column (8 + κ)
  MainHolds : USt → Stk → Prop
  rel_of : ∀ s c, MainHolds s c → FlockHolds κ (qf c) → Rel D s c
  MainOK : USt → Stk → List E → Prop
  errMain : ℝ≥0∞
  mainSound : ∀ s c, Pr{let ch ← Compose.draws E 3}[¬ MainHolds s c ∧ MainOK s c ch] ≤ errMain
  polys : USt → Stk → List E → Done → Stk → List (Polynomial E)
  degSum : ℕ
  deg_le : ∀ s c1 ch fd c2, ((polys s c1 ch fd c2).map Polynomial.natDegree).sum ≤ degSum
  main_of_polys : ∀ s c1 ch fd c2, (∀ P ∈ polys s c1 ch fd c2, P = 0) → MainOK s c1 ch
  zb : Done → Polynomial E
  zb_ne : ∀ fd, zb fd ≠ 0
  degBad : ℕ
  zb_deg : ∀ fd, (zb fd).natDegree ≤ degBad
  diffs : USt → Stk → List E → Done → Stk → E → List E → List (List E)
  nRel : ℕ
  diffs_len : ∀ s c1 ch fd c2 t vals, ∀ d ∈ diffs s c1 ch fd c2 t vals, d.length ≤ nRel
  diffs_count : ∀ s c1 ch fd c2 t vals, (diffs s c1 ch fd c2 t vals).length ≤ 4
  diffs_eval : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    ∀ P ∈ polys s c1 ch fd c2, P.eval t = 0
  diffs_flock : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    FlockEndHolds (qf c1) (F3.outM fd)
  diffs_pending : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    PendingHolds (F3.outM fd).2.2
  prod : USt → Stk → List E → Done → Stk → E → List E → E → E → ProdSum
  prod_vars : ∀ s c1 ch fd c2 t vals ρ l, (prod s c1 ch fd c2 t vals ρ l).vars = 2 * np + 1
  target : USt → Stk → List E → Done → Stk → E → List E → E → E → E
  batch_start : ∀ s c1 ch fd c2 t vals ρ l, PendingHolds (F3.outM fd).2.2 →
    (prod s c1 ch fd c2 t vals ρ l).T [] + target s c1 ch fd c2 t vals ρ l =
      powComb ((diffs s c1 ch fd c2 t vals).map fun d => powComb d ρ) l

/-! ## The states -/

section States

variable {D : Deployment} {κ : ℕ} (F3 : FlockSound3 κ) {np : ℕ} (I : UniIds3 D F3 np) (BR : PairBatch np)

/-- **Flock's end**: its rounds completed. -/
def FlockDone3 (fd : Done) : Prop := DoneFits F3.prog.rounds fd

/-- **The state after the completed rounds `q`** (`q` nonempty). -/
def uniS3 (s : USt) (q : Op Stk) : Prop :=
  ∃ c1, (rd q 0).1.1 = some c1 ∧
    if q.length ≤ F3.prog.rounds.length + 1 then
      I.MainOK s c1 (rd q 0).2 ∧
        DoneFits (F3.prog.rounds.take (q.length - 1)) (fdOf F3.prog.rounds.length q) ∧
          F3.S (I.qf c1) (fdOf F3.prog.rounds.length q)
    else ∃ c2, (rd q (F3.prog.rounds.length + 1)).1.1 = some c2 ∧
      FlockDone3 F3 (fdOf F3.prog.rounds.length q) ∧
      PendingHolds (F3.outM (fdOf F3.prog.rounds.length q)).2.2 ∧
      ((I.zb (fdOf F3.prog.rounds.length q)).eval ((rd q (F3.prog.rounds.length + 1)).2.headD 0) = 0 ∨
      if q.length = F3.prog.rounds.length + 2 then
        ∃ vals, ∀ d ∈ I.diffs s c1 (rd q 0).2 (fdOf F3.prog.rounds.length q) c2
          ((rd q (F3.prog.rounds.length + 1)).2.headD 0) vals, ∀ x ∈ d, x = 0
      else
        BR.St (I.prod s c1 (rd q 0).2 (fdOf F3.prog.rounds.length q) c2
            ((rd q (F3.prog.rounds.length + 1)).2.headD 0)
            (rd q (F3.prog.rounds.length + 2)).1.2
            ((rd q (F3.prog.rounds.length + 2)).2.headD 0)
            ((rd q (F3.prog.rounds.length + 2)).2.getD 1 0))
          (I.target s c1 (rd q 0).2 (fdOf F3.prog.rounds.length q) c2
            ((rd q (F3.prog.rounds.length + 1)).2.headD 0)
            (rd q (F3.prog.rounds.length + 2)).1.2
            ((rd q (F3.prog.rounds.length + 2)).2.headD 0)
            ((rd q (F3.prog.rounds.length + 2)).2.getD 1 0))
          (brOf F3.prog.rounds.length q))

/-- **The state before a round's challenges**: before round `0`, the relation of `C1`'s candidate; before `t`,
the identities as polynomials for `C2`'s candidate, Flock's end and its pending claim; else the state after the
rounds before. -/
def uniPre3 (s : USt) (p : Op Stk) (m : Option Stk × List E) : Prop :=
  if p.length = 0 then ∃ c, m.1 = some c ∧ Rel D s c
  else if p.length = F3.prog.rounds.length + 1 then
    ∃ c1 c2, (rd p 0).1.1 = some c1 ∧ m.1 = some c2 ∧
      (∀ P ∈ I.polys s c1 (rd p 0).2 (fdOf F3.prog.rounds.length p) c2, P = 0) ∧
      FlockEndHolds (I.qf c1) (F3.outM (fdOf F3.prog.rounds.length p)) ∧
      PendingHolds (F3.outM (fdOf F3.prog.rounds.length p)).2.2 ∧
      FlockDone3 F3 (fdOf F3.prog.rounds.length p)
  else uniS3 F3 I BR s p

/-- **The state after a round's challenges.** -/
def uniPost3 (s : USt) (p : Op Stk) (m : Option Stk × List E) (c : List E) : Prop :=
  uniS3 F3 I BR s (p ++ [(m, c)])

/-- **The rounds' errors.** -/
noncomputable def uniErr3 (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then I.errMain
  else if j ≤ F3.prog.rounds.length then F3.err (j - 1)
  else if j = F3.prog.rounds.length + 1 then
    ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else if j = F3.prog.rounds.length + 2 then
    ((I.nRel - 1 + (4 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else if j < F3.prog.rounds.length + 3 + np then BR.errPair
  else BR.errLast

end States

end UniSound
