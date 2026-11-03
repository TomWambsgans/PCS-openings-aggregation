-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsOps.lean` (and `FsChain.lean`'s
-- tail) for π1-rec3's verifier (`formal/UniStatement`'s `verifyWithFs … .rec3 true`: three `PCS_OPEN` calls).
import UniSound.FsFinal
import UniSound.Rec3.Fs3

/-!
# π1-rec3's three openings, its check, and the tail

`FsOps.lean`'s openings for π1-rec3 (`uniOps3`): `C1` (round `0`'s root) and `C2` (round `nF + 1`'s), opened by the
computable decoder (`uniTc`, unchanged), and the setup's stack `F` at the setup's root, each a `WhirShape.large`
of a plain layout at its layout word's variables. Flock's `A0`, `B0` are **not** opened (π1-rec3 walks the
lincheck's terminal: no matrices' claim), though the setup still commits them (three trees, unchanged).

* **The chain's statement and messages** are `FsChain.lean`'s (`uniSpec`, `uView`, `uDone`: generic in the
  rounds), at `rec3Rounds` (`uRounds3`); **the tail** (`uTail3`) is three scalars (the stacks' values at the
  batch's point; no `a`, `b`).
* **The check** (`uniCheck3`): the transcript completes the rounds, every value the chain program requires zero
  is, and its result is π1-rec3's shape (`WellFormed3`: one point claim per commitment, of its layout word's
  variables, and **no** matrices' claim, which `verifyWithFs … .rec3 true` rejects).
* **`good`** (`uniGood3`: a candidate satisfies its commitment's claims) and **`goodS`** (`uniGoodS3`: the setup's
  honest stack satisfies its claim; there is no `A0`, `B0` claim).
* **`root_rec3Rounds`**: the rounds with a root are `0` and `nF + 1`.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

/-! ## The tail -/

/-- **π1-rec3's tail**: the three scalars after the rounds (the stacks' values at the batch's point). -/
def uTail3 (rounds : List RoundSpec) (π : UPf) : List E :=
  (List.range 3).map fun k => scalarAt π.proof.stream (24 + roundsBytes rounds + 24 * k)

@[simp] theorem length_uTail3 (rounds : List RoundSpec) (π : UPf) : (uTail3 rounds π).length = 3 := by
  simp [uTail3]

/-! ## The rounds with a root -/

theorem root_rec3Rounds (fr : List RoundSpec) (hfr : ∀ r ∈ fr, r.root = false) (nV np i : ℕ)
    (h : ((rec3Rounds fr nV np).getD i ⟨false, 0, 0⟩).root = true) : i = 0 ∨ i = fr.length + 1 := by
  rcases i with _ | k
  · exact Or.inl rfl
  · right
    have e : (rec3Rounds fr nV np).getD (k + 1) ⟨false, 0, 0⟩ =
        (fr ++ (([⟨true, 0, 0⟩, ⟨false, nV, 1⟩] : List RoundSpec) ++
          (List.replicate np (⟨false, 8, 0⟩ : RoundSpec) ++ ([⟨false, 2, 0⟩] : List RoundSpec)))).getD k
          ⟨false, 0, 0⟩ := by
      rw [rec3Rounds_eq]
      rfl
    rw [e] at h
    by_contra hk
    rcases Nat.lt_or_ge k fr.length with hlt | hge
    · rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt] at h
      rw [hfr _ (List.getElem_mem hlt)] at h
      exact Bool.false_ne_true h
    · rw [List.getD_append_right _ _ _ _ hge] at h
      obtain ⟨j, hj⟩ : ∃ j, k - fr.length = j + 1 := ⟨k - fr.length - 1, by omega⟩
      rw [hj] at h
      simp only [List.cons_append, List.getD_cons_succ] at h
      rcases j with _ | j
      · simp at h
      · simp only [List.getD_cons_succ, List.nil_append] at h
        rw [List.getD_eq_getElem?_getD] at h
        rcases hj' : (List.replicate np (⟨false, 8, 0⟩ : RoundSpec) ++ ([⟨false, 2, 0⟩] : List RoundSpec))[j]? with
            _ | r
        · rw [hj'] at h
          simp at h
        · rw [hj', Option.getD_some] at h
          have hm := List.mem_of_getElem? hj'
          rw [List.mem_append, List.mem_replicate, List.mem_singleton] at hm
          rcases hm with ⟨-, rfl⟩ | rfl <;> simp at h

/-! ## The verifier's openings -/

section Ops

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)

/-- π1-rec3's rounds. -/
abbrev uRounds3 : List RoundSpec := rec3Rounds F3.prog.rounds nV np

/-- The PIOP's statement a proof announces. -/
def uSt3 (π : UPf) : USt := ustOf (uView (uRounds3 F3 nV np) π).1

/-- **The chain program's result** on a proof and challenges. -/
def uOut3 (π : UPf) (ch : List (List E)) : Reduced :=
  (C.prog (uSt3 F3 nV np π).1 (uSt3 F3 nV np π).2).out (uDone (uRounds3 F3 nV np) π ch)
    (uTail3 (uRounds3 F3 nV np) π)

/-- **The result is π1-rec3's shape**: one opening per commitment, in order, its point claims of its layout
word's variables, and no matrices' claim. -/
def WellFormed3 (r : Reduced) : Prop :=
  r.openings.map Prod.fst = commitments ∧
    (∀ c ∈ claimsOf r .c1, c.point.length = wv D 0) ∧
    (∀ c ∈ claimsOf r .c2, c.point.length = wv D 1) ∧
    (∀ c ∈ claimsOf r .setup, c.point.length = wv D 2) ∧
    r.matrices = none

/-- **The verifier's check** (what an accepting run satisfies): the transcript completes the rounds, every value
the chain program requires zero is, and its result is π1-rec3's shape. -/
def uniCheck3 (π : UPf) (ch : List (List E)) : Prop :=
  DoneFits (uRounds3 F3 nV np) (uDone (uRounds3 F3 nV np) π ch) ∧
    (C.prog (uSt3 F3 nV np π).1 (uSt3 F3 nV np π).2).ZerosVanish (uDone (uRounds3 F3 nV np) π ch)
      (uTail3 (uRounds3 F3 nV np) π) ∧
    WellFormed3 D (uOut3 D F3 nV np C π ch)

/-- `C1`'s claims. -/
def cl1_3 (π : UPf) (ch : List (List E)) : Stmt (plainL (wv D 0)).stacking :=
  uCl D 0 (claimsOf (uOut3 D F3 nV np C π ch) .c1)

/-- `C2`'s claims. -/
def cl2_3 (π : UPf) (ch : List (List E)) : Stmt (plainL (wv D 1)).stacking :=
  uCl D 1 (claimsOf (uOut3 D F3 nV np C π ch) .c2)

/-- The setup's claims. -/
def cl3_3 (π : UPf) (ch : List (List E)) : Stmt (plainL (wv D 2)).stacking :=
  uCl D 2 (claimsOf (uOut3 D F3 nV np C π ch) .setup)

variable {D} in
/-- **π1-rec3's three openings**: `C1` and `C2` (rounds `0`, `nF + 1`), the setup's stack (the setup's root),
each its one claim. -/
noncomputable def uniOps3 (hs : UniShapes D) (qF : LeanVM.Protocol.Column (wv D 2)) :
    List (WhirOp UPf E Stk) :=
  [⟨shapeK hs 0 (by decide), cl1_3 D F3 nV np C, fun π => π.proof.c1,
      .round 0 fun q => rdTab (tabOf _ q)⟩,
    ⟨shapeK hs 1 (by decide), cl2_3 D F3 nV np C, fun π => π.proof.c2,
      .round (F3.prog.rounds.length + 1) fun q => rdTab (tabOf _ q)⟩,
    ⟨shapeK hs 2 (by decide), cl3_3 D F3 nV np C, fun π => π.proof.setup,
      .setup (fun π => toB π.roots.bytecode) qF⟩]

/-- **A candidate is good**: at `C1`'s and `C2`'s rounds, a stack satisfying its opening's claims. -/
def uniGood3 (i : ℕ) (π : UPf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧
      ∀ cl ∈ (cl1_3 D F3 nV np C π ch).claims, mleStk q (wv D 0) cl.point = cl.value
  else if i = F3.prog.rounds.length + 1 then ∃ q, c = some q ∧
      ∀ cl ∈ (cl2_3 D F3 nV np C π ch).claims, mleStk q (wv D 1) cl.point = cl.value
  else True

/-- **The setup's stack is good**: the setup's honest stack satisfies its opening's claims. -/
def uniGoodS3 (π : UPf) (ch : List (List E)) : Prop :=
  ∀ cl ∈ (cl3_3 D F3 nV np C π ch).claims,
    mleStk (fun i => (setupStack D.prog D.shape).getD i 0) (wv D 2) cl.point = cl.value

end Ops

end UniSound

/-- info: 'UniSound.root_rec3Rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.root_rec3Rounds
