-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The openings are `formal/Compose`'s
-- `WhirOp`s (`ListChainKDoom.lean`); the claims are `UniStatement.verifyWith`'s.
import UniSound.FsChain

/-!
# The univariate verifier's five openings, its check, and the links

`ListChainKDoom.lean`'s openings for the univariate verifier (`uniOps`): `C1` (round `0`'s root)
and `C2` (round `nF + 1`'s), opened by the computable decoder (`tableCode`, the candidates read
back as stacks, `rdTab`); the setup's stack `F`, and Flock's `A0`, `B0` (the setup's roots), each
a `WhirShape.large` of a plain layout (`plainL v`: one chunk of `2^v` words, lane `l` its block
`l`, `PCS_OPEN`'s layout), at the deployment's layout words' variables (`UniShapes`: `24 … 28`).

* **The check** (`uniCheck`): the transcript completes the rounds, every value the chain program
  requires zero is, and its result is well formed (one point claim per commitment, of its
  layout word's variables, and Flock's matrices' claim): what an accepting run satisfies.
* **The claims** (`claimsOf`, `matClaims`), **`good`** (a candidate satisfies its commitment's
  claims: `uniGood`) and **`goodS`** (the setup's and Flock's honest stacks satisfy theirs).
* **`hlink_uni`**: the composition's last link from `FsLayer`'s (`ClaimsHold`, `openedOf`), the
  candidates `none` but at `C1`'s and `C2`'s rounds (`opened_eq_openedOf`); **`hok_round`**:
  `WhirOp.OK` of the round openings (`tabEval_rdTab`: a decoded table's evaluation is its stack's
  multilinear extension, `cubeEq`); **`root_uniRounds`**: the rounds with a root are `0` and
  `nF + 1`.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

/-! ## The rounds with a root -/

theorem root_uniRounds (fr : List RoundSpec) (hfr : ∀ r ∈ fr, r.root = false) (nV V i : ℕ)
    (h : ((uniRounds fr nV V).getD i ⟨false, 0, 0⟩).root = true) : i = 0 ∨ i = fr.length + 1 := by
  rcases i with _ | k
  · exact Or.inl rfl
  · right
    have e : (uniRounds fr nV V).getD (k + 1) ⟨false, 0, 0⟩ =
        (fr ++ (([⟨true, 0, 0⟩, ⟨false, nV, 1⟩] : List RoundSpec) ++
          List.replicate V (⟨false, 2, 0⟩ : RoundSpec))).getD k ⟨false, 0, 0⟩ := by
      simp [uniRounds, List.append_assoc]
    rw [e] at h
    by_contra hk
    rcases Nat.lt_or_ge k fr.length with hlt | hge
    · rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt] at h
      rw [hfr _ (List.getElem_mem hlt)] at h
      exact Bool.false_ne_true h
    · have hk' : fr.length + 1 ≤ k := by omega
      rw [List.getD_append_right _ _ _ _ hge] at h
      obtain ⟨j, hj⟩ : ∃ j, k - fr.length = j + 1 := ⟨k - fr.length - 1, by omega⟩
      rw [hj] at h
      simp only [List.cons_append, List.getD_cons_succ] at h
      rcases j with _ | j
      · simp at h
      · simp only [List.getD_cons_succ, List.nil_append] at h
        rw [List.getD_eq_getElem?_getD] at h
        rcases hj' : (List.replicate V (⟨false, 2, 0⟩ : RoundSpec))[j]? with _ | r
        · rw [hj'] at h
          simp at h
        · rw [hj'] at h
          have := List.mem_replicate.mp (List.mem_of_getElem? hj')
          rw [Option.getD_some, this.2] at h
          simp at h

/-! ## The opened transcript -/

/-- A round's candidate in `openedOf`: `c1` at round `0`, `c2` at round `nF + 1`. -/
def candAt (nF : ℕ) (c1 c2 : Stk) (j : ℕ) : Option Stk :=
  if j = 0 then some c1 else if j = nF + 1 then some c2 else none

theorem opened_eq_zipIdx (nF : ℕ) (c1 c2 : Stk) : ∀ (ums : List UMsg) (ch : List (List E))
    (cs : List (Option Stk)) (k : ℕ), ch.length = ums.length → cs.length = ums.length →
    (∀ i (h : i < cs.length), cs[i] = candAt nF c1 c2 (k + i)) →
    opened cs (ums.map toRMsg) ch =
      ((ums.zip ch).zipIdx k).map fun x : (UMsg × List E) × ℕ =>
        ((candAt nF c1 c2 x.2, x.1.1.2), x.1.2)
  | [], _, _, _, _, _, _ => by simp [opened]
  | u :: us, c :: chs, c0 :: cs', k, hch, hcs, hc => by
    simp only [List.map_cons, opened, List.headD_cons, List.tail_cons, List.zip_cons_cons,
      List.zipIdx_cons, List.cons.injEq]
    refine ⟨?_, opened_eq_zipIdx nF c1 c2 us chs cs' (k + 1) (by simpa using hch)
      (by simpa using hcs) fun i h => ?_⟩
    · have := hc 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at this
      rw [this]
      rfl
    · have := hc (i + 1) (by simpa using h)
      simp only [List.getElem_cons_succ] at this
      rw [this, show k + (i + 1) = k + 1 + i by omega]
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, h, _ => by simp at h

theorem opened_eq_openedOf (nF : ℕ) (c1 c2 : Stk) (ums : List UMsg) (ch : List (List E))
    (cs : List (Option Stk)) (hch : ch.length = ums.length) (hcs : cs.length = ums.length)
    (hc : ∀ i (h : i < cs.length), cs[i] = candAt nF c1 c2 i) :
    opened cs (ums.map toRMsg) ch = openedOf nF c1 c2 (ums.zip ch) := by
  rw [opened_eq_zipIdx nF c1 c2 ums ch cs 0 hch hcs (fun i h => by rw [hc i h, Nat.zero_add])]
  rfl

/-! ## A decoded table's evaluation is its stack's multilinear extension -/

/-- A table of the layout as a stack. -/
def rdTab {L : WhirBridge.Layout} (T : Tab L) : Stk := fun i => if h : i < 2 ^ L.vars then T[i] else 0

theorem eqEval_boolPoint (x : ℕ) : ∀ p : List E,
    Verifier.eqEval (boolPoint p.length x) p = cubeEq p p.length x := by
  intro p
  induction p using List.reverseRecOn with
  | nil => simp [Verifier.eqEval, boolPoint, cubeEq]
  | append_singleton p a ih =>
    have hb : boolPoint (p ++ [a]).length x =
        boolPoint p.length x ++ [if x.testBit p.length then 1 else 0] := by
      simp [boolPoint, List.range_succ]
    have hz : Verifier.eqEval (boolPoint (p ++ [a]).length x) (p ++ [a]) =
        Verifier.eqEval (boolPoint p.length x) p * (1 + (if x.testBit p.length then 1 else 0) + a) := by
      rw [hb]
      unfold Verifier.eqEval
      rw [List.zipWith_append (by simp [boolPoint]), List.foldl_append]
      rfl
    have hc : cubeEq (p ++ [a]) (p ++ [a]).length x =
        cubeEq p p.length x * (1 + a + if x.testBit p.length then 1 else 0) := by
      unfold cubeEq
      rw [List.length_append, List.length_singleton, Finset.prod_range_succ,
        Finset.prod_congr rfl fun k hk => by rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hk)],
        List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    rw [hz, hc, ih]
    ring

theorem tabEval_rdTab (L : WhirBridge.Layout) (T : Tab L) (p : List E) (hp : p.length = L.vars) :
    tabEval L T p = mleStk (rdTab T) L.vars p := by
  have he : ∀ x, Verifier.eqEval (boolPoint L.vars x) p = cubeEq p L.vars x := fun x => by
    have := eqEval_boolPoint x p
    rwa [hp] at this
  unfold tabEval mleStk
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [he, mul_comm]
  congr 2
  simp [rdTab]

/-! ## The plain layouts, the shapes -/

/-- **A plain layout** of `2^v` words (`plainLayout`, `PCS_OPEN`'s): one chunk, lane `l` its block
`l`. -/
abbrev plainL (v : ℕ) : WhirBridge.Layout := WhirBridge.Layout.new v v v [(0, 2 ^ v)]

theorem newOK_plain (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) : NewOK v v v [(0, 2 ^ v)] := by
  interval_cases v <;> decide +kernel

/-- **The plain shape of `2^v` words**, `24 ≤ v ≤ 28` (`WhirShape.large`). -/
@[reducible] noncomputable def plainShape (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) : WhirShape :=
  WhirShape.large v v v [(0, 2 ^ v)] (newOK_plain v h1 h2) h1 h2

theorem extra_plainL (v : ℕ) : (plainL v).extra = [] := WhirBridge.Layout.extra_of_none rfl

/-- A layout word's variables (`layoutWordVars`): `C1`, `C2`, the setup, `A0`, `B0`. -/
def wv (D : Deployment) (k : ℕ) : ℕ := layoutWordVars ((layoutWords D.shape).getD k [])

/-- **The deployment's stacks are large**: the five layout words name `24 … 28` variables. -/
structure UniShapes (D : Deployment) : Prop where
  lo : ∀ k < 5, 24 ≤ wv D k
  hi : ∀ k < 5, wv D k ≤ 28

/-- The `k`-th opening's shape. -/
@[reducible] noncomputable def shapeK {D : Deployment} (hs : UniShapes D) (k : ℕ) (hk : k < 5) :
    WhirShape :=
  plainShape (wv D k) (hs.lo k hk) (hs.hi k hk)

/-- An array as a column of `2^v` words (missing words `0`). -/
def colOf (a : Array K) (v : ℕ) : LeanVM.Protocol.Column v := ⟨Vector.ofFn fun i => a.getD i.val 0⟩

/-! ## The claims -/

/-- **The point claims of a commitment** in the verifier's result. -/
def claimsOf (r : Reduced) (c : Commitment) : List WhirBridge.Claim :=
  r.openings.filterMap fun o => if o.1 = c then
    match o.2 with
    | .point pt v _ => some ⟨pt, v⟩
    | .weighted _ => none
    else none

/-- **Flock's matrices' claim**, on `A0` (`left`) or `B0`. -/
def matClaims (r : Reduced) (left : Bool) : List WhirBridge.Claim :=
  match r.matrices with
  | some mc => [⟨mc.point, if left then mc.a else mc.b⟩]
  | none => []

/-- **The opening's statement**: the claims, when they are at most one and of the layout's
variables (else none, which the opening rejects). -/
def mkStmt (L : WhirBridge.Layout) (hL : L.extra = []) (cs : List WhirBridge.Claim) :
    Stmt L.stacking :=
  if h : cs.length ≤ 1 ∧ ∀ c ∈ cs, c.point.length = L.vars then
    ⟨cs, by
      show cs.length + L.extra.length ≤ 2 ^ 46 + 1
      rw [hL, List.length_nil]
      omega, h.2⟩
  else ⟨[], by
      show 0 + L.extra.length ≤ 2 ^ 46 + 1
      rw [hL]
      decide, by simp⟩

theorem mkStmt_claims (L : WhirBridge.Layout) (hL : L.extra = []) (cs : List WhirBridge.Claim)
    (h1 : cs.length ≤ 1) (h2 : ∀ c ∈ cs, c.point.length = L.vars) :
    (mkStmt L hL cs).claims = cs := by
  unfold mkStmt
  split_ifs with h
  · rfl
  · exact absurd ⟨h1, h2⟩ h

theorem mkStmt_wide (L : WhirBridge.Layout) (hL : L.extra = []) (cs : List WhirBridge.Claim) :
    ∀ c ∈ (mkStmt L hL cs).claims, c.point.length = L.vars :=
  (mkStmt L hL cs).wide

/-! ## The verifier's openings -/

section Ops

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)

/-- The main line's rounds. -/
abbrev uRounds : List RoundSpec := uniRounds Fl.prog.rounds nV V

/-- The PIOP's statement a proof announces. -/
def uSt (π : UPf) : USt := ustOf (uView (uRounds Fl nV V) π).1

/-- **The chain program's result** on a proof and challenges. -/
def uOut (π : UPf) (ch : List (List E)) : Reduced :=
  (C.prog (uSt Fl nV V π).1 (uSt Fl nV V π).2).out (uDone (uRounds Fl nV V) π ch)
    (uTail (uRounds Fl nV V) π)

/-- **The result is well formed**: one opening per commitment, in order, its point claims of its
layout word's variables, and Flock's matrices' claim of `A0`'s. -/
def WellFormed (r : Reduced) : Prop :=
  r.openings.map Prod.fst = commitments ∧
    (∀ c ∈ claimsOf r .c1, c.point.length = wv D 0) ∧
    (∀ c ∈ claimsOf r .c2, c.point.length = wv D 1) ∧
    (∀ c ∈ claimsOf r .setup, c.point.length = wv D 2) ∧
    (∀ mc, r.matrices = some mc → mc.point.length = wv D 3 ∧ mc.point.length = wv D 4)

/-- **The verifier's check** (what an accepting run satisfies): the transcript completes the
rounds, every value the chain program requires zero is, and its result is well formed. -/
def uniCheck (π : UPf) (ch : List (List E)) : Prop :=
  DoneFits (uRounds Fl nV V) (uDone (uRounds Fl nV V) π ch) ∧
    (C.prog (uSt Fl nV V π).1 (uSt Fl nV V π).2).ZerosVanish (uDone (uRounds Fl nV V) π ch)
      (uTail (uRounds Fl nV V) π) ∧
    WellFormed D (uOut D Fl nV V C π ch)

/-- The `k`-th opening's statement on its plain layout. -/
def uCl (k : ℕ) (cs : List WhirBridge.Claim) : Stmt (plainL (wv D k)).stacking :=
  mkStmt _ (extra_plainL _) cs

/-- `C1`'s claims. -/
def cl1 (π : UPf) (ch : List (List E)) : Stmt (plainL (wv D 0)).stacking :=
  uCl D 0 (claimsOf (uOut D Fl nV V C π ch) .c1)

/-- `C2`'s claims. -/
def cl2 (π : UPf) (ch : List (List E)) : Stmt (plainL (wv D 1)).stacking :=
  uCl D 1 (claimsOf (uOut D Fl nV V C π ch) .c2)

/-- The setup's claims. -/
def cl3 (π : UPf) (ch : List (List E)) : Stmt (plainL (wv D 2)).stacking :=
  uCl D 2 (claimsOf (uOut D Fl nV V C π ch) .setup)

/-- `A0`'s claim. -/
def cl4 (π : UPf) (ch : List (List E)) : Stmt (plainL (wv D 3)).stacking :=
  uCl D 3 (matClaims (uOut D Fl nV V C π ch) true)

/-- `B0`'s claim. -/
def cl5 (π : UPf) (ch : List (List E)) : Stmt (plainL (wv D 4)).stacking :=
  uCl D 4 (matClaims (uOut D Fl nV V C π ch) false)

variable {D} in
/-- **The five openings**: `C1` and `C2` (rounds `0`, `nF + 1`), the setup's stack, `A0`, `B0` (the
setup's roots), each its one claim. -/
noncomputable def uniOps (hs : UniShapes D) (qF : LeanVM.Protocol.Column (wv D 2))
    (qA : LeanVM.Protocol.Column (wv D 3)) (qB : LeanVM.Protocol.Column (wv D 4)) :
    List (WhirOp UPf E Stk) :=
  [⟨shapeK hs 0 (by decide), cl1 D Fl nV V C, fun π => π.proof.c1,
      .round 0 fun q => rdTab (tabOf _ q)⟩,
    ⟨shapeK hs 1 (by decide), cl2 D Fl nV V C, fun π => π.proof.c2,
      .round (Fl.prog.rounds.length + 1) fun q => rdTab (tabOf _ q)⟩,
    ⟨shapeK hs 2 (by decide), cl3 D Fl nV V C, fun π => π.proof.setup,
      .setup (fun π => toB π.roots.bytecode) qF⟩,
    ⟨shapeK hs 3 (by decide), cl4 D Fl nV V C, fun π => π.proof.a0,
      .setup (fun π => toB π.roots.a0) qA⟩,
    ⟨shapeK hs 4 (by decide), cl5 D Fl nV V C, fun π => π.proof.b0,
      .setup (fun π => toB π.roots.b0) qB⟩]

variable {D} in
/-- **The decoders**: `C1`'s (round `0`) and `C2`'s, `tableCode` of their shapes. -/
noncomputable def uniTc (hs : UniShapes D) (i : ℕ) : TableCode Stk :=
  if i = 0 then tableCode (shapeK hs 0 (by decide)).L (shapeK hs 0 (by decide)).R
      (shapeK hs 0 (by decide)).adm rdTab
  else tableCode (shapeK hs 1 (by decide)).L (shapeK hs 1 (by decide)).R
      (shapeK hs 1 (by decide)).adm rdTab

/-- **A candidate is good**: at `C1`'s and `C2`'s rounds, a stack satisfying its opening's claims. -/
def uniGood (i : ℕ) (π : UPf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧
      ∀ cl ∈ (cl1 D Fl nV V C π ch).claims, mleStk q (wv D 0) cl.point = cl.value
  else if i = Fl.prog.rounds.length + 1 then ∃ q, c = some q ∧
      ∀ cl ∈ (cl2 D Fl nV V C π ch).claims, mleStk q (wv D 1) cl.point = cl.value
  else True

/-- **The setup's stacks are good**: the setup's honest stack, `A0` and `B0` satisfy their
openings' claims. -/
def uniGoodS (π : UPf) (ch : List (List E)) : Prop :=
  (∀ cl ∈ (cl3 D Fl nV V C π ch).claims,
      mleStk (fun i => (setupStack D.prog D.shape).getD i 0) (wv D 2) cl.point = cl.value) ∧
    (∀ cl ∈ (cl4 D Fl nV V C π ch).claims,
      mleArr (flockMatrixStack true) (wv D 3) cl.point = cl.value) ∧
    (∀ cl ∈ (cl5 D Fl nV V C π ch).claims,
      mleArr (flockMatrixStack false) (wv D 4) cl.point = cl.value)

end Ops

end UniSound
