-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The round-by-round form is
-- `formal/Compose/Compose/ListChainK.lean`'s `Piop`.
import UniSound.Sumcheck

/-!
# The univariate PIOP, round by round

The main line's rounds as the chain sees them (`uniRounds`):

| round | message | challenges |
|---|---|---|
| `0` | `C1`'s root | `α ∈ E^4`, `β`, `γ` |
| `1 … nF` | Flock's rounds (`FlockSound.prog.rounds`) | Flock's |
| `nF + 1` | `C2`'s root | `t` |
| `nF + 2` | the `nV` values at `t` | `ρ`, `λ` |
| `nF + 3 …` | the batching sumcheck's `V` rounds, `c0, c2` each | its point, one each |

then the three stacks' values at the batch's point (the tail, which no challenge follows) and the
five openings.

**The states** (`uniPiop`, in the form of `Compose.Piop`: the state before a round's challenges
`pre`, after them `post`), for a statement `s` (the public input and the row counts) and the
candidates `c1`, `c2` of `C1`'s and `C2`'s roots (stacks, `Stk`):

* before round `0`: **leanVM 42422001's relation** holds of `c1`'s Lv42 stack (`Rel`);
* after round `0` and Flock's rounds: the **bus and constraint state** `MainOK s c1 (α, β, γ)` (some
  heap and quotients can still satisfy the identities), and **Flock's state** on `q_flock`
  (`FlockSound.S`) after the Flock rounds so far;
* before `t`: the **identities hold as polynomials** for `c2` (`polys`, all zero), Flock's claim on
  `q_flock` holds, its checks pass and its matrices' claims hold;
* after `t`: **some values make every relation true** at `t` (`diffs`, all zero), Flock's checks
  and matrices as before;
* after `ρ, λ`: the **batch's target is the sum** `Σ_u g(u)` (`ProdSum.T []`);
* after each sumcheck round: the claim is the partial sum (`SumState`).

**The errors** (`uniErr`): round `0` the bus and the constraints' batching (`errMain`: `4N/|E|`
and the `γ` term, `mainSound`); Flock's rounds Flock's (`FlockSound.err`); `t` Schwartz–Zippel for
every identity (`degSum / |E|`, the sum of the identities' degrees); `ρ, λ` the two combinations
(`(nRel − 1 + 2) / |E|`); each sumcheck round `2 / |E|`. `uniPiop_sound` proves each.

**The identity model** (`UniIds`): what the states are made of and the facts the rounds need,
the bridges between the verifier's relations and Lv42's relation. Its fields are the end
theorem's mathematical obligations; `UniSound.Bus` discharges `mainSound` from `Heap`'s bus.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

/-! ## Round-by-round soundness on a list of rounds -/

/-- **An opened transcript** (`Compose.Opened`): each round's candidate (if it has a root) and
values, and its challenges. -/
abbrev Op (M : Type) := Compose.Opened M E

/-- **A protocol's round-by-round soundness on its rounds** (`Compose.Piop`, with the rounds in
place of the chain's specification). -/
structure RbrPiop (rounds : List Compose.RoundSpec) (St M : Type) where
  pre : St → Op M → Option M × List E → Prop
  post : St → Op M → Option M × List E → List E → Prop
  pre_post : ∀ s p m c m', pre s (p ++ [(m, c)]) m' → post s p m c
  err : ℕ → ℝ≥0∞
  sound : ∀ (j : ℕ) (s : St) (p : Op M) (m : Option M × List E), j < rounds.length →
    p.length = j → Pr{let c ← Compose.draws E ((rounds.getD j ⟨false, 0, 0⟩).ns + 1)}[
      ¬ pre s p m ∧ post s p m c] ≤ err j

/-- **The protocol of a chain with these rounds** (`Compose.Piop`). -/
def RbrPiop.toPiop {St M : Type} (K : Compose.ChainSpec E St) {rounds : List Compose.RoundSpec}
    (R : RbrPiop rounds St M) (hK : K.rounds = rounds) : Compose.Piop K M where
  pre := R.pre
  post := R.post
  pre_post := R.pre_post
  err := R.err
  sound j s p m hj hp := by
    have h := R.sound j s p m (hK ▸ hj) hp
    simpa only [Compose.ChainSpec.spec, hK] using h

/-! ## The statement, the candidates -/

/-- **A statement**: the public input's 32 bytes and the proof's row counts. -/
abbrev USt := Vector UInt8 32 × List ℕ

/-- **A candidate**: a stack, word by word. -/
abbrev Stk := ℕ → K

/-- **leanVM 42422001's relation** of a `C1` candidate: its Lv42 stack (`lv42Stack`) at the row
counts satisfies `M3Holds` for the public input. -/
def Rel (D : Deployment) (s : USt) (c : Stk) : Prop :=
  D.Relation s.2 s.1 (lv42Stack D.prog (D.sizes s.2) D.shape c)

/-! ## The rounds -/

/-- **The main line's rounds**: `C1` and `α, β, γ`; Flock's; `C2` and `t`; the `nV` values and
`ρ, λ`; the `V` rounds of the batching sumcheck. -/
def uniRounds (flockRounds : List Compose.RoundSpec) (nV V : ℕ) : List Compose.RoundSpec :=
  [⟨true, 0, 5⟩] ++ flockRounds ++ [⟨true, 0, 0⟩, ⟨false, nV, 1⟩] ++ List.replicate V ⟨false, 2, 0⟩

/-! ## The identity model -/

/-- **The identity model of the main line**: the states' ingredients, for the Flock phase `Fl` on
`q_flock` of `2^(8 + κ)` cells, and the facts each round needs.

* `qf c`: `c`'s column `q_flock`; `MainHolds s c`: the relation but for Flock's region
  (`ConstraintsVanish ∧ Balanced ∧ CountsNonzero ∧ PublicLinesHold` of `c`'s Lv42 stack);
  `rel_of`: with Flock's predicate on `qf c`, the relation.
* `MainOK s c (α, β, γ)`: the state after round `0` for the bus and the constraints;
  `mainSound`: round `0` turns `¬ MainHolds` into `MainOK` with probability at most `errMain`.
* `polys s c1 (α, β, γ) c2`: the identities `C1`, `C2` must satisfy, as polynomials in `t`;
  `main_of_polys`: all zero, the bus and constraint state holds; `deg_le`: their degrees sum to at
  most `degSum`.
* `diffs … t vals`: for each commitment, each of its relations' `Σ terms + value` at `t` with the
  values `vals` (zero when the relation holds; the verifier's relations, in `combine`'s order),
  and as a fourth entry the pending reduction's `Σ G L̂ ŝ + claim`; `diffs_eval`: all zero, every
  identity vanishes at `t`; `diffs_flock`: all zero, Flock's claim on `q_flock` holds (it is one
  of `C1`'s relations).
* `prod … ρ λ`: the batch's `g = Σ_{k<3} λ^k W_k C_k + λ³ G L` (`ProdSum`, over `V` variables;
  iteration 2's lever 4a: the pending matrices' sum is the fourth product), `target` its claimed
  sum `Σ_k λ^k v_k + λ³ claim`; `batch_start`: `Σ_u g(u) + target` is the combination by `λ` of
  the commitments' combinations by `ρ` of their relations' `diffs` (`combine`, `weightAt`).

The model must cover **every row count the verifier accepts**, `0 … 2^h` of a table of height
`h` (iteration 2 checks only the range), at Lv42's sizes `D.sizes rows` (`τ = ⌈log₂ rows⌉`, below
`h` for a count up to `2^(h−1)`, where honest quotients do not fit: soundness must hold there all
the same). -/
structure UniIds (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) where
  nV : ℕ
  V : ℕ
  qf : Stk → LeanVM.Protocol.Column (8 + κ)
  MainHolds : USt → Stk → Prop
  rel_of : ∀ s c, MainHolds s c → FlockHolds κ (qf c) → Rel D s c
  MainOK : USt → Stk → List E → Prop
  errMain : ℝ≥0∞
  mainSound : ∀ s c, Pr{let ch ← Compose.draws E 6}[¬ MainHolds s c ∧ MainOK s c ch] ≤ errMain
  polys : USt → Stk → List E → Stk → List (Polynomial E)
  degSum : ℕ
  deg_le : ∀ s c1 ch c2, ((polys s c1 ch c2).map Polynomial.natDegree).sum ≤ degSum
  main_of_polys : ∀ s c1 ch c2, (∀ P ∈ polys s c1 ch c2, P = 0) → MainOK s c1 ch
  diffs : USt → Stk → List E → Done → Stk → E → List E → List (List E)
  nRel : ℕ
  diffs_len : ∀ s c1 ch fd c2 t vals, ∀ d ∈ diffs s c1 ch fd c2 t vals, d.length ≤ nRel
  diffs_count : ∀ s c1 ch fd c2 t vals, (diffs s c1 ch fd c2 t vals).length ≤ 4
  diffs_eval : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    ∀ P ∈ polys s c1 ch c2, P.eval t = 0
  diffs_flock : ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffs s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    FlockEndHolds (qf c1) (Fl.prog.out fd [])
  prod : USt → Stk → List E → Done → Stk → E → List E → E → E → ProdSum
  prod_vars : ∀ s c1 ch fd c2 t vals ρ l, (prod s c1 ch fd c2 t vals ρ l).vars = V
  target : USt → Stk → List E → Done → Stk → E → List E → E → E → E
  batch_start : ∀ s c1 ch fd c2 t vals ρ l,
    (prod s c1 ch fd c2 t vals ρ l).T [] + target s c1 ch fd c2 t vals ρ l =
      powComb ((diffs s c1 ch fd c2 t vals).map fun d => powComb d ρ) l

/-! ## Reading an opened transcript -/

/-- Round `j` of an opened transcript. -/
def rd {M : Type} (q : Op M) (j : ℕ) : (Option M × List E) × List E := q.getD j ((none, []), [])

/-- Flock's transcript in an opened one: rounds `1 … nF`, their values and challenges. -/
def fdOf {M : Type} (nF : ℕ) (q : Op M) : Done :=
  ((q.drop 1).take nF).map fun x => ((none, x.1.2), x.2)

/-- The batching sumcheck's rounds in an opened one: from round `nF + 3` on. -/
def brOf {M : Type} (nF : ℕ) (q : Op M) : List (List E × List E) :=
  (q.drop (nF + 3)).map fun x => (x.1.2, x.2)

section Read

variable {M : Type}

theorem rd_append_lt (q l : Op M) (j : ℕ) (h : j < q.length) : rd (q ++ l) j = rd q j := by
  simp [rd, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rd_append_self (q : Op M) (x : (Option M × List E) × List E) : rd (q ++ [x]) q.length = x := by
  simp [rd, List.getD_eq_getElem?_getD]

theorem fdOf_append_le (nF : ℕ) (q : Op M) (x : (Option M × List E) × List E) (h1 : 1 ≤ q.length)
    (h2 : q.length ≤ nF) : fdOf nF (q ++ [x]) = fdOf nF q ++ [((none, x.1.2), x.2)] := by
  unfold fdOf
  rw [List.drop_append_of_le_length h1, List.take_of_length_le (by simp; omega),
    List.take_of_length_le (by simp; omega)]
  simp

theorem fdOf_append_gt (nF : ℕ) (q : Op M) (x : (Option M × List E) × List E)
    (h : nF + 1 ≤ q.length) : fdOf nF (q ++ [x]) = fdOf nF q := by
  unfold fdOf
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem fdOf_singleton (nF : ℕ) (x : (Option M × List E) × List E) : fdOf nF [x] = [] := by
  simp [fdOf]

theorem brOf_append (nF : ℕ) (q : Op M) (x : (Option M × List E) × List E)
    (h : nF + 3 ≤ q.length) : brOf nF (q ++ [x]) = brOf nF q ++ [(x.1.2, x.2)] := by
  unfold brOf
  rw [List.drop_append_of_le_length h]
  simp

theorem brOf_of_length (nF : ℕ) (q : Op M) (h : q.length ≤ nF + 3) : brOf nF q = [] := by
  simp [brOf, List.drop_eq_nil_of_le h]

theorem length_fdOf (nF : ℕ) (q : Op M) (h : q.length ≤ nF + 1) :
    (fdOf nF q).length = q.length - 1 := by
  simp [fdOf]
  omega

theorem length_brOf (nF : ℕ) (q : Op M) : (brOf nF q).length = q.length - (nF + 3) := by
  simp [brOf]

end Read

/-! ## The rounds' specifications -/

section Rounds

variable (Fr : List Compose.RoundSpec) (nV V : ℕ)

theorem length_uniRounds : (uniRounds Fr nV V).length = Fr.length + 3 + V := by
  simp [uniRounds]
  omega

theorem uniRounds_zero : (uniRounds Fr nV V).getD 0 ⟨false, 0, 0⟩ = ⟨true, 0, 5⟩ := rfl

theorem uniRounds_flock (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ Fr.length) :
    (uniRounds Fr nV V).getD j ⟨false, 0, 0⟩ = Fr.getD (j - 1) ⟨false, 0, 0⟩ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [uniRounds, List.getD_eq_getElem?_getD, Nat.add_sub_cancel]
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.getElem?_cons_succ,
    List.getElem?_append_left (by omega)]

theorem uniRounds_c2 : (uniRounds Fr nV V).getD (Fr.length + 1) ⟨false, 0, 0⟩ = ⟨true, 0, 0⟩ := by
  simp only [uniRounds, List.getD_eq_getElem?_getD]
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.getElem?_cons_succ,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem uniRounds_vals :
    (uniRounds Fr nV V).getD (Fr.length + 2) ⟨false, 0, 0⟩ = ⟨false, nV, 1⟩ := by
  simp only [uniRounds, List.getD_eq_getElem?_getD]
  rw [List.append_assoc, List.append_assoc, List.singleton_append,
    show Fr.length + 2 = (Fr.length + 1) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by omega), show Fr.length + 1 - Fr.length = 1 by omega]
  rfl

theorem uniRounds_batch (j : ℕ) (h1 : Fr.length + 3 ≤ j) (h2 : j < Fr.length + 3 + V) :
    (uniRounds Fr nV V).getD j ⟨false, 0, 0⟩ = ⟨false, 2, 0⟩ := by
  simp only [uniRounds, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [List.getElem?_replicate]
  split_ifs with h
  · rfl
  · omega

end Rounds

/-! ## The states -/

section States

variable {D : Deployment} {κ : ℕ} (Fl : FlockSound κ) (I : UniIds D Fl)

/-- **Flock's end**: its rounds completed, its pending reduction's claim its sum. -/
def FlockDone (fd : Done) : Prop :=
  DoneFits Fl.prog.rounds fd ∧ PendingHolds (Fl.prog.out fd []).2.2

/-- **The state after the completed rounds `q`** (`q` nonempty). -/
def uniS (s : USt) (q : Op Stk) : Prop :=
  ∃ c1, (rd q 0).1.1 = some c1 ∧
    if q.length ≤ Fl.prog.rounds.length + 1 then
      I.MainOK s c1 (rd q 0).2 ∧
        DoneFits (Fl.prog.rounds.take (q.length - 1)) (fdOf Fl.prog.rounds.length q) ∧
          Fl.S (I.qf c1) (fdOf Fl.prog.rounds.length q)
    else ∃ c2, (rd q (Fl.prog.rounds.length + 1)).1.1 = some c2 ∧
      FlockDone Fl (fdOf Fl.prog.rounds.length q) ∧
      if q.length = Fl.prog.rounds.length + 2 then
        ∃ vals, ∀ d ∈ I.diffs s c1 (rd q 0).2 (fdOf Fl.prog.rounds.length q) c2
          ((rd q (Fl.prog.rounds.length + 1)).2.headD 0) vals, ∀ x ∈ d, x = 0
      else
        SumState (I.prod s c1 (rd q 0).2 (fdOf Fl.prog.rounds.length q) c2
            ((rd q (Fl.prog.rounds.length + 1)).2.headD 0)
            (rd q (Fl.prog.rounds.length + 2)).1.2
            ((rd q (Fl.prog.rounds.length + 2)).2.headD 0)
            ((rd q (Fl.prog.rounds.length + 2)).2.getD 1 0)).oracle
          (I.target s c1 (rd q 0).2 (fdOf Fl.prog.rounds.length q) c2
            ((rd q (Fl.prog.rounds.length + 1)).2.headD 0)
            (rd q (Fl.prog.rounds.length + 2)).1.2
            ((rd q (Fl.prog.rounds.length + 2)).2.headD 0)
            ((rd q (Fl.prog.rounds.length + 2)).2.getD 1 0))
          (brOf Fl.prog.rounds.length q)

/-- **The state before a round's challenges**: before round `0`, the relation of `C1`'s candidate;
before `t`, the identities as polynomials for `C2`'s candidate and Flock's end; else the state
after the rounds before. -/
def uniPre (s : USt) (p : Op Stk) (m : Option Stk × List E) : Prop :=
  if p.length = 0 then ∃ c, m.1 = some c ∧ Rel D s c
  else if p.length = Fl.prog.rounds.length + 1 then
    ∃ c1 c2, (rd p 0).1.1 = some c1 ∧ m.1 = some c2 ∧
      (∀ P ∈ I.polys s c1 (rd p 0).2 c2, P = 0) ∧
      FlockEndHolds (I.qf c1) (Fl.prog.out (fdOf Fl.prog.rounds.length p) []) ∧
      FlockDone Fl (fdOf Fl.prog.rounds.length p)
  else uniS Fl I s p

/-- **The state after a round's challenges.** -/
def uniPost (s : USt) (p : Op Stk) (m : Option Stk × List E) (c : List E) : Prop :=
  uniS Fl I s (p ++ [(m, c)])

/-- **The rounds' errors.** -/
noncomputable def uniErr (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then I.errMain
  else if j ≤ Fl.prog.rounds.length then Fl.err (j - 1)
  else if j = Fl.prog.rounds.length + 1 then (I.degSum : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else if j = Fl.prog.rounds.length + 2 then
    ((I.nRel - 1 + (4 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else ((2 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

end States

end UniSound
