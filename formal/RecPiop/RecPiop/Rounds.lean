-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The round-by-round form is
-- `formal/Compose/Compose/ListChainK.lean`'s `Piop`, as `formal/UniSound/UniSound/Piop.lean` builds it
-- for the univariate PIOP; the counting of uniform draws is `formal/UniSound/UniSound/Prob.lean`'s,
-- for any field.
import RecPiop.Identity
import RecPiop.Fold
import Compose.ListChainK

/-!
# π2's PIOP, round by round

π2's rounds as the chain sees them (`pi2Rounds`; `PI2.md` §2, after §9's lever 2):

| round | message | challenges |
|---|---|---|
| `0` | `W`'s root | `α, β, γ` |
| `1` | `Q`'s root | `t` |
| `2` | the `2^r` fold values `a_k` and `ξ = κ(t) + βσ(t)` | `ρ` |

then the claims (no challenge follows): `W`'s fold at `ρ`, `Q`'s at `ρ'` (the identity at `t`
as one combination of `h(t)` and `q(t)`) and at the top coefficient (`Σ_V h`), the setup's at `β`.

**The candidates** (`Model`): a candidate of `W`'s root stands for the witness's polynomial `w`
(degree below `N`) and the true fold values `A_k(t)` at every `t`, with the verifier's cells from
them the row's cells `w(t + ω_c)` (`cells_fold`: the `B` basis, the tables' layer); a candidate of
`Q`'s root stands for `h` (below `N`) and `q` (below `4N`); the setup's polynomials `σ`, `κ` are
fixed (`L = 1`).

**The states** (`pre`, `post`, for a statement `s` with public limbs `pubOf s`):

* before round `0`: **the relation** of `W`'s candidate (`Rel`: `Satisfies`, the copy constraints
  and the public ports);
* after `α, β, γ`: **`CopyOK`** (some `h` meets the identity on `V_m` and sums to the target);
* before `t`: the public denominators nonzero, **the identity zero as a polynomial** for `Q`'s
  candidate, `Σ_V h` the target (`Pre1`);
* after `t`: the same with **the identity zero at `t`** (`Post1`);
* before `ρ`: the state after `t`;
* after `ρ`: **the claims hold** (`Post2`): `Σ_V h` the target, the setup's claim `ξ = κ(t) + βσ(t)`,
  `Q`'s claim (the identity at `t` with the verifier's `d_pull`, `d_push`, `1_S` from the fold
  values and `ξ`), and `W`'s fold at `ρ` (`foldAt`).

**The errors** (`err`, each proved, `piop`'s `sound`): round `0`
`(3N − 1 + Σ_j d_j)/|F|` (`Circuit.card_copyOK_le`), round `1` `(5N − 1)/|F|` (the identity's
degree, `Circuit.card_idPoly_eval_eq_zero_le`), round `2` `(2^r − 1)/|F|` (`W`'s fold,
`card_foldAt_eq_le`; with the fold values and `ξ` right, `Q`'s claim **is** the identity at `t`,
`qClaim_iff`). ListChainU multiplies round `j`'s by the candidate lists of the roots of rounds
`0..j`: `L_W`, `L_W L_Q`, `L_W L_Q`.

**`d_j`** (`hbind`, a hypothesis of `piop`): port `j`'s bad `γ` for limbs that differ;
`RecPiop.Ports` gives `0` (three limbs) and `1` (four limbs) for limbs in `K`.
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset Polynomial OracleComp
open scoped ENNReal

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-! ## Uniform draws by counting -/

section Draws

variable [Fintype F] [SampleableType F]

theorem draws_succ (n : ℕ) : Compose.draws F (n + 1) =
    ($ᵗ F : ProbComp F) >>= fun a => Compose.draws F n >>= fun l => pure (a :: l) := rfl

/-- **`n` uniform challenges by counting.** -/
theorem prEvent_draws_card : ∀ (n : ℕ) (P : List F → Prop) [DecidablePred P],
    Pr{let c ← Compose.draws F n}[P c] =
      ((univ.filter fun v : Fin n → F => P (List.ofFn v)).card : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) ^ n
  | 0, P, _ => by
    simp only [Compose.draws, pow_zero, div_one]
    rw [prEvent_pure]
    by_cases h : P []
    · simp only [h, ite_true]
      have : (univ.filter fun v : Fin 0 → F => P (List.ofFn v)) = univ :=
        filter_true_of_mem fun v _ => by simpa [List.ofFn_zero] using h
      rw [this, card_univ]
      simp
    · simp only [h, ite_false]
      have : (univ.filter fun v : Fin 0 → F => P (List.ofFn v)) = ∅ :=
        filter_false_of_mem fun v _ => by simpa [List.ofFn_zero] using h
      rw [this]
      simp
  | n + 1, P, _ => by
    classical
    rw [draws_succ]
    have e1 : Pr{let c ← (($ᵗ F : ProbComp F) >>= fun a => Compose.draws F n >>= fun l =>
        pure (a :: l))}[P c] =
        ∑ a : F, Pr{let x ← ($ᵗ F : ProbComp F)}[x = a] *
          Pr{let c ← (Compose.draws F n >>= fun l => pure (a :: l))}[P c] :=
      prEvent_bind_eq_sum_fintype _ _ _
    rw [e1]
    have e2 : ∀ a : F, Pr{let c ← (Compose.draws F n >>= fun l => pure (a :: l))}[P c] =
        ((univ.filter fun v : Fin n → F => P (a :: List.ofFn v)).card : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) ^ n := by
      intro a
      rw [← prEvent_draws_card n (fun l => P (a :: l))]
      simp only [bind_pure_comp, prEvent_map]
    simp only [e2, SampleableType.prEvent_uniformSample_eq_singleton]
    rw [← Finset.mul_sum, ← ENNReal.sum_div]
    have hc : ∑ a : F, ((univ.filter fun v : Fin n → F => P (a :: List.ofFn v)).card : ℝ≥0∞) =
        ((univ.filter fun v : Fin (n + 1) → F => P (List.ofFn v)).card : ℝ≥0∞) := by
      rw [← Nat.cast_sum]
      congr 1
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun x _ => Fin.cons x.1 x.2) (fun x hx => ?_) (fun x hx y hy h => ?_)
        (fun v hv => ?_)
      · simp only [mem_sigma, mem_univ, mem_filter, true_and] at hx ⊢
        rw [List.ofFn_succ]
        simpa using hx
      · obtain ⟨a, v⟩ := x
        obtain ⟨b, w⟩ := y
        simp only at h
        have h1 := congrFun h 0
        simp only [Fin.cons_zero] at h1
        subst h1
        have h2 : v = w := funext fun i => by simpa using congrFun h i.succ
        subst h2
        rfl
      · refine ⟨⟨v 0, Fin.tail v⟩, ?_, Fin.cons_self_tail v⟩
        simp only [mem_sigma, mem_univ, mem_filter, true_and] at hv ⊢
        rw [List.ofFn_succ] at hv
        exact hv
    rw [hc, pow_succ, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv
      (Or.inl (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))
      (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
    ring

/-- An event on `n + 1` challenges of at most `c · |F|^n` tuples has probability at most
`c / |F|`. -/
theorem prEvent_draws_le_of_card (n : ℕ) (P : List F → Prop) [DecidablePred P] (c : ℕ)
    (h : (univ.filter fun v : Fin (n + 1) → F => P (List.ofFn v)).card ≤ c * Fintype.card F ^ n) :
    Pr{let x ← Compose.draws F (n + 1)}[P x] ≤ (c : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [prEvent_draws_card]
  have hE : (Fintype.card F : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hEt : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ((univ.filter fun v : Fin (n + 1) → F => P (List.ofFn v)).card : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) ^ (n + 1)
      ≤ ((c * Fintype.card F ^ n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ (n + 1) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr h) _
    _ = (c : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_pow, pow_succ, mul_comm (c : ℝ≥0∞),
          ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ hE) (ENNReal.pow_ne_top hEt)]

theorem getD_ofFn {n : ℕ} (v : Fin n → F) (i : ℕ) (hi : i < n) :
    (List.ofFn v).getD i 0 = v ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Three challenges counted as triples. -/
theorem card_fin3_le (P : List F → Prop) [DecidablePred P] (Q : F × F × F → Prop)
    [DecidablePred Q] (h : ∀ v : Fin 3 → F, P (List.ofFn v) → Q (v 0, v 1, v 2)) :
    (univ.filter fun v : Fin 3 → F => P (List.ofFn v)).card ≤ (univ.filter Q).card := by
  refine Finset.card_le_card_of_injOn (fun v => (v 0, v 1, v 2)) (fun v hv => ?_)
    (fun v _ w _ hvw => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_univ _, h v hv.2⟩
  · simp only [Prod.mk.injEq] at hvw
    funext i
    fin_cases i
    · exact hvw.1
    · exact hvw.2.1
    · exact hvw.2.2

/-- One challenge counted as a point. -/
theorem card_fin1_le (P : List F → Prop) [DecidablePred P] (Q : F → Prop) [DecidablePred Q]
    (h : ∀ v : Fin 1 → F, P (List.ofFn v) → Q (v 0)) :
    (univ.filter fun v : Fin 1 → F => P (List.ofFn v)).card ≤ (univ.filter Q).card := by
  refine Finset.card_le_card_of_injOn (fun v => v 0) (fun v hv => ?_) (fun v _ w _ hvw => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_univ _, h v hv.2⟩
  · funext i
    fin_cases i
    exact hvw

end Draws

/-! ## The rounds, the candidates, the verifier at `t` -/

/-- **π2's rounds**: `W`'s root then `α, β, γ`; `Q`'s root then `t`; the `2^r` fold values and
`ξ`, then `ρ`. -/
def pi2Rounds (r : ℕ) : List Compose.RoundSpec :=
  [⟨true, 0, 2⟩, ⟨true, 0, 0⟩, ⟨false, 2 ^ r + 1, 0⟩]

/-- **The verifier's row cells at `t`** from the fold values: `v_x = Σ_k a_k eq(k, z)`,
`z_l = w_l(t) + ω_{x >> l}` (`PI2.md` §2 step 2; the sibling trick of §9 lever 3a computes the
same). -/
def cellsOf (r : ℕ) (ω : ℕ → F) (a : ℕ → F) (t : F) (x : ℕ) : F :=
  ∑ k ∈ range (2 ^ r), a k * ∏ l ∈ range r,
    (if k.testBit l then QuotientSecurity.sq^[l] t + ω (x >>> l)
      else 1 + (QuotientSecurity.sq^[l] t + ω (x >>> l)))

theorem cellsOf_congr (r : ℕ) (ω : ℕ → F) {a a' : ℕ → F} (h : ∀ k < 2 ^ r, a k = a' k)
    (t : F) (x : ℕ) : cellsOf r ω a t x = cellsOf r ω a' t x :=
  Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.mp hk)]

/-- **What the candidates stand for** (the tables' layer, a parameter): `W`'s candidate the
witness's polynomial and its fold values at every `t` (the verifier's cells from them are the
row's cells), `Q`'s candidate `h` and `q`, and the setup's polynomials. -/
structure Model (G : Circuit F) (ω : ℕ → F) (M : Type) where
  setup : SetupPolys G ω
  wP : M → F[X]
  wP_deg : ∀ c, (wP c).natDegree < G.N
  hP : M → F[X]
  hP_deg : ∀ c, (hP c).natDegree < G.N
  qP : M → F[X]
  qP_deg : ∀ c, (qP c).natDegree < 4 * G.N
  fold : M → F → ℕ → F
  cells_fold : ∀ c t x, x < G.W → cellsOf G.logW ω (fold c t) t x = (wP c).eval (t + ω x)

/-- The verifier's pull denominator at `t`: `α + v_0 + βt`. -/
def dPullAt (v : ℕ → F) (α β t : F) : F := α + v 0 + β * t

namespace Circuit

variable (G : Circuit F) (ω : ℕ → F)

/-- **The verifier's push denominator at `t`** from the cells and `ξ = κ(t) + βσ(t)`:
`α + v_0 + Σ_p I_p(t)·(E_p(v_{k_p ⊕ ·}) + v_0) + ξ`. -/
noncomputable def dPushAt (v : ℕ → F) (ξ α γ t : F) : F :=
  α + v 0 + ∑ p ∈ G.pairs, (G.ind ω p).eval t *
    ((G.regionRole p.1 p.2).value γ (v 0) (fun c => v (p.2 ^^^ c)) + v 0) + ξ

/-- **`Q`'s claim at `t`**, multiplied out: `c_h h(t) + c_q q(t) = (1 + 1_S) d_push + d_pull`,
`c_h = d_pull d_push`, `c_q = Z_V(t)`; the opening's normalised form
`(1 + ρ')h(t) + ρ'q(t) = X/(S_d Y)` at `ρ' = c_q/(c_h + c_q)` is this where `c_h + c_q ≠ 0`
(`qClaim_iff_normalised`). -/
def QClaim (v : ℕ → F) (ξ α β γ t ht qt : F) : Prop :=
  dPullAt v α β t * G.dPushAt ω v ξ α γ t * ht + (G.zV ω).eval t * qt =
    (1 + (G.holePoly ω).eval t) * G.dPushAt ω v ξ α γ t + dPullAt v α β t

variable {G ω} {n : ℕ}

theorem regionRole_reads_lt (hV : G.Valid) {p : Block × ℕ} (hp : p ∈ G.pairs) {c : ℕ}
    (hc : c ∈ (G.regionRole p.1 p.2).reads) : c < G.W := by
  rcases regionRole_mem hV (mem_pairs.mp hp).1 p.2 with ⟨r, hr, hm⟩ | hf
  · exact hV.reads_lt r hr _ hm c hc
  · rw [hf] at hc; simp [Role.reads] at hc

/-- **With the true cells and the true `ξ`, the verifier's push denominator is `d_push(t)`.** -/
theorem dPushAt_eq (hV : G.Valid) (hP : Points ω n) (S : SetupPolys G ω) (wP : F[X])
    (α β γ t ξ : F) {v : ℕ → F} (hv : ∀ x < G.W, v x = wP.eval (t + ω x))
    (hξ : ξ = S.κP.eval t + β * S.σP.eval t) :
    G.dPushAt ω v ξ α γ t = (G.dPushP ω S wP α β γ).eval t := by
  have hW : 0 < G.W := Nat.two_pow_pos _
  have hv0 : v 0 = wP.eval t := by rw [hv 0 hW, hP.zero, add_zero]
  unfold dPushAt dPushP pushPoly
  simp only [eval_add, eval_mul, eval_C, eval_finsetSum]
  have hs : ∀ p ∈ G.pairs, (G.ind ω p).eval t *
      ((G.regionRole p.1 p.2).value γ (v 0) (fun c => v (p.2 ^^^ c)) + v 0) =
      (G.ind ω p).eval t * ((G.formulaPoly ω wP γ p).eval t + wP.eval t) := by
    intro p hp
    rw [hv0]
    congr 2
    unfold formulaPoly
    rw [Role.value_eval]
    refine Role.value_congr _ γ (fun _ => rfl) fun c hc => ?_
    have hk := (mem_pairs.mp hp).2.1
    rw [hv _ (Nat.xor_lt_two_pow hk (regionRole_reads_lt hV hp hc))]
    simp [cellPoly, eval_comp]
  rw [Finset.sum_congr rfl hs, hξ, hv0]
  ring

/-- **With the true values, `Q`'s claim is the identity at `t`.** -/
theorem qClaim_iff (hV : G.Valid) (hP : Points ω n) (S : SetupPolys G ω) (wP hP' qP : F[X])
    (α β γ t ξ : F) {v : ℕ → F} (hv : ∀ x < G.W, v x = wP.eval (t + ω x))
    (hξ : ξ = S.κP.eval t + β * S.σP.eval t) :
    G.QClaim ω v ξ α β γ t (hP'.eval t) (qP.eval t) ↔
      (G.idPoly ω S wP hP' qP α β γ).eval t = 0 := by
  have hW : 0 < G.W := Nat.two_pow_pos _
  have hpull : dPullAt v α β t = (dPullP wP α β).eval t := by
    unfold dPullAt dPullP
    rw [hv 0 hW, hP.zero, add_zero]
    simp
  have key : (G.idPoly ω S wP hP' qP α β γ).eval t =
      (dPullAt v α β t * G.dPushAt ω v ξ α γ t * hP'.eval t + (G.zV ω).eval t * qP.eval t) +
        ((1 + (G.holePoly ω).eval t) * G.dPushAt ω v ξ α γ t + dPullAt v α β t) := by
    rw [hpull, dPushAt_eq hV hP S wP α β γ t ξ hv hξ]
    unfold idPoly
    simp only [eval_add, eval_mul, eval_one]
    ring
  unfold QClaim
  rw [key, CharTwo.add_eq_zero]

/-- **`Q`'s claim, normalised** (the opening's form): where `c_h + c_q ≠ 0`, the multiplied-out
claim is `(1 + ρ')h + ρ'q = RHS/(c_h + c_q)` at `ρ' = c_q/(c_h + c_q)`. -/
theorem qClaim_iff_normalised (v : ℕ → F) (ξ α β γ t ht qt : F)
    (hY : dPullAt v α β t * G.dPushAt ω v ξ α γ t + (G.zV ω).eval t ≠ 0) :
    G.QClaim ω v ξ α β γ t ht qt ↔
      (1 + (G.zV ω).eval t / (dPullAt v α β t * G.dPushAt ω v ξ α γ t + (G.zV ω).eval t)) * ht +
          (G.zV ω).eval t / (dPullAt v α β t * G.dPushAt ω v ξ α γ t + (G.zV ω).eval t) * qt =
        ((1 + (G.holePoly ω).eval t) * G.dPushAt ω v ξ α γ t + dPullAt v α β t) /
          (dPullAt v α β t * G.dPushAt ω v ξ α γ t + (G.zV ω).eval t) := by
  set ch := dPullAt v α β t * G.dPushAt ω v ξ α γ t
  set cq := (G.zV ω).eval t
  have e : 1 + cq / (ch + cq) = ch / (ch + cq) := by
    field_simp
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  unfold QClaim
  rw [e, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_left_inj' hY]

end Circuit

/-! ## The states -/

section States

variable {St M : Type} (G : Circuit F) (ω : ℕ → F) (Mo : Model G ω M) (pubOf : St → ℕ → List F)

/-- Round `j` of an opened transcript. -/
def rd (q : Compose.Opened M F) (j : ℕ) : (Option M × List F) × List F := q.getD j ((none, []), [])

theorem rd_append_lt (q l : Compose.Opened M F) (j : ℕ) (h : j < q.length) :
    rd (q ++ l) j = rd q j := by
  simp [rd, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rd_append_self (q : Compose.Opened M F) (x : (Option M × List F) × List F) :
    rd (q ++ [x]) q.length = x := by
  simp [rd, List.getD_eq_getElem?_getD]

/-- **The relation** of `W`'s candidate: its witness satisfies the circuit for the statement's
public limbs. -/
def Rel (s : St) (c : M) : Prop := G.Satisfies (pubOf s) (fun i => (Mo.wP c).eval (ω i))

/-- The public denominators at `(α, β, γ)` are nonzero. -/
def PubOK (s : St) (α β γ : F) : Prop := ∀ j < G.nP, G.dPub ω (pubOf s) α β γ j ≠ 0

/-- **`Σ_V h` is the target.** -/
def SumOK (s : St) (cQ : M) (α β γ : F) : Prop :=
  ∑ i ∈ range G.N, (Mo.hP cQ).eval (ω i) = G.target ω (pubOf s) α β γ

/-- The identity of the candidates. -/
noncomputable def idOf (cW cQ : M) (α β γ : F) : F[X] :=
  G.idPoly ω Mo.setup (Mo.wP cW) (Mo.hP cQ) (Mo.qP cQ) α β γ

/-- `(α, β, γ)` of round `0`'s challenges. -/
def abc (c : List F) : F × F × F := (c.getD 0 0, c.getD 1 0, c.getD 2 0)

/-- **The state after `α, β, γ`.** -/
def S0 (s : St) (cW : M) (c : List F) : Prop :=
  G.CopyOK ω (pubOf s) (fun i => (Mo.wP cW).eval (ω i)) (abc c).1 (abc c).2.1 (abc c).2.2

/-- **The state before `t`**: the identity zero as a polynomial. -/
def Pre1 (s : St) (cW : M) (c₀ : List F) (cQ : M) : Prop :=
  PubOK G ω pubOf s (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 ∧
    idOf G ω Mo cW cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 = 0 ∧
      SumOK G ω Mo pubOf s cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2

/-- **The state after `t`**: the identity zero at `t`. -/
def Post1 (s : St) (cW : M) (c₀ : List F) (cQ : M) (c₁ : List F) : Prop :=
  PubOK G ω pubOf s (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 ∧
    (idOf G ω Mo cW cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2).eval (c₁.getD 0 0) = 0 ∧
      SumOK G ω Mo pubOf s cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2

/-- The fold values of round `2`'s message. -/
def foldVals (vals : List F) : ℕ → F := fun k => vals.getD k 0

/-- `ξ` of round `2`'s message. -/
def xiOf (r : ℕ) (vals : List F) : F := vals.getD (2 ^ r) 0

/-- **The claims** (the state after `ρ`): `Σ_V h` the target, the setup's claim at `β`, `Q`'s claim
at `t`, `W`'s fold at `ρ`. -/
def Post2 (s : St) (cW : M) (c₀ : List F) (cQ : M) (c₁ vals c₂ : List F) : Prop :=
  PubOK G ω pubOf s (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 ∧
    SumOK G ω Mo pubOf s cQ (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 ∧
      xiOf G.logW vals = Mo.setup.κP.eval (c₁.getD 0 0) +
        (abc c₀).2.1 * Mo.setup.σP.eval (c₁.getD 0 0) ∧
      G.QClaim ω (cellsOf G.logW ω (foldVals vals) (c₁.getD 0 0)) (xiOf G.logW vals)
        (abc c₀).1 (abc c₀).2.1 (abc c₀).2.2 (c₁.getD 0 0)
        ((Mo.hP cQ).eval (c₁.getD 0 0)) ((Mo.qP cQ).eval (c₁.getD 0 0)) ∧
      foldAt G.logW (foldVals vals) (c₂.getD 0 0) =
        foldAt G.logW (Mo.fold cW (c₁.getD 0 0)) (c₂.getD 0 0)

/-- **The state before a round's challenges.** -/
def pre (s : St) (p : Compose.Opened M F) (m : Option M × List F) : Prop :=
  if p.length = 0 then ∃ c, m.1 = some c ∧ Rel G ω Mo pubOf s c
  else if p.length = 1 then
    ∃ cW cQ, (rd p 0).1.1 = some cW ∧ m.1 = some cQ ∧ Pre1 G ω Mo pubOf s cW (rd p 0).2 cQ
  else if p.length = 2 then
    ∃ cW cQ, (rd p 0).1.1 = some cW ∧ (rd p 1).1.1 = some cQ ∧
      Post1 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2
  else False

/-- **The state after a round's challenges.** -/
def post (s : St) (p : Compose.Opened M F) (m : Option M × List F) (c : List F) : Prop :=
  if p.length = 0 then ∃ cW, m.1 = some cW ∧ S0 G ω Mo pubOf s cW c
  else if p.length = 1 then
    ∃ cW cQ, (rd p 0).1.1 = some cW ∧ m.1 = some cQ ∧ Post1 G ω Mo pubOf s cW (rd p 0).2 cQ c
  else if p.length = 2 then
    ∃ cW cQ, (rd p 0).1.1 = some cW ∧ (rd p 1).1.1 = some cQ ∧
      Post2 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2 m.2 c
  else False

/-- **The rounds' errors.** -/
noncomputable def err [Fintype F] (d : ℕ → ℕ) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then ((3 * G.N - 1 + ∑ i ∈ range G.nP, d i : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
  else if j = 1 then ((5 * G.N - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
  else ((2 ^ G.logW - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)

end States

/-! ## The rounds' soundness -/

section Sound

variable {St M : Type} {G : Circuit F} {ω : ℕ → F} (Mo : Model G ω M) (pubOf : St → ℕ → List F)
variable {n : ℕ}

/-- **The next round's state implies this round's after** (`Compose.Piop.pre_post`). -/
theorem pre_post (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (s : St)
    (p : Compose.Opened M F) (m : Option M × List F) (c : List F) (m' : Option M × List F)
    (h : pre G ω Mo pubOf s (p ++ [(m, c)]) m') : post G ω Mo pubOf s p m c := by
  unfold pre at h
  unfold post
  rw [List.length_append, List.length_singleton] at h
  by_cases h0 : p.length = 0
  · rw [ite_eq_left h0]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)] at h
    obtain ⟨cW, cQ, hW, -, hpre⟩ := h
    have hp : p = [] := List.eq_nil_of_length_eq_zero h0
    subst hp
    have e : rd ([] ++ [(m, c)] : Compose.Opened M F) 0 = (m, c) := rfl
    rw [e] at hW hpre
    obtain ⟨hpub, hid, hsum⟩ := hpre
    exact ⟨cW, hW, Circuit.copyOK_of_idPoly hV hP hn Mo.setup (pubOf s) (Mo.wP cW) (Mo.hP cQ)
      (Mo.qP cQ) _ _ _ hid hsum hpub⟩
  · rw [ite_eq_right h0]
    by_cases h1 : p.length = 1
    · rw [ite_eq_left h1]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)] at h
      obtain ⟨cW, cQ, hW, hQ, hpost⟩ := h
      rw [rd_append_lt p _ 0 (by omega)] at hW hpost
      have e : rd (p ++ [(m, c)]) 1 = (m, c) := by rw [← h1]; exact rd_append_self p (m, c)
      rw [e] at hQ hpost
      exact ⟨cW, cQ, hW, hQ, hpost⟩
    · rw [ite_eq_right h1]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at h
      exact h.elim

variable [Fintype F] [SampleableType F]

/-- **Round `0`'s error**: `(3N − 1 + Σ_j d_j)/|F|` over `α, β, γ` (the copy argument). -/
theorem sound_zero (hV : G.Valid) (hP : Points ω n) (hn : G.logN + 1 ≤ n) (d : ℕ → ℕ)
    (hbind : ∀ s c, ∀ j < G.nP, G.limbVals (fun i => (Mo.wP c).eval (ω i)) j ≠ pubOf s j →
      (univ.filter fun γ : F => G.push (fun i => (Mo.wP c).eval (ω i)) γ (G.port j) =
        G.pubFp γ (pubOf s) j).card ≤ d j)
    (s : St) (m : Option M × List F) :
    Pr{let c ← Compose.draws F (2 + 1)}[¬ pre G ω Mo pubOf s [] m ∧ post G ω Mo pubOf s [] m c] ≤
      err G d 0 := by
  classical
  have hω : ∀ a < 2 * G.N, ∀ b < 2 * G.N, ω a = ω b → a = b := by
    have h2 : 2 * G.N ≤ 2 ^ n := by
      unfold Circuit.N
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) hn
    intro a ha b hb h
    exact hP.inj a (by omega) b (by omega) h
  unfold err
  rw [ite_eq_left rfl]
  refine prEvent_draws_le_of_card 2 _ _ ?_
  by_cases hpre : pre G ω Mo pubOf s [] m
  · rw [Finset.filter_false_of_mem fun v _ h => h.1 hpre]
    exact Nat.zero_le _
  cases hm : m.1 with
  | none =>
    rw [Finset.filter_false_of_mem fun v _ h => by
      have h2 := h.2
      unfold post at h2
      rw [ite_eq_left List.length_nil] at h2
      obtain ⟨cW, hW, -⟩ := h2
      rw [hm] at hW
      simp at hW]
    exact Nat.zero_le _
  | some cW =>
    have hns : ¬ Rel G ω Mo pubOf s cW := fun h' => hpre (by
      unfold pre
      rw [ite_eq_left List.length_nil]
      exact ⟨cW, hm, h'⟩)
    refine (card_fin3_le (fun c => ¬ pre G ω Mo pubOf s [] m ∧ post G ω Mo pubOf s [] m c)
      (fun v => G.CopyOK ω (pubOf s) (fun i => (Mo.wP cW).eval (ω i))
      v.1 v.2.1 v.2.2) fun v hv => ?_).trans
        (Circuit.card_copyOK_le ω hV hω (pubOf s) _ d (hbind s cW) hns)
    have h2 := hv.2
    unfold post at h2
    rw [ite_eq_left List.length_nil] at h2
    obtain ⟨cW', hW', hS⟩ := h2
    rw [hm] at hW'
    cases Option.some.inj hW'
    unfold S0 abc at hS
    rw [getD_ofFn v 0 (by norm_num), getD_ofFn v 1 (by norm_num), getD_ofFn v 2 (by norm_num)] at hS
    exact hS

/-- **Round `1`'s error**: `(5N − 1)/|F|` over `t` (the identity's degree). -/
theorem sound_one (hV : G.Valid) (d : ℕ → ℕ) (s : St) (p : Compose.Opened M F)
    (hp : p.length = 1) (m : Option M × List F) :
    Pr{let c ← Compose.draws F (0 + 1)}[¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c] ≤
      err G d 1 := by
  classical
  unfold err
  rw [ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_eq_left rfl]
  refine prEvent_draws_le_of_card 0 _ _ ?_
  rw [pow_zero, mul_one]
  have hpost : ∀ c, post G ω Mo pubOf s p m c ↔ ∃ cW cQ, (rd p 0).1.1 = some cW ∧
      m.1 = some cQ ∧ Post1 G ω Mo pubOf s cW (rd p 0).2 cQ c := by
    intro c
    unfold post
    rw [ite_eq_right (by omega), ite_eq_left hp]
  by_cases hex : ∃ cW cQ, (rd p 0).1.1 = some cW ∧ m.1 = some cQ
  · obtain ⟨cW, cQ, hW, hQ⟩ := hex
    by_cases hpre : pre G ω Mo pubOf s p m
    · rw [Finset.filter_false_of_mem fun v _ h => h.1 hpre]
      exact Nat.zero_le _
    have hnp : ¬ Pre1 G ω Mo pubOf s cW (rd p 0).2 cQ := fun h => hpre (by
      unfold pre
      rw [ite_eq_right (by omega), ite_eq_left hp]
      exact ⟨cW, cQ, hW, hQ, h⟩)
    refine (card_fin1_le (fun c => ¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c)
      (fun t => idOf G ω Mo cW cQ (abc (rd p 0).2).1 (abc (rd p 0).2).2.1 (abc (rd p 0).2).2.2 ≠ 0 ∧
      (idOf G ω Mo cW cQ (abc (rd p 0).2).1 (abc (rd p 0).2).2.1 (abc (rd p 0).2).2.2).eval t = 0)
      fun v hv => ?_).trans ?_
    · obtain ⟨cW', cQ', hW', hQ', h1⟩ := (hpost _).mp hv.2
      rw [hW] at hW'
      rw [hQ] at hQ'
      cases Option.some.inj hW'
      cases Option.some.inj hQ'
      obtain ⟨hpub, hev, hsum⟩ := h1
      refine ⟨fun h0 => hnp ⟨hpub, h0, hsum⟩, ?_⟩
      rw [getD_ofFn v 0 (by norm_num)] at hev
      exact hev
    · by_cases h0 :
          idOf G ω Mo cW cQ (abc (rd p 0).2).1 (abc (rd p 0).2).2.1 (abc (rd p 0).2).2.2 = 0
      · rw [Finset.filter_false_of_mem fun t _ h => h.1 h0]
        exact Nat.zero_le _
      · refine (Finset.card_le_card fun t ht => ?_).trans
          (Circuit.card_idPoly_eval_eq_zero_le hV Mo.setup (Mo.wP_deg cW) (Mo.hP_deg cQ)
            (Mo.qP_deg cQ) _ _ _ h0)
        rw [Finset.mem_filter] at ht ⊢
        exact ⟨ht.1, ht.2.2⟩
  · rw [Finset.filter_false_of_mem fun v _ h => hex (by
      obtain ⟨cW, cQ, hW, hQ, -⟩ := (hpost _).mp h.2
      exact ⟨cW, cQ, hW, hQ⟩)]
    exact Nat.zero_le _

/-- **Round `2`'s error**: `(2^r − 1)/|F|` over `ρ` (`W`'s fold; with the right fold values and
`ξ`, `Q`'s claim is the identity at `t`). -/
theorem sound_two (hV : G.Valid) (hP : Points ω n) (d : ℕ → ℕ) (s : St)
    (p : Compose.Opened M F) (hp : p.length = 2) (m : Option M × List F) :
    Pr{let c ← Compose.draws F (0 + 1)}[¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c] ≤
      err G d 2 := by
  classical
  unfold err
  rw [ite_eq_right (by decide : (2 : ℕ) ≠ 0), ite_eq_right (by decide : (2 : ℕ) ≠ 1)]
  refine prEvent_draws_le_of_card 0 _ _ ?_
  rw [pow_zero, mul_one]
  have hpost : ∀ c, post G ω Mo pubOf s p m c ↔ ∃ cW cQ, (rd p 0).1.1 = some cW ∧
      (rd p 1).1.1 = some cQ ∧ Post2 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2 m.2 c := by
    intro c
    unfold post
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hp]
  by_cases hex : ∃ cW cQ, (rd p 0).1.1 = some cW ∧ (rd p 1).1.1 = some cQ
  · obtain ⟨cW, cQ, hW, hQ⟩ := hex
    by_cases hpre : pre G ω Mo pubOf s p m
    · rw [Finset.filter_false_of_mem fun v _ h => h.1 hpre]
      exact Nat.zero_le _
    have hnp : ¬ Post1 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2 := fun h => hpre (by
      unfold pre
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hp]
      exact ⟨cW, cQ, hW, hQ, h⟩)
    have hclaims : ∀ c, post G ω Mo pubOf s p m c →
        Post2 G ω Mo pubOf s cW (rd p 0).2 cQ (rd p 1).2 m.2 c := by
      intro c h
      obtain ⟨cW', cQ', hW', hQ', h2⟩ := (hpost c).mp h
      rw [hW] at hW'
      rw [hQ] at hQ'
      cases Option.some.inj hW'
      cases Option.some.inj hQ'
      exact h2
    by_cases hfold : ∃ k < 2 ^ G.logW, foldVals m.2 k ≠ Mo.fold cW ((rd p 1).2.getD 0 0) k
    · refine (card_fin1_le (fun c => ¬ pre G ω Mo pubOf s p m ∧ post G ω Mo pubOf s p m c)
        (fun ρ => foldAt G.logW (foldVals m.2) ρ =
        foldAt G.logW (Mo.fold cW ((rd p 1).2.getD 0 0)) ρ) fun v hv => ?_).trans
          (card_foldAt_eq_le G.logW hfold)
      have h2 := (hclaims _ hv.2).2.2.2.2
      rw [getD_ofFn v 0 (by norm_num)] at h2
      exact h2
    · push Not at hfold
      rw [Finset.filter_false_of_mem fun v _ h => hnp (by
        obtain ⟨hpub, hsum, hξ, hq, -⟩ := hclaims _ h.2
        have hv : ∀ x < G.W, cellsOf G.logW ω (foldVals m.2) ((rd p 1).2.getD 0 0) x =
            (Mo.wP cW).eval ((rd p 1).2.getD 0 0 + ω x) := fun x hx => by
          rw [cellsOf_congr G.logW ω hfold _ x, Mo.cells_fold cW _ x hx]
        exact ⟨hpub, (Circuit.qClaim_iff hV hP Mo.setup (Mo.wP cW) (Mo.hP cQ) (Mo.qP cQ) _ _ _
          _ (xiOf G.logW m.2) hv hξ).mp hq, hsum⟩)]
      exact Nat.zero_le _
  · rw [Finset.filter_false_of_mem fun v _ h => hex (by
      obtain ⟨cW, cQ, hW, hQ, -⟩ := (hpost _).mp h.2
      exact ⟨cW, cQ, hW, hQ⟩)]
    exact Nat.zero_le _

/-- **π2's PIOP in `Compose.Piop`'s form**, for any chain whose rounds are π2's: the states
`pre`, `post`, the errors `err` (round `0` `(3N − 1 + Σ_j d_j)/|F|`, round `1` `(5N − 1)/|F|`,
round `2` `(2^r − 1)/|F|`), each proved. The hypotheses: a valid circuit, points injective on
`[0, 2N)` (`n ≥ log N + 1`), and the ports' binding `d_j` (`RecPiop.Ports`). -/
noncomputable def piop (K : Compose.ChainSpec F St) (hK : K.rounds = pi2Rounds G.logW)
    (hV : G.Valid) (hP : Points ω n) (hn : G.logN + 1 ≤ n) (d : ℕ → ℕ)
    (hbind : ∀ s c, ∀ j < G.nP, G.limbVals (fun i => (Mo.wP c).eval (ω i)) j ≠ pubOf s j →
      (univ.filter fun γ : F => G.push (fun i => (Mo.wP c).eval (ω i)) γ (G.port j) =
        G.pubFp γ (pubOf s) j).card ≤ d j) :
    Compose.Piop K M where
  pre := pre G ω Mo pubOf
  post := post G ω Mo pubOf
  pre_post := pre_post Mo pubOf hV hP (by omega)
  err := err G d
  sound j s p m hj hp := by
    have hlen : K.rounds.length = 3 := by rw [hK]; rfl
    rw [hlen] at hj
    interval_cases j
    · have hs : (K.spec 0).ns = 2 := by simp [Compose.ChainSpec.spec, hK, pi2Rounds]
      rw [hs, List.eq_nil_of_length_eq_zero hp]
      exact sound_zero Mo pubOf hV hP hn d hbind s m
    · have hs : (K.spec 1).ns = 0 := by simp [Compose.ChainSpec.spec, hK, pi2Rounds]
      rw [hs]
      exact sound_one Mo pubOf hV d s p hp m
    · have hs : (K.spec 2).ns = 0 := by simp [Compose.ChainSpec.spec, hK, pi2Rounds]
      rw [hs]
      exact sound_two Mo pubOf hV hP d s p hp m

end Sound

end RecPiop
