-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The split of the bad challenges (a
-- vanishing denominator, the log-derivative sum, the fingerprints in `γ`) follows
-- `formal/QuotientSecurity/Counting.lean` (crates/quotient's copy argument).
import RecPiop.Circuit
import RecPiop.LogUp

/-!
# π2's copy argument

`PI2.md` §1: on `V_m`, `h = (1 + 1_S)/(α + w + βx) + 1/(α + P + βσ)`, and `Σ_V h = Σ_j 1/(α + F_j +
βτ_j)`; the holes (`1_S = 1`) pull nothing. As a family of (value, tag) pairs (`entries`,
`entryVal`): a **pull** `(w_i, ω_i)` at every non-hole, a **push** `(P_i, ω_{σ_i})` at every
position, a **public term** `(F_j, ω_{N+j})` at every port, `2N` in all (`card_entries_le`).

* **Every tag twice** (`copy_of_even`): with `ω` injective on `[0, 2N)` and the layout valid, a tag
  `ω_j` of a non-hole is one pull and one push (`σ` a bijection onto the non-holes), an outside tag
  `ω_{N+j}` one push and one public term (`σ (port j) = N + j`), a hole's tag nothing. So if the
  family is zero mod 2 (`EvenAll`: the log-derivative sum is zero as a rational function of
  `(α, β)`, `cleared_eq_zero_iff`), every non-hole's pull is the push meant for it and every port's
  push is its public fingerprint (`eq_of_even_of_pair`).
* **The identities give the sum** (`logSum_of_copyOK`): the verifier's state after `α, β, γ`
  (`CopyOK`: the public denominators nonzero, and some values `h_i` meeting the identity
  `h d_pull d_push + (1 + 1_S) d_push + d_pull = 0` at every position and summing to the target),
  where no pull's denominator vanishes, makes every denominator nonzero and the family's
  log-derivative sum zero. At a hole the identity is `d_pull (h d_push + 1) = 0`: the hole's pull
  is out of the sum (REVIEW-REC.md N1's vanishing case is a pull's denominator zero, counted).
* **`card_copyOK_le`**: if the witness does not satisfy the circuit, at most
  `(3N − 1 + Σ_j d_j)·|F|²` triples `(α, β, γ)` reach `CopyOK`: `N |F|²` where a pull's denominator
  vanishes, `(2N − 1) |F|²` where the family is odd mod 2 but its sum zero (logUp,
  `card_logSum_eq_zero_le`, for each `γ`), and `d_j |F|²` where port `j`'s limbs differ from the
  public ones but their fingerprints agree at `γ` (`hbind`; `d_j = 0` for the element ports,
  `1` for the four-limb ones, `RecPiop.Ports`). **`prob_copyOK_le`**: at a uniform `(α, β, γ)`,
  probability at most `(3N − 1 + Σ_j d_j)/|F|`.
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset

/-- **An entry of the copy argument**: a pull, a push, or a public term. -/
inductive Entry where
  | pull (i : ℕ)
  | push (i : ℕ)
  | pub (j : ℕ)
deriving DecidableEq

namespace Circuit

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F] (G : Circuit F)

/-! ## The family -/

/-- **The copy argument's entries**: a pull at every non-hole, a push at every position, a public
term at every port. -/
def entries : Finset Entry :=
  ((range G.N).filter fun i => ¬ G.IsHole i).image Entry.pull ∪
    ((range G.N).image Entry.push ∪ (range G.nP).image Entry.pub)

/-- **An entry's (value, tag) pair**, the tags the points `ω`. -/
def entryVal (ω : ℕ → F) (pub : ℕ → List F) (w : ℕ → F) (γ : F) : Entry → F × F
  | .pull i => (w i, ω i)
  | .push i => (G.push w γ i, ω (G.sigma i))
  | .pub j => (G.pubFp γ pub j, ω (G.N + j))

theorem mem_entries (z : Entry) : z ∈ G.entries ↔
    (∃ i < G.N, ¬ G.IsHole i ∧ z = .pull i) ∨ (∃ i < G.N, z = .push i) ∨
      (∃ j < G.nP, z = .pub j) := by
  simp only [entries, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (⟨i, ⟨hi, hh⟩, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, hh, rfl⟩
    · exact Or.inr (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
  · rintro (⟨i, hi, hh, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, ⟨hi, hh⟩, rfl⟩
    · exact Or.inr (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)

variable {G}

/-! ## Ports and holes -/

theorem port_eq_getElem {j : ℕ} (hj : j < G.nP) : G.port j = G.ports[j] := by
  unfold port
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem port_lt (hV : G.Valid) {j : ℕ} (hj : j < G.nP) : G.port j < G.N ∧ G.IsHole (G.port j) := by
  rw [port_eq_getElem hj]
  exact (hV.ports_holes _).mp (List.getElem_mem _)

theorem port_inj (hV : G.Valid) {j j' : ℕ} (hj : j < G.nP) (hj' : j' < G.nP)
    (h : G.port j = G.port j') : j = j' := by
  rw [port_eq_getElem hj, port_eq_getElem hj'] at h
  exact (hV.ports_nodup.getElem_inj_iff).mp h

theorem exists_port_of_hole (hV : G.Valid) {i : ℕ} (hi : i < G.N) (hh : G.IsHole i) :
    ∃ j < G.nP, G.port j = i := by
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem ((hV.ports_holes i).mpr ⟨hi, hh⟩)
  exact ⟨j, hj, by rw [port_eq_getElem hj, he]⟩

/-- **There are as many holes as ports.** -/
theorem card_holes (hV : G.Valid) : ((range G.N).filter G.IsHole).card = G.nP := by
  have : (range G.N).filter G.IsHole = G.ports.toFinset := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, hV.ports_holes]
  rw [this, List.toFinset_card_of_nodup hV.ports_nodup]
  rfl

theorem nP_le (hV : G.Valid) : G.nP ≤ G.N := by
  rw [← card_holes hV]
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

theorem N_pos : 0 < G.N := Nat.two_pow_pos _

theorem sigma_lt (hV : G.Valid) {i : ℕ} (hi : i < G.N) : G.sigma i < 2 * G.N := by
  by_cases hh : G.IsHole i
  · obtain ⟨j, hj, rfl⟩ := exists_port_of_hole hV hi hh
    rw [hV.sigma_port j hj]
    have := nP_le hV
    omega
  · have := (hV.sigma_inside i hi hh).1
    omega

/-- **The family has `2N` entries**: `N − nP` pulls, `N` pushes, `nP` public terms. -/
theorem card_entries_le (hV : G.Valid) : G.entries.card ≤ 2 * G.N := by
  have hA : (((range G.N).filter fun i => ¬ G.IsHole i).image Entry.pull).card ≤ G.N - G.nP := by
    refine Finset.card_image_le.trans (le_of_eq ?_)
    have := Finset.card_filter_add_card_filter_not (s := range G.N) G.IsHole
    rw [card_holes hV, Finset.card_range] at this
    omega
  have hB : ((range G.N).image Entry.push).card ≤ G.N :=
    Finset.card_image_le.trans (Finset.card_range _).le
  have hC : ((range G.nP).image Entry.pub).card ≤ G.nP :=
    Finset.card_image_le.trans (Finset.card_range _).le
  have hP := nP_le hV
  unfold entries
  refine (Finset.card_union_le _ _).trans ?_
  have := Finset.card_union_le ((range G.N).image Entry.push) ((range G.nP).image Entry.pub)
  omega

/-! ## Every tag twice -/

variable (ω : ℕ → F)

/-- **The copy argument's conclusion from the family zero mod 2**: every non-hole's pull is the
push meant for it, and every port's push is its public fingerprint. -/
theorem copy_of_even (hV : G.Valid) (hω : ∀ a < 2 * G.N, ∀ b < 2 * G.N, ω a = ω b → a = b)
    (pub : ℕ → List F) (w : ℕ → F) (γ : F) (hev : EvenAll G.entries (G.entryVal ω pub w γ)) :
    (∀ i < G.N, ¬ G.IsHole i → w (G.sigma i) = G.push w γ i) ∧
      ∀ j < G.nP, G.push w γ (G.port j) = G.pubFp γ pub j := by
  have hP := nP_le hV
  constructor
  · intro i hi hh
    obtain ⟨hj, hjh⟩ := hV.sigma_inside i hi hh
    have hx : Entry.pull (G.sigma i) ∈ G.entries :=
      (mem_entries G _).mpr (Or.inl ⟨_, hj, hjh, rfl⟩)
    have h := eq_of_even_of_pair G.entries (G.entryVal ω pub w γ) hev (y := Entry.push i) hx
      (fun z hz ht => by
        rcases (mem_entries G z).mp hz with ⟨a, ha, -, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · exact Or.inl (by rw [hω a (by omega) _ (by omega) ht])
        · have := hω _ (sigma_lt hV ha) _ (by omega) ht
          exact Or.inr (by rw [hV.sigma_inj a ha i hi this])
        · have := hω _ (by omega) _ (by omega) ht
          omega)
    simp only [entryVal, Prod.mk.injEq] at h
    exact h.1
  · intro j hj
    obtain ⟨hpj, hph⟩ := port_lt hV hj
    have hx : Entry.push (G.port j) ∈ G.entries := (mem_entries G _).mpr (Or.inr (Or.inl ⟨_, hpj, rfl⟩))
    have h := eq_of_even_of_pair G.entries (G.entryVal ω pub w γ) hev (y := Entry.pub j) hx
      (fun z hz ht => by
        simp only [entryVal, hV.sigma_port j hj] at ht
        rcases (mem_entries G z).mp hz with ⟨a, ha, -, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · have := hω a (by omega) _ (by omega) ht
          omega
        · have hs := hω _ (sigma_lt hV ha) _ (by omega) ht
          by_cases hah : G.IsHole a
          · obtain ⟨j', hj', rfl⟩ := exists_port_of_hole hV ha hah
            rw [hV.sigma_port j' hj'] at hs
            exact Or.inl (by rw [show j' = j by omega])
          · have := (hV.sigma_inside a ha hah).1
            omega
        · have := hω _ (by omega) _ (by omega) ht
          exact Or.inr (by rw [show b = j by omega]))
    simp only [entryVal, Prod.mk.injEq] at h
    exact h.1

/-- **The copy argument, deterministic**: if the log-derivative sum of the family is zero as a
rational function of `(α, β)` (its cleared numerator vanishes), every non-hole's pull is the push
meant for it and every port's push is its public fingerprint. -/
theorem copy_of_cleared_eq_zero (hV : G.Valid)
    (hω : ∀ a < 2 * G.N, ∀ b < 2 * G.N, ω a = ω b → a = b) (pub : ℕ → List F) (w : ℕ → F) (γ : F)
    (h : cleared (oddPairs G.entries (G.entryVal ω pub w γ)) = 0) :
    (∀ i < G.N, ¬ G.IsHole i → w (G.sigma i) = G.push w γ i) ∧
      ∀ j < G.nP, G.push w γ (G.port j) = G.pubFp γ pub j :=
  copy_of_even ω hV hω pub w γ ((cleared_eq_zero_iff _ _).mp h)

/-! ## The identities give the sum -/

variable (G)

/-- A pull's denominator `α + w_i + β ω_i`. -/
def _root_.RecPiop.dPull (w : ℕ → F) (α β : F) (i : ℕ) : F := den α β (w i, ω i)

/-- A push's denominator `α + P_i + β ω_{σ_i}`. -/
def dPush (w : ℕ → F) (α β γ : F) (i : ℕ) : F := den α β (G.push w γ i, ω (G.sigma i))

/-- A public term's denominator `α + F_j + β ω_{N+j}`. -/
def dPub (pub : ℕ → List F) (α β γ : F) (j : ℕ) : F := den α β (G.pubFp γ pub j, ω (G.N + j))

/-- **The public target** `T = Σ_j 1/(α + F_j + β ω_{N+j})`. -/
def target (pub : ℕ → List F) (α β γ : F) : F :=
  ∑ j ∈ range G.nP, (G.dPub ω pub α β γ j)⁻¹

/-- **The holes' indicator** `1_S` on positions. -/
def holeInd (i : ℕ) : F := if G.IsHole i then 1 else 0

/-- **The identity at position `i`**, for a value `h_i` of `h`:
`h d_pull d_push + (1 + 1_S) d_push + d_pull = 0` (`q Z_V` vanishes on `V_m`). -/
def PointId (w : ℕ → F) (α β γ hv : F) (i : ℕ) : Prop :=
  hv * dPull ω w α β i * G.dPush ω w α β γ i + (1 + G.holeInd i) * G.dPush ω w α β γ i +
    dPull ω w α β i = 0

/-- **The state after `α, β, γ`**: the public denominators nonzero (the verifier inverts their
product), and some values of `h` on `V_m` meet the identity at every position and sum to the
target. -/
structure CopyOK (pub : ℕ → List F) (w : ℕ → F) (α β γ : F) : Prop where
  pub_ne : ∀ j < G.nP, G.dPub ω pub α β γ j ≠ 0
  sums : ∃ hv : ℕ → F, (∀ i < G.N, G.PointId ω w α β γ (hv i) i) ∧
    ∑ i ∈ range G.N, hv i = G.target ω pub α β γ

variable {G}

/-- **The identity at a position, solved**: where the pull's denominator is not zero, the push's is
not either, and `h_i = 1/d_pull + 1/d_push` (a non-hole) or `1/d_push` (a hole). -/
theorem hv_eq {w : ℕ → F} {α β γ hv : F} {i : ℕ} (h : G.PointId ω w α β γ hv i)
    (hp : dPull ω w α β i ≠ 0) :
    G.dPush ω w α β γ i ≠ 0 ∧
      hv = (if G.IsHole i then 0 else (dPull ω w α β i)⁻¹) + (G.dPush ω w α β γ i)⁻¹ := by
  unfold PointId holeInd at h
  set a := dPull ω w α β i
  set b := G.dPush ω w α β γ i
  by_cases hh : G.IsHole i
  · simp only [hh, ite_true] at h ⊢
    rw [CharTwo.add_self_eq_zero, zero_mul, add_zero] at h
    have h1 : a * (hv * b + 1) = 0 := by rw [← h]; ring
    have h2 : hv * b = 1 := CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hp)
    have hb : b ≠ 0 := fun h0 => by rw [h0, mul_zero] at h2; exact zero_ne_one h2
    refine ⟨hb, ?_⟩
    rw [zero_add]
    field_simp
    exact h2
  · simp only [hh, ite_false] at h ⊢
    rw [add_zero, one_mul] at h
    have h1 : hv * a * b = b + a := CharTwo.add_eq_zero.mp (by rw [← h]; ring)
    have hb : b ≠ 0 := fun h0 => by
      rw [h0, mul_zero, zero_add] at h1
      exact hp h1.symm
    refine ⟨hb, ?_⟩
    field_simp
    linear_combination h1

/-- **The identities give the log-derivative sum.** In the state after `α, β, γ`, if no pull's
denominator vanishes, every denominator of the family is nonzero and its log-derivative sum is
zero. -/
theorem logSum_of_copyOK {pub : ℕ → List F} {w : ℕ → F} {α β γ : F} (h : G.CopyOK ω pub w α β γ)
    (hpull : ∀ i < G.N, dPull ω w α β i ≠ 0) :
    (∀ x ∈ G.entries, den α β (G.entryVal ω pub w γ x) ≠ 0) ∧
      logSum G.entries (G.entryVal ω pub w γ) α β = 0 := by
  obtain ⟨hv, hid, hsum⟩ := h.sums
  have hsol := fun i (hi : i < G.N) => hv_eq ω (hid i hi) (hpull i hi)
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases (mem_entries G x).mp hx with ⟨i, hi, -, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · exact hpull i hi
    · exact (hsol i hi).1
    · exact h.pub_ne j hj
  · have hd1 : Disjoint (((range G.N).filter fun i => ¬ G.IsHole i).image Entry.pull)
        ((range G.N).image Entry.push ∪ (range G.nP).image Entry.pub) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      rcases Finset.mem_union.mp hz' with h' | h' <;>
        · obtain ⟨_, -, he⟩ := Finset.mem_image.mp h'
          cases he
    have hd2 : Disjoint ((range G.N).image Entry.push) ((range G.nP).image Entry.pub) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨_, -, he⟩ := Finset.mem_image.mp hz'
      cases he
    unfold logSum entries
    rw [Finset.sum_union hd1, Finset.sum_union hd2,
      Finset.sum_image (fun a _ b _ h => Entry.pull.inj h),
      Finset.sum_image (fun a _ b _ h => Entry.push.inj h),
      Finset.sum_image (fun a _ b _ h => Entry.pub.inj h)]
    have hT : ∑ j ∈ range G.nP, (den α β (G.entryVal ω pub w γ (Entry.pub j)))⁻¹ =
        G.target ω pub α β γ := rfl
    rw [hT, ← hsum]
    have hh : ∑ i ∈ range G.N, hv i =
        ∑ i ∈ (range G.N).filter (fun i => ¬ G.IsHole i), (dPull ω w α β i)⁻¹ +
          ∑ i ∈ range G.N, (G.dPush ω w α β γ i)⁻¹ := by
      rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hsol i (Finset.mem_range.mp hi)).2]
      by_cases hh : G.IsHole i <;> simp [hh]
    rw [hh, ← add_assoc]
    exact CharTwo.add_self_eq_zero _

/-! ## Counting the bad challenges -/

variable [Fintype F]

omit [CharP F 2] [DecidableEq F] in
/-- Triples counted by their last coordinate. -/
theorem card_triple_le (P : F × F × F → Prop) [DecidablePred P] (c : ℕ)
    (h : ∀ γ : F, (univ.filter fun ab : F × F => P (ab.1, ab.2, γ)).card ≤ c) :
    (univ.filter P).card ≤ c * Fintype.card F := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v : F × F × F => v.2.2) (t := univ)
    fun _ _ => Finset.mem_univ _]
  calc ∑ γ : F, ((univ.filter P).filter fun v => v.2.2 = γ).card ≤ ∑ _γ : F, c := by
        refine Finset.sum_le_sum fun γ _ => ?_
        have hsub : ((univ.filter P).filter fun v => v.2.2 = γ) ⊆
            (univ.filter fun ab : F × F => P (ab.1, ab.2, γ)).image fun ab => (ab.1, ab.2, γ) := by
          intro v hv
          rw [Finset.mem_filter, Finset.mem_filter] at hv
          refine Finset.mem_image.mpr ⟨(v.1, v.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
            ?_⟩
          · rw [← hv.2]; exact hv.1.2
          · rw [← hv.2]
        exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (h γ))
    _ = c * Fintype.card F := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

omit [CharP F 2] [DecidableEq F] in
/-- An event on the last coordinate of a triple. -/
theorem card_filter_last (Q : F → Prop) [DecidablePred Q] :
    (univ.filter fun v : F × F × F => Q v.2.2).card = (univ.filter Q).card * Fintype.card F ^ 2 := by
  have : (univ.filter fun v : F × F × F => Q v.2.2) = univ ×ˢ (univ ×ˢ univ.filter Q) := by
    ext v
    simp
  rw [this, Finset.card_product, Finset.card_product, Finset.card_univ]
  ring

/-- A pull's denominator vanishes at `|F|²` triples. -/
theorem card_dPull_eq_zero_le (w : ℕ → F) (i : ℕ) :
    (univ.filter fun v : F × F × F => dPull ω w v.1 v.2.1 i = 0).card ≤ Fintype.card F ^ 2 := by
  classical
  refine (Finset.card_le_card (t := univ.image fun p : F × F => (w i + p.1 * ω i, p.1, p.2))
    fun v hv => ?_).trans (Finset.card_image_le.trans (by simp [sq]))
  rw [Finset.mem_filter] at hv
  refine Finset.mem_image.mpr ⟨(v.2.1, v.2.2), Finset.mem_univ _, ?_⟩
  have h := hv.2
  unfold dPull den at h
  have : v.1 = w i + v.2.1 * ω i := CharTwo.add_eq_zero.mp (by rw [← h]; ring)
  rw [← this]

open Classical in
/-- **The copy argument's soundness, counting form.** If the witness `w` does not satisfy the
circuit for the public limbs `pub`, at most `(3N − 1 + Σ_j d_j)·|F|²` triples `(α, β, γ)` reach the
state `CopyOK`, `d_j` bounding the `γ` at which port `j`'s fingerprints of different limbs agree
(`hbind`). -/
theorem card_copyOK_le (hV : G.Valid) (hω : ∀ a < 2 * G.N, ∀ b < 2 * G.N, ω a = ω b → a = b)
    (pub : ℕ → List F) (w : ℕ → F) (d : ℕ → ℕ)
    (hbind : ∀ j < G.nP, G.limbVals w j ≠ pub j →
      (univ.filter fun γ : F => G.push w γ (G.port j) = G.pubFp γ pub j).card ≤ d j)
    (hns : ¬ G.Satisfies pub w) :
    (univ.filter fun v : F × F × F => G.CopyOK ω pub w v.1 v.2.1 v.2.2).card ≤
      (3 * G.N - 1 + ∑ j ∈ range G.nP, d j) * Fintype.card F ^ 2 := by
  set A := univ.filter fun v : F × F × F => ∃ i < G.N, dPull ω w v.1 v.2.1 i = 0
  set B := univ.filter fun v : F × F × F => ¬ EvenAll G.entries (G.entryVal ω pub w v.2.2) ∧
    (∀ x ∈ G.entries, den v.1 v.2.1 (G.entryVal ω pub w v.2.2 x) ≠ 0) ∧
      logSum G.entries (G.entryVal ω pub w v.2.2) v.1 v.2.1 = 0
  set Cj := fun j => univ.filter fun v : F × F × F =>
    G.limbVals w j ≠ pub j ∧ G.push w v.2.2 (G.port j) = G.pubFp v.2.2 pub j
  -- The bad triples are in `A ∪ B ∪ ⋃ Cj`.
  have hsub : (univ.filter fun v : F × F × F => G.CopyOK ω pub w v.1 v.2.1 v.2.2) ⊆
      A ∪ (B ∪ (range G.nP).biUnion Cj) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    by_cases hA : ∃ i < G.N, dPull ω w v.1 v.2.1 i = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)
    push Not at hA
    obtain ⟨hden, hlog⟩ := logSum_of_copyOK ω hv.2 hA
    by_cases hE : EvenAll G.entries (G.entryVal ω pub w v.2.2)
    · obtain ⟨hcopy, hports⟩ := copy_of_even ω hV hω pub w v.2.2 hE
      refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
      by_contra hC
      apply hns
      refine ⟨fun i hi hh => by rw [hcopy i hi hh, G.push_gamma w hh], fun j hj => ?_⟩
      by_contra hne
      exact hC (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hports j hj⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE, hden, hlog⟩))
  -- The three counts.
  have hAc : A.card ≤ G.N * Fintype.card F ^ 2 := by
    have : A ⊆ (range G.N).biUnion fun i =>
        univ.filter fun v : F × F × F => dPull ω w v.1 v.2.1 i = 0 := by
      intro v hv
      obtain ⟨i, hi, h0⟩ := (Finset.mem_filter.mp hv).2
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h0⟩⟩
    refine (Finset.card_le_card this).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ i ∈ range G.N, (univ.filter fun v : F × F × F => dPull ω w v.1 v.2.1 i = 0).card
        ≤ ∑ _i ∈ range G.N, Fintype.card F ^ 2 :=
          Finset.sum_le_sum fun i _ => card_dPull_eq_zero_le ω w i
      _ = G.N * Fintype.card F ^ 2 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hBc : B.card ≤ (2 * G.N - 1) * Fintype.card F ^ 2 := by
    refine (card_triple_le _ ((2 * G.N - 1) * Fintype.card F) fun γ => ?_).trans (le_of_eq ?_)
    · by_cases hE : EvenAll G.entries (G.entryVal ω pub w γ)
      · rw [Finset.filter_false_of_mem fun ab _ h => h.1 hE, Finset.card_empty]
        exact Nat.zero_le _
      · refine (Finset.card_le_card fun ab hab => ?_).trans
          ((card_logSum_eq_zero_le G.entries (G.entryVal ω pub w γ) hE).trans
            (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (card_entries_le hV) 1)))
        rw [Finset.mem_filter] at hab ⊢
        exact ⟨hab.1, hab.2.2⟩
    · ring
  have hCc : ((range G.nP).biUnion Cj).card ≤ (∑ j ∈ range G.nP, d j) * Fintype.card F ^ 2 := by
    refine Finset.card_biUnion_le.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hne : G.limbVals w j ≠ pub j
    · have : Cj j = univ.filter fun v : F × F × F =>
          G.push w v.2.2 (G.port j) = G.pubFp v.2.2 pub j := by
        ext v
        simp [Cj, hne]
      rw [this]
      refine le_of_eq_of_le
        (card_filter_last (fun γ => G.push w γ (G.port j) = G.pubFp γ pub j)) ?_
      exact Nat.mul_le_mul_right _ (hbind j (Finset.mem_range.mp hj) hne)
    · have : Cj j = ∅ := Finset.filter_false_of_mem fun v _ h => hne h.1
      rw [this, Finset.card_empty]
      exact Nat.zero_le _
  have hN := N_pos (G := G)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  refine (Nat.add_le_add hAc ((Finset.card_union_le _ _).trans (Nat.add_le_add hBc hCc))).trans
    (le_of_eq ?_)
  rw [← add_mul, ← add_mul, ← add_assoc]
  congr 1
  omega

open Classical OracleComp in
/-- **The copy argument's soundness.** If the witness does not satisfy the circuit, a uniform
`(α, β, γ)` reaches `CopyOK` with probability at most `(3N − 1 + Σ_j d_j)/|F|`. -/
theorem prob_copyOK_le [SampleableType F] (hV : G.Valid)
    (hω : ∀ a < 2 * G.N, ∀ b < 2 * G.N, ω a = ω b → a = b)
    (pub : ℕ → List F) (w : ℕ → F) (d : ℕ → ℕ)
    (hbind : ∀ j < G.nP, G.limbVals w j ≠ pub j →
      (univ.filter fun γ : F => G.push w γ (G.port j) = G.pubFp γ pub j).card ≤ d j)
    (hns : ¬ G.Satisfies pub w) :
    Pr{let v ← $ᵗ (F × F × F)}[G.CopyOK ω pub w v.1 v.2.1 v.2.2] ≤
      ((3 * G.N - 1 + ∑ j ∈ range G.nP, d j : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample, Fintype.card_prod, Fintype.card_prod]
  have hF : (Fintype.card F : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hFt : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ((univ.filter fun v : F × F × F => G.CopyOK ω pub w v.1 v.2.1 v.2.2).card : ENNReal) /
        ((Fintype.card F * (Fintype.card F * Fintype.card F) : ℕ) : ENNReal)
      ≤ (((3 * G.N - 1 + ∑ j ∈ range G.nP, d j) * Fintype.card F ^ 2 : ℕ) : ENNReal) /
          ((Fintype.card F * (Fintype.card F * Fintype.card F) : ℕ) : ENNReal) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr (card_copyOK_le ω hV hω pub w d hbind hns)) _
    _ = _ := by
        rw [show Fintype.card F * (Fintype.card F * Fintype.card F) =
          Fintype.card F * Fintype.card F ^ 2 by ring, Nat.cast_mul, Nat.cast_mul,
          ENNReal.mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ Fintype.card_ne_zero))
            (ENNReal.natCast_ne_top _)]

end Circuit

end RecPiop
