-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.Fresh.Tree

/-!
# Fresh Fiat–Shamir inputs: the duplex

The duplex carries its capacity (lanes `16 .. 25`) from one permutation to the next; the prover's
messages only fill the rate. **A fresh capacity** (`CapOK`): no input the oracle holds has it, and
it is not zero (the seed's). Then the next permutation's input is fresh, its answer is fresh, and
its capacity is fresh again (`NoHit.cap`, `NoHit.capz`): every draw's input is fresh
(`trip_draw`), and so is every absorbing permutation's (`trip_absorb`).

**Grinding** (`trip_grind`): the tries share the capacity, and differ in the nonce's lane
(`tryInput_inj`, nonces below `2^64`); the successful try's answer is fresh. If none succeeds, the
state is the one before, whose input differs from every try's in the nonce's tag lane (`0`, not `4`)
(`InpFresh`): the next draw's input is still fresh.

Every input these steps log is a Keccak-256 input or a state of nonzero capacity (`DFrame`).
-/

open OracleComp OracleSpec QuotientRpm
open scoped ENNReal

namespace QuotientZk.Deployed.Fresh

set_option linter.unusedSectionVars false

/-! ## The permutation's input -/

theorem capOf_input (d : Dx) : capOf d.input = capOf d.st := by
  unfold capOf Dx.input
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_drop, Vector.getElem_toList, Vector.getElem_ofFn]
  rw [if_neg (by omega)]
  rfl

theorem input_lane (d : Dx) (p : ℕ) (hp : p < 4) (x : Limbs) (tag : UInt64)
    (h : d.pend[p]? = some (x, tag)) :
    d.input[4 * p]'(by omega) = x.1 ∧ d.input[4 * p + 3]'(by omega) = tag := by
  unfold Dx.input
  simp only [Vector.getElem_ofFn]
  have e1 : (4 * p) / 4 = p := by omega
  have e2 : (4 * p + 3) / 4 = p := by omega
  have e3 : (4 * p) % 4 = 0 := by omega
  have e4 : (4 * p + 3) % 4 = 3 := by omega
  rw [if_pos (by omega), if_pos (by omega)]
  simp [e1, e2, h, e3, e4]

theorem input_lane_none (d : Dx) (p : ℕ) (hp : p < 4) (h : d.pend[p]? = none) :
    d.input[4 * p + 3]'(by omega) = 0 := by
  unfold Dx.input
  simp only [Vector.getElem_ofFn]
  have e2 : (4 * p + 3) / 4 = p := by omega
  rw [if_pos (by omega)]
  simp only [e2, h]

/-- A grinding try's input: the nonce absorbed with tag `4`. -/
def tryInput (d : Dx) (a : UInt64) : KSt := Dx.input ⟨d.st, d.pend ++ [((a, 0, 0), tagNonce)]⟩

theorem capOf_tryInput (d : Dx) (a : UInt64) : capOf (tryInput d a) = capOf d.st :=
  capOf_input _

theorem tryInput_inj (d : Dx) (hp : d.pend.length < 4) {a b : UInt64}
    (h : tryInput d a = tryInput d b) : a = b := by
  have ha := (input_lane ⟨d.st, d.pend ++ [((a, 0, 0), tagNonce)]⟩ d.pend.length hp (a, 0, 0) tagNonce
    (by simp)).1
  have hb := (input_lane ⟨d.st, d.pend ++ [((b, 0, 0), tagNonce)]⟩ d.pend.length hp (b, 0, 0) tagNonce
    (by simp)).1
  unfold tryInput at h
  rw [h] at ha
  exact ha.symm.trans hb

theorem input_ne_tryInput (d : Dx) (hp : d.pend.length < 4) (a : UInt64) :
    d.input ≠ tryInput d a := by
  intro h
  have h1 := input_lane_none d d.pend.length hp (by simp)
  have h2 := (input_lane ⟨d.st, d.pend ++ [((a, 0, 0), tagNonce)]⟩ d.pend.length hp (a, 0, 0) tagNonce
    (by simp)).2
  unfold tryInput at h
  rw [h] at h1
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ## Fresh capacities -/

/-- A fresh capacity: no input the oracle holds has it, and it is not the seed's. -/
def CapOK (K0 : List Inp) (st : DSt) (c : KSt) : Prop :=
  (∀ y ∈ dom K0 st, ∀ w, y = .inr w → capOf w ≠ capOf c) ∧ capOf c ≠ zeroCap

/-- A duplex whose capacity is fresh. -/
def CapFresh (K0 : List Inp) (st : DSt) (d : Dx) : Prop := CapOK K0 st d.st ∧ d.pend.length ≤ 4

/-- A duplex whose next input is fresh (enough for a draw). -/
def InpFresh (K0 : List Inp) (st : DSt) (d : Dx) : Prop :=
  (.inr d.input : Inp) ∉ dom K0 st ∧ capOf d.st ≠ zeroCap ∧ d.pend.length ≤ 4

theorem CapFresh.inp {K0 : List Inp} {st : DSt} {d : Dx} (h : CapFresh K0 st d) :
    InpFresh K0 st d :=
  ⟨fun hm => h.1.1 _ hm _ rfl (capOf_input d), h.1.2, h.2⟩

theorem CapOK.of_noHit {K0 : List Inp} {st : DSt} {t : Inp} {u : Out} (hu : NoHit K0 st t u) :
    CapOK K0 (addE st t u) u.2 :=
  ⟨fun y hy w hw => hu.cap y ((mem_dom_addE K0 st t u y).mp hy) w hw, hu.capz⟩

theorem CapOK.of_noHitH {K0 : List Inp} {n : ℕ} {st : DSt} {t : Inp} {u : Out} (hu : NoHit K0 st t u) :
    CapOK K0 (addH n st t u) u.2 :=
  ⟨fun y hy w hw => hu.cap y ((mem_dom_addH K0 n st t u y).mp hy) w hw, hu.capz⟩

/-- The inputs the duplex logs: Keccak-256 inputs, or states of nonzero capacity. -/
def DFrame (y : Inp) : Prop := IsInl y ∨ ∃ w, y = .inr w ∧ capOf w ≠ zeroCap

/-- A fresh capacity is kept by Keccak-256 inputs. -/
theorem CapOK.ext {K0 : List Inp} {Φ : Inp → Prop} {st st' : DSt} {c : KSt} (h : CapOK K0 st c)
    (he : Ext Φ st st') (hΦ : ∀ y, Φ y → IsInl y) : CapOK K0 st' c :=
  ⟨fun y hy w hw => (he.mem_dom hy).elim (fun hy => h.1 y hy w hw) (fun hy => by
    obtain ⟨b, rfl⟩ := hΦ y hy; cases hw), h.2⟩

/-! ## The duplex's steps -/

section Steps

variable {S : Type} {P : Proto S Inp Out Msg Tbl Pos} {s : S} {cw : Fin 3 → Bytes32 → List UInt8}
  {K0 : List Inp}

/-- A permutation from a fresh capacity: a fresh capacity. -/
theorem trip_perm_cap (d : Dx) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ CapOK K0 st₀ d.st) (perm d.input)
      (fun x st => ExtP DFrame st₀ st ∧ CapOK K0 st x) := by
  refine Trip.ginv ((trip_perm_fresh _ _).mono (fun st ⟨hg, hst, hc⟩ => ?_) (fun _ _ h => h))
  subst hst
  have hm : (.inr d.input : Inp) ∉ dom K0 st := fun hm => hc.1 _ hm _ rfl (capOf_input d)
  exact ⟨hm, fun u hu => ⟨ExtP.of_addE u (hg.cache_none hm)
    (Or.inr ⟨_, rfl, by rw [capOf_input]; exact hc.2⟩), CapOK.of_noHit hu⟩⟩

/-- How many scalars wait after one more. -/
def absorb1 (p : ℕ) : ℕ := if p = 4 then 1 else p + 1

/-- How many scalars wait after `k` more. -/
def absorbN : ℕ → ℕ → ℕ
  | p, 0 => p
  | p, k + 1 => absorbN (absorb1 p) k

theorem absorbN_le (p k : ℕ) (hp : p ≤ 4) : absorbN p k ≤ 4 := by
  induction k generalizing p with
  | zero => exact hp
  | succ k ih => exact ih _ (by unfold absorb1; split_ifs <;> omega)

/-- **Absorbing a scalar**: a fifth one first permutes (from a fresh capacity, to a fresh one). -/
theorem trip_absorb (d : Dx) (x : Limbs) (tag : UInt64) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ CapFresh K0 st₀ d) (d.absorb x tag)
      (fun d' st => ExtP DFrame st₀ st ∧ CapFresh K0 st d' ∧
        d'.pend.length = absorb1 d.pend.length) := by
  unfold Dx.absorb
  split_ifs with h
  · refine Trip.bind ((trip_perm_cap d st₀).mono (fun st ⟨h1, h2⟩ => ⟨h1, h2.1⟩) (fun _ _ h => h))
      fun x' => ?_
    exact (Trip.pure _ _).mono (fun st ⟨he, hc⟩ => ⟨he, ⟨hc, by simp⟩, by simp [absorb1, h]⟩)
      (fun _ _ h => h)
  · exact (Trip.pure _ _).mono (fun st ⟨hst, hc⟩ => by
      subst hst
      have := hc.2
      exact ⟨ExtP.refl _, ⟨hc.1, by simp; omega⟩, by simp [absorb1, h]⟩) (fun _ _ h => h)

/-- **Absorbing scalars**. -/
theorem trip_absorbAll : ∀ (d : Dx) (xs : List Limbs) (st₀ : DSt),
    Trip P s cw K0 (fun st => st = st₀ ∧ CapFresh K0 st₀ d) (d.absorbAll xs)
      (fun d' st => ExtP DFrame st₀ st ∧ CapFresh K0 st d' ∧
        d'.pend.length = absorbN d.pend.length xs.length)
  | d, [], st₀ => by
    unfold Dx.absorbAll
    exact (Trip.pure _ _).mono (fun st ⟨hst, hc⟩ => by subst hst; exact ⟨ExtP.refl _, hc, rfl⟩)
      (fun _ _ h => h)
  | d, x :: xs, st₀ => by
    unfold Dx.absorbAll
    refine Trip.bind (trip_absorb d x tagObserve st₀) fun d' => Trip.intro fun st₁ ⟨he₁, hc₁, hp₁⟩ =>
      ((trip_absorbAll d' xs st₁).mono (fun st h => ⟨h, hc₁⟩) fun d'' st ⟨he, hc, hp⟩ =>
        ⟨he₁.trans he, hc, by simp [absorbN, hp, hp₁]⟩)

/-- **A draw from a fresh input**: one challenge, a fresh capacity, nothing waiting. -/
theorem trip_draw (d : Dx) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ InpFresh K0 st₀ d) d.draw
      (fun r st => Ext DFrame st₀ st ∧ HistGrow P.n 1 st₀ st ∧ CapFresh K0 st r.2 ∧
        r.2.pend = []) := by
  unfold Dx.draw
  refine Trip.ginv (Trip.bind ((trip_chalF _ _).mono (fun st ⟨hg, hst, hi⟩ => ?_)
    (fun _ _ h => h)) fun x => (Trip.pure _ _).mono (fun st h => h) (fun _ _ h => h))
  subst hst
  exact ⟨hi.1, fun u hu => ⟨Ext.of_addH u (hg.cache_none hi.1)
    (Or.inr ⟨_, rfl, by rw [capOf_input]; exact hi.2.1⟩), histGrow_addH _ _ hg.hist,
    ⟨CapOK.of_noHitH hu, by simp⟩, rfl⟩⟩

/-- **The seed**: from an input the oracle does not hold, a fresh capacity. -/
theorem trip_seed (iv : Bytes32) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ (.inr (seedInput iv) : Inp) ∉ dom K0 st₀) (seed iv)
      (fun d st => ExtP (fun y => y = .inr (seedInput iv)) st₀ st ∧ CapFresh K0 st d ∧
        d.pend = []) := by
  unfold seed
  refine Trip.ginv (Trip.bind ((trip_perm_fresh _ _).mono (fun st ⟨hg, hst, hi⟩ => ?_)
    (fun _ _ h => h)) fun x => (Trip.pure _ _).mono (fun st h => h) (fun _ _ h => h))
  subst hst
  exact ⟨hi, fun u hu => ⟨ExtP.of_addE u (hg.cache_none hi) rfl, ⟨CapOK.of_noHit hu, by simp⟩, rfl⟩⟩

/-! ## Grinding -/

/-- During grinding: the inputs of the capacity are the tries so far. -/
def GrindInv (K0 : List Inp) (st : DSt) (d : Dx) (cnt : ℕ) : Prop :=
  ∀ y ∈ dom K0 st, ∀ w, y = .inr w → capOf w = capOf d.st →
    ∃ m : ℕ, m < cnt ∧ w = tryInput d (UInt64.ofNat m)

theorem GrindInv.of_capOK {K0 : List Inp} {st : DSt} {d : Dx} (h : CapOK K0 st d.st) :
    GrindInv K0 st d 0 := fun y hy w hw hc => absurd hc (h.1 y hy w hw)

theorem ofNat_inj {m n : ℕ} (hm : m < 2 ^ 64) (hn : n < 2 ^ 64)
    (h : UInt64.ofNat m = UInt64.ofNat n) : m = n := by
  have h1 : (UInt64.ofNat m).toNat = m := by simp; omega
  have h2 : (UInt64.ofNat n).toNat = n := by simp; omega
  rw [← h1, ← h2, h]

/-- **One try**: its input is fresh, and so is its answer's capacity. -/
theorem trip_tryNonce (d : Dx) (hp : d.pend.length < 4) (hz : capOf d.st ≠ zeroCap) (cnt : ℕ)
    (hcnt : cnt < 2 ^ 64) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ GrindInv K0 st₀ d cnt)
      (tryNonce d (UInt64.ofNat cnt))
      (fun r st => ExtP DFrame st₀ st ∧ GrindInv K0 st d (cnt + 1) ∧ CapFresh K0 st r.2 ∧
        r.2.pend = []) := by
  unfold tryNonce
  have hab : d.absorb (UInt64.ofNat cnt, 0, 0) tagNonce =
      pure ⟨d.st, d.pend ++ [((UInt64.ofNat cnt, 0, 0), tagNonce)]⟩ := by
    unfold Dx.absorb; rw [if_neg (by omega)]
  rw [hab, pure_bind, show (⟨d.st, d.pend ++ [((UInt64.ofNat cnt, 0, 0), tagNonce)]⟩ : Dx).input =
    tryInput d (UInt64.ofNat cnt) from rfl]
  refine Trip.ginv (Trip.bind (mid := fun x st => ExtP DFrame st₀ st ∧
      GrindInv K0 st d (cnt + 1) ∧ CapFresh K0 st ⟨x, []⟩)
    ((trip_perm_fresh _ _).mono (fun st ⟨hg, hst, hgi⟩ => ?_) (fun _ _ h => h)) fun x =>
      (Trip.pure _ _).mono (fun st h => ⟨h.1, h.2.1, h.2.2, rfl⟩) (fun _ _ h => h))
  subst hst
  have hm : (.inr (tryInput d (UInt64.ofNat cnt)) : Inp) ∉ dom K0 st := fun hm => by
    obtain ⟨m, hm', he⟩ := hgi _ hm _ rfl (capOf_tryInput d _)
    have := ofNat_inj (by omega) hcnt (tryInput_inj d hp he).symm
    omega
  refine ⟨hm, fun u hu => ⟨ExtP.of_addE u (hg.cache_none hm)
    (Or.inr ⟨_, rfl, by rw [capOf_tryInput]; exact hz⟩), fun y hy w hw hc => ?_,
    ⟨CapOK.of_noHit hu, Nat.zero_le _⟩⟩⟩
  rcases (mem_dom_addE K0 st _ u y).mp hy with rfl | hy
  · exact ⟨cnt, by omega, (Sum.inr.inj hw).symm⟩
  · obtain ⟨m, hm', he⟩ := hgi y hy w hw hc
    exact ⟨m, by omega, he⟩

/-- **Grinding**: the next draw's input is fresh, whether a try succeeds or none does. -/
theorem trip_grind (d : Dx) (hp : d.pend.length < 4) (hz : capOf d.st ≠ zeroCap) :
    ∀ (fuel cnt : ℕ) (st₀ : DSt), fuel + cnt ≤ 2 ^ 64 →
    Trip P s cw K0 (fun st => st = st₀ ∧ GrindInv K0 st₀ d cnt)
      (grind d fuel (UInt64.ofNat cnt))
      (fun r st => ExtP DFrame st₀ st ∧ InpFresh K0 st r.2 ∧ r.2.pend.length < 4)
  | 0, cnt, st₀, _ => by
    unfold grind
    refine (Trip.pure _ _).mono (fun st ⟨hst, hgi⟩ => ?_) (fun _ _ h => h)
    subst hst
    refine ⟨ExtP.refl _, ⟨fun hm => ?_, hz, show d.pend.length ≤ 4 by omega⟩, hp⟩
    obtain ⟨m, -, he⟩ := hgi _ hm _ rfl (capOf_input d)
    exact input_ne_tryInput d hp _ he
  | fuel + 1, cnt, st₀, hf => by
    unfold grind
    refine Trip.bind (trip_tryNonce d hp hz cnt (by omega) st₀) fun r => Trip.intro fun st₁ hr => ?_
    obtain ⟨he₁, hgi, hcf, hpe⟩ := hr
    obtain ⟨ok, d'⟩ := r
    simp only at hcf hpe ⊢
    split_ifs with hok
    · exact (Trip.pure _ _).mono (fun st hst => by
        subst hst; exact ⟨he₁, hcf.inp, by simp [hpe]⟩) (fun _ _ h => h)
    · have e : UInt64.ofNat cnt + 1 = UInt64.ofNat (cnt + 1) := by
        apply UInt64.toNat_inj.mp
        simp [UInt64.toNat_add, UInt64.toNat_ofNat, Nat.add_mod]
      rw [e]
      exact (trip_grind d hp hz fuel (cnt + 1) st₁ (by omega)).mono
        (fun st hst => ⟨hst, hgi⟩)
        (fun r st ⟨he, hi, hpp⟩ => ⟨he₁.trans he, hi, hpp⟩)

end Steps

end QuotientZk.Deployed.Fresh
