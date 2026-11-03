-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The numbers follow
-- `formal/Compose/Compose/ListChainKDoomExample.lean`.
import UniSound.Fs
import UniSound.Bus

/-!
# Knowledge soundness of the univariate verifier, end to end (main line)

**`uniKnowledgeSoundness`**: `UniKnowledgeSoundness D (uniBound e₃₂)` for every deployment `D`, the
rounds' errors at most `e₃₂ = 2^32 / |E|`, from

* **`hFlock : FlockSound κ`** — **the Flock hypothesis** (the one assumption about BLAKE2s by
  Flock, `FlockInterface.lean`): Flock's front is a chain program, round-by-round sound from
  `FlockRegion.Holds` to its ring-switch claim and its pending matrices' reduction;
* **`I : UniIds D hFlock`** — the identity model (`Piop.lean`): the bus and constraint state with
  its round-`0` error, the identities as polynomials of bounded degree, the relations at `t`, the
  batch's products; the bridges between them and Lv42's `M3Holds`;
* **`C : UniCode …`**, **`hFin : UniFinal …`** — the code-level links (`Fs.lean`);
* **`hFs : FsLayer …`** — the Fiat–Shamir layer (`Fs.lean`): `ListChainK`'s closed
  random-permutation theorem for the univariate transcript, openings, setup and extractor;
* the numbers: `errMain`, Flock's rounds' errors at most `2^32 / |E|`, the identities' degrees
  and the merge polynomial's at most `2^32` in all, at most `2^32 − 2` relations on a commitment.

The protocol is `uniPiop hFlock I` (`PiopSound.lean`, proved): its states' last one follows from the
verifier's checks with true claims (`hlink_uniPiop`, from `hFin`), its first is the relation
(`hpre_uniPiop`), and every round's error is at most `e₃₂` (`uniErr_le`).

**`uniBound_le_bits`**: at most `2^-61` for an adversary of at most `2^64` calls of `π` and `π⁻¹`
(the five openings' doom terms, `≈ 5 · 2^-64`, dominate; the list term is `≈ 2^-69.4`).
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset WhirBridge
open scoped ENNReal

variable {D : Deployment} {κ : ℕ}

/-! ## The opened transcript of a completed one -/

theorem length_openedOf (nF : ℕ) (c1 c2 : Stk) (done : Done) :
    (openedOf nF c1 c2 done).length = done.length := by
  simp [openedOf]

theorem rd_openedOf (nF : ℕ) (c1 c2 : Stk) (done : Done) (j : ℕ) (h : j < done.length) :
    rd (openedOf nF c1 c2 done) j =
      ((if j = 0 then some c1 else if j = nF + 1 then some c2 else none, (done[j]'h).1.2),
        (done[j]'h).2) := by
  simp [rd, openedOf, List.getD_eq_getElem?_getD, h]

theorem doneFits_append_take : ∀ (rs₁ rs₂ : List Compose.RoundSpec) (d : Done),
    DoneFits (rs₁ ++ rs₂) d → DoneFits rs₁ (d.take rs₁.length)
  | [], _, _, _ => by simp [DoneFits]
  | r :: rs₁, rs₂, [], h => by simp [DoneFits] at h
  | r :: rs₁, rs₂, x :: d, h => by
    simp only [List.cons_append, DoneFits] at h
    simp only [List.length_cons, List.take_succ_cons, DoneFits]
    exact ⟨h.1, h.2.1, doneFits_append_take rs₁ rs₂ d h.2.2⟩

theorem doneFits_map_noRoot : ∀ (rs : List Compose.RoundSpec) (d : Done),
    (∀ r ∈ rs, r.root = false) → DoneFits rs d →
      DoneFits rs (d.map fun y => ((none, y.1.2), y.2))
  | [], [], _, _ => trivial
  | r :: rs, y :: d, hr, h => by
    simp only [DoneFits, List.map_cons] at h ⊢
    refine ⟨⟨?_, h.1.2⟩, h.2.1, doneFits_map_noRoot rs d (fun r' hr' => hr r' (by simp [hr'])) h.2.2⟩
    simp [hr r (by simp)]
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem take_map_zipIdx (nF : ℕ) (c1 c2 : Stk) : ∀ (l : Done) (k n : ℕ),
    ((((l.zipIdx k).map fun x : (UMsg × List E) × ℕ =>
        ((if x.2 = 0 then some c1 else if x.2 = nF + 1 then some c2 else none, x.1.1.2),
          x.1.2)).take n).map fun x : (Option Stk × List E) × List E =>
        (((none : Option (E × E)), x.1.2), x.2)) =
      (l.take n).map fun y : UMsg × List E => (((none : Option (E × E)), y.1.2), y.2)
  | [], _, _ => by simp
  | _ :: _, _, 0 => by simp
  | y :: l, k, n + 1 => by
    simp only [List.zipIdx_cons, List.map_cons, List.take_succ_cons, List.cons.injEq]
    exact ⟨by simp, take_map_zipIdx nF c1 c2 l (k + 1) n⟩

theorem fdOf_openedOf (nF : ℕ) (c1 c2 : Stk) (done : Done) :
    fdOf nF (openedOf nF c1 c2 done) =
      ((done.drop 1).take nF).map fun y : UMsg × List E => (((none : Option (E × E)), y.1.2), y.2) := by
  rcases done with _ | ⟨x, d⟩
  · simp [fdOf, openedOf]
  · unfold fdOf openedOf
    simp only [List.zipIdx_cons, List.map_cons, List.drop_succ_cons, List.drop_zero]
    exact take_map_zipIdx nF c1 c2 d 1 nF

/-! ## The links of `uniPiop` -/

variable (hFlock : FlockSound κ) (I : UniIds D hFlock)

theorem hpre_uniPiop (s : USt) (c : Stk) (m : List E) :
    (uniPiop hFlock I).pre s [] (some c, m) → Rel D s c := by
  intro h
  change uniPre hFlock I s [] (some c, m) at h
  unfold uniPre at h
  rw [ite_eq_left (List.length_nil : ([] : Op Stk).length = 0)] at h
  obtain ⟨c', hc', hr⟩ := h
  cases hc'
  exact hr

theorem hlink_uniPiop (C : UniCode D hFlock I.nV I.V) (hFin : UniFinal D hFlock I C) (s : USt)
    (done : Done) (tl : List E) (c1 c2 : Stk)
    (hd : DoneFits (uniRounds hFlock.prog.rounds I.nV I.V) done) (htl : tl.length = 5)
    (hz : (C.prog s.1 s.2).ZerosVanish done tl)
    (hc : ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2) :
    ∃ p m ch, openedOf hFlock.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧
      (uniPiop hFlock I).post s p m ch := by
  set nF := hFlock.prog.rounds.length
  set q := openedOf nF c1 c2 done with hq
  have hlen : done.length = nF + 3 + I.V := by
    rw [hd.length_eq, length_uniRounds]
  have hql : q.length = nF + 3 + I.V := by rw [hq, length_openedOf, hlen]
  have hne : q ≠ [] := by
    intro h
    rw [h] at hql
    simp only [List.length_nil] at hql
    omega
  refine ⟨q.dropLast, (q.getLast hne).1, (q.getLast hne).2, ?_, ?_⟩
  · exact (List.dropLast_append_getLast hne).symm
  change uniS hFlock I s (q.dropLast ++ [((q.getLast hne).1, (q.getLast hne).2)])
  rw [show q.dropLast ++ [((q.getLast hne).1, (q.getLast hne).2)] = q from
    List.dropLast_append_getLast hne]
  unfold uniS
  refine ⟨c1, ?_, ?_⟩
  · rw [hq, rd_openedOf _ _ _ _ 0 (by omega)]
    simp
  rw [ite_eq_right (by omega)]
  refine ⟨c2, ?_, ?_, ?_⟩
  · rw [hq, rd_openedOf _ _ _ _ (nF + 1) (by omega)]
    simp
  · -- Flock's rounds completed.
    show DoneFits hFlock.prog.rounds (fdOf nF q)
    rw [hq, fdOf_openedOf]
    refine doneFits_map_noRoot _ _ hFlock.rounds_root ?_
    rcases done with _ | ⟨x, d⟩
    · simp only [List.length_nil] at hlen
      omega
    · have h1 : DoneFits (hFlock.prog.rounds ++ ([⟨true, 0, 0⟩, ⟨false, I.nV, 1⟩] ++
          List.replicate I.V ⟨false, 2, 0⟩)) d := by
        have := hd
        simp only [uniRounds, List.append_assoc, List.singleton_append] at this
        exact this.2.2
      simpa using doneFits_append_take _ _ d h1
  · rw [ite_eq_right (by omega)]
    exact hFin s done tl c1 c2 hd htl hz hc

/-- **Every round's error is at most `2^32 / |E|`**, given the identity model's and Flock's
numbers. -/
theorem uniErr_le (hMain : I.errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 32) (hrel : I.nRel + 2 ≤ 2 ^ 32) (j : ℕ) :
    uniErr hFlock I j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  unfold uniErr
  split_ifs
  · exact hMain
  · exact hFl _
  · exact ENNReal.div_le_div_right (Nat.cast_le.mpr hdeg) _
  · exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _
  · exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by norm_num)) _

/-! ## The end theorem -/

/-- **Knowledge soundness of the univariate verifier for leanVM 42422001** (main line: Flock with
the slices in tower order, point claims), for the explicit extractor `uniExtractor`, with error
`uniBound (2^32 / |E|) Q` at `Q` calls of `π` and `π⁻¹`; **under the Flock hypothesis `hFlock`**,
the identity model `I`, the code-level links `C`, `hFin`, the Fiat–Shamir layer `hFs`, and the
numbers. -/
theorem uniKnowledgeSoundness (hFlock : FlockSound κ) (I : UniIds D hFlock)
    (C : UniCode D hFlock I.nV I.V) (hFin : UniFinal D hFlock I C)
    (hFs : FsLayer D hFlock I.nV I.V C)
    (hMain : I.errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 32) (hrel : I.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) :=
  hFs (uniPiop hFlock I) _ (uniErr_le hFlock I hMain hFl hdeg hrel) (hpre_uniPiop hFlock I)
    (hlink_uniPiop hFlock I C hFin)

/-! ## The bits -/

theorem cast_div_le_256 {a b : ℕ} (h : a ≤ b) :
    ((a : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((b : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr h) _

theorem inv_two_pow_128' : (2 : ℝ≥0∞)⁻¹ ^ 128 = ((2 ^ 128 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 128 + 128 from rfl, two_pow_div_two_pow]

/-- An opening's doom term at most `(X 2^128 + 5 X²) / 2^256` for `QA + QV ≤ X`. -/
theorem openingBoundAt_le' {QV QA X : ℕ} (h : QA + QV ≤ X) :
    openingBoundAt QV QA ≤ ((X * 2 ^ 128 + 5 * X * X : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold openingBoundAt
  rw [inv_two_pow_128', ENNReal.div_add_div_same, ← mul_div_assoc, ← Nat.cast_add, ← Nat.cast_mul]
  refine cast_div_le_256 ?_
  calc (QA + QV) * (2 ^ 128 + 5 * (QA + QV)) ≤ X * (2 ^ 128 + 5 * X) :=
        Nat.mul_le_mul h (by omega)
    _ = X * 2 ^ 128 + 5 * X * X := by ring

theorem div_192_eq' (a : ℕ) :
    ((a : ℕ) : ℝ≥0∞) / 2 ^ 192 = ((a * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 192 + 64 from rfl, pow_add,
    ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]

theorem cardE_cast : (Fintype.card E : ℝ≥0∞) = 2 ^ 192 := by
  rw [LeanVM.Protocol.card_E, Nat.cast_pow, Nat.cast_ofNat]

/-- **The bound in bits**: at most `2^-61` for an adversary of at most `2^64` calls of `π` and
`π⁻¹`. -/
theorem uniBound_le_bits (Q : ℕ) (hQ : Q ≤ 2 ^ 64) :
    uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 := by
  unfold uniBound uniN
  rw [cardE_cast, div_192_eq']
  have hX : 2 ^ 33 + Q + 10122 ≤ 18446744082299496586 := by
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    have h33 : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
    omega
  have b1 := openingBoundAt_le' (QV := 10122) (QA := 2 ^ 33 + Q) (X := 18446744082299496586) hX
  -- The list term.
  have hN : 2 ^ 33 + Q ≤ 18446744082299496586 := by omega
  have b2 : ((2 ^ 33 + Q : ℕ) : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) *
      (((2 ^ 32 * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256) + 8 * ((2 ^ 33 + Q : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤
      ((18446744082299496586 * (9952 ^ 2 * (2 ^ 32 * 2 ^ 64)) +
        8 * 18446744082299496586 * 18446744082299496586 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [← mul_div_assoc, ← Nat.cast_mul, show (8 : ℝ≥0∞) = ((8 : ℕ) : ℝ≥0∞) from rfl,
      ← Nat.cast_mul, ENNReal.div_add_div_same, ← Nat.cast_add, ← mul_div_assoc, ← Nat.cast_mul]
    refine cast_div_le_256 ?_
    calc (2 ^ 33 + Q) * (9952 ^ 2 * (2 ^ 32 * 2 ^ 64) + 8 * (2 ^ 33 + Q))
        ≤ 18446744082299496586 * (9952 ^ 2 * (2 ^ 32 * 2 ^ 64) + 8 * 18446744082299496586) :=
          Nat.mul_le_mul hN (by omega)
      _ = _ := by ring
  -- The random-permutation term.
  have b3 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have hq : (2 ^ 81 + Q) ^ 2 ≤ 2 ^ 164 := by
      have h82 : 2 ^ 81 + Q ≤ 2 ^ 82 := by
        have : (2 : ℕ) ^ 82 = 2 ^ 81 + 2 ^ 81 := by norm_num
        have h64 : (2 : ℕ) ^ 64 ≤ 2 ^ 81 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      calc (2 ^ 81 + Q) ^ 2 ≤ (2 ^ 82) ^ 2 := Nat.pow_le_pow_left h82 2
        _ = 2 ^ 164 := by norm_num
    have e1 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 = (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) := by
      rw [Nat.cast_pow]
    rw [e1]
    calc (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 508 ≤ ((2 ^ 164 : ℕ) : ℝ≥0∞) / 2 ^ 508 :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr hq) _
      _ = (2 : ℝ≥0∞)⁻¹ ^ 344 := by
          rw [Nat.cast_pow, Nat.cast_ofNat, show (508 : ℕ) = 164 + 344 from rfl,
            two_pow_div_two_pow]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 :=
          pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) (by norm_num)
      _ = ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [Nat.cast_one, one_div, ENNReal.inv_pow]
  refine (add_le_add (add_le_add (mul_le_mul' le_rfl b1) b2) b3).trans ?_
  rw [show (5 : ℝ≥0∞) = ((5 : ℕ) : ℝ≥0∞) from rfl, ← mul_div_assoc, ← Nat.cast_mul,
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
  calc _ ≤ ((2 ^ 195 : ℕ) : ℝ≥0∞) / 2 ^ 256 := cast_div_le_256 (by norm_num)
    _ = (2 : ℝ≥0∞)⁻¹ ^ 61 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 195 + 61 from rfl, two_pow_div_two_pow]

/-- **Knowledge soundness with the bound in bits** (main line): under the same hypotheses, the
deployed univariate verifier is knowledge sound for `uniExtractor` with error at most `2^-61` for
every adversary of at most `2^64` calls of `π` and `π⁻¹` (`ε Q = uniBound (2^32 / |E|) Q`,
explicit at every `Q`). -/
theorem uniKnowledgeSoundness_bits (hFlock : FlockSound κ) (I : UniIds D hFlock)
    (C : UniCode D hFlock I.nV I.V) (hFin : UniFinal D hFlock I C)
    (hFs : FsLayer D hFlock I.nV I.V C)
    (hMain : I.errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 32) (hrel : I.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  ⟨uniKnowledgeSoundness hFlock I C hFin hFs hMain hFl hdeg hrel, uniBound_le_bits⟩

/-- **Knowledge soundness, round `0` proved** (the bus `4N/|E|` and the constraints' batching,
`BusModel.mainSound`, from `formal/Heap`): the end theorem with the bus model `B` and the rest of
the identity model `J` in place of `UniIds`; **under the Flock hypothesis `hFlock`**. -/
theorem uniKnowledgeSoundness_bus (hFlock : FlockSound κ) (B : BusModel D κ)
    (J : UniIdsRest D hFlock B) (C : UniCode D hFlock J.nV J.V)
    (hFin : UniFinal D hFlock (UniIds.ofBus hFlock B J) C) (hFs : FsLayer D hFlock J.nV J.V C)
    (hB : 4 * B.N + B.ncv ≤ 2 ^ 32)
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : J.degSum + J.degBad ≤ 2 ^ 32) (hrel : J.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_bits hFlock (UniIds.ofBus hFlock B J) C hFin hFs (B.errMain_le hB) hFl hdeg
    hrel

end UniSound
