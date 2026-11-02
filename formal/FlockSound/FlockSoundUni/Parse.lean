-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSoundUni.Link
import FlockSoundUni.RoundByRound

/-!
# The transcript as Flock's run, and its bad family

`parse κ d` reads a transcript of `flockProg κ`'s rounds as `FlockSound`'s run
(`Front E 3 3 8 κ (4 + κ) 6`): `τ`'s sampled coordinates, the coset values, `z`, the zerocheck's
rounds (each message decoded from the claim before it, `msgPoly ∘ decodeMsg`, as the code decodes
it), `v_a`, `v_b`, `α`, the lincheck's rounds, the slices and the ring map. Every field reads the
rounds by position (`rd`), past the end `noRound`'s zeros, so a prefix of a transcript parses too.

**The bad family** (`flockBad κ`): the bad set of challenge `i` of round `j` is `Front.Bad`'s set at
that position (`badAt`) of the parse of the rounds so far, this round's message and its challenges
so far. Its sizes (`dBound`, from `card_bad`): `1` for each of `τ`'s `4 + κ` coordinates, `15` for
`z`, `2` for each zerocheck round, `3` for `α`, `2` for each lincheck round, `1` for each of the
ring map's six stages; round `j`'s error is the sum over its challenges: `4 + κ`, `15`, `2`
(`11 + κ` times), `3`, `2` (`8` times), `6`, over `|E|`.

**The prefix property** (`badAt_congr`): the bad set at `(j, i)` reads only the rounds before `j`,
round `j`'s message and its challenges before `i` (`AgreeAt`), by the `_congr` lemmas of
`FlockSound` (`pointBad_congr`, `sumBad_congr`, `ringBad_congr`) and their extensions here
(`trueAt_congr`, `sumBad_congr'`, `zcBad_congr`).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

/-! ## Congruence of the bad sets -/

section Congr

variable {F : Type*} [Field F]

theorem trueAt_congr : ∀ (m : ℕ) (w : Fin m → Option F) (Φ : (Fin m → F) → F) (χ χ' : Fin m → F)
    (j : Fin (m + 1)), (∀ i : Fin m, i.val < j.val → χ i = χ' i) →
    trueAt m w Φ χ j = trueAt m w Φ χ' j
  | 0, _, _, _, _, _, _ => rfl
  | m + 1, w, Φ, χ, χ', j, h => by
    refine Fin.cases (fun _ ↦ rfl) (fun j h ↦ ?_) j h
    rw [trueAt_succ, trueAt_succ, h 0 (Nat.succ_pos _)]
    exact trueAt_congr m _ _ _ _ j fun i hi ↦ h i.succ (by simpa using hi)

theorem claimAt_castSucc_congr {m : ℕ} (c₀ : F) (q q' : Fin m → F[X]) (χ χ' : Fin m → F) (j : Fin m)
    (hq : ∀ i : Fin m, i.val < j.val → q i = q' i) (hχ : ∀ i : Fin m, i.val < j.val → χ i = χ' i) :
    claimAt c₀ q χ j.castSucc = claimAt c₀ q' χ' j.castSucc := by
  obtain ⟨_ | k, hk⟩ := j
  · rfl
  · have e : (Fin.castSucc ⟨k + 1, hk⟩ : Fin (m + 1)) = (⟨k, by omega⟩ : Fin m).succ :=
      Fin.ext rfl
    rw [e]
    show (q _).eval (χ _) = (q' _).eval (χ' _)
    rw [hq _ (by simp), hχ _ (by simp)]

variable [Fintype F] [DecidableEq F]

/-- Round `j`'s bad challenges read its message and the challenges before it only. -/
theorem sumBad_congr' (d : ℕ) : ∀ (m : ℕ) (w : Fin m → Option F) (Φ : (Fin m → F) → F)
    (q q' : Fin m → F[X]) (χ χ' : Fin m → F) (j : Fin m), q j = q' j →
    (∀ i : Fin m, i.val < j.val → χ i = χ' i) →
    sumBad d m w Φ q χ j = sumBad d m w Φ q' χ' j
  | 0, _, _, _, _, _, _, j, _, _ => j.elim0
  | m + 1, w, Φ, q, q', χ, χ', j, hq, h => by
    refine Fin.cases (fun hq _ ↦ ?_) (fun j hq h ↦ ?_) j hq h
    · simp only [sumBad, Fin.cases_zero, hq]
    · rw [sumBad_succ, sumBad_succ, h 0 (Nat.succ_pos _)]
      exact sumBad_congr' d m _ _ _ _ _ _ j hq fun i hi ↦ h i.succ (by simpa using hi)

/-- **A zerocheck round's bad challenges** read the messages up to it and the challenges before
it only. -/
theorem zcBad_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (node : Bool × ι → F)
    (A B Z : ι → Cube n → F) (pin : Cube n → F) (τ : Fin n → F) (z c₀ : F) (q q' : Fin n → F[X])
    (χ χ' : Fin n → F) (j : Fin n) (hq : ∀ i : Fin n, i.val ≤ j.val → q i = q' i)
    (hχ : ∀ i : Fin n, i.val < j.val → χ i = χ' i) :
    zcBad node A B Z pin τ z c₀ q χ j = zcBad node A B Z pin τ z c₀ q' χ' j := by
  unfold zcBad
  rw [claimAt_castSucc_congr c₀ q q' χ χ' j (fun i hi ↦ hq i hi.le) hχ,
    trueAt_congr n _ _ χ χ' j.castSucc (fun i hi ↦ hχ i (by simpa using hi)),
    pointBad_congr n _ χ χ' j hχ, sumBad_congr' 2 n _ _ q q' χ χ' j (hq j le_rfl) hχ]

end Congr

/-! ## The main line's constants -/

/-- The ring map's stages in tower order (`towerRingMap`: stage `j` of shift `2^j`). -/
abbrev towerShifts : List ℕ := [1, 2, 4, 8, 16, 32]

/-- **leanVM's Flock at the main line**: skip `3` (`l = 3`), `4 + κ` sampled coordinates, the ring
map in tower order, the BLAKE2s R1CS. -/
abbrev mainSetup (κ : ℕ) : Setup E 3 3 8 κ 7 (4 + κ) :=
  setupOf 3 3 κ (4 + κ) rfl (by decide) (by omega) towerShifts
    Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs

/-- The column's bits on the cube. -/
abbrev zOf {κ : ℕ} (qf : Column (8 + κ)) : Cube (3 + 3) → Cube 8 → Cube κ → E :=
  colBits (k := 3) (l := 3) rfl qf

/-! ## The parse -/

/-- `τ`'s sampled coordinates. -/
def pSampled (d : Done) : List E := (rd d 0).2

/-- The coset values. -/
def pCoset (d : Done) : List E := (rd d 1).1.2

/-- `z`. -/
def pZ (d : Done) : E := (rd d 1).2.headD 0

/-- The zerocheck rounds' `eq` factors: the fixed coordinates, then the sampled. -/
def pEs (d : Done) : List (Option E) := (Flock.fixedChallenges ++ pSampled d).map some

/-- The zerocheck's starting claim, as the code computes it. -/
def pC0 (d : Done) : E := Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ pCoset d) (pZ d)

/-- The zerocheck's last claim. -/
def pRunning (κ : ℕ) (d : Done) : E := scClaim (pC0 d) (pEs d) (d.drop 2) (11 + κ)

/-- `v_a`. -/
def pVa (κ : ℕ) (d : Done) : E := (rd d (13 + κ)).1.2.getD 0 0

/-- `v_b`. -/
def pVb (κ : ℕ) (d : Done) : E := (rd d (13 + κ)).1.2.getD 1 0

/-- `α`. -/
def pAlpha (κ : ℕ) (d : Done) : E := (rd d (13 + κ)).2.headD 0

/-- The lincheck's starting claim, as the code computes it. -/
def pLc0 (κ : ℕ) (d : Done) : E :=
  pVa κ d + pAlpha κ d * pVb κ d + epow (pAlpha κ d) 2 * (pRunning κ d + pVa κ d * pVb κ d) +
    epow (pAlpha κ d) 3

/-- **The transcript as Flock's run.** -/
noncomputable def parse (κ : ℕ) (d : Done) : Front E 3 3 8 κ (4 + κ) 6 where
  τs a := (pSampled d).getD a 0
  cv b := (pCoset d).getD (cubeFin 3 b) 0
  z := pZ d
  zq t := msgPoly (decodeMsg (scClaim (pC0 d) (pEs d) (d.drop 2) t) ((pEs d).getD t none)
    (rd (d.drop 2) t).1.2)
  zχ t := (rd (d.drop 2) t).2.headD 0
  va := pVa κ d
  vb := pVb κ d
  α := pAlpha κ d
  lq t := msgPoly (decodeMsg (scClaim (pLc0 κ d) (List.replicate 8 none) (d.drop (14 + κ)) t) none
    (rd (d.drop (14 + κ)) t).1.2)
  lχ t := (rd (d.drop (14 + κ)) t).2.headD 0
  s cy := (rd d (22 + κ)).1.2.getD (cubeFin (3 + 3) cy) 0
  f a := (rd d (22 + κ)).2.getD a 0

/-! ## The bad family -/

/-- **The bad set of challenge `i` of round `j`**, for the column `qf` and the run `R`:
`Front.Bad`'s set at that position. -/
noncomputable def badAt {κ : ℕ} (qf : Column (8 + κ)) (R : Front E 3 3 8 κ (4 + κ) 6) (j i : ℕ) :
    Finset E :=
  if j = 0 then
    if h : i < 4 + κ then
      pointBad (4 + κ) (sampledTables (mainSetup κ).hsize (mainSetup κ).fixed
        (Front.zRes (mainSetup κ) (zOf qf))) R.τs ⟨i, h⟩
    else ∅
  else if j = 1 then
    if i = 0 then
      skipBad (mainSetup κ).node (Front.zA (mainSetup κ) (zOf qf)) (Front.zB (mainSetup κ) (zOf qf))
        (Front.zZ (zOf qf)) (Front.τ (mainSetup κ) R) R.cv
    else ∅
  else if h : j < 13 + κ then
    if i = 0 then
      zcBad (mainSetup κ).node (Front.zA (mainSetup κ) (zOf qf)) (Front.zB (mainSetup κ) (zOf qf))
        (Front.zZ (zOf qf)) (pinTab (zOf qf) (mainSetup κ).cpos) (Front.τ (mainSetup κ) R) R.z
        (Front.c₀ (mainSetup κ) R) R.zq R.zχ ⟨j - 2, by omega⟩
    else ∅
  else if j = 13 + κ then
    if i = 0 then
      alphaBad R.va R.vb (Front.vc (mainSetup κ) R)
        (skipVal (mainSetup κ).node (Front.zA (mainSetup κ) (zOf qf)) R.z R.zχ)
        (skipVal (mainSetup κ).node (Front.zB (mainSetup κ) (zOf qf)) R.z R.zχ)
        (skipVal (mainSetup κ).node (Front.zZ (zOf qf)) R.z R.zχ)
        (zhat (zOf qf) (Front.rt (mainSetup κ) R) (mainSetup κ).cpos)
    else ∅
  else if h : j < 22 + κ then
    if i = 0 then
      sumBad 2 8 (fun _ ↦ none)
        (linRev (linFun (mainSetup κ).A (mainSetup κ).B (zOf qf) (mainSetup κ).cpos (mainSetup κ).node
          R.z (Front.rl (mainSetup κ) R) (Front.rh (mainSetup κ) R) (Front.rt (mainSetup κ) R) R.α))
        R.lq R.lχ ⟨j - (14 + κ), by omega⟩
    else ∅
  else if j = 22 + κ then
    if h : i < 6 then
      ringBad univ (mainSetup κ).w (mainSetup κ).sh
        (fun cy ↦ R.s cy - strue (zOf qf) (Front.rt (mainSetup κ) R) (Front.χ' (mainSetup κ) R) cy) R.f
        ⟨i, h⟩
    else ∅
  else ∅

/-- **Flock's bad family**: the bad set of the next challenge, at its position, of the parse of the
rounds so far, this round's message and its challenges so far. -/
noncomputable def flockBad (κ : ℕ) : BadFamily κ := fun qf done msg pre ↦
  badAt qf (parse κ (done ++ [(msg, pre)])) done.length pre.length

/-- **The bad sets' sizes** (`card_bad`), by position. -/
def dBound (κ : ℕ) (j _i : ℕ) : ℕ :=
  if j = 0 then 1 else if j = 1 then 15 else if j < 13 + κ then 2 else if j = 13 + κ then 3
  else if j < 22 + κ then 2 else 1

theorem card_badAt {κ : ℕ} (qf : Column (8 + κ)) (R : Front E 3 3 8 κ (4 + κ) 6) (j i : ℕ) :
    (badAt qf R j i).card ≤ dBound κ j i := by
  obtain ⟨hτ, hz, hzc, hα, hlin, hring⟩ := card_bad 3 3 κ (4 + κ) rfl (by decide) (by omega) towerShifts
    Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs qf R
  unfold badAt
  by_cases h0 : j = 0
  · rw [ite_eq_left h0, show dBound κ j i = 1 by unfold dBound; split_ifs <;> omega]
    split_ifs
    · exact hτ _
    · simp
  rw [ite_eq_right h0]
  by_cases h1 : j = 1
  · rw [ite_eq_left h1, show dBound κ j i = 15 by unfold dBound; split_ifs <;> omega]
    split_ifs
    · exact hz.trans (by norm_num)
    · simp
  rw [ite_eq_right h1]
  by_cases h2 : j < 13 + κ
  · rw [dite_eq_left h2, show dBound κ j i = 2 by unfold dBound; split_ifs <;> omega]
    split_ifs
    · exact hzc _
    · simp
  rw [dite_eq_right h2]
  by_cases h3 : j = 13 + κ
  · rw [ite_eq_left h3, show dBound κ j i = 3 by unfold dBound; split_ifs <;> omega]
    split_ifs
    · exact hα
    · simp
  rw [ite_eq_right h3]
  by_cases h4 : j < 22 + κ
  · rw [dite_eq_left h4, show dBound κ j i = 2 by unfold dBound; split_ifs <;> omega]
    split_ifs
    · exact hlin _
    · simp
  rw [dite_eq_right h4, show dBound κ j i = 1 by unfold dBound; split_ifs <;> omega]
  split_ifs
  · exact hring _
  · simp
  · simp

theorem card_flockBad (κ : ℕ) : ∀ qf done msg pre,
    (flockBad κ qf done msg pre).card ≤ dBound κ done.length pre.length :=
  fun qf done msg pre ↦ card_badAt qf _ _ _

end FlockSound.Uni
