-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The verifier (`Flock.verifyDeferred`) is
-- `formal/UniStatement`'s, transcribed from `crates/leanvm_flock_gas/src/flock_min.rs`.
import FlockSoundUni.Shape

/-!
# Flock's front as a chain program, and its code-level link

`Flock.verifyDeferred F (14 + κ) flockMain` (skip `3`, the slices sent, the ring map in tower order)
is the chain program `flockProg κ` (no root, no zero, no tail), whose `23 + κ` rounds are:

* `⟨false, 0, 3 + κ⟩`: the zerocheck point's `4 + κ` sampled coordinates `τ`;
* `⟨false, 8, 0⟩`: the skip's `8` coset values, then `z`;
* `11 + κ` × `⟨false, 2, 0⟩`: the zerocheck's rounds (two scalars, a challenge);
* `⟨false, 2, 0⟩`: `v_a`, `v_b` (the end of `zerocheck`), then `α` (drawn in `front`);
* `8` × `⟨false, 2, 0⟩`: the lincheck's rounds;
* `⟨false, 64, 5⟩`: the `64` slices, then the ring map's six challenges (`ringEnd`).

The result (`outOf`) is the code's, from the rounds' reads (`flockOut`: the zerocheck's and the
lincheck's sumchecks decoded, `decodeSC`; `Pending.new`; the tower target). **`flock_link`**
is the equation of channel programs, for every lawful monad and permutation.
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics

/-- **Flock's rounds** at the main line, `κ` the table's batch bits. -/
def flockRounds (κ : ℕ) : List Compose.RoundSpec :=
  [⟨false, 0, 3 + κ⟩, ⟨false, 8, 0⟩] ++ List.replicate (11 + κ) ⟨false, 2, 0⟩ ++ [⟨false, 2, 0⟩] ++
    List.replicate 8 ⟨false, 2, 0⟩ ++ [⟨false, 64, 5⟩]

/-- **The code's result from the rounds' reads**: `τ`'s sampled coordinates, the coset values,
`z`, the zerocheck's rounds, `v_a`, `v_b`, `α`, the lincheck's rounds, the slices and the ring map. -/
def flockOut (sampled coset : List E) (z : E) (zc : Done) (vA vB alpha : E) (lc : Done)
    (slices map : List E) : List E × Option Flock.End × Flock.Pending :=
  let zr := decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ coset) z)
    ((Flock.fixedChallenges ++ sampled).map some) zc
  let lr := decodeSC (vA + alpha * vB + epow alpha 2 * (zr.2 + vA * vB) + epow alpha 3)
    (List.replicate 8 none) lc
  (lr.1.reverse ++ (zr.1.drop 3).drop 8, some (.ring map (Flock.towerTarget slices map)),
    Flock.Pending.new (some z) (zr.1.take 3) ((zr.1.drop 3).take 8) lr.1.reverse alpha lr.2 (some slices))

/-- **The result from the transcript**: its rounds read by position. -/
def outOf (κ : ℕ) (d : Done) : List E × Option Flock.End × Flock.Pending :=
  flockOut (rd d 0).2 (rd d 1).1.2 ((rd d 1).2.headD 0) ((d.drop 2).take (11 + κ))
    ((rd (d.drop (13 + κ)) 0).1.2.getD 0 0) ((rd (d.drop (13 + κ)) 0).1.2.getD 1 0)
    ((rd (d.drop (13 + κ)) 0).2.headD 0) ((d.drop (14 + κ)).take 8) (rd (d.drop (22 + κ)) 0).1.2
    (rd (d.drop (22 + κ)) 0).2

/-- **Flock's front as a chain program.** -/
def flockProg (κ : ℕ) : ChainProg (List E × Option Flock.End × Flock.Pending) where
  rounds := flockRounds κ
  zeros _ _ := []
  tail := 0
  tailZeros _ _ := []
  out d _ := outOf κ d

theorem flockProg_root (κ : ℕ) : ∀ s ∈ (flockProg κ).rounds, s.root = false := by
  intro s hs
  simp only [flockProg, flockRounds, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hs
  aesop

theorem flockProg_tail (κ : ℕ) : (flockProg κ).tail = 0 := rfl

/-- The transcript's segments. -/
theorem drop_shape {κ : ℕ} (r0 r1 r4 r6 : UMsg × List E) (zc lc : Done) (hzc : zc.length = 11 + κ)
    (hlc : lc.length = 8) :
    (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop 2 = zc ++ r4 :: (lc ++ [r6]) ∧
      (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (13 + κ) = r4 :: (lc ++ [r6]) ∧
      (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (14 + κ) = lc ++ [r6] ∧
      (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (22 + κ) = [r6] := by
  have h13 : (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (13 + κ) = r4 :: (lc ++ [r6]) := by
    rw [show 13 + κ = 2 + (11 + κ) by omega, ← List.drop_drop]
    exact List.drop_left' hzc
  have h14 : (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (14 + κ) = lc ++ [r6] := by
    rw [show 14 + κ = (13 + κ) + 1 by omega, ← List.drop_drop, h13]
    rfl
  refine ⟨rfl, h13, h14, ?_⟩
  rw [show 22 + κ = (14 + κ) + 8 by omega, ← List.drop_drop, h14]
  exact List.drop_left' hlc

theorem outOf_shape {κ : ℕ} (r0 r1 r4 r6 : UMsg × List E) (zc lc : Done) (hzc : zc.length = 11 + κ)
    (hlc : lc.length = 8) :
    outOf κ (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))) =
      flockOut r0.2 r1.1.2 (r1.2.headD 0) zc (r4.1.2.getD 0 0) (r4.1.2.getD 1 0) (r4.2.headD 0) lc
        r6.1.2 r6.2 := by
  obtain ⟨h2, h13, h14, h22⟩ := drop_shape (κ := κ) r0 r1 r4 r6 zc lc hzc hlc
  rw [outOf, h2, h13, h14, h22, List.take_left' hzc, List.take_left' hlc]
  rfl

/-! ## The link -/

section Link

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem nextScalars_zero : nextScalars (m := m) 0 = pure [] := by
  simp [nextScalars_eq, repeatM]

theorem nextScalars_two :
    nextScalars (m := m) 2 = (do
      let a ← nextScalar (m := m)
      let b ← nextScalar (m := m)
      pure [a, b]) := by
  simp [nextScalars_eq, repeatM]

theorem length_fixedChallenges : Flock.fixedChallenges.length = 7 := rfl

/-- The chain program runs its rounds' reads, then reads off the result. -/
theorem flockProg_run (κ : ℕ) (F : KeccakState → m KeccakState) :
    (flockProg κ).run F = (fun d ↦ outOf κ d) <$> readRounds F (flockRounds κ) := by
  rw [ChainProg.run, runRounds_eq (flockProg κ) F (fun _ _ ↦ rfl) _ (flockProg_root κ) []]
  simp [flockProg, ChainProg.requireZeros, nextScalars_eq, repeatM]

/-- **The code-level link**: `Flock.verifyDeferred` at `14 + κ` variables, main line, is the chain
program `flockProg κ`, for every lawful monad and permutation. -/
theorem flock_link (κ : ℕ) (F : KeccakState → m KeccakState) :
    Flock.verifyDeferred F (blake2sR1csLogSize + κ) flockMain = (flockProg κ).run F := by
  rw [flockProg_run]
  have h4 : blake2sR1csLogSize + κ - 3 - Flock.nFixed = 4 + κ := by
    simp only [blake2sR1csLogSize, Flock.nFixed]; omega
  have h11 : Flock.fixedChallenges.length + (4 + κ) = 11 + κ := by
    rw [length_fixedChallenges]; omega
  have h3 : 3 + κ + 1 = 4 + κ := by omega
  have h8 : Flock.lincheckRounds = 8 := rfl
  have hp : Flock.packing - 3 = 3 := rfl
  have hk : Flock.kBits = 64 := rfl
  have hr : Flock.ringMapShifts.length = 6 := rfl
  have h23 : (2 : ℕ) ^ 3 = 8 := rfl
  have h24 : (2 : ℕ) ^ (3 + 1) = 16 := rfl
  have h51 : 5 + 1 = 6 := rfl
  -- The code: its loops as reads, the zerocheck's coordinates fitted to their count.
  simp only [Flock.verifyDeferred, Flock.front, Flock.zerocheck, Flock.ringEnd, flockMain, h4,
    show (3 : ℕ) > 0 from by decide, ite_true, h8, hp, hk, hr, h23, h24, reduceCtorEq, ite_false]
  conv_lhs => rw [samples_fit F (4 + κ)]
  simp only [sumcheck_eq, sumcheckR_eq, List.length_map, List.length_append, length_fitL, h11,
    List.length_replicate, map_bind, bind_map_left, bind_assoc, pure_bind, map_pure]
  -- The program: its rounds' reads.
  conv_rhs => simp only [flockRounds, readRounds_append, readRounds, readRound, h3, List.append_assoc,
    List.cons_append, List.singleton_append, List.nil_append, bind_assoc, pure_bind, map_bind,
    bind_map_left, map_pure, nextScalars_zero, nextScalars_two, Nat.zero_add, h51, samples_one]
  conv_rhs => rw [samples_fit F (4 + κ)]
  -- Both: the sumchecks' rounds fitted to their counts, then the result read off.
  rw [readRounds_fit_replicate F (11 + κ), readRounds_fit_replicate F 8]
  simp only [bind_map_left, outOf_shape, length_fitN, List.headD_cons, List.getD_cons_zero,
    List.getD_cons_succ, flockOut]

end Link

end FlockSound.Uni
