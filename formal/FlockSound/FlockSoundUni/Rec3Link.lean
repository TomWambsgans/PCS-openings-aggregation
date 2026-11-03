-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The verifier (`Flock.verifyWalkedFs` at `.rec3`) is
-- `formal/UniStatement`'s `Rec.lean`, transcribed from `crates/leanvm_flock_gas/src/flock_min.rs` (`verify_walked`).
import FlockSoundUni.Link
import UniStatement.Rec

/-!
# π1-rec3's Flock front as a chain program, and its code-level link

`Flock.verifyWalkedFs F (14 + κ) flockMain .rec3` (skip `3`, the slices sent, the ring map in tower order, the
zerocheck's coordinates after the seven fixed ones the squares of one challenge, the lincheck's terminal walked) is
the chain program `flockProg3 κ` (no root, no tail), whose `23 + κ` rounds are the main line's but the first:

* `⟨false, 0, 0⟩`: **one** challenge `c`; the zerocheck point's `4 + κ` sampled coordinates are `squares c (4 + κ)`;
* `⟨false, 8, 0⟩`, `11 + κ` zerocheck rounds, `v_a, v_b` then `α`, `8` lincheck rounds: the main line's;
* `⟨false, 64, 5⟩`: the `64` slices, **the walk's zero** (`walkOf`: `walkedTerminal … + r_lc`, required before the
  ring map's challenges), then the ring map's six challenges.

The result (`outOf3`) is the code's, the point and the ring switch's end. **The main line's reading** of a
transcript is `outOf κ (expandFd κ d)`: the first round's challenge written out as its squares (`expandFd`), read by
the main line's `outOf` (point, end, pending); its point and end are `outOf3`'s (`outOf_expandFd`). **`flock_link3`**
is the equation of channel programs, for every lawful monad and permutation.
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics

/-- **π1-rec3's Flock rounds before the slices**: the squares' one challenge, the coset values, the zerocheck's
rounds, `v_a, v_b`, the lincheck's rounds. -/
def flockRounds3Pre (κ : ℕ) : List Compose.RoundSpec :=
  [⟨false, 0, 0⟩, ⟨false, 8, 0⟩] ++ List.replicate (11 + κ) ⟨false, 2, 0⟩ ++ [⟨false, 2, 0⟩] ++
    List.replicate 8 ⟨false, 2, 0⟩

/-- **π1-rec3's Flock rounds**, `κ` the table's batch bits. -/
def flockRounds3 (κ : ℕ) : List Compose.RoundSpec := flockRounds3Pre κ ++ [⟨false, 64, 5⟩]

theorem length_flockRounds3Pre (κ : ℕ) : (flockRounds3Pre κ).length = 22 + κ := by
  simp only [flockRounds3Pre, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem length_flockRounds3 (κ : ℕ) : (flockRounds3 κ).length = 23 + κ := by
  rw [flockRounds3, List.length_append, length_flockRounds3Pre, List.length_singleton]
  omega

/-- **The walk's zero from the rounds' reads**: the zerocheck's and the lincheck's sumchecks decoded (as `flockOut`),
then `walkedTerminal` at the front's skip point, row point, lincheck point, `α` and slices, plus `r_lc`. -/
def flockWalk (sampled coset : List E) (z : E) (zc : Done) (vA vB alpha : E) (lc : Done) (slices : List E) : E :=
  let zr := decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ coset) z)
    ((Flock.fixedChallenges ++ sampled).map some) zc
  let lr := decodeSC (vA + alpha * vB + epow alpha 2 * (zr.2 + vA * vB) + epow alpha 3)
    (List.replicate 8 none) lc
  Flock.walkedTerminal (some z) (zr.1.take 3) ((zr.1.drop 3).take 8) lr.1.reverse slices alpha + lr.2

/-- **The walk's zero from the transcript** before the slices' round, and the slices. -/
def walkOf (κ : ℕ) (d : Done) (slices : List E) : E :=
  flockWalk (squares ((rd d 0).2.headD 0) (4 + κ)) (rd d 1).1.2 ((rd d 1).2.headD 0) ((d.drop 2).take (11 + κ))
    ((rd (d.drop (13 + κ)) 0).1.2.getD 0 0) ((rd (d.drop (13 + κ)) 0).1.2.getD 1 0)
    ((rd (d.drop (13 + κ)) 0).2.headD 0) ((d.drop (14 + κ)).take 8) slices

/-- **The code's result from the rounds' reads**: the point (the main line's `flockOut`'s, at the squares) and the
ring switch's end. -/
def flockOut3 (sampled coset : List E) (z : E) (zc : Done) (vA vB alpha : E) (lc : Done)
    (slices map : List E) : List E × Flock.End :=
  ((flockOut sampled coset z zc vA vB alpha lc slices map).1, .ring map (Flock.towerTarget slices map))

/-- **The result from the transcript.** -/
def outOf3 (κ : ℕ) (d : Done) : List E × Flock.End :=
  flockOut3 (squares ((rd d 0).2.headD 0) (4 + κ)) (rd d 1).1.2 ((rd d 1).2.headD 0) ((d.drop 2).take (11 + κ))
    ((rd (d.drop (13 + κ)) 0).1.2.getD 0 0) ((rd (d.drop (13 + κ)) 0).1.2.getD 1 0)
    ((rd (d.drop (13 + κ)) 0).2.headD 0) ((d.drop (14 + κ)).take 8) (rd (d.drop (22 + κ)) 0).1.2
    (rd (d.drop (22 + κ)) 0).2

/-- **π1-rec3's Flock front as a chain program**: its one zero the walk's, in the slices' round. -/
def flockProg3 (κ : ℕ) : ChainProg (List E × Flock.End) where
  rounds := flockRounds3 κ
  zeros d msg := if d.length = 22 + κ then [walkOf κ d msg.2] else []
  tail := 0
  tailZeros _ _ := []
  out d _ := outOf3 κ d

theorem flockProg3_root (κ : ℕ) : ∀ s ∈ (flockProg3 κ).rounds, s.root = false := by
  intro s hs
  simp only [flockProg3, flockRounds3, flockRounds3Pre, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hs
  aesop

theorem flockProg3_tail (κ : ℕ) : (flockProg3 κ).tail = 0 := rfl

theorem length_squares : ∀ (c : E) (n : ℕ), (squares c n).length = n
  | _, 0 => rfl
  | c, n + 1 => by simp [squares, length_squares (c * c) n]

/-! ## The main line's reading -/

/-- **The transcript as the main line's**: the first round's challenge written out as its `4 + κ` squares. -/
def expandFd (κ : ℕ) : Done → Done
  | [] => []
  | (m, c) :: d => (m, squares (c.headD 0) (4 + κ)) :: d

theorem rd_expandFd_succ (κ : ℕ) (d : Done) (a : ℕ) : rd (expandFd κ d) (a + 1) = rd d (a + 1) := by
  cases d <;> rfl

theorem drop_expandFd (κ : ℕ) (d : Done) (a : ℕ) : (expandFd κ d).drop (a + 1) = d.drop (a + 1) := by
  cases d <;> rfl

theorem rd_expandFd_zero (κ : ℕ) (d : Done) (h : d ≠ []) :
    (rd (expandFd κ d) 0).2 = squares ((rd d 0).2.headD 0) (4 + κ) := by
  cases d with
  | nil => exact absurd rfl h
  | cons x d => rfl

/-- **The main line's reading has the program's point and end.** -/
theorem outOf_expandFd (κ : ℕ) (d : Done) (h : d ≠ []) :
    (outOf κ (expandFd κ d)).1 = (outOf3 κ d).1 ∧
      (outOf κ (expandFd κ d)).2.1 = some (outOf3 κ d).2 := by
  have e : outOf κ (expandFd κ d) = flockOut (squares ((rd d 0).2.headD 0) (4 + κ)) (rd d 1).1.2
      ((rd d 1).2.headD 0) ((d.drop 2).take (11 + κ))
      ((rd (d.drop (13 + κ)) 0).1.2.getD 0 0) ((rd (d.drop (13 + κ)) 0).1.2.getD 1 0)
      ((rd (d.drop (13 + κ)) 0).2.headD 0) ((d.drop (14 + κ)).take 8) (rd (d.drop (22 + κ)) 0).1.2
      (rd (d.drop (22 + κ)) 0).2 := by
    rw [outOf, rd_expandFd_zero κ d h, rd_expandFd_succ, drop_expandFd,
      show 13 + κ = (12 + κ) + 1 by omega, drop_expandFd, show 14 + κ = (13 + κ) + 1 by omega, drop_expandFd,
      show 22 + κ = (21 + κ) + 1 by omega, drop_expandFd]
  rw [e]
  exact ⟨rfl, rfl⟩

/-! ## The link -/

section Link

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem runRounds_append {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) :
    ∀ (a b : List Compose.RoundSpec) (done : Done),
      P.runRounds F (a ++ b) done = (P.runRounds F a done >>= fun d ↦ P.runRounds F b d)
  | [], b, done => by simp [ChainProg.runRounds]
  | s :: a, b, done => by
    cases h : s.root <;> simp [ChainProg.runRounds, h, bind_assoc, runRounds_append P F a b]

/-- **A chain program's rounds without roots, before its first zero, are their reads and draws.** -/
theorem runRounds_eq_of {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) (n : ℕ)
    (hz : ∀ done msg, done.length < n → P.zeros done msg = []) :
    ∀ (rs : List Compose.RoundSpec), (∀ s ∈ rs, s.root = false) → ∀ done : Done, done.length + rs.length ≤ n →
      P.runRounds F rs done = (fun d ↦ done ++ d) <$> readRounds F rs
  | [], _, done, _ => by simp [ChainProg.runRounds, readRounds]
  | s :: rs, hr, done, hl => by
    have hs : s.root = false := hr s (List.mem_cons_self ..)
    have hlt : done.length < n := by simp at hl; omega
    simp only [ChainProg.runRounds, hs, Bool.false_eq_true, ite_false, pure_bind, hz done _ hlt,
      ChainProg.requireZeros, readRounds, readRound, bind_assoc, map_bind]
    congr 1
    funext vals
    congr 1
    funext chs
    rw [runRounds_eq_of P F n hz rs (fun s hs ↦ hr s (List.mem_cons_of_mem _ hs)) _
      (by simp at hl ⊢; omega)]
    simp

/-- **The program runs its reads before the slices, the slices, the walk's zero, the ring map's draws**, then reads
off the result. -/
theorem flockProg3_run (κ : ℕ) (F : KeccakState → m KeccakState) :
    (flockProg3 κ).run F = (do
      let d ← readRounds F (flockRounds3Pre κ)
      let vals ← nextScalars (m := m) 64
      requireZero (m := m) (walkOf κ d vals)
      let chs ← samples F 6
      pure (outOf3 κ (d ++ [((none, vals), chs)]))) := by
  have hpre := runRounds_eq_of (flockProg3 κ) F (22 + κ)
    (fun done msg h ↦ by simp only [flockProg3]; rw [ite_eq_right (by omega)]) (flockRounds3Pre κ)
    (fun s hs ↦ flockProg3_root κ s (List.mem_append_left _ hs)) [] (by simp [length_flockRounds3Pre])
  rw [ChainProg.run, show (flockProg3 κ).rounds = flockRounds3Pre κ ++ [⟨false, 64, 5⟩] from rfl,
    runRounds_append, hpre]
  conv_lhs => rw [readRounds_fit F (flockRounds3Pre κ)]
  conv_rhs => rw [readRounds_fit F (flockRounds3Pre κ)]
  simp only [bind_map_left, bind_assoc, List.nil_append]
  congr 1
  funext d
  simp [ChainProg.runRounds, ChainProg.requireZeros, flockProg3, length_fitN, length_flockRounds3Pre,
    nextScalars_zero]

theorem walkOf_shape {κ : ℕ} (r0 r1 r4 : UMsg × List E) (zc lc : Done) (hzc : zc.length = 11 + κ)
    (hlc : lc.length = 8) (slices : List E) :
    walkOf κ (r0 :: r1 :: (zc ++ r4 :: lc)) slices =
      flockWalk (squares (r0.2.headD 0) (4 + κ)) r1.1.2 (r1.2.headD 0) zc (r4.1.2.getD 0 0) (r4.1.2.getD 1 0)
        (r4.2.headD 0) lc slices := by
  have h13 : (r0 :: r1 :: (zc ++ r4 :: lc)).drop (13 + κ) = r4 :: lc := by
    rw [show 13 + κ = 2 + (11 + κ) by omega, ← List.drop_drop]
    exact List.drop_left' hzc
  have h14 : (r0 :: r1 :: (zc ++ r4 :: lc)).drop (14 + κ) = lc := by
    rw [show 14 + κ = (13 + κ) + 1 by omega, ← List.drop_drop, h13]
    rfl
  have h2 : (r0 :: r1 :: (zc ++ r4 :: lc)).drop 2 = zc ++ r4 :: lc := rfl
  rw [walkOf, h2, h13, h14, List.take_left' hzc, List.take_of_length_le (l := lc) (by omega)]
  rfl

theorem outOf3_shape {κ : ℕ} (r0 r1 r4 r6 : UMsg × List E) (zc lc : Done) (hzc : zc.length = 11 + κ)
    (hlc : lc.length = 8) :
    outOf3 κ (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))) =
      flockOut3 (squares (r0.2.headD 0) (4 + κ)) r1.1.2 (r1.2.headD 0) zc (r4.1.2.getD 0 0) (r4.1.2.getD 1 0)
        (r4.2.headD 0) lc r6.1.2 r6.2 := by
  obtain ⟨h2, h13, h14, h22⟩ := drop_shape (κ := κ) r0 r1 r4 r6 zc lc hzc hlc
  rw [outOf3, h2, h13, h14, h22, List.take_left' hzc, List.take_left' hlc]
  rfl

/-- **The code-level link**: `Flock.verifyWalkedFs` at `14 + κ` variables, π1-rec3, is the chain program
`flockProg3 κ`, for every lawful monad and permutation. -/
theorem flock_link3 (κ : ℕ) (F : KeccakState → m KeccakState) :
    Flock.verifyWalkedFs F (blake2sR1csLogSize + κ) flockMain .rec3 = (flockProg3 κ).run F := by
  rw [flockProg3_run]
  have h4 : blake2sR1csLogSize + κ - 3 - Flock.nFixed = 4 + κ := by
    simp only [blake2sR1csLogSize, Flock.nFixed]; omega
  have h0 : (4 + κ = 0) = False := by simp
  have h11 : Flock.fixedChallenges.length + (4 + κ) = 11 + κ := by
    rw [length_fixedChallenges]; omega
  have h8 : Flock.lincheckRounds = 8 := rfl
  have hp : Flock.packing - 3 = 3 := rfl
  have hk : Flock.kBits = 64 := rfl
  have hr : Flock.ringMapShifts.length = 6 := rfl
  have h23 : (2 : ℕ) ^ 3 = 8 := rfl
  have h24 : (2 : ℕ) ^ (3 + 1) = 16 := rfl
  have h51 : 5 + 1 = 6 := rfl
  simp only [Flock.verifyWalkedFs, Flock.frontFs, Flock.zerocheckFs, drawRun, Flock.ringEnd, flockMain, h4, h0,
    ite_false, show (3 : ℕ) > 0 from by decide, ite_true, h8, hp, hk, hr, h23, h24, reduceCtorEq]
  simp only [sumcheck_eq, sumcheckR_eq, List.length_map, List.length_append, length_squares, h11,
    List.length_replicate, bind_map_left, bind_assoc, pure_bind]
  conv_rhs => simp only [flockRounds3Pre, readRounds_append, readRounds, readRound, List.append_assoc,
    List.cons_append, List.singleton_append, List.nil_append, bind_assoc, pure_bind, map_bind,
    bind_map_left, map_pure, nextScalars_zero, nextScalars_two, Nat.zero_add, h51, samples_one]
  rw [readRounds_fit_replicate F (11 + κ), readRounds_fit_replicate F 8]
  simp only [bind_map_left, outOf3_shape, walkOf_shape, length_fitN, List.headD_cons, List.getD_cons_zero,
    List.getD_cons_succ, flockOut3, flockWalk, flockOut, Option.getD_some]

end Link

end FlockSound.Uni
