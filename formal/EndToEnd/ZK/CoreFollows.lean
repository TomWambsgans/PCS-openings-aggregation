-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The verifier's program (`verifyStackedOpening`, `verifyWhir`, `whirLevels`, `foldRounds`,
-- `tailRounds`, `sampleQueriesAux`, `sumcheckRoundPoly`, `glue`, `ladder`) is leanerVM's (branch
-- `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/LeanVmVerifier.lean`); its monad laws
-- (`Prog.bind_assoc`) are `lean_vm/LeanVM/Protocol/Compile/Prog.lean`'s.
import ZK.CoreEv
import LeanVM.Protocol.Compile.Prog

/-!
# The verifier's program follows the skeleton's events

`Follows evs P` (`ZK/CoreEv.lean`): the program `P` makes the moves of the events `evs`. Here, for any
WHIR ladder (`whirEv`: the events of `whirLevels` level by level), **`follows_verifyStackedOpening`**:
the opening's program (`verifyStackedOpening` at rate `1/2`) follows `[draw, send 2] ++ whirEv`.

The proof composes the program's pieces along `bind` (`followsK_bind`, `follows_bind`: a piece that
ends in a return hands its value and the position draws to the rest): a sample is a draw,
`sumcheckRoundPoly` two reads, `foldRounds` rounds, the out-of-domain sample `m` draws and three reads,
`sampleQueriesAux` position draws whose positions are the draws' windows (`eToNat` of a challenge is
its three limbs' number), grinding a `17`-bit proof of work, the query the commitment's opening at those
positions, `tailRounds` the last rounds.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open QuotientZk.Deployed (positionsOf)

namespace PcsQuotient.EndToEnd.Core

open Render (limbsOf roundsEv oodEv)

set_option linter.unusedSectionVars false

/-! ## Following with a value -/

/-- **`P` follows the events and returns**: then `Q` holds of its value and the position draws. -/
def FollowsK {α : Type} : List Render.Ev → Prog α → List QuotientRpm.Limbs →
    (α → List QuotientRpm.Limbs → Prop) → Prop
  | [], P, pl, Q => ∃ a, P = .ret a ∧ Q a pl
  | .draw :: evs, P, pl, Q => ∃ k, P = .sample k ∧ ∀ c, FollowsK evs (k c) pl Q
  | .posDraw :: evs, P, pl, Q =>
    ∃ k, P = .sample k ∧ ∀ c, FollowsK evs (k c) (pl ++ [limbsOf c]) Q
  | .send n :: evs, P, pl, Q => FollowsReads n P fun R ↦ FollowsK evs R pl Q
  | .commit d :: evs, P, pl, Q => ∃ w k, P = .commit d w k ∧ FollowsK evs k pl Q
  | .grind :: evs, P, pl, Q => ∃ k, P = .grind 17 k ∧ FollowsK evs k pl Q
  | .opened lvl q b :: evs, P, pl, Q =>
    ∃ k, P = .query lvl (posOf pl b q) k ∧ ∀ rows, FollowsK evs (k rows) [] Q

theorem followsReads_mono {α : Type} {K K' : Prog α → Prop} (h : ∀ R, K R → K' R) :
    ∀ (n : ℕ) (P : Prog α), FollowsReads n P K → FollowsReads n P K'
  | 0, _, hP => h _ hP
  | n + 1, _, ⟨k, hk, hP⟩ => ⟨k, hk, fun x ↦ followsReads_mono h n _ (hP x)⟩

theorem followsReads_bind {α β : Type} {K : Prog α → Prop} {K' : Prog β → Prop} (f : α → Prog β)
    (h : ∀ R, K R → K' (R.bind f)) :
    ∀ (n : ℕ) (P : Prog α), FollowsReads n P K → FollowsReads n (P.bind f) K'
  | 0, _, hP => h _ hP
  | n + 1, _, ⟨k, hk, hP⟩ => by
    subst hk
    exact ⟨_, rfl, fun x ↦ followsReads_bind f h n _ (hP x)⟩

/-- Reads in two steps are reads in one. -/
theorem followsReads_add {α : Type} (K : Prog α → Prop) :
    ∀ (a b : ℕ) (P : Prog α), FollowsReads a P (fun R ↦ FollowsReads b R K) → FollowsReads (a + b) P K
  | 0, b, P, h => by rw [Nat.zero_add]; exact h
  | a + 1, b, P, ⟨k, hk, hP⟩ => by
    rw [Nat.add_right_comm]
    exact ⟨k, hk, fun x ↦ followsReads_add K a b _ (hP x)⟩

/-- **A piece that returns, then the rest.** -/
theorem followsK_bind {α β : Type} (f : α → Prog β) (evs' : List Render.Ev)
    (Q : α → List QuotientRpm.Limbs → Prop) (Q' : β → List QuotientRpm.Limbs → Prop)
    (hf : ∀ a pl', Q a pl' → FollowsK evs' (f a) pl' Q') :
    ∀ (evs : List Render.Ev) (P : Prog α) (pl : List QuotientRpm.Limbs), FollowsK evs P pl Q →
      FollowsK (evs ++ evs') (P.bind f) pl Q'
  | [], _, pl, ⟨a, rfl, ha⟩ => hf a pl ha
  | .draw :: evs, _, pl, ⟨k, rfl, hk⟩ => ⟨_, rfl, fun c ↦ followsK_bind f evs' Q Q' hf evs _ pl (hk c)⟩
  | .posDraw :: evs, _, pl, ⟨k, rfl, hk⟩ =>
    ⟨_, rfl, fun c ↦ followsK_bind f evs' Q Q' hf evs _ _ (hk c)⟩
  | .send n :: evs, P, pl, h =>
    followsReads_bind f (fun R hR ↦ followsK_bind f evs' Q Q' hf evs R pl hR) n P h
  | .commit d :: evs, _, pl, ⟨w, k, rfl, hk⟩ =>
    ⟨w, _, rfl, followsK_bind f evs' Q Q' hf evs _ pl hk⟩
  | .grind :: evs, _, pl, ⟨k, rfl, hk⟩ => ⟨_, rfl, followsK_bind f evs' Q Q' hf evs _ pl hk⟩
  | .opened lvl q b :: evs, _, pl, ⟨k, rfl, hk⟩ =>
    ⟨_, rfl, fun rows ↦ followsK_bind f evs' Q Q' hf evs _ [] (hk rows)⟩

/-- **A piece that returns, then a program following the rest.** -/
theorem follows_bind {α β : Type} (f : α → Prog β) (evs' : List Render.Ev)
    (Q : α → List QuotientRpm.Limbs → Prop)
    (hf : ∀ a pl', Q a pl' → Follows evs' (f a) pl') :
    ∀ (evs : List Render.Ev) (P : Prog α) (pl : List QuotientRpm.Limbs), FollowsK evs P pl Q →
      Follows (evs ++ evs') (P.bind f) pl
  | [], _, pl, ⟨a, rfl, ha⟩ => hf a pl ha
  | .draw :: evs, _, pl, ⟨k, rfl, hk⟩ => ⟨_, rfl, fun c ↦ follows_bind f evs' Q hf evs _ pl (hk c)⟩
  | .posDraw :: evs, _, pl, ⟨k, rfl, hk⟩ =>
    ⟨_, rfl, fun c ↦ follows_bind f evs' Q hf evs _ _ (hk c)⟩
  | .send n :: evs, P, pl, h =>
    followsReads_bind f (fun R hR ↦ follows_bind f evs' Q hf evs R pl hR) n P h
  | .commit d :: evs, _, pl, ⟨w, k, rfl, hk⟩ => ⟨w, _, rfl, follows_bind f evs' Q hf evs _ pl hk⟩
  | .grind :: evs, _, pl, ⟨k, rfl, hk⟩ => ⟨_, rfl, follows_bind f evs' Q hf evs _ pl hk⟩
  | .opened lvl q b :: evs, _, pl, ⟨k, rfl, hk⟩ =>
    ⟨_, rfl, fun rows ↦ follows_bind f evs' Q hf evs _ [] (hk rows)⟩

theorem followsK_mono {α : Type} {Q Q' : α → List QuotientRpm.Limbs → Prop}
    (h : ∀ a pl, Q a pl → Q' a pl) (evs : List Render.Ev) (P : Prog α) (pl : List QuotientRpm.Limbs)
    (hP : FollowsK evs P pl Q) : FollowsK evs P pl Q' := by
  have := followsK_bind (fun a ↦ Prog.ret a) [] Q Q' (fun a pl' ha ↦ ⟨a, rfl, h a pl' ha⟩) evs P pl hP
  rwa [List.append_nil, Prog.bind_ret] at this

/-! ## The pieces -/

theorem followsK_sample (pl : List QuotientRpm.Limbs) :
    FollowsK [.draw] Prog.sampleChallenge pl fun _ pl' ↦ pl' = pl :=
  ⟨_, rfl, fun _ ↦ ⟨_, rfl, rfl⟩⟩

theorem followsReads_readScalars {β : Type} (K : Prog β → Prop) :
    ∀ (n : ℕ) (gg : List E → Prog β), (∀ xs, K (gg xs)) →
      FollowsReads n ((Prog.readScalars n).bind gg) K
  | 0, gg, h => h []
  | n + 1, gg, h => by
    show FollowsReads (n + 1) ((Prog.readScalar.bind fun x ↦ (Prog.readScalars n).bind
      fun xs ↦ Prog.ret (x :: xs)).bind gg) K
    rw [Prog.bind_assoc]
    refine ⟨_, rfl, fun x ↦ ?_⟩
    show FollowsReads n (((Prog.readScalars n).bind fun xs ↦ Prog.ret (x :: xs)).bind gg) K
    rw [Prog.bind_assoc]
    exact followsReads_readScalars K n _ fun xs ↦ h (x :: xs)

theorem followsK_readScalars (n : ℕ) (pl : List QuotientRpm.Limbs) :
    FollowsK [.send n] (Prog.readScalars n) pl fun _ pl' ↦ pl' = pl := by
  have h := followsReads_readScalars (fun R ↦ FollowsK [] R pl fun _ pl' ↦ pl' = pl) n Prog.ret
    fun xs ↦ ⟨xs, rfl, rfl⟩
  rwa [Prog.bind_ret] at h

theorem followsK_sumcheckRoundPoly (claim : E) (pl : List QuotientRpm.Limbs) :
    FollowsK [.send 2] (sumcheckRoundPoly 3 claim none) pl fun _ pl' ↦ pl' = pl :=
  ⟨_, rfl, fun _ ↦ ⟨_, rfl, fun _ ↦ ⟨_, rfl, rfl⟩⟩⟩

theorem followsK_sampleChallenges : ∀ (m : ℕ) (pl : List QuotientRpm.Limbs),
    FollowsK (List.replicate m .draw) (Prog.sampleChallenges m) pl fun _ pl' ↦ pl' = pl
  | 0, pl => ⟨_, rfl, rfl⟩
  | m + 1, pl => by
    show FollowsK (.draw :: List.replicate m .draw) ((Prog.sampleChallenge.bind fun x ↦
      (Prog.sampleChallenges m).bind fun xs ↦ Prog.ret (x :: xs))) pl _
    refine ⟨_, rfl, fun c ↦ ?_⟩
    have h := followsK_bind (fun xs ↦ Prog.ret (c :: xs)) [] (fun _ pl' ↦ pl' = pl)
      (fun _ pl' ↦ pl' = pl) (fun a pl' h ↦ ⟨_, rfl, h⟩) _ _ pl (followsK_sampleChallenges m pl)
    rwa [List.append_nil] at h

/-- `foldRounds`: `n` rounds, the folds grown by `n`. -/
theorem followsK_foldRounds : ∀ (n : ℕ) (s : WhirState) (lf : List E) (pl : List QuotientRpm.Limbs),
    FollowsK (roundsEv n) (foldRounds n s lf) pl
      fun r pl' ↦ pl' = pl ∧ r.1.folds.length = s.folds.length + n
  | 0, s, lf, pl => ⟨_, rfl, rfl, rfl⟩
  | n + 1, s, lf, pl => by
    refine ⟨_, rfl, fun c ↦ ?_⟩
    have h := followsK_bind (fun quad ↦ foldRounds n { s with quad, folds := s.folds ++ [c] }
        (lf ++ [c])) (roundsEv n) (fun _ pl' ↦ pl' = pl)
      (fun r pl' ↦ pl' = pl ∧ r.1.folds.length = s.folds.length + (n + 1))
      (fun quad pl' hpl ↦ by
        subst hpl
        refine followsK_mono (fun r pl'' h ↦ ⟨h.1, ?_⟩) _ _ _ (followsK_foldRounds n _ _ pl')
        rw [h.2]
        simp only [List.length_append, List.length_singleton]
        omega) [.send 2] (sumcheckRoundPoly 3 (polyEval s.quad c) none) pl
        (followsK_sumcheckRoundPoly _ pl)
    exact h

/-- `tailRounds (m + 1)`: `m` rounds, then a draw. -/
theorem followsK_tailRounds : ∀ (m : ℕ) (quad : List E) (pl : List QuotientRpm.Limbs),
    FollowsK (roundsEv m ++ [.draw]) (tailRounds (m + 1) quad) pl fun _ pl' ↦ pl' = pl
  | 0, quad, pl => ⟨_, rfl, fun _ ↦ ⟨_, rfl, rfl⟩⟩
  | m + 1, quad, pl => by
    refine ⟨_, rfl, fun c ↦ ?_⟩
    show FollowsK (.send 2 :: (roundsEv m ++ [.draw]))
      ((sumcheckRoundPoly 3 (polyEval quad c) none).bind fun quad' ↦
        (tailRounds (m + 1) quad').bind fun r ↦ Prog.ret (c :: r.1, r.2)) pl _
    refine followsK_bind _ _ (fun _ pl' ↦ pl' = pl) _ (fun quad' pl' hpl ↦ ?_) [.send 2] _ pl
      (followsK_sumcheckRoundPoly _ pl)
    subst hpl
    have h := followsK_bind (fun r ↦ Prog.ret (c :: r.1, r.2)) [] (fun _ pl'' ↦ pl'' = pl')
      (fun _ pl'' ↦ pl'' = pl') (fun _ _ h ↦ ⟨_, rfl, h⟩) _ _ pl' (followsK_tailRounds m quad' pl')
    rwa [List.append_nil] at h

/-! ## The query positions -/

/-- The draws `sampleQueriesAux depth fuel remaining` takes. -/
def nDraws (depth : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, remaining =>
    if remaining = 0 then 0 else nDraws depth fuel (remaining - min (192 / depth) remaining) + 1

theorem kToNat_eq (a : K) : kToNat a = (K.lane a).toNat := rfl

/-- `eToNat` of a challenge is its limbs' number. -/
theorem eToNat_eq (c : E) : eToNat c =
    (limbsOf c).1.toNat + 2 ^ 64 * (limbsOf c).2.1.toNat + 2 ^ 128 * (limbsOf c).2.2.toNat := rfl

theorem chunk_eq (depth : ℕ) (c : E) (n : ℕ) (hn : n ≤ 192 / depth) :
    (List.range n).map (fun i ↦ (eToNat c >>> (i * depth)) % 2 ^ depth) =
      (positionsOf depth (limbsOf c)).take n := by
  unfold positionsOf
  rw [← List.map_take, List.take_range, min_eq_left hn, eToNat_eq]
  refine List.map_congr_left fun i _ ↦ ?_
  rw [Nat.shiftRight_eq_div_pow]

theorem length_positionsOf (b : ℕ) (x : QuotientRpm.Limbs) : (positionsOf b x).length = 192 / b := by
  simp [positionsOf]

/-- **`sampleQueriesAux`: position draws, the positions their windows.** -/
theorem followsK_sampleQueriesAux (depth : ℕ) (hd : 1 ≤ depth) (hd' : depth ≤ 192) :
    ∀ (fuel remaining : ℕ) (pl : List QuotientRpm.Limbs), remaining ≤ fuel →
    FollowsK (List.replicate (nDraws depth fuel remaining) .posDraw)
      (sampleQueriesAux depth fuel remaining) pl
      fun qs pl' ↦ ∃ new, pl' = pl ++ new ∧ qs = (new.flatMap (positionsOf depth)).take remaining
  | 0, remaining, pl, hr => by
    have : remaining = 0 := by omega
    subst this
    exact ⟨_, rfl, [], by simp, by simp⟩
  | fuel + 1, remaining, pl, hr => by
    by_cases h0 : remaining = 0
    · subst h0
      exact ⟨_, rfl, [], by simp, by simp⟩
    have hpos : 1 ≤ 192 / depth := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    rw [nDraws, if_neg h0, List.replicate_succ]
    show FollowsK (.posDraw :: List.replicate (nDraws depth fuel
        (remaining - min (192 / depth) remaining)) .posDraw)
      (sampleQueriesAux depth (fuel + 1) remaining) pl _
    unfold sampleQueriesAux
    rw [if_neg h0]
    refine ⟨_, rfl, fun c ↦ ?_⟩
    have h := followsK_bind (fun rest ↦ Prog.ret ((List.range (min (192 / depth) remaining)).map
        (fun i ↦ (eToNat c >>> (i * depth)) % 2 ^ depth) ++ rest)) []
      (fun qs pl' ↦ ∃ new, pl' = (pl ++ [limbsOf c]) ++ new ∧
        qs = (new.flatMap (positionsOf depth)).take (remaining - min (192 / depth) remaining))
      (fun qs pl' ↦ ∃ new, pl' = pl ++ new ∧
        qs = (new.flatMap (positionsOf depth)).take remaining)
      (fun rest pl' ⟨new, hpl, hq⟩ ↦ ⟨_, rfl, limbsOf c :: new, by rw [hpl]; simp, by
        rw [hq, chunk_eq depth c _ (min_le_left _ _), List.flatMap_cons, List.take_append,
          length_positionsOf]
        congr 1
        · rcases le_total remaining (192 / depth) with hle | hle
          · rw [min_eq_right hle]
          · rw [min_eq_left hle, List.take_of_length_le (by rw [length_positionsOf]),
              List.take_of_length_le (by rw [length_positionsOf]; exact hle)]
        · congr 1
          omega⟩) _ _ (pl ++ [limbsOf c])
      (followsK_sampleQueriesAux depth hd hd' fuel _ _ (by omega))
    rwa [List.append_nil] at h

end PcsQuotient.EndToEnd.Core
