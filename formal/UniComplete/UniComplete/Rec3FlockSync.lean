-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `FlockProverSync.lean` to π1-rec3: the
-- verifier is `Rec3VerifierH.lean`'s `verifyWalkedFsH … .rec3` (`formal/UniStatement/UniStatement/Rec.lean`'s
-- `Flock.verifyWalkedFs` with Keccak-256 an explicit call), the prover `Rec3Prover.lean`'s `flockProve3`.
import UniComplete.Rec3FlockShape
import UniComplete.FlockProverSync

/-!
# π1-rec3's Flock prover and `verifyWalkedFsH … .rec3` in step: `FlockSyncs3`

**`flockSyncs3`**: at a pure Keccak-256 `H`, for every variant with the slices sent and every writer, π1-rec3's walked
verifier `verifyWalkedFsH (pure ∘ H) log_n variant .rec3`, on a channel synchronised with the prover's writer, reads
back the prover's messages, draws the same challenges, collects **one** value, the walk's zero `walkZero3 H log_n
variant q w` (`requireZero (walkedTerminal … + r_lc)`, a verifier-only step), and returns `(out.point, out.end_)`, the
channel synchronised after (`Rec3FlockDefs.lean`'s `FlockSyncs3`). Piece by piece, the main line's
(`FlockProverSync.lean`) but where π1-rec3 differs:

* `syncs_drawRun3`: the zerocheck's draw, `drawRunH .rec3` (one `sampleH`, then `squares`) against `drawRunW` (one
  `sampleW`, then `squares`), nothing drawn for an empty run;
* `syncs_zerocheck3`, `syncs_front3`: `FlockP.syncs_zerocheck`, `FlockP.syncs_front` with that draw; the rounds are the
  main line's (`FlockP.syncs_zcRounds`, `FlockP.syncs_lcRounds`);
* `syncs_requireZero_then`: the walk's `requireZero`, the verifier's alone (the prover writes nothing), collects its
  value (`syncs_requireZero`);
* `syncs_ringEnd3`: the ring switch's end, returned as it is (the main line's `FlockP.syncs_ringEnd` returns it
  wrapped in `some`).

The verifier's programs are unfolded by `simp only` with their join points inlined, never evaluated; the walk's
terminal (`walkedTerminal`, a loop over `2^14` positions) is never unfolded: the value collected is matched with
`walkZero3` by its definition (`walkZero3_eq'`, `rfl`), before the slices are rewritten.
-/

namespace UniComplete.Rec3

open UniStatement UniStatement.Flock LeanVM.Parameters LeanVM.Protocol.KeccakHash

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## `Syncs` helpers -/

section Helpers

variable {α β γ δ : Type}

/-- The collected values, rewritten. -/
theorem syncs_congr_zs {v : ChanM Id α} {p : WrM Id β} {w : Wr} {a : α} {zs zs' : List E} (h : Syncs v p w a zs)
    (e : zs = zs') : Syncs v p w a zs' := e ▸ h

/-- **A first step that collects nothing**: the bind lemma with the first step's values empty. -/
theorem syncs_bind_nil {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {w : Wr} {a : α}
    {c : γ} {zs : List E} (h1 : Syncs v p w a []) (h2 : Syncs (f a) (g (p.run w).1) (p.run w).2 c zs) :
    Syncs (v >>= f) (p >>= g) w c zs :=
  syncs_congr_zs (Syncs.bind h1 h2) (List.nil_append zs)

/-- **The walk's `require_zero`**, the verifier's alone: it collects `x`, then the rest synchronises. -/
theorem syncs_requireZero_then {x : E} {f : ChanM Id γ} {g : WrM Id δ} {w : Wr} {c : γ} (h : Syncs f g w c []) :
    Syncs (requireZero (m := Id) x >>= fun _ ↦ f) g w c [x] := by
  have h2 := Syncs.bind (f := fun _ ↦ f) (g := fun _ ↦ g) (syncs_requireZero x w) h
  exact FlockP.Syncs.congr_p (syncs_congr_zs h2 (List.append_nil [x])) (pure_bind () fun _ ↦ g)

end Helpers

variable (H : List UInt8 → LeanVM.Protocol.Digest)

/-! ## The zerocheck's draw -/

/-- `drawRunH .rec3`, unfolded. -/
theorem drawRunH_rec3 (n : ℕ) :
    drawRunH (m := Id) (Pure.pure ∘ H) .rec3 n =
      if n = 0 then Pure.pure [] else (sampleH (m := Id) (Pure.pure ∘ H) >>= fun c ↦ Pure.pure (squares c n)) :=
  rfl

/-- `drawRunW`, unfolded. -/
theorem drawRunW_unfold (n : ℕ) :
    drawRunW (m := Id) (Pure.pure ∘ H) n =
      if n = 0 then Pure.pure [] else (sampleW (m := Id) (Pure.pure ∘ H) >>= fun c ↦ Pure.pure (squares c n)) :=
  rfl

/-- **The zerocheck's draw at π1-rec3**: `drawRunH .rec3` reads nothing and draws the prover's one challenge (none for
an empty run), returning its squares. -/
theorem syncs_drawRun3 (n : ℕ) (w : Wr) :
    Syncs (drawRunH (m := Id) (Pure.pure ∘ H) .rec3 n) (drawRunW (m := Id) (Pure.pure ∘ H) n) w
      ((drawRunW (m := Id) (Pure.pure ∘ H) n).run w).1 [] := by
  rw [drawRunH_rec3, drawRunW_unfold]
  by_cases hn : n = 0
  · simp only [if_pos hn]
    exact FlockP.Syncs.pure' [] [] w
  · simp only [if_neg hn]
    refine FlockP.Syncs.bind' (syncs_sample H w) ?_
    refine FlockP.Syncs.congr_a (FlockP.Syncs.pure' _ _ _) ?_
    simp only [FlockP.run_bind_id, FlockP.run_pure_id, sampleW_run]

/-! ## The zerocheck, the front, the ring switch's end -/

/-- **The zerocheck at π1-rec3**: the run of squares, the coset values and `z` (with a skip), the rounds, `v_a`,
`v_b`. -/
theorem syncs_zerocheck3 (logN k : ℕ) (wit : FlockP.Wit) (w : Wr) :
    Syncs (zerocheckFsH (m := Id) (Pure.pure ∘ H) logN k .rec3) (zerocheckW3 (m := Id) (Pure.pure ∘ H) logN k wit) w
      (((zerocheckW3 (m := Id) (Pure.pure ∘ H) logN k wit).run w).1.1,
        ((zerocheckW3 (m := Id) (Pure.pure ∘ H) logN k wit).run w).1.2.1,
        ((zerocheckW3 (m := Id) (Pure.pure ∘ H) logN k wit).run w).1.2.2.1,
        ((zerocheckW3 (m := Id) (Pure.pure ∘ H) logN k wit).run w).1.2.2.2.1,
        ((zerocheckW3 (m := Id) (Pure.pure ∘ H) logN k wit).run w).1.2.2.2.2) [] := by
  by_cases hk : 0 < k
  · have hk' : (k > 0) = True := eq_true hk
    unfold zerocheckFsH zerocheckW3 FlockP.skipW
    simp only [hk', ↓reduceIte, bind_assoc, pure_bind, FlockP.sumcheckH_eq, FlockP.startAt]
    refine FlockP.Syncs.bind' (syncs_drawRun3 H (logN - k - nFixed) w) ?_
    refine FlockP.Syncs.bind' (FlockP.syncs_scalars' (FlockP.cosetValues k (fixedChallenges ++
      ((drawRunW (m := Id) (Pure.pure ∘ H) (logN - k - nFixed)).run w).1) wit) (2 ^ k)
      (FlockP.cosetValues_length _ _ _) _) ?_
    refine FlockP.Syncs.bind' (syncs_sample H _) ?_
    refine FlockP.Syncs.bind' (FlockP.syncs_zcRounds H (fixedChallenges ++
      ((drawRunW (m := Id) (Pure.pure ∘ H) (logN - k - nFixed)).run w).1) _ _ _ _ _) ?_
    refine FlockP.Syncs.bind' (syncs_scalar _ _) ?_
    refine FlockP.Syncs.bind' (syncs_scalar _ _) ?_
    refine FlockP.Syncs.congr_a (FlockP.Syncs.pure' _ _ _) ?_
    simp only [FlockP.run_bind_id, FlockP.run_pure_id, sampleW_run]
  · have hk' : (k > 0) = False := eq_false hk
    unfold zerocheckFsH zerocheckW3 FlockP.skipW
    simp only [hk', ↓reduceIte, bind_assoc, pure_bind, FlockP.sumcheckH_eq, FlockP.startNone]
    refine FlockP.Syncs.bind' (syncs_drawRun3 H (logN - k - nFixed) w) ?_
    refine FlockP.Syncs.bind' (FlockP.syncs_zcRounds H (fixedChallenges ++
      ((drawRunW (m := Id) (Pure.pure ∘ H) (logN - k - nFixed)).run w).1) 0 wit.a wit.b wit.c
      ((drawRunW (m := Id) (Pure.pure ∘ H) (logN - k - nFixed)).run w).2) ?_
    refine FlockP.Syncs.bind' (syncs_scalar _ _) ?_
    refine FlockP.Syncs.bind' (syncs_scalar _ _) ?_
    refine FlockP.Syncs.congr_a (FlockP.Syncs.pure' _ _ _) ?_
    simp only [FlockP.run_bind_id, FlockP.run_pure_id, sampleW_run]

/-- **The front at π1-rec3**: the zerocheck, `α`, the lincheck, the slices; the verifier's `Front` is the prover's. -/
theorem syncs_front3 (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (hc : variant.slices ≠ .claim) :
    Syncs (frontFsH (m := Id) (Pure.pure ∘ H) logN variant .rec3) (frontW3 (m := Id) (Pure.pure ∘ H) logN variant q)
      w ((frontW3 (m := Id) (Pure.pure ∘ H) logN variant q).run w).1.1 [] := by
  have hc' : (variant.slices = .claim) = False := eq_false hc
  unfold frontFsH frontW3 FlockP.sendSlices
  simp only [hc', ↓reduceIte, bind_assoc, pure_bind, FlockP.sumcheckH_eq, map_eq_bind_pure_comp]
  refine FlockP.Syncs.bind' (syncs_zerocheck3 H logN variant.skip (FlockP.witOf logN q) w) ?_
  refine FlockP.Syncs.bind' (syncs_sample H _) ?_
  simp only [sampleW_run, FlockP.lcClaim]
  refine FlockP.Syncs.bind' (FlockP.syncs_lcRounds H lincheckRounds _
    (FlockP.lcWeightsOf variant.skip
      ((zerocheckW3 (m := Id) (Pure.pure ∘ H) logN variant.skip (FlockP.witOf logN q)).run w).1
      (Wr.sampled H ((zerocheckW3 (m := Id) (Pure.pure ∘ H) logN variant.skip (FlockP.witOf logN q)).run w).2).1)
    (FlockP.lcWitnessOf variant.skip q
      ((zerocheckW3 (m := Id) (Pure.pure ∘ H) logN variant.skip (FlockP.witOf logN q)).run w).1)
    (Wr.sampled H ((zerocheckW3 (m := Id) (Pure.pure ∘ H) logN variant.skip (FlockP.witOf logN q)).run w).2).2) ?_
  refine FlockP.Syncs.bind' (FlockP.syncs_scalars' _ kBits (FlockP.lcRounds_z_length H _ _ _ _ _ _) _) ?_
  refine FlockP.Syncs.congr_a (FlockP.Syncs.pure' _ _ _) ?_
  simp only [FlockP.run_bind_id, FlockP.run_pure_id, sampleW_run, FlockP.frontOf]

/-- **The ring switch's end**: the map's `6` challenges, the target, returned as it is. -/
theorem syncs_ringEnd3 (variant : Variant) (s : List E) (w : Wr) :
    Syncs (Flock.ringEndH (m := Id) (Pure.pure ∘ H) variant s) (FlockP.ringEndW (m := Id) (Pure.pure ∘ H) variant s) w
      ((FlockP.ringEndW (m := Id) (Pure.pure ∘ H) variant s).run w).1 [] := by
  unfold Flock.ringEndH FlockP.ringEndW
  simp only [bind_assoc, pure_bind]
  refine FlockP.Syncs.bind' (syncs_samples H ringMapShifts.length w) ?_
  refine FlockP.Syncs.congr_a (FlockP.Syncs.pure' _ _ _) ?_
  simp only [FlockP.run_bind_id, FlockP.run_pure_id]

/-! ## `FlockSyncs3` -/

/-- `walkZero3`, unfolded (the walk's terminal itself left folded). -/
theorem walkZero3_eq' (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) :
    walkZero3 H logN variant q w =
      walkedTerminal ((frontW3 (m := Id) (Pure.pure ∘ H) logN variant q).run w).1.1.zSkip
          ((frontW3 (m := Id) (Pure.pure ∘ H) logN variant q).run w).1.1.rowLow
          ((frontW3 (m := Id) (Pure.pure ∘ H) logN variant q).run w).1.1.chiIn
          ((frontW3 (m := Id) (Pure.pure ∘ H) logN variant q).run w).1.1.chiInPrime
          (((frontW3 (m := Id) (Pure.pure ∘ H) logN variant q).run w).1.1.slices.getD [])
          ((frontW3 (m := Id) (Pure.pure ∘ H) logN variant q).run w).1.1.alpha +
        ((frontW3 (m := Id) (Pure.pure ∘ H) logN variant q).run w).1.1.rLc :=
  rfl

/-- **`FlockSyncs3` of π1-rec3's honest Flock prover** (`Rec3FlockDefs.lean`'s statement): at a pure Keccak-256,
every `log_n`, every variant with the slices sent, every writer; the value collected is the walk's zero on the
prover's front, `walkZero3`. -/
theorem flockSyncs3 (logN : ℕ) (variant : Variant) (q : Array K) (hc : variant.slices ≠ .claim) :
    FlockSyncs3 H (flockProve3 (m := Id) (Pure.pure ∘ H)) logN variant q (walkZero3 H logN variant q) := by
  intro w
  have hsl := frontW3_slices (Pure.pure ∘ H) logN variant q w hc
  rw [walkZero3_eq' H logN variant q w]
  unfold verifyWalkedFsH flockProve3
  refine syncs_bind_nil (syncs_front3 H logN variant q w hc) ?_
  refine syncs_requireZero_then ?_
  -- `rw`, not `simp`, for `getD`: `simp` uses the `rfl` lemma as a definitional step, and the kernel's check of
  -- `(some s).getD [] ≡ s` then reduces the projections of the prover's run (deep recursion).
  rw [hsl, Option.getD_some]
  simp only [FlockP.endW]
  refine FlockP.Syncs.bind' (syncs_ringEnd3 H variant _ _) ?_
  refine FlockP.Syncs.congr_a (FlockP.Syncs.pure' _ _ _) ?_
  simp only [FlockP.run_bind_id, FlockP.run_pure_id, hsl, FlockP.endW, FlockP.assemble]

end UniComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniComplete.Rec3.syncs_drawRun3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.syncs_drawRun3

/-- info: 'UniComplete.Rec3.syncs_front3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.syncs_front3

/-- info: 'UniComplete.Rec3.flockSyncs3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.flockSyncs3
