-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `FsLayer128` is `Fs.lean`'s
-- `FsLayer` with the bound `uniBound128`; `hlab_uni` reads the seed of `FsGame.lean`'s two-oracle
-- game (`ivAdv`: the adversary, then the contract's IV).
import UniSound.FsGame

/-!
# The Fiat–Shamir layer at `≥ 128` bits: the bound and the seed

**`uniBound128 e Q`**, for an adversary of `Q` calls of `π` and `π⁻¹` (`N = uniN Q = 2^33 + Q`
bounds every count):

```
N (ε + 5 N / 2^256) + N (9952² e + 8 N / 2^256) + 2 N² / 2^256 + (2^81 + Q)² / 2^508,
ε = 269 · 2^-137 = 2^-128.93
```

* the openings, **once for all five** (`Compose.prEvent_doomF_le`): a fresh query extends at most
  one opening's transcript, so the doom terms are one union family's, at the exact certified
  per-group bound `ε` (`WhirBridge.εExact`: the weakest group at `2^24 ..= 2^28` has `128.95`
  bits), in place of `5 · openingBoundAt 10122 N` at `2^-128`;
* the chain, **without the seed's tag** (`Compose.knowledgeSoundness_listChainU_closed128`): the
  lists `9952² e`, the collisions `8 N / 2^256`;
* **the seed's pair** (`Compose.prEvent_pairTr_le`): the seed `name ‖ iv ‖ input` is a step's
  input only if an answer equals `name ‖ iv[0:16]`, and `iv` is an answer (the contract's IV,
  `hlab_uni`): two answers, one the other's prefix after `name`, `2 N² / 2^256`;
* the random permutation, as `uniBound`'s.

At `Q = 2^64` it is `2^-64.88` (`EndToEnd/Review/UniSoundnessNumbers128.py`, exact rationals).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-- **The univariate verifier's bound at `≥ 128` bits** at `Q` adversary calls, rounds' errors at
most `e`: the openings once at `269 · 2^-137`, the chain without the tag, the seed's pair, the
permutation. -/
noncomputable def uniBound128 (e : ℝ≥0∞) (Q : ℕ) : ℝ≥0∞ :=
  (uniN Q : ℝ≥0∞) * (269 * (2 : ℝ≥0∞)⁻¹ ^ 137 + ((5 * uniN Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (uniN Q : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) * e + ((8 * uniN Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((2 * uniN Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

/-- **The Fiat–Shamir layer at `≥ 128` bits**: `FsLayer` with the bound `uniBound128`. -/
def FsLayer128 (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V) :
    Prop :=
  ∀ (R : RbrPiop (uniRounds Fl.prog.rounds nV V) USt Stk) (e : ℝ≥0∞), (∀ j, R.err j ≤ e) →
    (∀ s c m, R.pre s [] (some c, m) → Rel D s c) →
    (∀ (s : USt) done tl c1 c2, DoneFits (uniRounds Fl.prog.rounds nV V) done → tl.length = 5 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf Fl.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch) →
    UniKnowledgeSoundness D (uniBound128 e)

/-! ## The seed is `name ‖ iv ‖ input`, the IV an answer the adversary asked -/

theorem uniLabel_take32 (s : FSt) : (uniLabel s).take 32 = name ++ s.1.toList.take 16 := by
  have hn : name.length = 16 := name_length
  unfold uniLabel
  rw [List.append_assoc, List.take_append, List.take_of_length_le (l := name) (by omega), hn,
    List.take_append_of_le_length (l₁ := s.1.toList) (by simp)]

theorem eval_ivKC (D : Deployment) (π : UPf) (T : KTable) :
    evalWithAnswerFn (QueryImpl.ofFn T) (ivKC D π) = viewT T (ivInput D π.roots) := by
  simp only [ivKC, hash256, callKeccak256, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

theorem log_ivKC (D : Deployment) (π : UPf) (T : KTable) :
    (tableQueryLog (ivKC D π) T).map Sigma.fst = [Sum.inl (ivInput D π.roots)] := by
  simp only [ivKC, hash256, callKeccak256, tableQueryLog_bind, tableQueryLog_pure]
  rfl

/-- **The seed's first 32 bytes are `name ‖ iv[0:16]`, `iv` the answer to the adversary's last
query** (`ivAdv`: the contract's IV of the proof the setup fixes): the univariate game's `hlab`. -/
theorem hlab_uni (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (hs : UniShapes D)
    (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf) (T : KTable) :
    ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG (uSetup D hs) uFix (ivAdv D A₀)) T).map
        Sigma.fst ∧
      ((uSpec Fl nV V).label (uView (uRounds Fl nV V) (evalWithAnswerFn (QueryImpl.ofFn T)
          (withSetupG (uSetup D hs) uFix (ivAdv D A₀)))).1).take 32 =
        name ++ (viewT T w).toList.take (32 - name.length) := by
  obtain ⟨hl, he⟩ := withSetupG_run (uSetup D hs) uFix (ivAdv D A₀) T
  set s := evalWithAnswerFn (QueryImpl.ofFn T) (uSetup D hs)
  set π := evalWithAnswerFn (QueryImpl.ofFn T) (A₀ s)
  refine ⟨ivInput D (uFix s π).roots, ?_, ?_⟩
  · rw [hl, List.map_append]
    refine List.mem_append_right _ ?_
    simp only [ivAdv, tableQueryLog_bind, tableQueryLog_map, List.map_append, List.mem_append]
    refine Or.inr ?_
    rw [log_ivKC]
    exact List.mem_singleton_self _
  · rw [he]
    have hev : evalWithAnswerFn (QueryImpl.ofFn T) (ivAdv D A₀ s) =
        setIv (viewT T (ivInput D (uFix s π).roots)) π := by
      simp only [ivAdv, evalWithAnswerFn_bind, evalWithAnswerFn_map, eval_ivKC]
      rfl
    rw [hev, name_length]
    show (uniLabel (uView (uRounds Fl nV V) (uFix s (setIv _ π))).1).take 32 = _
    rw [uniLabel_take32]
    rfl

end UniSound

/-- info: 'UniSound.hlab_uni' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.hlab_uni
