-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (F0a/F2/F4 review).
-- Addressed: the deployed experiment now computes the circuit's commitment with the oracle before the
-- adversary runs (`Compose/Deployed.lean`, `withSetup`, `wiringSetup`); the label holds the proof's `ir`,
-- and the setup's root commits to the wiring stack (`Compose/WiringSetup.lean`, `extract_wiringSetup`).
import Compose.Final

/-!
# Review: the circuit's commitment in F4's experiment is a constant the oracle never produced

`rootExperiment W A openings` (`Compose/ListChain.lean`, and `kcExperiment` of `TwoOracle.lean` alike)
starts the random oracle from the empty cache and hashes `W.indexRoot` into the chain's label, but no
step of the experiment computes the wiring table's Merkle tree with the oracle: `W.indexRoot` is a field
of the `Wire`, fixed before the oracle is drawn. So:

* `merkleWord_eq_none_of_no_preimage`: if no input the transcript asked is answered by a root, every
  position of its Merkle word is `none` (whatever the table, the decoder sees the empty word);
* `prob_indexRoot_answered`: in `rootExperiment`, the probability that **any** query of the run (the
  adversary's, the chain's, the openings') is answered by `W.indexRoot` is at most
  `(Q + 6 + QV) / 2^256`.

Hence, except with that probability, the candidate list `merkleCommit … W.indexRoot` read off the
transcript is `dec (fun _ => none)`: a constant that does not depend on the wiring table. The planned
discharge of `hσ` ("the circuit's commitment is the setup's, honest, so its only candidate is the wiring
table", `Compose/README.md`) is impossible in this experiment; and, the deployed wiring opening checking
Merkle paths against `W.indexRoot` through the same oracle, the honest prover is (with the same
probability) not accepted in it either. The experiment needs a setup step (the index root computed by the
oracle from the wiring table, before or as the adversary runs) for `hσ` to say anything about the wiring.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose.Review

open QuotientRpm QuotientSecurity QuotientSecurity.Params Compose

theorem uniq_empty {α : Type} : uniq (∅ : Finset α) = none := rfl

/-- A root no input of the history answers has the empty Merkle word. -/
theorem merkleWord_eq_none_of_no_preimage (H : Hist) (T : Table) (height leafLen : ℕ) (r : Bytes32)
    (h : ∀ z ∈ H, T z ≠ r) (p : Fin (2 ^ height)) : merkleWord H T height leafLen r p = none := by
  have hb : ∀ n, below H T r.toList n = none := by
    intro n
    unfold below
    have : H.filter (fun z => (T z).toList = r.toList ∧ z.length = n) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun z hz hzr => h z hz (Vector.toList_inj.mp hzr.1)
    rw [this]
    rfl
  unfold merkleWord
  cases height with
  | zero => exact hb leafLen
  | succ k =>
    rw [posBits_succ_review]
    simp [leafAt, hb 64]
where
  posBits_succ_review {k : ℕ} {q : ℕ} : posBits (k + 1) q = q.testBit k :: posBits k q := by
    simp [posBits, List.range_succ]

/-- Some fresh input of a list satisfying `P` makes `FreshBad` of `P` (a predicate ignoring the
history) hold. -/
theorem freshBad_of_exists {τ : Type} (P : List UInt8 → τ → Prop) (T : τ) :
    ∀ (H : Hist) (L : List (List UInt8)), (∃ x ∈ L, x ∉ H ∧ P x T) →
      FreshBad (fun _ x T => P x T) T H L
  | _, [], ⟨_, hx, _⟩ => by simp at hx
  | H, y :: ys, ⟨x, hx, hxH, hP⟩ => by
    by_cases hy : y ∉ H ∧ P y T
    · exact Or.inl hy
    · refine Or.inr (freshBad_of_exists P T (insert y H) ys ⟨x, ?_, ?_, hP⟩)
      · rcases List.mem_cons.mp hx with rfl | h
        · exact absurd ⟨hxH, hP⟩ hy
        · exact h
      · intro hm
        rcases Finset.mem_insert.mp hm with rfl | h
        · exact hy ⟨hxH, hP⟩
        · exact hxH h

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) {O β : Type}

/-- **The index root is answered by some query of the run with probability at most
`(Q + 6 + QV) / 2^256`.** -/
theorem prob_indexRoot_answered (A : OracleComp HashSpec (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp HashSpec β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    Pr{let z ← (simulateQ randomOracle (rootExperiment W A post)).run' ∅}[
        ∃ x ∈ histOfTr z.2, tableOfTr z.2 x = W.indexRoot] ≤
      ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (1 / 2 ^ 256) := by
  classical
  refine prEvent_randomOracle_le_of_freshBad (rootExperiment W A post) (Q + 6 + QV)
    (rootExperiment_queryBound W A post Q QV hQ hV) (Set.range fun v : Bytes32 => v.toList)
    (Set.finite_range _) _ (fun _ x T => T x = W.indexRoot) _ (fun S hS c t ht hcard => ?_)
    (fun T h => ?_)
  · show Pr{let g ← $ᵗ (↥S → Bytes32)}[tableOf c g t.1 = W.indexRoot] ≤ _
    simp only [tableOf_fresh c ht]
    refine (prEvent_cell t (fun u => u = W.indexRoot)).trans ?_
    rw [SampleableType.prEvent_uniformSample, card_bytes32]
    have : (Finset.univ.filter fun u : Bytes32 => u = W.indexRoot).card = 1 := by
      rw [Finset.filter_eq' Finset.univ W.indexRoot]
      simp
    rw [this]
    simp only [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, le_refl]
  · obtain ⟨hlogE, hevalE⟩ := rootExperiment_run W A post T
    rw [hevalE] at h
    obtain ⟨x, hx, hxr⟩ := h
    simp only at hx hxr
    set tr : Transcript := (tableQueryLog (rootRun W A post) T).map fun q => (q.1, q.2)
    have hxL : x ∈ (tableQueryLog (rootRun W A post) T).map Sigma.fst := by
      simpa [histOfTr, tr, List.map_map] using hx
    have hT : tableOfTr tr x = T x := by
      refine tableOfTr_eq T tr (fun e he => ?_) x (by simpa [tr, List.map_map] using hxL)
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      exact tableQueryLog_snd T _ q hq
    rw [hlogE]
    exact freshBad_of_exists (fun x T => T x = W.indexRoot) T ∅ _
      ⟨x, hxL, Finset.notMem_empty _, hT ▸ hxr⟩

/-- **So the wiring root's candidates read off the transcript are, except with that probability,
the decoder's output on the empty word**, whatever the wiring table. -/
theorem indexRoot_cands_const (c : TableCode B.Msg₁) (tr : Transcript)
    (h : ¬ ∃ x ∈ histOfTr tr, tableOfTr tr x = W.indexRoot) :
    c.commit.cands (histOfTr tr) (tableOfTr tr) W.indexRoot = c.dec fun _ => none := by
  show c.dec _ = _
  congr 1
  funext p
  exact merkleWord_eq_none_of_no_preimage _ _ _ _ _ (fun z hz hzr => h ⟨z, hz, hzr⟩) p

end Compose.Review

#print axioms Compose.Review.prob_indexRoot_answered
#print axioms Compose.Review.indexRoot_cands_const
