-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The model (`RandomPermutationOracles`, `runWithRandomPermutation`, `queryPermutation`,
-- `keccak256OverPermutation`) is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/RandomPermutation.lean`, `common/Common/WithHash.lean`).
import ZK.ProverBridgeEager
import ZK.ProverBridgeSkel
import ZK.ProverBridgeParam
import ZK.Format

/-!
# The prover bridge from a fixed permutation

`ProverBridge` (`ZK/Real.lean`) compares two games of the random-permutation model at fixed coins: the
statement's prover then the distinguisher, and the skeleton's prover `proverJ` then `fmt` then the
distinguisher. Drawn first (`ProverBridgeEager.lean`), the permutation `π` makes both deterministic
but for the skeleton's private completions:

* the statement's prover with `π` is `proverDet π`, its run in `Id` (`sim_prover`: the prover reads
  `π` through any monad morphism, `ProverBridgeParam.lean`);
* the skeleton's prover with `π` outputs, for some completions `gH`, `gF`, `skelDet P (Gof (kDet π) π
  gH gF) s skel` (`mem_support_proverJ`), Keccak-256 over `π` being `kDet π`;
* `fmt` with `π` is `fmtDet π`.

**`proverBridge_of_det`**: if, for every permutation `π` and completions, `fmtDet` of the skeleton's
proof is the statement's proof whenever the statement's prover makes one (`hcore`, a statement about
programs, no probability left), then `ProverBridge` holds with `εR Q = δ`, `δ` any bound on the
probability that the statement's prover makes no proof (`hnone`: a proof of work exhausting its
`2^25` nonces, or the reduction rejecting its own challenges). The distinguisher's queries, the
repeated queries (the chain replayed by `reduceWith`, the wiring tree built twice, `fmt`'s), the order of
the queries and the skeleton's grinding past `2^25` cost nothing.
-/

open OracleComp OracleSpec Common
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open QuotientZk.DRpm (implJ proverJ coinR zkGameRpmD)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto)
open Eager (St permImpl frac)

set_option linter.unusedSectionVars false

/-! ## The deterministic runs -/

/-- `π` in `Id`. -/
def permId (π : Equiv.Perm St) : St → Id St := fun x ↦ pure (π x)

/-- **The statement's prover against the permutation `π`**: its run in `Id`. -/
def proverDet (π : Equiv.Perm St) (stmt : Statement) (w : Secret)
    (c : Masks × Padding × Padding) : Option Proof :=
  (prover (permId π) stmt w c).run

/-- **Keccak-256 over `π`**, its 32 bytes. -/
def kDet (π : Equiv.Perm St) (m : List UInt8) : DigestBytes :=
  Digest.toBytes (keccak256With (permId π) m).run

/-- `π` and `π⁻¹` in `Id`. -/
def permOnly (π : Equiv.Perm St) : QueryImpl PermSpec Id
  | .forward x => pure (π x)
  | .inverse y => pure (π.symm y)

/-- **`fmt` against `π`.** -/
def fmtDet (π : Equiv.Perm St) (stmt : Statement) (pf : QuotientZk.Deployed.Proof) : Option Proof :=
  (simulateQ (permOnly π) (fmt stmt pf)).run

/-! ## The games with `π` drawn -/

theorem sim_queryPermutation (π : Equiv.Perm St) (x : St) :
    simulateQ (permImpl π) (queryPermutation x) = pure (π x) := by
  simp only [queryPermutation, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map]
  rfl

theorem sim_prover (π : Equiv.Perm St) (stmt : Statement) (w : Secret)
    (c : Masks × Padding × Padding) :
    simulateQ (permImpl π) (prover queryPermutation stmt w c) = pure (proverDet π stmt w c) := by
  have h1 := Param.prover_hom (simHom (permImpl π)) queryPermutation stmt w c
  have h2 := Param.prover_hom (idHom ProbComp) (permId π) stmt w c
  simp only [simHom_app, sim_queryPermutation] at h1
  simp only [idHom_app] at h2
  rw [h1]
  exact h2.symm

theorem sim_keccak (π : Equiv.Perm St) (m : List UInt8) :
    simulateQ (permImpl π) (keccak256OverPermutation m) = pure (kDet π m) := by
  unfold keccak256OverPermutation
  have h1 := Param.keccak256With_hom (simHom (permImpl π)) queryPermutation m
  have h2 := Param.keccak256With_hom (idHom ProbComp) (permId π) m
  simp only [simHom_app, sim_queryPermutation] at h1
  simp only [idHom_app] at h2
  rw [simulateQ_map, h1]
  have e : (fun x ↦ (pure (π x) : ProbComp St)) = fun x ↦ pure (permId π x).run := rfl
  rw [e, ← h2, map_pure]
  rfl

theorem sim_proverJ {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (π : Equiv.Perm St) (s : S)
    {β : Type} (skel : OracleComp DSpec β) :
    simulateQ (permImpl π) (proverJ P keccak256OverPermutation queryPermutation (coinR KSt)
        (coinR DigestBytes) s skel) =
      proverJ P (fun m ↦ pure (kDet π m)) (fun x ↦ pure (π x))
        (simulateQ (permImpl π) (coinR KSt)) (simulateQ (permImpl π) (coinR DigestBytes)) s skel := by
  rw [QuotientZk.DRpm.simulateQ_proverJ]
  simp only [sim_keccak, sim_queryPermutation]

theorem sim_permQuery_query (π : Equiv.Perm St) (q : PermSpec.Domain) :
    simulateQ (permImpl π) (QuotientZk.permQuery q) = pure (permOnly π q).run := by
  rcases q with x | y <;>
    simp only [QuotientZk.permQuery, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map] <;> rfl

/-- **A computation of `π` and `π⁻¹`, with `π` drawn**, is its run in `Id`. -/
theorem sim_permQuery (π : Equiv.Perm St) {α : Type} (X : OracleComp PermSpec α) :
    simulateQ (permImpl π) (simulateQ QuotientZk.permQuery X) =
      pure (simulateQ (permOnly π) X).run := by
  have h := (simHom (permImpl π)).app_simulateQ QuotientZk.permQuery X
  simp only [simHom_app] at h
  rw [h]
  simp only [sim_permQuery_query]
  exact simulateQ_pure_eq (permOnly π) X

/-! ## The bridge -/

/-- The event of a bit. -/
theorem prEvent_bind_true {α : Type} (mx : ProbComp α) (g : α → ProbComp Bool) :
    Pr{let b ← mx >>= g}[b = true] = prEvent (mx >>= fun a ↦ (fun b ↦ b = true) <$> g a) := by
  rw [← map_bind]

/-- **The prover bridge from programs**: if for every permutation `π` and completions the formatted
skeleton's proof is the statement's prover's whenever that makes one (`hcore`), the prover bridge
holds with `εR Q = δ`, `δ` a bound on the statement's prover making no proof (`hnone`). -/
theorem proverBridge_of_det {S : Type} [SampleableType S] (stmt : Statement) (w : Secret)
    (P : Proto S Inp Out Msg Tbl Pos) (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (coinsOf : S → Masks × Padding × Padding) (δ : ℝ≥0∞)
    (hcore : ∀ (s : S) (π : Equiv.Perm St) (gH : List UInt8 → KSt) (gF : KSt → DigestBytes)
      (x : Proof), proverDet π stmt w (coinsOf s) = some x →
        fmtDet π stmt (skelDet P (Gof (kDet π) π gH gF) s skel) = some x)
    (hnone : ∀ s : S,
      Pr{let r ← runWithRandomPermutation (prover queryPermutation stmt w (coinsOf s))}[r = none] ≤ δ) :
    ProverBridge stmt w P skel (fmt stmt) coinsOf (fun _ ↦ δ) := by
  intro D₀ Q _ s
  let Bad : Equiv.Perm St → Prop := fun π ↦ (proverDet π stmt w (coinsOf s)).isNone = true
  have hc := Eager.close_of_perm
    (prover queryPermutation stmt w (coinsOf s) >>= fun pf ↦ simulateQ liftPerm (D₀ pf))
    (zkGameRpmD P skel (fun pf ↦ fmt stmt pf >>= D₀) s) Bad ?_
  · refine hc.mono ?_
    have hfrac : Pr{let r ← runWithRandomPermutation (prover queryPermutation stmt w (coinsOf s))}[
        r = none] = frac Bad := by
      refine Eager.prEvent_eq_frac _ _ Bad fun π ↦ ?_
      rw [sim_prover]
      classical
      rw [prEvent_pure]
      simp only [Bad, Option.isNone_iff_eq_none]
    rw [← hfrac]
    exact hnone s
  · intro π hπ
    simp only [Bad, Option.isNone_iff_eq_none] at hπ
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hπ
    -- the statement's side
    have hL : simulateQ (permImpl π)
        (prover queryPermutation stmt w (coinsOf s) >>= fun pf ↦ simulateQ liftPerm (D₀ pf)) =
        simulateQ (permImpl π) (simulateQ QuotientZk.permQuery (D₀ (some x))) := by
      rw [simulateQ_bind, sim_prover, pure_bind, hx]
      rfl
    -- the skeleton's side
    have hR : simulateQ (permImpl π) (zkGameRpmD P skel (fun pf ↦ fmt stmt pf >>= D₀) s) =
        proverJ P (fun m ↦ pure (kDet π m)) (fun x ↦ pure (π x))
          (simulateQ (permImpl π) (coinR KSt)) (simulateQ (permImpl π) (coinR DigestBytes)) s skel
          >>= fun pf ↦ simulateQ (permImpl π)
            (simulateQ QuotientZk.permQuery (D₀ (fmtDet π stmt pf))) := by
      unfold zkGameRpmD
      rw [simulateQ_bind, sim_proverJ]
      refine bind_congr fun pf ↦ ?_
      rw [simulateQ_bind, simulateQ_bind, sim_permQuery, pure_bind]
      rfl
    rw [hL, hR, prEvent_bind_true]
    rw [OracleComp.prEvent_bind_congr_of_support _ _
      (fun _ ↦ (fun b ↦ b = true) <$>
        simulateQ (permImpl π) (simulateQ QuotientZk.permQuery (D₀ (some x)))) ?_]
    · rw [OracleComp.prEvent_bind_const]
    · intro pf hpf
      obtain ⟨gH, gF, rfl⟩ := mem_support_proverJ P (kDet π) π _ _ s skel pf hpf
      rw [hcore s π gH gF x hx]

end PcsQuotient.EndToEnd

/--
info: 'PcsQuotient.EndToEnd.proverBridge_of_det' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.proverBridge_of_det
