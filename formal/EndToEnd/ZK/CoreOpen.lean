-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The opening's prover (`proveOpeningWith`, `runFrom`) and sponge are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0) and `formal/Statement`'s.
import ZK.CoreTrees

/-!
# An opening: the statement's proof and `fmt`'s

At a deployed opening (its program following the skeleton's events, its commitments' depths, its
level-0 tree a tree of its word at its height), both sides are the statement's event-driven run
`runEvS` from the sponge after the root's two scalars:

* **`proveOpening_eq`**: the statement's opening proof (`proveOpeningWith` against `π`) is the root's
  scalars then `runEvS`'s stream, and its openings;
* **`fillOpening_eq`**: `fmt`'s production (`fillOpening` against `π`) on a stream whose limbs are the
  root's scalars then `runEvS`'s stream, and on its multiproofs, is that same proof.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover

namespace PcsQuotient.EndToEnd.Core

open Render (limbsOf)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

theorem eOfLimbs_limbsOf (x : E) : eOfLimbs (limbsOf x) = x :=
  Primitives.F192.ofLimbs_limb x

theorem map_eOfLimbs_limbsOf (l : List E) : (l.map limbsOf).map eOfLimbs = l := by
  rw [List.map_map]
  exact (List.map_congr_left fun x _ ↦ eOfLimbs_limbsOf x).trans (List.map_id l)

variable (π : Equiv.Perm Eager.St) (fuel : ℕ)

theorem sim_openingSponge (L : PcsQuotient.Layout) (cls : List PcsQuotient.Claim) :
    simulateQ (permOnly π) (openingSpongeWith permF L cls) = openingSpongeWith (permId π) L cls := by
  have h := Param.openingSpongeWith_hom (simHom (permOnly π)) permF L cls
  simp only [simHom_app, Merkle.sim_permF] at h
  exact h

/-- The sponge an opening's run starts from: the opening's, then the root's two scalars. -/
def startSponge (L : PcsQuotient.Layout) (cls : List PcsQuotient.Claim) (root : Digest) : Sponge :=
  (absorb (permId π) (absorb (permId π) (openingSpongeWith (permId π) L cls).run
    (digestScalars root).1 dsObserve).run (digestScalars root).2 dsObserve).run

/-- **The statement's opening proof** on a program following the events. -/
theorem proveOpening_eq (evs : List Render.Ev) (L : PcsQuotient.Layout) (tree : Tree)
    (stack : Array K) (cls : List PcsQuotient.Claim)
    (hF : Follows evs (verifyStackedOpening L.logN logInvRate (stackClaims L cls)) []) :
    (proveOpeningWith (permId π) fuel L tree stack cls).run =
      (runEvS π fuel evs (some (openingScript L stack cls)) (startSponge π L cls tree.root) [tree]
        []).map fun t ↦ ⟨(digestScalars tree.root).1 :: (digestScalars tree.root).2 :: t.1, t.2.1⟩ := by
  have h := runFrom_eq_runEvS π fuel evs _ (some (openingScript L stack cls))
    (startSponge π L cls tree.root) [tree] [] hF
  show ((runFrom (permId π) fuel _ _ (startSponge π L cls tree.root) [tree]).run).map _ = _
  rw [h, Option.map_map]
  rfl

/-- **`fmt`'s production of an opening** from the run's stream and multiproofs. -/
theorem fillOpening_eq (evs : List Render.Ev) (L : PcsQuotient.Layout) (tree : Tree)
    (cls : List PcsQuotient.Claim) (S : Option (Script Unit)) (str : List E) (ops : List Opening)
    (ms : List Multi)
    (hF : Follows evs (verifyStackedOpening L.logN logInvRate (stackClaims L cls)) [])
    (hH : HeightsOK evs [tree.height]) (hT : TreeOK π tree)
    (hh : tree.height = L.logN - laneFold + logInvRate)
    (hr : runEvS π fuel evs S (startSponge π L cls tree.root) [tree] [] = some (str, ops, ms)) :
    (simulateQ (permOnly π) (fillOpening L tree.root cls
        ((((digestScalars tree.root).1 :: (digestScalars tree.root).2 :: str).map limbsOf), ms))).run =
      some ⟨(digestScalars tree.root).1 :: (digestScalars tree.root).2 :: str, ops⟩ := by
  unfold fillOpening
  rw [map_eOfLimbs_limbsOf]
  simp only [simulateQ_bind, simulateQ_pure, sim_openingSponge, sim_absorbF]
  obtain ⟨st', h1, h2⟩ := fill_runEvS π fuel evs _ S (startSponge π L cls tree.root) [tree] [] str ops
    ms [] [] [(tree.root, L.logN - laneFold + logInvRate, 2 ^ laneFold)] [] hF
    (by simpa using hH) (by simpa using hT) (by simp [hh]) hr
  simp only [List.append_nil] at h1
  have h1' : (simulateQ (permOnly π) (fillRun (verifyStackedOpening L.logN logInvRate
      (stackClaims L cls)) ⟨startSponge π L cls tree.root, str, ms,
        [(tree.root, L.logN - laneFold + logInvRate, 2 ^ laneFold)], []⟩)).run = some st' := h1
  show (Option.map _ ((simulateQ (permOnly π) (fillRun _ ⟨startSponge π L cls tree.root, str, ms,
    [(tree.root, L.logN - laneFold + logInvRate, 2 ^ laneFold)], []⟩)).run)) = _
  rw [h1', Option.map_some, h2, List.nil_append]

end PcsQuotient.EndToEnd.Core
