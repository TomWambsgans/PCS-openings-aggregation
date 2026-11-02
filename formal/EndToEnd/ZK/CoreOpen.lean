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

/-! ## The skeleton's opening -/

section Skel

variable {S₀ : Type} (P : QuotientZk.Proto S₀ QuotientZk.Deployed.Inp QuotientZk.Deployed.Out
  QuotientZk.Deployed.Msg QuotientZk.Deployed.Tbl QuotientZk.Deployed.Pos)
  (gH : List UInt8 → QuotientZk.Deployed.KSt) (gF : QuotientZk.Deployed.KSt → DigestBytes) (s : S₀)

local notation "G" => Gof (kDet π) π gH gF

open Merkle (runDet_bind runDet_pure)

/-- **The skeleton's opening is the statement's run**: from the claims' bytes `cb` (the first message),
the seed related to the opening's sponge (`hseed`), the level-0 tree the statement's `tree` (of depth
`sh.depth₀`), the renderer's later messages its drive of the script `Sc` from the statement's tree
(`hmsg`), the skeleton's stream is the root's two scalars then the run's stream, its multiproofs the
run's. -/
theorem opening_eq (sh : QuotientZk.Deployed.OpenShape) (L : PcsQuotient.Layout)
    (cls : List PcsQuotient.Claim) (tree : Tree) (cb : List UInt8) (hist₀ : List QuotientZk.Deployed.Out)
    (Sc : Script Unit) (str : List E) (ops : List Opening) (ms : List Multi)
    (hfuel : fuel < 2 ^ 64) (hT : TreeOK π tree) (hd : tree.height = sh.depth₀)
    (hH : HeightsOK (Render.openingEv sh) [tree.height])
    (hL : (Render.openingEv sh).getLast? = some .draw)
    (hq : sh.levels.length ≤ (sh.queries.drop 1).length)
    (hn : hist₀.length + drawsIn (Render.openingEv sh) ≤ P.n)
    (hm0 : P.msgFn s hist₀ = [QuotientZk.Deployed.Item.bytes cb])
    (hseed : Duplex.Rel ⟨π (QuotientZk.Deployed.seedInput (kDet π (sh.ivPrefix ++ cb))), []⟩
      (openingSpongeWith (permId π) L cls).run)
    (hmsg : ∀ chs : List QuotientZk.Deployed.Out, 1 ≤ chs.length →
      chs.length < drawsIn (Render.openingEv sh) →
      P.msgFn s (hist₀ ++ chs) = Render.lastMsg (Render.evRun (Render.openingEv sh) chs
        ⟨some Sc, [(tree.height, tree.word)], [], [], []⟩))
    (hr : runEvS π fuel (Render.openingEv sh) (some Sc) (startSponge π L cls tree.root) [tree] [] =
      some (str, ops, ms)) :
    (runDet P G s (QuotientZk.Deployed.opening sh (treeBytesOf tree)) hist₀).1 =
      (((digestScalars tree.root).1 :: (digestScalars tree.root).2 :: str).map limbsOf, ms) := by
  have hroot : QuotientZk.Deployed.rootOf (treeBytesOf tree) = Digest.toBytes tree.root := by
    have h1 := Merkle.tree_root π tree.height tree.word
    rw [← Merkle.tree_levels] at h1
    unfold Merkle.treeBytes at h1
    rw [← hT] at h1
    exact h1
  obtain ⟨a1, a2⟩ := absorbAll_rel P π gH gF s [(digestScalars tree.root).1,
    (digestScalars tree.root).2] _ _ hist₀ hseed
  simp only [List.map_cons, List.map_nil] at a1 a2
  have e3 : ∀ iv, runDet P G s (QuotientZk.Deployed.seed iv) hist₀ =
      (⟨π (QuotientZk.Deployed.seedInput iv), []⟩, hist₀) := fun iv ↦ by
    unfold QuotientZk.Deployed.seed
    rw [runDet_bind, Duplex.runDet_perm, runDet_pure]
  unfold QuotientZk.Deployed.opening
  rw [runDet_bind, runDet_getMsg, hm0]
  simp only
  rw [runDet_bind, Merkle.runDet_hashH, runDet_bind, e3, runDet_bind, hroot, rootLimbs_toBytes]
  dsimp only [Gof]
  rw [a1]
  set o₀ : QuotientZk.Deployed.OSt := ⟨(runDet P G s (QuotientZk.Deployed.Dx.absorbAll ⟨π (QuotientZk.Deployed.seedInput
    (kDet π (sh.ivPrefix ++ cb))), []⟩ [limbsOf (digestScalars tree.root).1,
      limbsOf (digestScalars tree.root).2]) hist₀).1, [], [treeBytesOf tree],
    [limbsOf (digestScalars tree.root).1, limbsOf (digestScalars tree.root).2], []⟩ with ho₀
  show (runDet P G s (openTail sh o₀) hist₀).1 = _
  rw [openTail_run P G s sh o₀ (treeBytesOf tree) rfl (by
    rw [← hd]; unfold treeBytesOf; rw [List.length_map, Array.length_toList, hT];
    exact (Merkle.treeLevels_length π _ _)) hq hist₀, runDet_bind, runDet_pure]
  have hI : DriveInv o₀ ⟨some Sc, [(tree.height, tree.word)], [], [], []⟩ (some Sc)
      (startSponge π L cls tree.root) [tree] [] (Render.openingEv sh) :=
    ⟨a2, rfl, rfl, rfl, rfl, Or.inr rfl⟩
  obtain ⟨e1, e2⟩ := drive P π gH gF s fuel hfuel _ o₀ [] hist₀ _ _ [tree] _ str ops ms hI
    (by simpa using hT) (by simpa using hH) (Or.inr hL) hn hmsg hr
  rw [e1, e2]
  rfl

end Skel

end PcsQuotient.EndToEnd.Core

/-- info: 'PcsQuotient.EndToEnd.Core.opening_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.opening_eq

/-- info: 'PcsQuotient.EndToEnd.Core.fillOpening_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.fillOpening_eq
