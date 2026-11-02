-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Real

/-!
# Monad morphisms

The statement's prover and its pieces (`formal/Statement`, mumbai's runners) are written over a
permutation `F` in any monad. Reading such a program through a **monad morphism** `φ : m → n` (pure
and bind preserved) is the same program over `φ ∘ F` (`ProverBridgeParam.lean`, one lemma per
function). Two morphisms are used: running an oracle computation with an implementation
(`simHom`, `simulateQ`), and reading a computation of `Id` in any monad (`idHom`, `pure`).

* `MHom.app_map`, `MHom.app_mapM_list`, `MHom.app_mapM_array`: the morphism through `map` and the
  traversals;
* `MHom.app_simulateQ`: a morphism after a simulation is the simulation by the morphism's image
  of the implementation;
* `simulateQ_pure_eq`: an implementation that answers every query purely runs a computation as
  `pure` of its run in `Id`.
-/

open OracleComp OracleSpec

namespace PcsQuotient.EndToEnd

/-- **A monad morphism**: a map of computations preserving `pure` and `bind`. -/
structure MHom (m n : Type → Type) [Monad m] [Monad n] where
  app : {α : Type} → m α → n α
  app_pure : ∀ {α : Type} (a : α), app (pure a) = pure a
  app_bind : ∀ {α β : Type} (x : m α) (f : α → m β), app (x >>= f) = app x >>= fun a ↦ app (f a)

namespace MHom

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] (φ : MHom m n)

theorem app_map {α β : Type} (f : α → β) (x : m α) : φ.app (f <$> x) = f <$> φ.app x := by
  rw [map_eq_bind_pure_comp, φ.app_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_apply, φ.app_pure]
  rfl

theorem app_seqRight {α β : Type} (x : m α) (y : m β) : φ.app (x *> y) = φ.app x *> φ.app y := by
  rw [seqRight_eq_bind, φ.app_bind, seqRight_eq_bind]

theorem app_mapM_list {α β : Type} (f : α → m β) :
    ∀ l : List α, φ.app (l.mapM f) = l.mapM fun a ↦ φ.app (f a)
  | [] => by simp only [List.mapM_nil, φ.app_pure]
  | a :: l => by
    simp only [List.mapM_cons, φ.app_bind, φ.app_pure]
    refine congrArg _ (funext fun b ↦ ?_)
    rw [app_mapM_list f l]

theorem app_mapM_array {α β : Type} (f : α → m β) (a : Array α) :
    φ.app (a.mapM f) = a.mapM fun x ↦ φ.app (f x) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, φ.app_map, φ.app_mapM_list]

end MHom

/-- **Running an oracle computation with an implementation** is a monad morphism. -/
def simHom {ι : Type} {spec : OracleSpec.{0, 0} ι} {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl spec r) : MHom (OracleComp spec) r where
  app x := simulateQ impl x
  app_pure a := simulateQ_pure impl a
  app_bind x f := simulateQ_bind impl x f

@[simp] theorem simHom_app {ι : Type} {spec : OracleSpec.{0, 0} ι} {r : Type → Type} [Monad r]
    [LawfulMonad r] (impl : QueryImpl spec r) {α : Type} (x : OracleComp spec α) :
    (simHom impl).app x = simulateQ impl x := rfl

/-- **A computation of `Id`, read in any monad** (`pure` of its value) is a monad morphism. -/
def idHom (n : Type → Type) [Monad n] [LawfulMonad n] : MHom Id n where
  app x := pure x.run
  app_pure _ := rfl
  app_bind x f := by rw [pure_bind]; rfl

@[simp] theorem idHom_app (n : Type → Type) [Monad n] [LawfulMonad n] {α : Type} (x : Id α) :
    (idHom n).app x = pure x.run := rfl

/-- **A morphism after a simulation** is the simulation by the morphism's image. -/
theorem MHom.app_simulateQ {ι : Type} {spec : OracleSpec.{0, 0} ι} {m n : Type → Type} [Monad m]
    [Monad n] [LawfulMonad m] [LawfulMonad n] (φ : MHom m n) (impl : QueryImpl spec m) {α : Type}
    (X : OracleComp spec α) :
    φ.app (simulateQ impl X) = simulateQ (fun t ↦ φ.app (impl t)) X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure, φ.app_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, φ.app_bind, ih]

/-- **An implementation that answers purely** runs a computation as `pure` of its run in `Id`. -/
theorem simulateQ_pure_eq {ι : Type} {spec : OracleSpec.{0, 0} ι} {n : Type → Type} [Monad n]
    [LawfulMonad n] (g : QueryImpl spec Id) {α : Type} (X : OracleComp spec α) :
    simulateQ (fun t ↦ (pure (g t).run : n _)) X = pure (simulateQ g X).run :=
  ((idHom n).app_simulateQ g X).symm

end PcsQuotient.EndToEnd
