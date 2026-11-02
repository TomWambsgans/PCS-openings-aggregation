-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The run (`runFrom`), the sponge (`absorb`, `squeeze`), the proofs of work (`findNonceM`,
-- `powStepM`) and the trees (`buildTreeM`, `Tree.opening`) are leanerVM's (branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Run.lean`, `Statement/LeanVmVerifier.lean`);
-- `runEvS` is `runFrom` driven by an opening's events instead of the verifier's program.
import ZK.CoreSpec
import ZK.ProverBridgeDuplex
import ZK.ProverBridgeMerkle

/-!
# An opening's run, driven by its events

The statement's prover runs WHIR's honest script against the verifier's program (mumbai's
`runFrom`); the skeleton runs its opening as a fixed sequence of events (`Render.Ev`: draws, scalars
sent, commitments, grinding, opened rows). Here the two meet:

* **`runEvS`**: `runFrom` with the events in place of the program: a draw squeezes, `k` scalars are
  the script's next `k` sent and absorbed, a commitment builds the script's matrix's tree and absorbs
  its root, grinding is the proof-of-work search, opened rows are the trees' at the positions of the
  draws since the last opening. Besides the stream and the openings it outputs, per opening, the
  pruned multiproof the skeleton sends (`multiOf`);
* **`Follows evs P`**: the program `P` makes the moves of the events, whatever it reads or samples;
* **`runFrom_eq_runEvS`**: on a program that follows the events, `runFrom` is `runEvS`;
* **`fill_runEvS`**: `fmt`'s production (`fillRun`) on `runEvS`'s stream and multiproofs reproduces its
  openings (`expandMulti_eq`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open QuotientZk.Deployed (sortedUnique prune positionsOf)

namespace PcsQuotient.EndToEnd.Core

open Render (limbsOf)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## Following the events -/

/-- The program after reading the values `xs`, in order. -/
def afterReads {α : Type} : Prog α → List E → Prog α
  | .read k, x :: xs => afterReads (k x) xs
  | P, _ => P

theorem afterReads_nil {α : Type} (P : Prog α) : afterReads P [] = P := by
  cases P <;> rfl

/-- `P` reads `n` scalars, whatever they are, then continues as a program satisfying `K`. -/
def FollowsReads {α : Type} : ℕ → Prog α → (Prog α → Prop) → Prop
  | 0, P, K => K P
  | n + 1, P, K => ∃ k, P = .read k ∧ ∀ x, FollowsReads n (k x) K

/-- The query positions of the position draws `pl` on a tree of depth `b`: their `b`-bit windows,
the first `q`. -/
def posOf (pl : List QuotientRpm.Limbs) (b q : ℕ) : List ℕ :=
  (pl.flatMap (positionsOf (max b 1))).take q

/-- **The program makes the events' moves**: a draw is a sample, `k` scalars `k` reads, a commitment
of depth `d` a commitment of height `d`, grinding a `17`-bit proof of work, the opened rows a query of
the commitment at the positions of the position draws since the last; it ends at a return or a
rejection. -/
def Follows {α : Type} : List Render.Ev → Prog α → List QuotientRpm.Limbs → Prop
  | [], P, _ => (∃ a, P = .ret a) ∨ P = .fail
  | .draw :: evs, P, pl => ∃ k, P = .sample k ∧ ∀ c, Follows evs (k c) pl
  | .posDraw :: evs, P, pl => ∃ k, P = .sample k ∧ ∀ c, Follows evs (k c) (pl ++ [limbsOf c])
  | .send n :: evs, P, pl => FollowsReads n P fun Q ↦ Follows evs Q pl
  | .commit d :: evs, P, pl => ∃ w k, P = .commit d w k ∧ Follows evs k pl
  | .grind :: evs, P, pl => ∃ k, P = .grind 17 k ∧ Follows evs k pl
  | .opened lvl q b :: evs, P, pl =>
    ∃ k, P = .query lvl (posOf pl b q) k ∧ ∀ rows, Follows evs (k rows) []

/-! ## The statement's run on the events -/

section Run

variable (π : Equiv.Perm Eager.St) (fuel : ℕ)

/-- A tree's levels as bytes. -/
def treeBytesOf (t : Tree) : List (List QuotientRpm.Bytes32) :=
  t.levels.toList.map fun a ↦ a.toList.map Digest.toBytes

/-- **The pruned multiproof** of a tree at the positions `ps`: the sorted distinct positions, their rows
as words, `PrunedMerklePaths::prune`'s siblings. -/
def multiOf (t : Tree) (ps : List ℕ) : Multi :=
  (sortedUnique ps, (sortedUnique ps).map fun p ↦ (t.word p).map K.lane,
    prune (treeBytesOf t) (sortedUnique ps))

/-- The next `k` scalars a script sends, absorbed with tag `1`. -/
def sendsS : ℕ → Option (Script Unit) → Sponge → List E × Option (Script Unit) × Sponge
  | 0, S, sp => ([], S, sp)
  | k + 1, S, sp =>
    let r := sendsS k (Script.afterSend S) (absorb (permId π) sp (Script.msgOf S) dsObserve).run
    (Script.msgOf S :: r.1, r.2)

/-- **The statement's run driven by the events** (`runFrom` with the events for the program): the
stream, the openings and the multiproofs, or `none` when a proof of work finds no nonce below
`fuel`. -/
def runEvS : List Render.Ev → Option (Script Unit) → Sponge → List Tree → List QuotientRpm.Limbs →
    Option (List E × List Opening × List Multi)
  | [], _, _, _, _ => some ([], [], [])
  | .draw :: evs, S, sp, cs, pl =>
    let r := (squeeze (permId π) sp).run
    runEvS evs (Script.afterSample r.1 S) r.2 cs pl
  | .posDraw :: evs, S, sp, cs, pl =>
    let r := (squeeze (permId π) sp).run
    runEvS evs (Script.afterSample r.1 S) r.2 cs (pl ++ [limbsOf r.1])
  | .send k :: evs, S, sp, cs, pl =>
    let r := sendsS π k S sp
    (runEvS evs r.2.1 r.2.2 cs pl).map fun t ↦ (r.1 ++ t.1, t.2)
  | .commit d :: evs, S, sp, cs, pl =>
    let tree := (buildTreeM (permId π) d (Script.wordOf S)).run
    let sp0 := (absorb (permId π) sp (digestScalars tree.root).1 dsObserve).run
    let sp1 := (absorb (permId π) sp0 (digestScalars tree.root).2 dsObserve).run
    (runEvS evs (Script.afterCommit S) sp1 (cs ++ [tree]) pl).map fun t ↦
      ((digestScalars tree.root).1 :: (digestScalars tree.root).2 :: t.1, t.2)
  | .grind :: evs, S, sp, cs, pl =>
    match (findNonceM (permId π) 17 sp fuel).run with
    | none => none
    | some n =>
      let r := (powStepM (permId π) sp n).run
      (runEvS evs (Script.afterGrind S) r.2 cs pl).map fun t ↦ (n :: t.1, t.2)
  | .opened lvl q b :: evs, S, sp, cs, pl =>
    match cs[lvl]? with
    | none => some ([], [], [])
    | some tree =>
      let ps := posOf pl b q
      let rows := ps.map fun p ↦ tree.word (p % 2 ^ tree.height)
      (runEvS evs (Script.afterQuery rows S) sp cs []).map fun t ↦
        (t.1, ps.map tree.opening ++ t.2.1, multiOf tree ps :: t.2.2)

/-! ## `runFrom` on a program following the events -/

theorem runFrom_grind_run {α : Type} (bits : ℕ) (k : Prog α) (S : Option (Script Unit)) (sp : Sponge)
    (cs : List Tree) :
    (runFrom (permId π) fuel (.grind bits k) S sp cs).run =
      match (findNonceM (permId π) bits sp fuel).run with
      | none => none
      | some n => ((runFrom (permId π) fuel k (Script.afterGrind S) (powStepM (permId π) sp n).run.2
          cs).run).map fun (t : List E × List Opening) ↦ (n :: t.1, t.2) := by
  show (match (findNonceM (permId π) bits sp fuel).run with
    | none => (pure none : Id _)
    | some n => do
      let r ← powStepM (permId π) sp n
      let t ← runFrom (permId π) fuel k (Script.afterGrind S) r.2 cs
      pure (t.map fun (t : List E × List Opening) ↦ (n :: t.1, t.2))).run = _
  rcases (findNonceM (permId π) bits sp fuel).run with _ | n <;> rfl

theorem runEvS_grind (evs : List Render.Ev) (S : Option (Script Unit)) (sp : Sponge) (cs : List Tree)
    (pl : List QuotientRpm.Limbs) :
    runEvS π fuel (.grind :: evs) S sp cs pl =
      match (findNonceM (permId π) 17 sp fuel).run with
      | none => none
      | some n => (runEvS π fuel evs (Script.afterGrind S) (powStepM (permId π) sp n).run.2 cs
          pl).map fun t ↦ (n :: t.1, t.2) := rfl

theorem runFrom_query_run {α : Type} (i : ℕ) (ps : List ℕ) (k : List (List K) → Prog α)
    (S : Option (Script Unit)) (sp : Sponge) (cs : List Tree) :
    (runFrom (permId π) fuel (.query i ps k) S sp cs).run =
      match cs[i]? with
      | none => some ([], [])
      | some tree => ((runFrom (permId π) fuel (k (ps.map fun q ↦ tree.word (q % 2 ^ tree.height)))
          (Script.afterQuery (ps.map fun q ↦ tree.word (q % 2 ^ tree.height)) S) sp cs).run).map
          fun (t : List E × List Opening) ↦ (t.1, ps.map tree.opening ++ t.2) := by
  conv_lhs => unfold runFrom
  rcases cs[i]? with _ | tree <;> rfl

theorem runEvS_opened (lvl q b : ℕ) (evs : List Render.Ev) (S : Option (Script Unit)) (sp : Sponge)
    (cs : List Tree) (pl : List QuotientRpm.Limbs) :
    runEvS π fuel (.opened lvl q b :: evs) S sp cs pl =
      match cs[lvl]? with
      | none => some ([], [], [])
      | some tree =>
        (runEvS π fuel evs (Script.afterQuery ((posOf pl b q).map fun p ↦
            tree.word (p % 2 ^ tree.height)) S) sp cs []).map fun t ↦
          (t.1, (posOf pl b q).map tree.opening ++ t.2.1, multiOf tree (posOf pl b q) :: t.2.2) :=
  rfl

theorem runFrom_reads {α : Type} (K : Prog α → Prop) :
    ∀ (n : ℕ) (P : Prog α) (S : Option (Script Unit)) (sp : Sponge) (cs : List Tree),
      FollowsReads n P K →
      K (afterReads P (sendsS π n S sp).1) ∧
      (runFrom (permId π) fuel P S sp cs).run =
        ((runFrom (permId π) fuel (afterReads P (sendsS π n S sp).1) (sendsS π n S sp).2.1
          (sendsS π n S sp).2.2 cs).run).map fun t ↦ ((sendsS π n S sp).1 ++ t.1, t.2)
  | 0, P, S, sp, cs, h => by
    refine ⟨by rw [sendsS, afterReads_nil]; exact h, ?_⟩
    simp only [sendsS, afterReads_nil, List.nil_append]
    cases (runFrom (permId π) fuel P S sp cs).run <;> rfl
  | n + 1, P, S, sp, cs, h => by
    obtain ⟨k, rfl, hk⟩ := h
    obtain ⟨hK, hr⟩ := runFrom_reads K n (k (Script.msgOf S)) (Script.afterSend S)
      (absorb (permId π) sp (Script.msgOf S) dsObserve).run cs (hk _)
    refine ⟨hK, ?_⟩
    show ((runFrom (permId π) fuel (k (Script.msgOf S)) (Script.afterSend S)
        (absorb (permId π) sp (Script.msgOf S) dsObserve).run cs).run).map
        (fun t ↦ (Script.msgOf S :: t.1, t.2)) = _
    rw [hr, Option.map_map]
    rfl

/-- **`runFrom` on a program following the events is `runEvS`** (its stream and openings). -/
theorem runFrom_eq_runEvS : ∀ (evs : List Render.Ev) {α : Type} (P : Prog α) (S : Option (Script Unit))
    (sp : Sponge) (cs : List Tree) (pl : List QuotientRpm.Limbs), Follows evs P pl →
    (runFrom (permId π) fuel P S sp cs).run =
      (runEvS π fuel evs S sp cs pl).map fun t ↦ (t.1, t.2.1)
  | [], _, P, S, sp, cs, pl, h => by
    rcases h with ⟨a, rfl⟩ | rfl <;> rfl
  | .draw :: evs, _, P, S, sp, cs, pl, h => by
    obtain ⟨k, rfl, hk⟩ := h
    exact runFrom_eq_runEvS evs _ _ _ _ pl (hk _)
  | .posDraw :: evs, _, P, S, sp, cs, pl, h => by
    obtain ⟨k, rfl, hk⟩ := h
    exact runFrom_eq_runEvS evs _ _ _ _ _ (hk _)
  | .send n :: evs, _, P, S, sp, cs, pl, h => by
    obtain ⟨hK, hr⟩ := runFrom_reads π fuel _ n P S sp cs h
    rw [hr, runFrom_eq_runEvS evs _ _ _ _ pl hK]
    show _ = ((runEvS π fuel evs (sendsS π n S sp).2.1 (sendsS π n S sp).2.2 cs pl).map
      fun t ↦ ((sendsS π n S sp).1 ++ t.1, t.2)).map fun t ↦ (t.1, t.2.1)
    rw [Option.map_map, Option.map_map]
    rfl
  | .commit d :: evs, _, P, S, sp, cs, pl, h => by
    obtain ⟨w, k, rfl, hk⟩ := h
    show ((runFrom (permId π) fuel k (Script.afterCommit S) _ _).run).map _ = _
    rw [runFrom_eq_runEvS evs _ _ _ _ pl hk]
    show _ = ((runEvS π fuel evs _ _ _ pl).map _).map _
    rw [Option.map_map, Option.map_map]
    rfl
  | .grind :: evs, _, P, S, sp, cs, pl, h => by
    obtain ⟨k, rfl, hk⟩ := h
    rw [runFrom_grind_run, runEvS_grind]
    rcases (findNonceM (permId π) 17 sp fuel).run with _ | n
    · rfl
    · simp only
      rw [runFrom_eq_runEvS evs _ _ _ _ pl hk, Option.map_map, Option.map_map]
      rfl
  | .opened lvl q b :: evs, _, P, S, sp, cs, pl, h => by
    obtain ⟨k, rfl, hk⟩ := h
    rw [runFrom_query_run, runEvS_opened]
    rcases cs[lvl]? with _ | tree
    · rfl
    · simp only
      rw [runFrom_eq_runEvS evs _ _ _ _ [] (hk _), Option.map_map, Option.map_map]
      rfl

end Run

end PcsQuotient.EndToEnd.Core
