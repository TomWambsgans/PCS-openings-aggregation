-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The trees (`buildTreeM`, `commitWith`, `stackWordFast`) are leanerVM's (branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Run.lean`, `Statement/Prover/Ntt.lean`).
import ZK.CoreDeployed
import ZK.CoreTables

/-!
# The skeleton's level-0 trees are the statement's

Against the oracle, the skeleton's level-0 tree of an opening (`Deployed.tree₀`) is, level by level as
bytes, the statement's commitment's tree (`Merkle.treeBytes` of `commitWith`'s word):

* **`tree₀_secret`**: a secret table's, its leaves the deployed prover's rows (`PbRow`, read after the
  table's challenges), once those rows are the bytes of a word's rows (`pbRow_W`, `pbRow_Q`);
* **`tree₀_public`**: a public table's, its rows hashed (`tree₀` of the wiring shape on `rowsWD`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Prover
open QuotientZk.Deployed (Out Inp Msg Tbl Pos DSpec)

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

section Trees

variable {S₀ : Type} (P : QuotientZk.Proto S₀ (List UInt8) Out Msg Tbl Pos) (π : Equiv.Perm Eager.St)
  (gH : List UInt8 → QuotientZk.Deployed.KSt) (gF : QuotientZk.Deployed.KSt → DigestBytes) (s : S₀)

local notation "G" => Gof (kDet π) π gH gF

open Merkle (runDet_bind runDet_pure)

theorem runDet_leafH (k : Tbl) (x : ℕ) (hist : List Out) (hk : P.cK k ≤ hist.length) :
    runDet (QuotientZk.DRpm.ofBytes P) G s (QuotientZk.Deployed.leafH k x) hist =
      (kDet π (P.rowFn s (hist.take (P.cK k)) k ⟨x % 2 ^ 23, Nat.mod_lt _ (by positivity)⟩), hist) := by
  unfold QuotientZk.Deployed.leafH
  rw [runDet_query_bind, runDet_pure]
  have hk' : ¬ hist.length < (QuotientZk.DRpm.ofBytes P).cK k := not_lt.mpr hk
  simp only [implDet, StateT.run, hk', ↓reduceIte]
  rfl

theorem runDet_mapM_leafH (k : Tbl) (hist : List Out) (hk : P.cK k ≤ hist.length) :
    ∀ l : List ℕ, runDet (QuotientZk.DRpm.ofBytes P) G s (l.mapM (QuotientZk.Deployed.leafH k)) hist =
      (l.map fun x ↦ kDet π (P.rowFn s (hist.take (P.cK k)) k ⟨x % 2 ^ 23,
        Nat.mod_lt _ (by positivity)⟩), hist)
  | [] => by rw [List.mapM_nil, runDet_pure]; rfl
  | x :: l => by
    rw [List.mapM_cons, runDet_bind, runDet_leafH P π gH gF s k x hist hk, runDet_bind,
      runDet_mapM_leafH k hist hk l, runDet_pure]
    rfl

/-- **A secret table's level-0 tree** is the statement's tree of the word whose rows its leaves'
rows are. -/
theorem tree₀_secret (sh : QuotientZk.Deployed.OpenShape) (k : Tbl) (hsec : sh.secret = some k)
    (word : Word) (hist : List Out) (hk : P.cK k ≤ hist.length)
    (hrow : ∀ x < 2 ^ sh.depth₀, P.rowFn s (hist.take (P.cK k)) k ⟨x % 2 ^ 23,
      Nat.mod_lt _ (by positivity)⟩ = (word x).flatMap kBytes) :
    runDet (QuotientZk.DRpm.ofBytes P) G s (QuotientZk.Deployed.tree₀ sh) hist =
      (Merkle.treeBytes π sh.depth₀ word, hist) := by
  unfold QuotientZk.Deployed.tree₀
  rw [hsec]
  simp only
  rw [runDet_bind, runDet_mapM_leafH P π gH gF s k hist hk, Merkle.runDet_levels, Merkle.tree_levels]
  congr 2
  refine List.map_congr_left fun x hx ↦ ?_
  rw [hrow x (List.mem_range.mp hx)]

end Trees

section Public

variable {S₀ : Type} (P : QuotientZk.Proto S₀ Inp Out Msg Tbl Pos) (π : Equiv.Perm Eager.St)
  (gH : List UInt8 → QuotientZk.Deployed.KSt) (gF : QuotientZk.Deployed.KSt → DigestBytes) (s : S₀)

local notation "G" => Gof (kDet π) π gH gF

open Merkle (runDet_bind runDet_pure)

/-- **The wiring table's level-0 tree** (its rows `rowsWD`) is the statement's circuit commitment's
tree. -/
theorem tree₀_wiring (id : QuotientRpm.Bytes32) (hist : List Out) :
    runDet P G s (QuotientZk.Deployed.tree₀ (QuotientZk.Deployed.wiringShape id rowsWD)) hist =
      (Merkle.treeBytes π 19 (stackWordFast (cellVars logRows) 1 (membership logRows).wiringTable),
        hist) := by
  unfold QuotientZk.Deployed.tree₀
  simp only [QuotientZk.Deployed.wiringShape]
  rw [runDet_bind, rowsWD_eq, List.mapM_map]
  have h := runDet_mapM_hashH P π gH gF s
    (fun i ↦ (stackWordFast (cellVars logRows) 1 (membership logRows).wiringTable i).flatMap kBytes)
    (List.range (2 ^ 19)) hist
  simp only [Function.comp_def] at h ⊢
  rw [h, Merkle.runDet_levels, Merkle.tree_levels]
  have hf : (fun m ↦ (Gof (kDet π) π gH gF (Sum.inl m)).1) = kDet π := rfl
  simp only [hf]

end Public

end PcsQuotient.EndToEnd.Core
