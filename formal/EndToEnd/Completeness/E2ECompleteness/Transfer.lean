-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s Keccak-256 transfer (`Common.keccak256_transfer2`) and leanVM's
-- reading of the two calls in it (`LeanVM.Rpm.rpm_le_of_rom`, which this generalises from a prover
-- then a verifier to any honest computation and any event).
import LeanVM.Protocol.LeanVMRpm

/-!
# From the random-permutation model to the two-call random-oracle model

An honest computation over the two calls (`KeccakCalls`: Keccak-256 and Keccak-f[1600]) that
follows the duplex discipline (`DuplexVm`: every permutation call continues a duplex, or starts one
at a zero capacity) and makes at most `N` block calls (`hashBlocks`) is, against the sponge over the
random permutation (`keccakCallsOverRandomPermutation`), as against two independent random
oracles, up to `rpmError N = N² / 2^508` (`Common.keccak256_transfer2`, the indifferentiability of
the sponge). **`rpm_le_rom`**: any event of its output.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Semantics LeanVM.Protocol
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

/-- **The random-permutation model is the two-call random-oracle model, up to `rpmError N`**, for
an honest computation that follows the duplex discipline and makes at most `N` block calls: any
event of its output. -/
theorem rpm_le_rom {β : Type} (G : OracleComp KeccakCalls β) {N : ℕ} (hd : DuplexVm G [])
    (hN : Common.QueryCostAtMost G hashBlocks N) (q : β → Prop) {ε : ℝ≥0∞}
    (hrom : Pr{let v ← (simulateQ KeccakCalls.randomOracle G).run' ∅}[q v] ≤ ε) :
    Pr{let v ← (simulateQ keccakCallsOverRandomPermutation G).run' []}[q v] ≤
      ε + rpmError N := by
  have hG : Common.QueryCostAtMost (honestGame G) gameCost N := by
    rw [honestGame, Common.rpmGame2, simulateQ_pure, pure_bind, simulateQ_pure, pure_bind]
    exact isWeightBound_hfEmbed_toRHF hN
  rw [(rpmHonest_evalDistEq _).prEvent_eq, honestGame]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ())
    (fun _ ↦ (pure () : OracleComp RSpec Unit)) (fun _ _ ↦ simulateQ toRHF G)
    (fun _ _ ↦ duplex_toRHF _ [] hd) N hG q
  refine h1.trans (add_le_add (le_of_eq_of_le ?_ hrom) le_rfl)
  have e1 : Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
      Common.advS2 Common.keccakPadding Common.KState.zero
        ((fun _ ↦ (pure () : OracleComp RSpec Unit)) x) >>= fun a ↦
          (fun _ _ ↦ simulateQ toRHF G) x a) =
      (simulateQ HFS.romImpl (simulateQ toRHF G)).run' ∅ := by
    simp [Common.romRun2, Common.advS2]
  rw [e1, (run'_toRHF _ _).prEvent_eq, cmap_empty]

end E2ECompleteness
