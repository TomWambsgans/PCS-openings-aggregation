-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The contract is `formal/RecStatement`'s
-- (`RecStatement/Security.lean`: `contractWith`, `pcsOpenAt`, `contractPi1Openings`, `pi1OpsOf`, the experiment
-- `recSoundnessExperiment2`; `RecStatement/Calls.lean`: `pcsCalls`, `callWord`).
import RecCompose.Pi2Run
import RecCompose.Part1

/-!
# The contract's π1 openings are the calldata's: `CallsPure`

**`callsPure`**: on every outcome of π2's knowledge-soundness experiment whose contract accepts, the contract's first
three calls decode under the registry, to the openings `pi1OpsOf` reads off the calldata.

* π2's run over the permutation succeeds only on a stream of `pi2Bytes` bytes, and then its public scalars and pair
  points are the stream's (`runWith_post`), as are those of the run over Keccak-f[1600] at the IV `[]` that `pi1OpsOf`
  runs (`run_ok_of_runWith`); π1's three calls read nothing else of the run (`callWord_congr`, `pcsCalls_take`);
* the contract accepts only if each of its six calls decoded (`pcsOpenAt` answers `false` to a call that does not:
  `holds_pcsOpenAt`, `holds_forIn_and`), so the first three do (`contractPi1Openings_some`);
* the experiment's every outcome is one of these (`contractWith_post`, through the experiment's binds, `simulateQ` and
  the run: `Holds`, `holds_support`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics (KeccakState)
open OracleComp OracleSpec Common

/-! ## π1's calls read only the public data -/

theorem callWord_congr (reads : List Read) (stream : Array UInt8) {r r' : Reduced} (hs : r.scalars = r'.scalars)
    (hp : r.pairPoints = r'.pairPoints) : callWord reads stream r = callWord reads stream r' := by
  funext w
  cases w <;> simp [callWord, hs, hp]

theorem pcsCalls_length (c : Circuit) (pi1 : List (List CallWord)) (sr : List UInt8) (stream : Array UInt8)
    (r : Reduced) : (pcsCalls c pi1 sr stream r).length = pi1.length + 3 := by
  simp [pcsCalls]

theorem pcsCalls_take (c : Circuit) (pi1 : List (List CallWord)) (sr : List UInt8) (stream : Array UInt8)
    (r : Reduced) (h : pi1.length = 3) :
    (pcsCalls c pi1 sr stream r).take 3 = pi1.map (·.map (callWord c.reads stream r)) := by
  unfold pcsCalls
  simp only
  rw [List.take_append_of_le_length (by simp [h])]
  exact List.take_of_length_le (by simp [h])

/-- **`mapM` in `Option` succeeds when each step does.** -/
theorem mapM_option_some {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, (f x).isSome) → ∃ ys, l.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (List.mem_cons_self ..))
    obtain ⟨ys, hys⟩ := mapM_option_some f l fun z hz ↦ h z (List.mem_cons_of_mem _ hz)
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- The contract's π1 openings exist when its first three calls decode. -/
theorem contractPi1Openings_some (reg : List (List UInt8 × Opener)) (calls : List (List (List UInt8)))
    (h : ∀ words ∈ calls.take 3, (decodeWith reg words).isSome) : ∃ ops, contractPi1Openings reg calls = some ops := by
  unfold contractPi1Openings
  exact mapM_option_some _ _ fun words hw ↦ by simpa using h words hw

/-! ## The contract's loop of openings -/

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **`PCS_OPEN` answers `false` to a call that does not decode.** -/
theorem holds_pcsOpenAt (F : KeccakState → m KeccakState) (reg : List (List UInt8 × Opener))
    (words : List (List UInt8)) (p : LeanVM.Protocol.Compile.Proof) :
    Holds (pcsOpenAt F reg words p) fun b ↦ b = true → (decodeWith reg words).isSome := by
  unfold pcsOpenAt
  split
  · exact holds_pure fun h ↦ absurd h (by simp)
  · rename_i h
    exact holds_mono (holds_true _) fun _ _ _ ↦ by rw [h]; rfl
  · rename_i h
    exact holds_mono (holds_true _) fun _ _ _ ↦ by rw [h]; rfl

/-- **A loop that ands its body's answers** answers `true` only if its start does and every body's answer was `true`
for an element with `G`. -/
theorem holds_forIn_and {γ : Type} (G : γ → Prop) (f : γ → Bool → m (ForInStep Bool))
    (hf : ∀ x b, Holds (f x b) fun st ↦ ∃ c, st = .yield (b && c) ∧ (c = true → G x)) :
    ∀ (l : List γ) (b : Bool), Holds (forIn l b f) fun r ↦ r = true → b = true ∧ ∀ x ∈ l, G x
  | [], b => by
    simp only [List.forIn_nil]
    exact holds_pure fun h ↦ ⟨h, by simp⟩
  | x :: l, b => by
    rw [List.forIn_cons]
    refine holds_bind (hf x b) fun st ⟨c, hst, hc⟩ ↦ ?_
    subst hst
    simp only
    refine holds_mono (holds_forIn_and G f hf l (b && c)) fun r hr h ↦ ?_
    obtain ⟨hbc, hl⟩ := hr h
    simp only [Bool.and_eq_true] at hbc
    refine ⟨hbc.1, fun y hy ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hc hbc.2
    · exact hl y hy

/-- **The contract accepts only on calldata whose π1 openings are its first three calls'**, decoded. -/
theorem contractWith_post (F : KeccakState → m KeccakState) (D : RecDeployment) (roots : RecSetupRoots)
    (input : Vector UInt8 32) (proof : RecProof) :
    Holds (D.contractWith F roots input proof) fun x ↦ x.1 = true →
      ∃ ops, pi1OpsOf D roots input proof.stream = some ops ∧ contractPi1Openings (registryAt D roots) x.2 = some ops := by
  unfold RecDeployment.contractWith
  refine holds_bind (holds_true _) fun iv _ ↦
    holds_bind (runWith_post F (Spec.of (D.circuitAt roots.pi1).circuit) iv input.toList proof.stream) fun o ho ↦ ?_
  split
  · exact holds_pure fun h ↦ absurd h (by simp)
  · rename_i r hr
    split_ifs with hacc
    · exact holds_pure fun h ↦ absurd h (by simp)
    dsimp only
    split_ifs with hlen
    · exact holds_pure fun h ↦ absurd h (by simp)
    · refine holds_bind (holds_forIn_and (fun x ↦ (decodeWith (registryOf D.pi1.shape
          (D.circuitAt roots.pi1).circuit.logN) x.1).isSome) _ (fun x b ↦ ?_) _ true) fun ok hok ↦ holds_pure fun h ↦ ?_
      · obtain ⟨words, p⟩ := x
        simp only
        exact holds_bind (holds_pcsOpenAt F _ words p) fun c hc ↦ holds_pure ⟨c, rfl, hc⟩
      · simp only at h
        obtain ⟨-, hdec⟩ := hok h
        set calls := pcsCalls (D.circuitAt roots.pi1).circuit (pi1CallsWith D.pi1Calls roots.pi1.bytecode)
          (digestBytes roots.pi2) proof.stream r with hcalls
        have hlen' : calls.length = 6 := by simpa using hlen
        have hpi1 : (pi1CallsWith D.pi1Calls roots.pi1.bytecode).length = 3 := by
          have := pcsCalls_length (D.circuitAt roots.pi1).circuit (pi1CallsWith D.pi1Calls roots.pi1.bytecode)
            (digestBytes roots.pi2) proof.stream r
          rw [← hcalls] at this
          omega
        have hopen : proof.openings.length = 6 := rfl
        obtain ⟨ops, hops⟩ := contractPi1Openings_some (registryAt D roots) calls fun words hw ↦ by
          have hwc : words ∈ calls := List.mem_of_mem_take hw
          have hfst : (calls.zip proof.openings).map Prod.fst = calls :=
            List.map_fst_zip (by rw [hlen', hopen])
          rw [← hfst] at hwc
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hwc
          exact hdec x hx
        refine ⟨ops, ?_, hops⟩
        obtain ⟨hsz, hsc, hpp⟩ := ho.1 r hr
        obtain ⟨r', hr', hsc', hpp'⟩ := run_ok_of_runWith (m := m) (Spec.of (D.circuitAt roots.pi1).circuit)
          input.toList proof.stream [] r hsz hsc hpp
        unfold pi1OpsOf
        simp only
        rw [hr']
        simp only
        rw [← hops]
        unfold contractPi1Openings
        rw [pcsCalls_take _ _ _ _ _ hpi1, pcsCalls_take _ _ _ _ _ hpi1,
          callWord_congr _ _ hsc' hpp']

end Generic

/-! ## On the experiment's outcomes -/

/-- **`CallsPure`**: on every outcome of π2's knowledge-soundness experiment whose contract accepts, the contract's
first three calls decode under the registry, to the openings `pi1OpsOf` reads off the calldata. -/
theorem callsPure (D : RecDeployment) : CallsPure D := by
  intro A
  refine holds_support ?_
  unfold recSoundnessExperiment2 runWithRandomPermutation
  refine holds_run' (holds_simulateQ _ ?_) []
  refine holds_bind (holds_true _) fun trees _ ↦ holds_bind (holds_true _) fun zt _ ↦ ?_
  obtain ⟨z, transcript⟩ := zt
  refine holds_bind (contractWith_post queryPermutation D trees.roots z.1 z.2) fun ac hac ↦ ?_
  obtain ⟨accepted, calls⟩ := ac
  exact holds_pure hac

end RecCompose

/-- info: 'RecCompose.callsPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.callsPure
