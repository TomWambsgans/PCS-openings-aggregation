-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The proof pattern (one commutation lemma per function, pushed through the binds; the run by induction
-- on the program) is adapted from `formal/EndToEnd/Completeness/E2ECompleteness/WithHash.lean`
-- (`simulateQ_runFromWithHash`, `simulateQ_proveWithH`), with a monad morphism for `simulateQ`. The
-- functions are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Keccak.lean`'s
-- `absorbBlockWith`, `absorbWith`, `keccak256With`; `Statement/LeanVmVerifier.lean`'s `duplex`, `absorb`,
-- `squeeze`; `Statement/Prover/Run.lean`'s `leafDigestsM`, `parentsM`, `levelsM`, `buildTreeM`,
-- `powStepM`, `searchM`, `findNonceM`, `runFrom`) and `formal/Statement`'s.
import ZK.ProverBridgeHom

/-!
# The honest prover is parametric in its monad

The statement's honest prover (`PcsQuotient.prover`) is a program over a permutation
`F : KeccakState → m KeccakState` in any monad `m`. Read through a monad morphism `φ : m → n`
(`MHom`, `ProverBridgeHom.lean`), it is the same program over `φ ∘ F` (`prover_hom`):

`φ.app (prover F stmt w coins) = prover (fun x ↦ φ.app (F x)) stmt w coins`.

One lemma per function, each `φ.app (f F …) = f (φ ∘ F) …`, from the leaves up: Keccak-256 over the
permutation (`absorbBlockWith`, `absorbWith`, `keccak256With`); the sponge (`duplex`, `absorb`,
`squeeze`); the Merkle trees (`leafDigestsM`, `parentsM`, `levelsM`, `buildTreeM`, `commitWith`); the
reduction's chain and verifier (`Chain.startWith`, `Chain.squeezeWith`, `reduceWith`); the proofs of
work (`powStepM`, `searchM`, `findNonceM`); the script's run against the program (`runFrom`, by
induction on the program); the opening (`openingSpongeWith`, `proveOpeningWith`); the prover
(`proveWith`, for any circuit, `proverWith`, `prover`); and the setup (`indexRootWith`, `setupWith`).
Each pushes `φ` through the binds only: no pure computation of the prover is unfolded or evaluated.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient PcsQuotient.Transcript

set_option autoImplicit false

namespace PcsQuotient.EndToEnd.Param

section Programs

variable {m n : Type → Type} [Monad m] [Monad n] (φ : MHom m n) (F : KeccakState → m KeccakState)

/-! ### Keccak-256 over the permutation -/

theorem absorbBlockWith_hom (state : KeccakState) (block : List UInt8) :
    φ.app (absorbBlockWith F state block) = absorbBlockWith (fun x ↦ φ.app (F x)) state block :=
  rfl

theorem absorbWith_hom : ∀ (blocks : ℕ) (state : KeccakState) (data : List UInt8),
    φ.app (absorbWith F blocks state data) = absorbWith (fun x ↦ φ.app (F x)) blocks state data
  | 0, state, data => by simp only [absorbWith, absorbBlockWith_hom]
  | blocks + 1, state, data => by
    simp only [absorbWith, φ.app_bind, absorbBlockWith_hom, absorbWith_hom blocks]

theorem keccak256With_hom (data : List UInt8) :
    φ.app (keccak256With F data) = keccak256With (fun x ↦ φ.app (F x)) data := by
  simp only [keccak256With, φ.app_bind, φ.app_pure, absorbWith_hom]

/-! ### The sponge -/

theorem duplex_hom (sp : Sponge) : φ.app (duplex F sp) = duplex (fun x ↦ φ.app (F x)) sp := by
  simp only [duplex, φ.app_bind, φ.app_pure]

theorem absorb_hom (sp : Sponge) (x : E) (tag : ℕ) :
    φ.app (Compile.absorb F sp x tag) = Compile.absorb (fun y ↦ φ.app (F y)) sp x tag := by
  simp only [Compile.absorb]
  split <;> simp only [φ.app_bind, φ.app_pure, duplex_hom]

theorem squeeze_hom (sp : Sponge) : φ.app (squeeze F sp) = squeeze (fun x ↦ φ.app (F x)) sp := by
  simp only [squeeze, φ.app_bind, φ.app_pure, duplex_hom]

/-! ### The reduction's chain and verifier -/

theorem startWith_hom (lbl : List UInt8) :
    φ.app (Chain.startWith F lbl) = Chain.startWith (fun x ↦ φ.app (F x)) lbl := by
  simp only [Chain.startWith, φ.app_bind, φ.app_pure, keccak256With_hom]

theorem squeezeWith_hom (c : Chain) :
    φ.app (c.squeezeWith F) = c.squeezeWith (fun x ↦ φ.app (F x)) := by
  simp only [Chain.squeezeWith, φ.app_bind, φ.app_pure, keccak256With_hom]

/-- The pairs `let (x, c) ← …` binds are matched by structure eta: `simp` reads through them. -/
theorem reduceWith_hom (logRows : ℕ) (indexRoot : Digest) (stmt : Statement) (p : ReductionProof) :
    φ.app (reduceWith F logRows indexRoot stmt p) =
      reduceWith (fun x ↦ φ.app (F x)) logRows indexRoot stmt p := by
  unfold reduceWith
  split
  · simp only [φ.app_pure]
  · rw [φ.app_bind, startWith_hom]
    congr 1; funext c
    dsimp only
    split
    · simp only [φ.app_pure]
    · simp only [φ.app_bind, squeezeWith_hom]
      congr 1; funext x₁; congr 1; funext x₂; congr 1; funext x₃
      split
      · simp only [φ.app_pure]
      · simp only [φ.app_bind, φ.app_pure, squeezeWith_hom]

/-! ### The opening's sponge and the proofs of work -/

theorem openingSpongeWith_hom (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim) :
    φ.app (openingSpongeWith F L claims) = openingSpongeWith (fun x ↦ φ.app (F x)) L claims := by
  simp only [openingSpongeWith, φ.app_bind, φ.app_pure, keccak256With_hom]

theorem powStepM_hom (sp : Sponge) (x : E) :
    φ.app (powStepM F sp x) = powStepM (fun y ↦ φ.app (F y)) sp x := by
  simp only [powStepM, φ.app_bind, absorb_hom, squeeze_hom]

theorem searchM_hom (bits : ℕ) (sp : Sponge) : ∀ (start count : ℕ),
    φ.app (searchM F bits sp start count) = searchM (fun x ↦ φ.app (F x)) bits sp start count
  | _, 0 => by simp only [searchM, φ.app_pure]
  | start, count + 1 => by
    simp only [searchM, φ.app_bind, powStepM_hom]
    congr 1; funext r
    split
    · simp only [φ.app_pure]
    · exact searchM_hom bits sp (start + 1) count

theorem findNonceM_hom (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    φ.app (findNonceM F bits sp fuel) = findNonceM (fun x ↦ φ.app (F x)) bits sp fuel := by
  unfold findNonceM
  split
  · simp only [φ.app_pure]
  · exact searchM_hom φ F bits sp 0 fuel

end Programs

section Lawful

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  (φ : MHom m n) (F : KeccakState → m KeccakState)

/-! ### Merkle trees -/

theorem leafDigestsM_hom (height : ℕ) (word : Word) :
    φ.app (leafDigestsM F height word) = leafDigestsM (fun x ↦ φ.app (F x)) height word := by
  simp only [leafDigestsM, φ.app_mapM_array, keccak256With_hom]

theorem parentsM_hom (level : Array Digest) (count : ℕ) :
    φ.app (parentsM F level count) = parentsM (fun x ↦ φ.app (F x)) level count := by
  simp only [parentsM, φ.app_mapM_array, keccak256With_hom]

theorem levelsM_hom : ∀ (k : ℕ) (level : Array Digest),
    φ.app (levelsM F k level) = levelsM (fun x ↦ φ.app (F x)) k level
  | 0, level => by simp only [levelsM, φ.app_pure]
  | k + 1, level => by
    simp only [levelsM, φ.app_bind, φ.app_pure, parentsM_hom, levelsM_hom k]

theorem buildTreeM_hom (height : ℕ) (word : Word) :
    φ.app (buildTreeM F height word) = buildTreeM (fun x ↦ φ.app (F x)) height word := by
  simp only [buildTreeM, φ.app_bind, φ.app_pure, leafDigestsM_hom, levelsM_hom]

theorem commitWith_hom (μ : ℕ) (stack : Array K) :
    φ.app (commitWith F μ stack) = commitWith (fun x ↦ φ.app (F x)) μ stack :=
  buildTreeM_hom φ F _ _

/-! ### The setup -/

theorem indexRootWith_hom (c : Circuit) :
    φ.app (c.indexRootWith F) = c.indexRootWith (fun x ↦ φ.app (F x)) := by
  simp only [Circuit.indexRootWith, φ.app_bind, φ.app_pure, commitWith_hom]

/-- **The setup** read through `φ` is the setup over `φ ∘ F`. -/
theorem setupWith_hom : φ.app (setupWith F) = setupWith (fun x ↦ φ.app (F x)) :=
  indexRootWith_hom φ F _

/-! ### The script's run against the program -/

/-- **The run** (mumbai's `runFrom`), by induction on the program. -/
theorem runFrom_hom (fuel : ℕ) {α β : Type} (P : Prog α) :
    ∀ (S : Option (Script β)) (sp : Sponge) (cs : List LeanVM.Prover.Tree),
      φ.app (runFrom F fuel P S sp cs) = runFrom (fun x ↦ φ.app (F x)) fuel P S sp cs := by
  induction P with
  | ret a => intro S sp cs; simp only [runFrom, φ.app_pure]
  | fail => intro S sp cs; simp only [runFrom, φ.app_pure]
  | read k ih =>
    intro S sp cs
    simp only [runFrom, φ.app_bind, φ.app_pure, absorb_hom, ih]
  | sample k ih =>
    intro S sp cs
    simp only [runFrom, φ.app_bind, squeeze_hom, ih]
  | grind bits k ih =>
    intro S sp cs
    simp only [runFrom, φ.app_bind, findNonceM_hom]
    congr 1; funext o
    cases o with
    | none => simp only [φ.app_pure]
    | some x => simp only [φ.app_bind, φ.app_pure, powStepM_hom, ih]
  | commit ht w k ih =>
    intro S sp cs
    simp only [runFrom, φ.app_bind, φ.app_pure, buildTreeM_hom, absorb_hom, ih]
  | query i ps k ih =>
    intro S sp cs
    simp only [runFrom]
    split
    · simp only [φ.app_pure]
    · simp only [φ.app_bind, φ.app_pure, ih]

/-! ### The opening and the prover -/

theorem proveOpeningWith_hom (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree)
    (stack : Array K) (claims : List PcsQuotient.Claim) :
    φ.app (proveOpeningWith F fuel L tree stack claims) =
      proveOpeningWith (fun x ↦ φ.app (F x)) fuel L tree stack claims := by
  simp only [proveOpeningWith, φ.app_bind, φ.app_pure, openingSpongeWith_hom, absorb_hom,
    runFrom_hom]

/-- **The prover of any circuit**: `φ` pushed through the binds, the pure computations untouched. -/
theorem proveWith_hom (fuel : ℕ) (circuit : Circuit) (stmt : Statement) (cells : Array K)
    (masks : Masks) (witnessPad quotientPad : Padding) :
    φ.app (proveWith F fuel circuit stmt cells masks witnessPad quotientPad) =
      proveWith (fun x ↦ φ.app (F x)) fuel circuit stmt cells masks witnessPad quotientPad := by
  unfold proveWith
  simp only [φ.app_bind, commitWith_hom, startWith_hom, squeezeWith_hom, reduceWith_hom]
  congr 1; funext indexTree; congr 1; funext witnessTree; congr 1; funext c
  congr 1; funext x₁; congr 1; funext x₂; congr 1; funext x₃
  congr 1; funext quotientTree; congr 1; funext x₄; congr 1; funext red
  split
  · simp only [φ.app_pure]
  · simp only [φ.app_bind, proveOpeningWith_hom]
    congr 1; funext o₁
    split
    · simp only [φ.app_bind, proveOpeningWith_hom]
      congr 1; funext o₂
      split
      · simp only [φ.app_bind, proveOpeningWith_hom]
        congr 1; funext o₃
        split <;> simp only [φ.app_pure]
      · simp only [φ.app_pure]
    · simp only [φ.app_pure]

theorem proverWith_hom (fuel : ℕ) (stmt : Statement) (w : Secret) (masks : Masks)
    (witnessPad quotientPad : Padding) :
    φ.app (proverWith F fuel stmt w masks witnessPad quotientPad) =
      proverWith (fun x ↦ φ.app (F x)) fuel stmt w masks witnessPad quotientPad :=
  proveWith_hom φ F _ _ _ _ _ _ _

end Lawful

/-- **The honest prover read through a monad morphism** is the honest prover over the permutation
read through it. -/
theorem prover_hom {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (φ : MHom m n) (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (stmt : Statement) (w : Secret) (coins : Masks × Padding × Padding) :
    φ.app (prover F stmt w coins) = prover (fun x ↦ φ.app (F x)) stmt w coins :=
  proverWith_hom φ F _ _ _ _ _ _

end PcsQuotient.EndToEnd.Param

/-- info: 'PcsQuotient.EndToEnd.Param.prover_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PcsQuotient.EndToEnd.Param.prover_hom
