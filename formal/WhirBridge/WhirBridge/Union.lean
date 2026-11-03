/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

One Fiat-Shamir family for several openings of `opening::verify` (`crates/quotient/src/opening.rs`)
on different layouts: the construction of `Family.lean` (adapted from leanerVM `mumbai`'s
`anyProgram`, `leanVmSeeds`, `anyCert`, https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0,
MIT OR Apache-2.0: `lean_vm/LeanVM/Protocol/EndToEnd/Sound/Statements.lean`) with the shape's index
read before the statement, and `Exact.lean`'s `roots_sound` on it.
-/
import WhirBridge.Exact

/-!
# The openings of several shapes as one family

`ExactShape ε`: a valid layout at an admissible shape whose deployed codes meet the per-group
bound `ε` (`hε`) above the batching lead (`hB`), and the opening's query count `QO`.
`ExactShape.large`: every public layout `Layout.new` accepts at `2^24 ..= 2^28` words, at
`εExact`. For a list `shs` of shapes whose verifier prefixes are distinct (`hpre`):

* **the union family**: statements `Σ j, Stmt (shs.get j).L.stacking`; one program (`uProg`)
  reads the index `j` in unary (`j` scalars `skipE`, then `stopE`), then runs shape `j`'s program
  of every statement (`famProgram`); a statement's root is those reads, then its claims' reads
  (`uRoot`), and the roots are prefix-free (`uRoot_inj`); the seeding is shape `j`'s
  (`famSeed (openingPrefix L_j R_j)`), and the IV's input names the shape (the prefixes have one
  length, `openingPrefix_length`, and are distinct) and the claims (`stmt_eq_of_bytes`)
  (`uSeeds`). The index is read in unary so that no bound on the number of shapes is needed (one
  scalar holds `2^64` values).
* **`union_sound`**: an adversary of at most `QA` queries that outputs a shape's index, a root,
  claims on that shape's layout and a proof makes that shape's `opening::verify` accept while
  every candidate table of the root's word violates one of the claims with probability at most
  `(QA + QV) · (ε + 5 (QA + QV) / 2^256)`, `QV` above every shape's `QO`: **one** charge of
  `ε` per query for all the shapes together.
* **`largeShapes`**: the plain layouts `Layout.new μ μ μ [(0, 2^μ)]`, `μ = 24 ..= 28`, at
  `εExact`; their prefixes are distinct (`largeShapes_nodup`, from their `log_n`,
  `openingPrefix_logN`).
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (wordE kNat kNat_ofBits limb_wordE reachable_of_after_reads
  boundary_map_read grindBits_map_read commits_map_read)
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The shapes -/

/-- **An opening's shape at the per-group bound `ε`**: a valid layout at an admissible shape
(rate `2^-R`), whose deployed codes meet `ε` (`hε`) above the batching lead (`hB`), and the
opening's query count `QO` (of the proven program of every statement, from any prefix). -/
structure ExactShape (ε : ℝ≥0∞) where
  L : Layout
  R : ℕ
  hL : L.Valid
  adm : Whir.Admissible L.logN R
  hε : ∀ config, Whir.ladder L.logN R = some config →
    whirEps (LeanVM.Protocol.Whir.Params.deployedCodes L.logN R) config ≤ ε
  hB : ∀ J ≤ 2 ^ 46 + 1, eBatch J (code₀ L.logN R) ≤ ε
  QO : ℕ
  queries : ∀ pre z, IsTotalQueryBound
    (verifierFam (famSeeds L.stacking pre) (famProgram L.stacking R) z) QO

/-- **A public layout of `2^24 ..= 2^28` words that `Layout::new` accepts**, at `εExact`, with the
shape's query count `QO = largeQueries log_n` (as `WhirShape.large`). -/
@[reducible] noncomputable def ExactShape.large (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ))
    (hS : NewOK vars logChunk logN chunks) (h1 : largeMin ≤ logN) (h2 : logN ≤ largeMax) :
    ExactShape εExact where
  L := Layout.new vars logChunk logN chunks
  R := logInvRate
  hL := Layout.new_valid hS
  adm := admissible_large h1 h2
  hε _ hc := whirEps_le_exact h1 h2 hc
  hB _ hJ := eBatch_le_exact h1 h2 hJ
  QO := largeQueries logN
  queries pre z := isTotalQueryBound_fam_large _ h1 h2 pre z

/-! ## Reading the index -/

/-- The scalar that skips a shape. -/
def skipE : E := wordE (K.ofBits 1)

/-- The scalar that stops at a shape. -/
def stopE : E := wordE (K.ofBits 0)

theorem kNat_stopE : kNat (stopE.limb 0) = 0 := by
  simp only [stopE, limb_wordE]
  exact kNat_ofBits (by norm_num)

theorem kNat_skipE : kNat (skipE.limb 0) = 1 := by
  simp only [skipE, limb_wordE]
  exact kNat_ofBits (by norm_num)

theorem stopE_ne_skipE : stopE ≠ skipE := fun h ↦ by
  have h0 := kNat_stopE
  rw [h, kNat_skipE] at h0
  exact absurd h0 (by norm_num)

/-- The index `j` in unary: `j` skips, then a stop. -/
def selScalars (j : ℕ) : List E := List.replicate j skipE ++ [stopE]

theorem sel_zero (r : List Ev) : (selScalars 0).map Ev.read ++ r = Ev.read stopE :: r := rfl

theorem sel_succ (j : ℕ) (r : List Ev) :
    (selScalars (j + 1)).map Ev.read ++ r = Ev.read skipE :: ((selScalars j).map Ev.read ++ r) := by
  simp only [selScalars, List.replicate_succ, List.cons_append, List.map_cons]

/-- **Select a program by its index**: read scalars, skipping one program per `skipE`, until a
stop. -/
def selProg {α : Type} (f : α → Prog Bool) : List α → Prog Bool
  | [] => .fail
  | a :: as => .read fun e ↦ if kNat (e.limb 0) = 0 then f a else selProg f as

theorem selProg_stop {α : Type} (f : α → Prog Bool) (a : α) (as : List α) (rest : List Ev) :
    (selProg f (a :: as)).after (Ev.read stopE :: rest) = (f a).after rest := by
  show (if kNat (stopE.limb 0) = 0 then f a else selProg f as).after rest = _
  rw [if_pos kNat_stopE]

theorem selProg_skip {α : Type} (f : α → Prog Bool) (a : α) (as : List α) (rest : List Ev) :
    (selProg f (a :: as)).after (Ev.read skipE :: rest) = (selProg f as).after rest := by
  show (if kNat (skipE.limb 0) = 0 then f a else selProg f as).after rest = _
  rw [if_neg (by rw [kNat_skipE]; norm_num)]

/-- **The index's reads lead to the indexed program.** -/
theorem after_selProg {α : Type} (f : α → Prog Bool) :
    ∀ (as : List α) (j : ℕ) (hj : j < as.length) (rest : List Ev),
      (selProg f as).after ((selScalars j).map Ev.read ++ rest) = (f (as.get ⟨j, hj⟩)).after rest
  | [], _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | a :: as, 0, _, rest =>
    (congrArg (selProg f (a :: as)).after (sel_zero rest)).trans (selProg_stop f a as rest)
  | a :: as, j + 1, hj, rest =>
    (congrArg (selProg f (a :: as)).after (sel_succ j rest)).trans
      ((selProg_skip f a as _).trans (after_selProg f as j (by simpa using hj) rest))

theorem cons_prefix_inj {a b : Ev} {l l' h : List Ev} (h1 : a :: l <+: h) (h2 : b :: l' <+: h) :
    a = b ∧ ∃ h', l <+: h' ∧ l' <+: h' := by
  obtain ⟨t, rfl⟩ := h1
  obtain ⟨t', ht'⟩ := h2
  simp only [List.cons_append, List.cons.injEq] at ht'
  exact ⟨ht'.1.symm, l ++ t, ⟨t, rfl⟩, ⟨t', ht'.2⟩⟩

/-- **Two indices' reads on one history are one index's.** -/
theorem sel_eq_of_prefix : ∀ (j j' : ℕ) {r r' h : List Ev},
    (selScalars j).map Ev.read ++ r <+: h → (selScalars j').map Ev.read ++ r' <+: h → j = j'
  | 0, 0, _, _, _, _, _ => rfl
  | 0, j' + 1, r, r', _, h1, h2 => by
    rw [sel_zero] at h1
    rw [sel_succ] at h2
    exact absurd (Ev.read.inj (cons_prefix_inj h1 h2).1) stopE_ne_skipE
  | j + 1, 0, r, r', _, h1, h2 => by
    rw [sel_succ] at h1
    rw [sel_zero] at h2
    exact absurd (Ev.read.inj (cons_prefix_inj h1 h2).1).symm stopE_ne_skipE
  | j + 1, j' + 1, r, r', _, h1, h2 => by
    rw [sel_succ] at h1
    rw [sel_succ] at h2
    obtain ⟨-, h', p1, p2⟩ := cons_prefix_inj h1 h2
    rw [sel_eq_of_prefix j j' p1 p2]

theorem prefix_drop_of_append {l₁ l₂ h : List Ev} (hp : l₁ ++ l₂ <+: h) :
    l₂ <+: h.drop l₁.length := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.append_assoc, List.drop_left]
  exact List.prefix_append _ _

/-! ## The union family -/

section Union

variable {ε : ℝ≥0∞}

/-- **The union's statements**: a shape's index and a statement on its layout. -/
abbrev USt (shs : List (ExactShape ε)) : Type := Σ j : Fin shs.length, Stmt (shs.get j).L.stacking

/-- **The union's inputs**: a shape's index, a root, claims on its layout. -/
abbrev UIn (shs : List (ExactShape ε)) : Type :=
  Σ j : Fin shs.length, Digest × Stmt (shs.get j).L.stacking

/-- **The union's verifier**: the indexed shape's `opening::verify`. -/
def uVer (shs : List (ExactShape ε)) (z : UIn shs × Proof) : OracleComp KeccakCalls Bool :=
  ourVerifier (shs.get z.1.1).L (shs.get z.1.1).R (z.1.2, z.2)

/-- **The union's event**: the indexed shape's (`OpeningDoomed`). -/
def UDoomed (shs : List (ExactShape ε)) (z : UIn shs × Proof) (c : KeccakCalls.QueryCache) :
    Prop :=
  OpeningDoomed (shs.get z.1.1).L (shs.get z.1.1).R (z.1.2, z.2) c

/-- The union family's event in stack terms: the indexed shape's (`FamDoomed`). -/
def UFamDoomed (shs : List (ExactShape ε)) (z : USt shs × Proof) (c : KeccakCalls.QueryCache) :
    Prop :=
  FamDoomed (shs.get z.1.1).L.stacking (shs.get z.1.1).R (z.1.2, z.2) c

/-- **The program of every statement of every shape**: the index, read in unary, then the
indexed shape's program of every statement (`famProgram`). -/
def uProg (shs : List (ExactShape ε)) : Prog Bool :=
  selProg (fun s : ExactShape ε ↦ famProgram s.L.stacking s.R) shs

/-- **A statement's root**: the reads of its index, then of its claims (`famHistory`). -/
def uRoot (shs : List (ExactShape ε)) (x : USt shs) : List Ev :=
  (selScalars x.1.1 ++ famScalars x.2).map Ev.read

theorem uRoot_eq (shs : List (ExactShape ε)) (x : USt shs) :
    uRoot shs x = (selScalars x.1.1).map Ev.read ++ famHistory x.2 := by
  simp only [uRoot, List.map_append, famHistory]

theorem after_uRoot (shs : List (ExactShape ε)) (x : USt shs) :
    (uProg shs).after (uRoot shs x) =
      some (variantProg (shs.get x.1).L.stacking (shs.get x.1).R x.2.claims) := by
  rw [uRoot_eq, uProg,
    after_selProg (fun s : ExactShape ε ↦ famProgram s.L.stacking s.R) shs x.1.1 x.1.2]
  exact after_famHistory x.2

theorem rootOk_uRoot (shs : List (ExactShape ε)) (x : USt shs) :
    RootOk (uProg shs) (uRoot shs x) := by
  have ha := after_uRoot shs x
  exact ⟨reachable_of_after_reads _ ha, boundary_map_read (by simp [selScalars]),
    grindBits_map_read _, commits_map_read _, by simp [ha]⟩

/-- **Roots are prefix-free**: two roots on one history are one statement's. -/
theorem uRoot_inj (shs : List (ExactShape ε)) {x x' : USt shs} {h : List Ev}
    (hx : uRoot shs x <+: h) (hx' : uRoot shs x' <+: h) : x = x' := by
  obtain ⟨j, a⟩ := x
  obtain ⟨j', a'⟩ := x'
  rw [uRoot_eq] at hx hx'
  have hj : j = j' := Fin.ext (sel_eq_of_prefix j.1 j'.1 hx hx')
  subst hj
  obtain rfl : a = a' := fam_eq_of_prefix (prefix_drop_of_append hx) (prefix_drop_of_append hx')
  rfl

theorem uRootsOK (shs : List (ExactShape ε)) :
    RootsOK (uProg shs) (uRoot shs)
      fun x ↦ variantProg (shs.get x.1).L.stacking (shs.get x.1).R x.2.claims :=
  ⟨after_uRoot shs, rootOk_uRoot shs, fun hx hx' ↦ uRoot_inj shs hx hx'⟩

/-- Distinct prefixes name distinct shapes. -/
theorem idx_eq_of_prefix {shs : List (ExactShape ε)}
    (hpre : (shs.map fun s ↦ openingPrefix s.L s.R).Nodup) {j j' : Fin shs.length}
    (h : openingPrefix (shs.get j).L (shs.get j).R = openingPrefix (shs.get j').L (shs.get j').R) :
    j = j' := by
  have hj : j.1 < (shs.map fun s ↦ openingPrefix s.L s.R).length := by simp
  have hj' : j'.1 < (shs.map fun s ↦ openingPrefix s.L s.R).length := by simp
  exact Fin.ext ((hpre.getElem_inj_iff (hi := hj) (hj := hj')).1 (by simpa using h))

/-- **Shapes whose verifier prefixes are distinct**, bundled: the union's seedings take the list
with its proof, so that no statement about them passes a proof argument (a statement with
`uSeeds shs hpre`, `hpre` a binder, timed out in elaboration). -/
structure UShapes (ε : ℝ≥0∞) where
  shs : List (ExactShape ε)
  nodup : (shs.map fun s ↦ openingPrefix s.L s.R).Nodup

/-- **The seedings of the union**: the indexed shape's (`famSeed` of its prefix). -/
def uSeeds (U : UShapes ε) : Seeds (USt U.shs) where
  seed x := famSeed (openingPrefix (U.shs.get x.1).L (U.shs.get x.1).R) x.2
  root := uRoot U.shs
  offs := []
  refs x ds hds i hi := by
    have hds1 : ds.length = 1 := hds
    have hd0 : ds.getD 0 default = ds[0] := by simp [List.getD_eq_getElem?_getD, hds1]
    rw [hds1] at hi
    interval_cases i
    left
    show laneDigest (seedInput (ds.getD 0 default) default) = ds[0]
    rw [laneDigest_seedInput, hd0]
  cap0 x ds := capOf_seedInput _ _
  inj H hH x x' ds ds' ha ha' he := by
    obtain ⟨j, a⟩ := x
    obtain ⟨j', a'⟩ := x'
    have hl : ds.length = 1 := ha.1
    have hl' : ds'.length = 1 := ha'.1
    have hiv : ds.getD 0 default = ds'.getD 0 default := by
      have := congrArg laneDigest he
      simpa [famSeed, laneDigest_seedInput] using this
    obtain ⟨f0, hf0, hH0⟩ := ha.2 0 (by omega)
    obtain ⟨f0', hf0', hH0'⟩ := ha'.2 0 (by omega)
    simp only [famSeed, List.getElem?_cons_zero, Option.some.injEq] at hf0 hf0'
    subst hf0 hf0'
    have e0 : ds[0] = ds'[0] := by
      simpa [List.getD_eq_getElem?_getD, hl, hl'] using hiv
    rw [e0] at hH0
    have hb : openingPrefix (U.shs.get j).L (U.shs.get j).R ++ claimsBytes a.claims =
        openingPrefix (U.shs.get j').L (U.shs.get j').R ++ claimsBytes a'.claims :=
      hH _ _ _ hH0 hH0'
    obtain ⟨hp, hc⟩ := List.append_inj hb (by rw [openingPrefix_length, openingPrefix_length])
    obtain rfl := idx_eq_of_prefix U.nodup hp
    rw [stmt_eq_of_bytes hc]

theorem verifierFam_uSeeds (U : UShapes ε) (z : USt U.shs × Proof) :
    verifierFam (uSeeds U) (uProg U.shs) z =
      verifierComp (famSeed (openingPrefix (U.shs.get z.1.1).L (U.shs.get z.1.1).R) z.1.2)
        (variantProg (U.shs.get z.1.1).L.stacking (U.shs.get z.1.1).R z.1.2.claims) z.2 := by
  show verifierComp _ (nodeAt (uProg U.shs) (uRoot U.shs z.1)) z.2 = _
  rw [nodeAt, after_uRoot]
  rfl

theorem verifierComp_famSeed {L : Stacking} (pre : Bytes) (x : Stmt L) (p : Prog Bool)
    (π : Proof) :
    verifierComp (famSeed pre x) p π = seedComp pre x.claims >>= fun seed ↦
      runProofWithHash callKeccak256 callKeccakF1600 p seed π := by
  simp only [verifierComp, LeanVM.Protocol.Compile.Rom.verify, Seed.run, Seed.hsRun, famSeed,
    seedComp, bind_assoc, pure_bind, List.nil_append, List.getD_cons_zero]

/-- The union's program makes at most `QV` queries, above every shape's `QO`. -/
theorem uqueries (U : UShapes ε) (QV : ℕ) (hQV : ∀ s ∈ U.shs, s.QO ≤ QV)
    (z : USt U.shs × Proof) :
    IsTotalQueryBound (verifierFam (uSeeds U) (uProg U.shs) z) QV := by
  have h := (U.shs.get z.1.1).queries (openingPrefix (U.shs.get z.1.1).L (U.shs.get z.1.1).R)
    (z.1.2, z.2)
  rw [verifierFam_fam] at h
  rw [verifierFam_uSeeds]
  exact h.mono (hQV _ (by simp))

/-- **Fiat-Shamir soundness of the union family**, in stack terms (`roots_sound`). -/
theorem ufam_sound (U : UShapes ε) (A : OracleComp KeccakCalls (USt U.shs × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) (QV : ℕ) (hQV : ∀ s ∈ U.shs, s.QO ≤ QV) :
    Pr{let z ← romExperiment A (verifierFam (uSeeds U) (uProg U.shs))}[
        z.1.2 = true ∧ UFamDoomed U.shs z.1.1 z.2] ≤
      (QA + QV : ℕ) * (ε + failBound (uSeeds U) (QA + QV)) :=
  roots_sound (X := USt U.shs) (P := uProg U.shs) (root := uRoot U.shs)
    (fun x : USt U.shs ↦ (U.shs.get x.1).L.stacking) (fun x : USt U.shs ↦ (U.shs.get x.1).R)
    (fun x : USt U.shs ↦ x.2.claims) (uRootsOK U.shs) (uSeeds U) (fun _ ↦ rfl)
    (fun x : USt U.shs ↦ (U.shs.get x.1).adm) (fun x : USt U.shs ↦ x.2.short) ε
    (fun x : USt U.shs ↦ (U.shs.get x.1).hε) (fun x : USt U.shs ↦ (U.shs.get x.1).hB) A QA hA
    QV (uqueries U QV hQV)

/-- `union_sound` on bundled shapes. -/
theorem union_soundU (U : UShapes ε) (A : OracleComp KeccakCalls (UIn U.shs × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) (QV : ℕ) (hQV : ∀ s ∈ U.shs, s.QO ≤ QV) :
    Pr{let z ← romExperiment A (uVer U.shs)}[z.1.2 = true ∧ UDoomed U.shs z.1.1 z.2] ≤
      ((QA + QV : ℕ) : ℝ≥0∞) * (ε + ((5 * (QA + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set f : UIn U.shs × Proof → USt U.shs × Proof := fun w ↦ (⟨w.1.1, w.1.2.2⟩, w.2)
  have hA' : IsTotalQueryBound (f <$> A) QA := (isQueryBound_map_iff A f QA _ _).mpr hA
  have hfam := ufam_sound U (f <$> A) QA hA' QV hQV
  rw [romExperiment_map, prEvent_map] at hfam
  have hbound : ((QA + QV : ℕ) : ℝ≥0∞) * (ε + failBound (uSeeds U) (QA + QV)) =
      ((QA + QV : ℕ) : ℝ≥0∞) * (ε + ((5 * (QA + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
    rw [failBound]
    simp [uSeeds]
  rw [hbound] at hfam
  refine le_trans ?_ hfam
  have hV' : (fun w ↦ verifierFam (uSeeds U) (uProg U.shs) (f w)) = fun w ↦
      seedComp (openingPrefix (U.shs.get w.1.1).L (U.shs.get w.1.1).R) w.1.2.2.claims >>=
        fun seed ↦ runProofWithHash callKeccak256 callKeccakF1600
          (variantProg (U.shs.get w.1.1).L.stacking (U.shs.get w.1.1).R w.1.2.2.claims) seed w.2 :=
    funext fun w ↦ (verifierFam_uSeeds U (f w)).trans (verifierComp_famSeed _ _ _ _)
  have hO : uVer U.shs = fun w ↦ if w.1.2.2.claims.isEmpty = false then
      (seedComp (openingPrefix (U.shs.get w.1.1).L (U.shs.get w.1.1).R) w.1.2.2.claims >>=
        fun seed ↦ if rootOf w.2 = some w.1.2.1 then
          runProofWithHash callKeccak256 callKeccakF1600
            (variantProg (U.shs.get w.1.1).L.stacking (U.shs.get w.1.1).R w.1.2.2.claims) seed w.2
        else pure false) else pure false :=
    funext fun w ↦ ourVerifier_eq _ _ (w.1.2, w.2)
  rw [hV', hO]
  refine romExperiment_le_of_reject A
    (fun w ↦ seedComp (openingPrefix (U.shs.get w.1.1).L (U.shs.get w.1.1).R) w.1.2.2.claims)
    (fun w seed ↦ runProofWithHash callKeccak256 callKeccakF1600
      (variantProg (U.shs.get w.1.1).L.stacking (U.shs.get w.1.1).R w.1.2.2.claims) seed w.2)
    (fun w ↦ w.1.2.2.claims.isEmpty = false) (fun w ↦ rootOf w.2 = some w.1.2.1)
    (fun w cache ↦ UDoomed U.shs w cache)
    (fun w cache ↦ UFamDoomed U.shs (f w) cache) fun w cache _ hr hbad ↦ ?_
  intro r hr' q hq
  rw [hr'] at hr
  obtain rfl := (Option.some.inj hr).symm
  obtain ⟨cl, hcl, hne⟩ := hbad q hq
  exact ⟨cl, hcl, fun h ↦ hne
    (((U.shs.get w.1.1).L.holds_iff (U.shs.get w.1.1).hL cl (w.1.2.2.wide cl hcl) q).1 h)⟩

/-- **Fiat-Shamir soundness of several openings at once**: for shapes whose verifier prefixes
are distinct, an adversary of at most `QA` queries to Keccak-256 and Keccak-f[1600] that outputs
a shape's index, a root, claims on that shape's layout and a proof makes that shape's
`opening::verify` accept while every candidate table of the word extracted for the root violates
one of the claims with probability at most `(QA + QV) · (ε + 5 (QA + QV) / 2^256)`, `QV` above
every shape's query count. -/
theorem union_sound (shs : List (ExactShape ε))
    (hpre : (shs.map fun s ↦ openingPrefix s.L s.R).Nodup)
    (A : OracleComp KeccakCalls (UIn shs × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hQV : ∀ s ∈ shs, s.QO ≤ QV) :
    Pr{let z ← romExperiment A (uVer shs)}[z.1.2 = true ∧ UDoomed shs z.1.1 z.2] ≤
      ((QA + QV : ℕ) : ℝ≥0∞) * (ε + ((5 * (QA + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  union_soundU ⟨shs, hpre⟩ A QA hA QV hQV

end Union

/-! ## Distinct prefixes -/

/-- **The prefix names `log_n`** (the `u64 L.logN` field, bytes `60 .. 68`), for `log_n < 2^64`. -/
theorem openingPrefix_logN {L L' : Layout} {R R' : ℕ} (h : openingPrefix L R = openingPrefix L' R')
    (hL : L.logN < 2 ^ 64) (hL' : L'.logN < 2 ^ 64) : L.logN = L'.logN := by
  have hlen : ∀ M : Layout, (label ++ u64 version ++ layoutId M).length = 60 := fun M ↦ by
    simp [u64, wordBytes, layoutId, digestBytes, label]
  have hlen4 : ∀ M : Layout,
      (label ++ u64 version ++ layoutId M ++ u64 M.logN).length = 68 := fun M ↦ by
    simp [u64, wordBytes, layoutId, digestBytes, label]
  unfold openingPrefix at h
  obtain ⟨h1, -⟩ := List.append_inj h (by rw [hlen4, hlen4])
  obtain ⟨-, h2⟩ := List.append_inj h1 (by rw [hlen, hlen])
  have h3 := congrArg UInt64.toNat (wordBytes_injective h2)
  simp only [Nat.toUInt64, UInt64.toNat_ofNat'] at h3
  rwa [Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hL'] at h3

/-- A list maps injectively under `f` where `f` determines `g` and `g` is injective. -/
theorem nodup_map_of_factor {α β γ : Type} {f : α → β} {g : α → γ} :
    ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, f a = f b → g a = g b) → (l.map g).Nodup →
      (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h, hg => by
    rw [List.map_cons, List.nodup_cons] at hg ⊢
    refine ⟨fun hm ↦ hg.1 ?_, nodup_map_of_factor (fun x hx y hy ↦
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hg.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
    exact List.mem_map.2 ⟨b, hb, h b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) hfb⟩

/-- **Shapes of distinct `log_n` have distinct prefixes.** -/
theorem nodup_prefix_of_logN {ε : ℝ≥0∞} {l : List (ExactShape ε)}
    (hb : ∀ s ∈ l, s.L.logN < 2 ^ 64) (h : (l.map fun s ↦ s.L.logN).Nodup) :
    (l.map fun s ↦ openingPrefix s.L s.R).Nodup :=
  nodup_map_of_factor (fun a ha b hb' hab ↦ openingPrefix_logN hab (hb a ha) (hb b hb')) h

/-! ## The plain layouts of `2^24 ..= 2^28` words -/

/-- A plain layout of `2^v` words (one chunk, lane `l` its block `l`) is one `Layout::new`
accepts (copied from `UniSound/FsOps.lean`'s `newOK_plain`, not imported). -/
theorem newOK_plain_large (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) : NewOK v v v [(0, 2 ^ v)] := by
  interval_cases v <;> decide +kernel

/-- **The plain shape of `2^v` words** at `εExact`. -/
@[reducible] noncomputable def plainShapeE (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) :
    ExactShape εExact :=
  ExactShape.large v v v [(0, 2 ^ v)] (newOK_plain_large v h1 h2) h1 h2

/-- **The plain shapes of `2^24 ..= 2^28` words**, at `εExact`. -/
noncomputable def largeShapes : List (ExactShape εExact) :=
  [plainShapeE 24 le_rfl (by norm_num), plainShapeE 25 (by norm_num) (by norm_num),
    plainShapeE 26 (by norm_num) (by norm_num), plainShapeE 27 (by norm_num) (by norm_num),
    plainShapeE 28 (by norm_num) le_rfl]

theorem largeShapes_logN : largeShapes.map (fun s ↦ s.L.logN) = [24, 25, 26, 27, 28] := rfl

/-- **The plain shapes' prefixes are distinct** (their `log_n` are). -/
theorem largeShapes_nodup : (largeShapes.map fun s ↦ openingPrefix s.L s.R).Nodup := by
  refine nodup_prefix_of_logN (fun s hs ↦ ?_) (by rw [largeShapes_logN]; decide)
  have h := List.mem_map_of_mem (f := fun s : ExactShape εExact ↦ s.L.logN) hs
  rw [largeShapes_logN] at h
  simp at h
  omega

/-- **Every plain layout of `2^24 ..= 2^28` words is a shape of `largeShapes`.** -/
theorem largeShapes_plain (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) :
    ∃ s ∈ largeShapes, s.L = Layout.new v v v [(0, 2 ^ v)] ∧ s.R = logInvRate := by
  refine ⟨plainShapeE v h1 h2, ?_, rfl, rfl⟩
  interval_cases v
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- **The plain shapes' query counts** are at most `9018` (`largeQueries_eq`). -/
theorem largeShapes_QO : ∀ s ∈ largeShapes, s.QO ≤ 9018 := by
  intro s hs
  obtain ⟨h24, h25, h26, h27, h28⟩ := largeQueries_eq
  simp only [largeShapes, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · show largeQueries 24 ≤ 9018
    omega
  · show largeQueries 25 ≤ 9018
    omega
  · show largeQueries 26 ≤ 9018
    omega
  · show largeQueries 27 ≤ 9018
    omega
  · show largeQueries 28 ≤ 9018
    omega

/-- The plain shapes' query counts are at most the uniform `10122` (`variantQueries`). -/
theorem largeShapes_QO_le : ∀ s ∈ largeShapes, s.QO ≤ 10122 :=
  fun s hs ↦ (largeShapes_QO s hs).trans (by norm_num)

/-- **The plain shapes at once**: `union_sound` at `εExact` on `largeShapes`, `QV = 9018`. -/
theorem union_sound_large (A : OracleComp KeccakCalls (UIn largeShapes × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (uVer largeShapes)}[
        z.1.2 = true ∧ UDoomed largeShapes z.1.1 z.2] ≤
      ((QA + 9018 : ℕ) : ℝ≥0∞) * (εExact + ((5 * (QA + 9018) : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  union_sound largeShapes largeShapes_nodup A QA hA 9018 largeShapes_QO

end WhirBridge

/-- info: 'WhirBridge.union_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.union_sound

/-- info: 'WhirBridge.ufam_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ufam_sound

/-- info: 'WhirBridge.openingPrefix_logN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.openingPrefix_logN

/-- info: 'WhirBridge.largeShapes_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.largeShapes_nodup

/-- info: 'WhirBridge.largeShapes_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.largeShapes_plain

/-- info: 'WhirBridge.largeShapes_QO_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.largeShapes_QO_le

/-- info: 'WhirBridge.union_sound_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.union_sound_large
