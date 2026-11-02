-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The list decoder is leanerVM `mumbai`'s (https://github.com/Verified-zkEVM/leanerVM, commit
-- 6175f1a07f0dc33bd3d640de0063d1006143ee91, MIT OR Apache-2.0): `decodeStacks` of
-- `Statement/Extractor.lean` (CompPoly's Guruswami–Sudan decoder over `K`, lane by lane, then
-- the pruning across lanes), with its completeness and soundness
-- (`lean_vm/LeanVM/Protocol/Extraction/Prune.lean`) and the bridge from its candidates to the
-- specification's (`lean_vm/LeanVM/Protocol/EndToEnd/Sound/Extractor.lean`). They are used as
-- they are, imported; nothing of them is copied.
import Compose.ComposedKC
import Compose.Extract
import WhirBridge.Verifier
import LeanVM.Protocol.Extraction.Prune
import LeanVM.Protocol.EndToEnd.Sound.Extractor

/-!
# The decoder: the Johnson list, computed

`Final.lean`'s extractor climbs the witness table's Merkle tree and decodes the word with a
`TableCode`'s `dec`, a parameter there. Here it is a computable list decoder whose output is
**exactly** the list F2's opening soundness (`WhirBridge.ours_sound`, `OpeningDoomed`) quantifies
over: mumbai's `Candidates μ R (code₀ μ R).thr W`, the stacks whose encoding agrees with the
committed word on at least level 0's Johnson threshold of columns.

* **`decodeColumns μ R W`**: mumbai's `decodeStacks` (`Statement/Extractor.lean`): each of the
  `2^6` lanes of the word is list decoded by CompPoly's Guruswami–Sudan decoder over
  `K = GF(2^64)` (Lee–O'Sullivan interpolation, Roth–Ruckenstein roots, Shoup's trace splitter),
  on the `n = 2^(μ−6+R)` points `x_v = K.ofBits v` of the additive (novel-basis) Reed–Solomon
  code leanVM's WHIR commits with, at agreement `A = johnsonThreshold μ R`; the lanes' lists are
  then pruned prefix by prefix, a prefix kept while its lanes agree with the word on at least `A`
  common columns. Computable (a compiled `def`), deterministic.
* **`mem_decodeColumns`**: at every admissible shape, `q ∈ decodeColumns μ R W ↔
  q ∈ Candidates μ R (code₀ μ R).thr W`; **`nodup_decodeColumns`**: without repetition; so
  **`length_decodeColumns`**: its length *is* the number of candidates, at most level 0's
  certified `listHi` (`length_decodeColumns_le`), `≤ 2^18` at every admissible shape.
* **Tables** (`decodeTables`): each stack read back through the layout, `Layout.table`
  (`Table::read`: for a hidden layout `Layout.readHidden`, the overflow and share lanes summed,
  the odd lanes' pieces swapped; for a public one its blocks), as the `2^vars` entries
  (`tabOf`). `mem_decodeTables`: the tables of exactly the candidates;
  **`doomed_iff_decodeTables`**: F2's doom (every candidate's table violates a claim) is the same
  statement about the decoded list, a decidable one.
* **The Merkle word** (`merkleTables`): the decoder applied to `merkleWord`'s word read as
  mumbai's rows (`wordOfMerkle`). With the answers injective on the history,
  `candidates_wordOfMerkle`: its candidates are those of mumbai's `extract` of the root, the
  word of `OpeningDoomed`.
* **`tableCode L R hw read`**: the `TableCode` of `Final.lean` for **any** F2 layout `L` (public
  or hidden, `WhirBridge.Layout`; the read-back is `L.table`, whatever `Table::read` the layout
  transcribes) at an admissible rate `2^-R`: Merkle height `rootHeight`, leaves of `8 · 64` bytes,
  bound the certified `listHi`, and `dec` the decoded tables read as messages by `read`.
  `witnessCode`, `quotientCode`, `wiringCode`: at `WhirBridge`'s `witnessLayout`,
  `quotientLayout`, `wiringLayout` for `17 ≤ log_rows ≤ 22`, bounds `≤ 2^18`
  (`witnessCode_bound`, …, from `listHi_ours`), and at `log_rows = 22` exactly `7908`, `3564`,
  `9952` (`witnessCode_bound_deployed`, …, `listHi_deployed`). These read only the layouts'
  `logN` (decided), so a change of the hidden layouts' transcription that keeps their stack sizes
  leaves them as they are.
* **`knowledgeSoundness_decoded_kc`**: `knowledgeSoundness_merkle_kc` with `c₁ = witnessCode`,
  `c₂ = quotientCode`, its list hypotheses `h₁`, `h₂` discharged; `_certified` (through
  `knowledgeSoundness_merkle_kc_certified`, the `2^-138` form in mumbai's model for any codes of
  at most `7908` / `3564`): at `log_rows = 22`. `mem_witnessExtractor`: what the extractor
  returns, the reads of the candidates of mumbai's `extract` of the first root (no collision in
  the transcript).

**What `read` is.** F1's messages (`B.Msg₁`, `B.Msg₂`) are tuples of `Polynomial`s over the field
`F` of `2^192` elements (concretely `formal/Field/F192.lean`'s `F192`, CompPoly's `BF64.Ext3`, which
is mumbai's `E`: a table's `K` entries embed by `ofK`, `F192.ofF64`); how a table stands for a
message (the row polynomials of its columns, their masks) is the wire's, not the decoder's, so
`read` is a parameter (any function, computable or not). Everything up to the tables is
computable: `DecoderAxioms.lean` audits the definitions (no axiom outside proofs and types; their
`#print axioms` lists `Classical.choice` through `BF64`'s `Field` instance's proofs only).

**The cost** (`DecoderCost.lean`). The decoder makes at most `64` calls of the lane decoder, one
per lane, each on `n` points with multiplicity `m` and weighted degree `W = m·A − 1` (so a
`Y`-degree at most `ℓ = ⌊W/(k−1)⌋`, `k = 2^(μ−6)`), whose values are computed by the kernel
(`gsShape_witness`, `gsShape_quotient`, `gsShape_wiring`): for the witness table at
`log_rows = 22` (`μ = 25`), `n = 2^20`, `A = 741549`, `m = 1149`, `ℓ = 1625`, so
`n·m(m+1)/2 = 692767948800` interpolation conditions; for the quotient table (`μ = 28`),
`n = 2^23`, `A = 5933305`, `m = 522`, `ℓ = 738`, `1145070157824` conditions. Every intermediate
list is bounded by the certified list size: each lane's list and the prefixes kept after every
lane are at most `listMax ≤ listHi` (`length_laneListAt_le`, `length_pruneUpTo_le`, proved
through the Johnson bound of the interleaved code), so the pruning is at most `64 · listHi² · n`
symbol comparisons and `64 · listHi` forward transforms of `(μ − 6)·n` butterflies. The
interpolation (Lee–O'Sullivan with Mulders–Storjohann's reduction, on a basis of `ℓ + 1`
bivariate polynomials of `X`-degree at most `n·m`) dominates: polynomial in `n`, `m`, `ℓ`, but at
these sizes far from practical; an honest word (no errors) is decoded by mumbai's `fastStacks`
(interpolation alone) instead. The running time of CompPoly's interpolation and root finding is
read off the algorithms, not proved. `Test/DecoderToy.lean` runs the same code (`decodeStacksAt`)
at a toy shape.
-/

set_option linter.unusedSectionVars false

namespace Compose

open QuotientRpm
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd

/-! ## The decoder of a level-0 word -/

/-- **The list decoder** of a level-0 word of the stack of `2^μ` words at rate `2^-R`: mumbai's
`decodeStacks` (the `2^6` lanes list decoded by Guruswami–Sudan over `K` at the Johnson
threshold `johnsonThreshold μ R`, then pruned across lanes), each stack as a column. -/
def decodeColumns (μ R : ℕ) (W : Word) : List (Column μ) :=
  (LeanVM.Extraction.decodeStacks μ R W).map Column.mk

theorem admissible_bounds {μ R : ℕ} (hw : Whir.Admissible μ R) :
    (15 ≤ μ ∧ μ ≤ 28) ∧ (1 ≤ R ∧ R ≤ 4) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  unfold Whir.minLogStack at h1
  unfold Whir.maxLogStack at h2
  unfold Whir.minLogInvRate at h3
  unfold Whir.maxLogInvRate at h4
  omega

/-- Level 0's threshold is the decoder's (`thrOf_eq_johnsonThreshold`). -/
theorem thr_eq {μ R : ℕ} (hw : Whir.Admissible μ R) :
    (WhirBridge.code₀ μ R).thr = LeanVM.Extraction.johnsonThreshold μ R := by
  obtain ⟨level, rest, hc⟩ := Sound.exists_ladder hw
  exact Sound.thrOf_eq_johnsonThreshold hw hc

/-- **The decoder returns exactly the candidates**: at every admissible shape, a stack is in
the decoder's list iff its encoding agrees with the word on at least level 0's Johnson threshold
of columns. -/
theorem mem_decodeColumns {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) (q : Column μ) :
    q ∈ decodeColumns μ R W ↔ q ∈ Candidates μ R (WhirBridge.code₀ μ R).thr W := by
  obtain ⟨hμ, hR⟩ := admissible_bounds hw
  rw [thr_eq hw, decodeColumns]
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    exact Sound.candidates_of_values
      (LeanVM.Extraction.PruneProofs.decodeStacksAt_sound (by simp only [Whir.initialFold]; omega)
        (by simp only [Whir.initialFold]; omega) W hv)
  · intro h
    have hv := LeanVM.Extraction.PruneProofs.candidates_subset_decodeStacks hμ hR W
      (Sound.mem_candidates h le_rfl)
    rw [Set.mem_ofPred_eq] at hv
    exact List.mem_map.mpr ⟨q.values, hv, rfl⟩

theorem column_mk_injective (μ : ℕ) : Function.Injective (Column.mk : _ → Column μ) :=
  fun _ _ h ↦ congrArg Column.values h

/-- **Without repetition.** -/
theorem nodup_decodeColumns {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) :
    (decodeColumns μ R W).Nodup := by
  obtain ⟨hμ, -⟩ := admissible_bounds hw
  rw [decodeColumns]
  exact (LeanVM.Extraction.PruneProofs.nodup_decodeStacksAt
    (by simp only [Whir.initialFold]; omega) W).map (column_mk_injective μ)

/-- **The decoder's list is the candidate set**, as a finite set. -/
theorem decodeColumns_toSet {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) :
    {q | q ∈ decodeColumns μ R W} = Candidates μ R (WhirBridge.code₀ μ R).thr W := by
  ext q
  exact mem_decodeColumns hw W q

/-- **The list's length is the number of candidates.** -/
theorem length_decodeColumns {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) :
    (decodeColumns μ R W).length = (Candidates μ R (WhirBridge.code₀ μ R).thr W).ncard := by
  classical
  rw [← decodeColumns_toSet hw W]
  have : {q | q ∈ decodeColumns μ R W} = ↑(decodeColumns μ R W).toFinset := by
    ext q
    simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_decodeColumns hw W)]

/-- **At most the certified list size** `listHi` of level 0 (`listMax ≤ listHi`). -/
theorem length_decodeColumns_le {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) :
    (decodeColumns μ R W).length ≤ (Whir.Params.certOf μ R 0).listHi :=
  (length_decodeColumns hw W).le.trans
    ((WhirBridge.candidates_count hw W).2.trans (WhirBridge.listMax_le_listHi hw))

/-! ## Tables -/

/-- A table of the layout `L`: its `2^vars` entries. -/
abbrev Tab (L : WhirBridge.Layout) : Type := Vector K (2 ^ L.vars)

/-- **The table a stack stands for**, entry by entry `Layout.table` (`Table::read`). -/
def tabOf (L : WhirBridge.Layout) (q : Column L.logN) : Tab L :=
  Vector.ofFn fun t ↦ L.table q t.val

/-- A table's multilinear extension at `p` (`Table::eval`). -/
def tabEval (L : WhirBridge.Layout) (T : Tab L) (p : List E) : E :=
  ∑ t : Fin (2 ^ L.vars), ofK T[t] * Verifier.eqEval (boolPoint L.vars t.val) p

theorem tabEval_tabOf (L : WhirBridge.Layout) (q : Column L.logN) (p : List E) :
    tabEval L (tabOf L q) p = L.tableEval q p := by
  rw [tabEval, WhirBridge.Layout.tableEval,
    ← Fin.sum_univ_eq_sum_range
      (fun t ↦ ofK (L.table q t) * Verifier.eqEval (boolPoint L.vars t) p)]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [tabOf, Fin.getElem_fin, Vector.getElem_ofFn]

/-- **The decoded tables**: each decoded stack read back through the layout. -/
def decodeTables (L : WhirBridge.Layout) (R : ℕ) (W : Word) : List (Tab L) :=
  (decodeColumns L.logN R W).map (tabOf L)

/-- The decoded tables are the tables of exactly the candidates. -/
theorem mem_decodeTables {L : WhirBridge.Layout} {R : ℕ} (hw : Whir.Admissible L.logN R)
    (W : Word) (T : Tab L) :
    T ∈ decodeTables L R W ↔
      ∃ q ∈ Candidates L.logN R (WhirBridge.code₀ L.logN R).thr W, tabOf L q = T := by
  simp only [decodeTables, List.mem_map, mem_decodeColumns hw]

theorem length_decodeTables_le {L : WhirBridge.Layout} {R : ℕ} (hw : Whir.Admissible L.logN R)
    (W : Word) : (decodeTables L R W).length ≤ (Whir.Params.certOf L.logN R 0).listHi := by
  rw [decodeTables, List.length_map]
  exact length_decodeColumns_le hw W

/-- **F2's doom is a statement about the decoded list**: every candidate's table violates one of
the claims (`OpeningDoomed`, over the noncomputable candidate set) iff every decoded table
does. -/
theorem doomed_iff_decodeTables {L : WhirBridge.Layout} {R : ℕ} (hw : Whir.Admissible L.logN R)
    (W : Word) (claims : List WhirBridge.Claim) :
    (∀ q ∈ Candidates L.logN R (WhirBridge.code₀ L.logN R).thr W,
        ∃ cl ∈ claims, L.tableEval q cl.point ≠ cl.value) ↔
      ∀ T ∈ decodeTables L R W, ∃ cl ∈ claims, tabEval L T cl.point ≠ cl.value := by
  constructor
  · intro h T hT
    obtain ⟨q, hq, rfl⟩ := (mem_decodeTables hw W T).mp hT
    simpa only [tabEval_tabOf] using h q hq
  · intro h q hq
    simpa only [tabEval_tabOf] using h (tabOf L q) ((mem_decodeTables hw W _).mpr ⟨q, hq, rfl⟩)

/-! ## The Merkle word -/

/-- The candidates read only the columns of the code. -/
theorem candidates_congr {μ R A : ℕ} {W W' : Word}
    (h : ∀ v < 2 ^ (μ - laneBits + R), W v = W' v) :
    Candidates μ R A W = Candidates μ R A W' := by
  ext q
  simp only [Candidates, Set.mem_ofPred_eq, Agrees, laneOf]
  constructor
  · rintro ⟨S, hS, hag⟩
    exact ⟨S, hS, fun v hv u ↦ by rw [← h v v.isLt]; exact hag v hv u⟩
  · rintro ⟨S, hS, hag⟩
    exact ⟨S, hS, fun v hv u ↦ by rw [h v v.isLt]; exact hag v hv u⟩

/-- The bytes of a level-0 leaf: `2^6` words of `8` bytes. -/
abbrev leafBytes : ℕ := 8 * 2 ^ WhirBridge.laneFold

/-- **The candidates of the Merkle word are those of mumbai's `extract`** of the root, the word
of F2's `OpeningDoomed`, when the answers are injective on the history
(`wordOfMerkle_eq_extract` on the code's columns). -/
theorem candidates_wordOfMerkle {H : Hist} {T : Table} (hinj : Set.InjOn T ↑H) (D : Digest)
    (μ R A : ℕ) :
    Candidates μ R A (wordOfMerkle (WhirBridge.rootHeight μ R) (2 ^ WhirBridge.laneFold)
        (merkleWord H T (WhirBridge.rootHeight μ R) leafBytes (toB D))) =
      Candidates μ R A (Rom.extract (ansOf H T) D (WhirBridge.rootHeight μ R)
        (2 ^ WhirBridge.laneFold)) :=
  candidates_congr fun _ hv ↦ wordOfMerkle_eq_extract hinj D _ _ hv

/-- **The decoded tables of a Merkle word**: the word under a root, read off the history
(`merkleWord`), as mumbai's rows, decoded, read back as tables. -/
def merkleTables (L : WhirBridge.Layout) (R : ℕ)
    (w : Fin (2 ^ WhirBridge.rootHeight L.logN R) → Option (List UInt8)) : List (Tab L) :=
  decodeTables L R (wordOfMerkle (WhirBridge.rootHeight L.logN R) (2 ^ WhirBridge.laneFold) w)

/-- **The Merkle word's decoded tables are those of the candidates of mumbai's `extract`** of
the root, with the answers injective on the history. -/
theorem mem_merkleTables {L : WhirBridge.Layout} {R : ℕ} (hw : Whir.Admissible L.logN R)
    {H : Hist} {T : Table} (hinj : Set.InjOn T ↑H) (D : Digest) (X : Tab L) :
    X ∈ merkleTables L R (merkleWord H T (WhirBridge.rootHeight L.logN R) leafBytes (toB D)) ↔
      ∃ q ∈ Candidates L.logN R (WhirBridge.code₀ L.logN R).thr
          (Rom.extract (ansOf H T) D (WhirBridge.rootHeight L.logN R) (2 ^ WhirBridge.laneFold)),
        tabOf L q = X := by
  rw [merkleTables, mem_decodeTables hw, candidates_wordOfMerkle hinj]

/-! ## The table codes -/

/-- **The `TableCode` of a layout** at rate `2^-R`: the Merkle tree of level 0 (height
`rootHeight`, leaves of `8 · 2^6` bytes), the certified list bound `listHi`, and the decoder:
the decoded tables of the Merkle word, each read as a message by `read`. -/
def tableCode (L : WhirBridge.Layout) (R : ℕ) (hw : Whir.Admissible L.logN R) {M : Type}
    (read : Tab L → M) : TableCode M where
  height := WhirBridge.rootHeight L.logN R
  leafLen := leafBytes
  bound := (Whir.Params.certOf L.logN R 0).listHi
  dec w := (merkleTables L R w).map read
  length_dec w := by
    rw [List.length_map, merkleTables]
    exact length_decodeTables_le hw _

theorem tableCode_dec (L : WhirBridge.Layout) (R : ℕ) (hw : Whir.Admissible L.logN R)
    {M : Type} (read : Tab L → M) (w : Fin (2 ^ WhirBridge.rootHeight L.logN R) →
      Option (List UInt8)) :
    (tableCode L R hw read).dec w = (merkleTables L R w).map read := by
  simp only [tableCode]

/-- **What the table code decodes, under a root**: with the answers injective on the history,
the messages `read` of the tables of the candidates of mumbai's `extract` of the root. -/
theorem mem_tableCode_dec {L : WhirBridge.Layout} {R : ℕ} (hw : Whir.Admissible L.logN R)
    {M : Type} (read : Tab L → M) {H : Hist} {T : Table} (hinj : Set.InjOn T ↑H) (D : Digest)
    (g : M) :
    g ∈ (tableCode L R hw read).dec
        (merkleWord H T (WhirBridge.rootHeight L.logN R) leafBytes (toB D)) ↔
      ∃ q ∈ Candidates L.logN R (WhirBridge.code₀ L.logN R).thr
          (Rom.extract (ansOf H T) D (WhirBridge.rootHeight L.logN R) (2 ^ WhirBridge.laneFold)),
        read (tabOf L q) = g := by
  rw [tableCode_dec, List.mem_map]
  constructor
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨q, hq, rfl⟩ := (mem_merkleTables hw hinj D X).mp hX
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨tabOf L q, (mem_merkleTables hw hinj D _).mpr ⟨q, hq, rfl⟩, rfl⟩

/-- A table code's list commitment has the code's bound. -/
theorem TableCode.commit_bound {M : Type} (c : TableCode M) : c.commit.bound = c.bound :=
  rfl

section Ours

open WhirBridge (witnessLayout quotientLayout wiringLayout logInvRate layouts_ok)

variable (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows) {M : Type}

/-- The witness table's code (`witness_layout`, hidden, rate `1/2`). -/
def witnessCode (read : Tab (witnessLayout r) → M) : TableCode M :=
  tableCode (witnessLayout r) logInvRate (layouts_ok r h1 h2).1 read

/-- The quotient table's code (`quotient_layout`, hidden, rate `1/2`). -/
def quotientCode (read : Tab (quotientLayout r) → M) : TableCode M :=
  tableCode (quotientLayout r) logInvRate (layouts_ok r h1 h2).2.2 read

/-- The wiring table's code (`wiring_layout`, public, rate `1/2`). -/
def wiringCode (read : Tab (wiringLayout r) → M) : TableCode M :=
  tableCode (wiringLayout r) logInvRate (layouts_ok r h1 h2).2.1 read

/-- The certified list sizes of our three layouts are at most `2^18`, at every supported size. -/
theorem listHi_ours : ∀ r, WhirBridge.minLogRows ≤ r → r ≤ WhirBridge.maxLogRows →
    (Whir.Params.certOf (witnessLayout r).logN logInvRate 0).listHi ≤ 2 ^ 18 ∧
      (Whir.Params.certOf (quotientLayout r).logN logInvRate 0).listHi ≤ 2 ^ 18 ∧
      (Whir.Params.certOf (wiringLayout r).logN logInvRate 0).listHi ≤ 2 ^ 18 := by
  decide +kernel

/-- At `log_rows = 22`: `7908` witness, `3564` quotient and `9952` wiring candidates. -/
theorem listHi_deployed :
    (Whir.Params.certOf (witnessLayout 22).logN logInvRate 0).listHi = 7908 ∧
      (Whir.Params.certOf (quotientLayout 22).logN logInvRate 0).listHi = 3564 ∧
      (Whir.Params.certOf (wiringLayout 22).logN logInvRate 0).listHi = 9952 := by
  decide +kernel

theorem witnessCode_bound (read : Tab (witnessLayout r) → M) :
    (witnessCode r h1 h2 read).bound ≤ 2 ^ 18 :=
  (listHi_ours r h1 h2).1

theorem quotientCode_bound (read : Tab (quotientLayout r) → M) :
    (quotientCode r h1 h2 read).bound ≤ 2 ^ 18 :=
  (listHi_ours r h1 h2).2.1

theorem wiringCode_bound (read : Tab (wiringLayout r) → M) :
    (wiringCode r h1 h2 read).bound ≤ 2 ^ 18 :=
  (listHi_ours r h1 h2).2.2

theorem witnessCode_bound_deployed (read : Tab (witnessLayout 22) → M) :
    (witnessCode 22 (by decide) (by decide) read).bound = 7908 :=
  listHi_deployed.1

theorem quotientCode_bound_deployed (read : Tab (quotientLayout 22) → M) :
    (quotientCode 22 (by decide) (by decide) read).bound = 3564 :=
  listHi_deployed.2.1

theorem wiringCode_bound_deployed (read : Tab (wiringLayout 22) → M) :
    (wiringCode 22 (by decide) (by decide) read).bound = 9952 :=
  listHi_deployed.2.2

end Ours

/-! ## The composed statement with the decoder -/

open OracleSpec OracleComp NNReal
open scoped ENNReal
open QuotientSecurity QuotientSecurity.Params LeanVM
open WhirBridge (witnessLayout quotientLayout)

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) {O : Type}

/-- **The extractor with the decoder**: the witness table's Merkle word under the proof's first
root, decoded, its tables read as first messages. With the transcript's answers injective on its
inputs (no collision), it returns the reads of the tables of exactly the candidates of mumbai's
`extract` of that root, F2's `OpeningDoomed` word. -/
theorem mem_witnessExtractor (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows)
    (read₁ : Tab (witnessLayout r) → B.Msg₁) (z : Run F O Verdicts × Transcript)
    (hinj : Set.InjOn (tableOfTr z.2) ↑(histOfTr z.2)) (g : B.Msg₁) :
    g ∈ witnessExtractor (witnessCode r h1 h2 read₁) z ↔
      ∃ q ∈ Candidates (witnessLayout r).logN WhirBridge.logInvRate
          (WhirBridge.code₀ (witnessLayout r).logN WhirBridge.logInvRate).thr
          (Rom.extract (ansOf (histOfTr z.2) (tableOfTr z.2)) (Digest.ofRpm z.1.proof.r₁)
            (WhirBridge.rootHeight (witnessLayout r).logN WhirBridge.logInvRate)
            (2 ^ WhirBridge.laneFold)),
        read₁ (tabOf (witnessLayout r) q) = g := by
  have hr : z.1.proof.r₁ = toB (Digest.ofRpm z.1.proof.r₁) := (LeanVM.Rpm.digestToRpm_ofRpm _).symm
  have he : witnessExtractor (witnessCode r h1 h2 read₁) z =
      (tableCode (witnessLayout r) WhirBridge.logInvRate (WhirBridge.layouts_ok r h1 h2).1
        read₁).dec (merkleWord (histOfTr z.2) (tableOfTr z.2)
          (WhirBridge.rootHeight (witnessLayout r).logN WhirBridge.logInvRate) leafBytes
          (toB (Digest.ofRpm z.1.proof.r₁))) := by
    rw [← hr]
    rfl
  rw [he]
  exact mem_tableCode_dec _ read₁ hinj _ g

/-- **Knowledge soundness composed with the openings, in mumbai's two-oracle model, with the
decoder**: `knowledgeSoundness_merkle_kc` for the witness and quotient tables' codes of our
layouts (any supported size `17 ≤ log_rows ≤ 22`), their list bounds discharged
(`listHi_ours`). What remains are the three openings' terms and the reads `read₁`, `read₂` of a
table as F1's messages. -/
theorem knowledgeSoundness_decoded_kc (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows)
    (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24) (hw : P.words = 8)
    (hd : B.identity ≤ 2 ^ 28)
    (read₁ : Tab (witnessLayout r) → B.Msg₁) (read₂ : Tab (quotientLayout r) → B.Msg₂)
    (A : OracleComp KeccakCalls (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp KeccakCalls Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WitnessDoomed (witnessCode r h1 h2 read₁).commit z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      QuotientDoomed W (quotientCode r h1 h2 read₂).commit z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
        Accepted (P := P) z ∧ ∀ g ∈ witnessExtractor (witnessCode r h1 h2 read₁) z,
          ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
        4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  knowledgeSoundness_merkle_kc W hq hN hw hd (witnessCode r h1 h2 read₁)
    (quotientCode r h1 h2 read₂) (witnessCode_bound r h1 h2 read₁)
    (quotientCode_bound r h1 h2 read₂) A openings Q QV hQ hV εW εσ εQ hW hσ hQd

/-- **`knowledgeSoundness_merkle_kc` with the certified lists**: for table codes of at most `7908`
witness and `3564` quotient candidates and identities of degree at most `2^29`, the reduction's
part is `(Q + 6 + QV) (2^-138 + 4 (Q + 6 + QV) / 2^256)` (as `knowledgeSoundness_merkle_certified`
in the one-oracle model). -/
theorem knowledgeSoundness_merkle_kc_certified (hq : Fintype.card F = 2 ^ 192)
    (hN : P.nCells = 2 ^ 24) (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 29)
    (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) (h₁ : c₁.bound ≤ 7908)
    (h₂ : c₂.bound ≤ 3564)
    (A : OracleComp KeccakCalls (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp KeccakCalls Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WitnessDoomed c₁.commit z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      QuotientDoomed W c₂.commit z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
        Accepted (P := P) z ∧
          ∀ g ∈ witnessExtractor c₁ z, ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 138 : ℝ≥0) : ℝ≥0∞) +
        4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_composed_kc W c₁.commit c₂.commit A openings Q QV hQ hV εW εσ εQ hW
    hσ hQd).trans ?_
  gcongr
  exact listError_le_certified hq hN hw hd h₁ h₂

/-- **The same at the deployed size** `log_rows = 22`, with the decoder: the certified lists
(`7908` witness, `3564` quotient candidates) and identities of degree at most `2^29`, the
reduction's part `(Q + 6 + QV) (2^-138 + 4 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_decoded_kc_certified (hq : Fintype.card F = 2 ^ 192)
    (hN : P.nCells = 2 ^ 24) (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 29)
    (read₁ : Tab (witnessLayout 22) → B.Msg₁) (read₂ : Tab (quotientLayout 22) → B.Msg₂)
    (A : OracleComp KeccakCalls (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp KeccakCalls Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WitnessDoomed (witnessCode 22 (by decide) (by decide) read₁).commit z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
      QuotientDoomed W (quotientCode 22 (by decide) (by decide) read₂).commit z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (kcExperiment W A openings)).run' ∅}[
        Accepted (P := P) z ∧
          ∀ g ∈ witnessExtractor (witnessCode 22 (by decide) (by decide) read₁) z,
            ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 138 : ℝ≥0) : ℝ≥0∞) +
        4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  knowledgeSoundness_merkle_kc_certified W hq hN hw hd
    (witnessCode 22 (by decide) (by decide) read₁) (quotientCode 22 (by decide) (by decide) read₂)
    (witnessCode_bound_deployed read₁).le (quotientCode_bound_deployed read₂).le A openings Q QV
    hQ hV εW εσ εQ hW hσ hQd

end Compose
