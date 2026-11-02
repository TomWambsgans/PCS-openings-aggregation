/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

The three layouts `crates/quotient/src/protocol.rs` opens (`wiring_layout`, `witness_layout`,
`quotient_layout`), through the mirrors of `Layout::new` and `Layout::hidden`, for every supported
circuit size, and what the bridge's theorems need of them, decided.
-/
import WhirBridge.Hidden

/-!
# Our layouts

`wiringLayout r`, `witnessLayout r`, `quotientLayout r` transcribe `protocol.rs:84-144` at
`2^r` rows: the wiring table public (`Layout::new`), the witness and quotient tables hidden
(`Layout::hidden`, `7` random lanes, pieces of `2^8`). For every supported size
(`MIN_LOG_ROWS = 17 ≤ r ≤ MAX_LOG_ROWS = 22`), decided by kernel evaluation (`decide +kernel`, no
`native_decide`):

* `layouts_ok`: their stacks (`log_n = m`, `m + 1`, `m + 4`, `m = r + 2`) are admissible at rate
  `1/2`, the shapes mumbai's deployed WHIR codes cover;
* `layouts_valid`: each is `Layout.Valid` (the wiring layout a valid public stacking, the other two
  `HiddenOK` with pieces of `2^8`), what `Layout.holds_iff` needs;
* `layouts_shape`: `40`, `64`, `63` lanes, the overflow and share lanes `38, 39` and `61, 62`,
  `33` and `167` pieces, as `review_f2f3.rs` checks of the Rust.

The Rust's constructors are transcribed, not trusted: `Test/Check.lean` recomputes the 76-byte
prefix of each of the 18 layouts (its id is Keccak-256 of every field) and compares it with the
Rust's, and runs the Lean verifier on deployed openings of all three tables.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier

/-- `cell_vars(log_rows) = log_rows + 2` (`protocol.rs:84-87`). -/
def cellVars (logRows : ℕ) : ℕ := logRows + 2

/-- `MIN_LOG_ROWS` (`protocol.rs:104`). -/
def minLogRows : ℕ := 17

/-- `MAX_LOG_ROWS` (`protocol.rs:107`). -/
def maxLogRows : ℕ := 22

/-- `LOG_PIECE` (`opening.rs:52`). -/
def logPieceDeployed : ℕ := 8

/-- `WITNESS_RANDOM_LANES` (`protocol.rs:97`). -/
def witnessRandomLanes : ℕ := 7

/-- `QUOTIENT_RANDOM_LANES` (`protocol.rs:100`). -/
def quotientRandomLanes : ℕ := 7

/-- `wiring_layout` (`protocol.rs:90-93`): the stack is the table, public. -/
def wiringLayout (logRows : ℕ) : Layout :=
  Layout.new (cellVars logRows) (cellVars logRows) (cellVars logRows) [(0, 2 ^ cellVars logRows)]

/-- `witness_layout` (`protocol.rs:116-119`): the four row polynomials, then their masks, sixteen
entries of the next chunk; hidden. -/
def witnessLayout (logRows : ℕ) : Layout :=
  Layout.hidden (cellVars logRows + 1) (cellVars logRows) (cellVars logRows + 1)
    [(0, 2 ^ cellVars logRows), (1, 16)] witnessRandomLanes logPieceDeployed

/-- `Q_SPILL = PUBLIC_EXCESS + 64` (`protocol.rs:34-37`). -/
def qSpill : ℕ := 9216 + 64

/-- `quotient_chunks(m, spill, tail)` (`protocol.rs:133-144`). -/
def quotientChunks (m spill tail : ℕ) : List (ℕ × ℕ) :=
  let n := 2 ^ m
  ((List.range 3).flatMap fun e ↦
      (16 * e, n) :: (List.range 3).map (fun digit ↦ (16 * e + 4 + digit, n)) ++
        [(16 * e + 7, spill)]) ++
    [(8, n), (9, 3 * n / 4 + tail)]

/-- `quotient_layout` (`protocol.rs:126-129`): `m + 6` variables, stacked in lanes of a quarter
chunk; hidden. -/
def quotientLayout (logRows : ℕ) : Layout :=
  Layout.hidden (cellVars logRows + 6) (cellVars logRows) (cellVars logRows + 4)
    (quotientChunks (cellVars logRows) qSpill 64) quotientRandomLanes logPieceDeployed

/-- `LOG_ROWS` (`crates/quotient/src/circuit.rs`): the deployed size. -/
def logRows : ℕ := 22

/-- The hidden shape's conditions as one decidable conjunction. -/
def HiddenOKb (L : Layout) (s : ℕ) : Prop :=
  L.logPiece = some s ∧ laneFold ≤ L.logN ∧ s < L.logLane ∧ L.logLane ≤ L.vars ∧
    L.lanes.length ≤ 2 ^ laneFold ∧ L.pieces.length < 2 ^ (L.logLane - s) ∧
    L.lanes[L.overflow]? = some .overflow ∧ L.lanes[L.share.getD 0]? = some .random ∧
    L.pieces.Nodup ∧ (∀ p ∈ L.pieces, p < 2 ^ (L.vars - s)) ∧
    (L.blockLanes.map Prod.fst).Nodup ∧
    ∀ bi ∈ L.blockLanes, bi.1 < 2 ^ (L.vars - L.logLane) ∧
      bi.2 % 2 + 2 ^ (L.logLane - s) * bi.1 ∈ L.pieces ∧
      ∀ p ∈ L.pieces, p / 2 ^ (L.logLane - s) = bi.1 → p % 2 ^ (L.logLane - s) = bi.2 % 2

instance (L : Layout) (s : ℕ) : Decidable (HiddenOKb L s) := by
  unfold HiddenOKb; infer_instance

theorem HiddenOKb.toHiddenOK {L : Layout} {s : ℕ} (h : HiddenOKb L s) : L.HiddenOK s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The public shape's conditions as one decidable conjunction. -/
def PublicOKb (L : Layout) : Prop :=
  L.logPiece = none ∧ (∀ l ∈ L.lanes, l.blockD < 2 ^ (L.vars - L.logLane) ∧
      l = .block l.blockD) ∧
    laneFold ≤ L.logN ∧ L.logLane ≤ L.vars ∧ L.lanes.length ≤ 2 ^ laneFold

instance (L : Layout) : Decidable (PublicOKb L) := by
  unfold PublicOKb; infer_instance

theorem PublicOKb.toValid {L : Layout} (h : PublicOKb L) : L.Valid := by
  refine Or.inl ⟨⟨h.1, fun l hl ↦ ⟨l.blockD, (h.2.1 l hl).2⟩⟩, ⟨h.2.2.1, h.2.2.2.1, ?_, ?_⟩⟩
  · simpa [Blocks.lanes, Layout.toBlocks] using h.2.2.2.2
  · intro b hb
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hb
    exact (h.2.1 l hl).1

/-- **Our layouts' stacks are admissible** at rate `1/2`, for every supported size. -/
theorem layouts_ok : ∀ r, minLogRows ≤ r → r ≤ maxLogRows →
    Whir.Admissible (witnessLayout r).logN logInvRate ∧
      Whir.Admissible (wiringLayout r).logN logInvRate ∧
      Whir.Admissible (quotientLayout r).logN logInvRate := by
  decide +kernel

theorem layouts_okb : ∀ r, minLogRows ≤ r → r ≤ maxLogRows →
    HiddenOKb (witnessLayout r) logPieceDeployed ∧ PublicOKb (wiringLayout r) ∧
      HiddenOKb (quotientLayout r) logPieceDeployed := by
  decide +kernel

/-- **Our layouts are valid**, for every supported size: the meaning of their claims
(`Layout.holds_iff`) holds of them. -/
theorem layouts_valid (r : ℕ) (h1 : minLogRows ≤ r) (h2 : r ≤ maxLogRows) :
    (witnessLayout r).Valid ∧ (wiringLayout r).Valid ∧ (quotientLayout r).Valid :=
  have h := layouts_okb r h1 h2
  ⟨Or.inr ⟨_, h.1.toHiddenOK⟩, h.2.1.toValid, Or.inr ⟨_, h.2.2.toHiddenOK⟩⟩

/-- **Our layouts' shape** (what `review_f2f3.rs` checks of the Rust): `40`, `64`, `63` lanes;
the overflow and share lanes `L − 2`, `L − 1`; `33` and `167` pieces. -/
theorem layouts_shape : ∀ r, minLogRows ≤ r → r ≤ maxLogRows →
    (witnessLayout r).lanes.length = 40 ∧ (wiringLayout r).lanes.length = 64 ∧
      (quotientLayout r).lanes.length = 63 ∧
      (witnessLayout r).overflow = 38 ∧ (witnessLayout r).share = some 39 ∧
      (quotientLayout r).overflow = 61 ∧ (quotientLayout r).share = some 62 ∧
      (witnessLayout r).pieces.length = 33 ∧ (quotientLayout r).pieces.length = 167 := by
  decide +kernel

/-- At `LOG_ROWS = 22`: the witness, wiring and quotient stacks have `25`, `24`, `28`
variables. -/
theorem deployed_sizes :
    (witnessLayout logRows).logN = 25 ∧ (wiringLayout logRows).logN = 24 ∧
      (quotientLayout logRows).logN = 28 := by
  decide +kernel

end WhirBridge
