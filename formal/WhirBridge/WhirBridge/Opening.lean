/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

The opening check of `crates/quotient/src/opening.rs` (`verify`, with `Layout`) as a program of the
verifier language of leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0,
MIT OR Apache-2.0: `Statement/LeanVmVerifier.lean`, its transcription of leanVM's verifier at
`c445e3d5`), and its reading as mumbai's stacked opening `verifyStackedOpening`. The hidden branch of
the weight started from the review's transcription (`formal/Review/HiddenWeight.lean`, this
repository, commit 4d5dd40), and follows the hidden layout's redesign with the gadget.
-/
import LeanVM.Protocol.Whir.Sound.Spec
import LeanVM.Protocol.EndToEnd.Sound.Glue

/-!
# The opening check

`opening::verify(layout, root, claims, proof)` (`crates/quotient/src/opening.rs:780-887`):

1. reject unless every claim's point has the table's `vars` coordinates;
2. start the transcript from the IV `keccak256(prefix(layout) ‖ claims)` and a zero public digest
   (`iv`, `opening.rs:633-643`), read the root as the proof's first two scalars and reject unless it
   is the root expected;
3. sample `λ`, set `λ_i = λ^i` for `i ≤ m` (`m` claims: one power more than the claims, the
   gadget's), the target `Σ_{i<m} λ_i v_i`, and the weight closure (`opening.rs:841-876`): per
   claim, its point's lane coordinates and its scales (`Layout::scales`, `opening.rs:284-301`) times
   `λ_i`, then, at a stack point `x = low ‖ high`, the sum of the claims' terms and the gadget's:
   * a **public** layout (`log_piece = None`): `eq(p[..ℓ], low) · on_blocks`, `on_blocks` the
     lane sum `Σ_l scale_l · eq_index(high, l)` over the block lanes; no gadget;
   * a **hidden** layout (`log_piece = Some(s)`): `below · ((above + first_above · first_piece) ·
     on_blocks + pieces · on_overflow)`, the block lanes' `eq` with their first piece taken out and
     the overflow lane's pieces; and the **gadget**, `λ_m · Σ_{g,i} β_i · eq_index(low, D + 3g + i)
     · Σ_{l ∈ pattern g} eq_index(high, l)` (`D = 2^s − 9`, patterns `{0, 31}`, `{1, 30}`, `{32}`,
     `β = 1, t, t²`): one more claim, of value zero;
4. `verify_whir(transcript, log_n, placed, LOG_INV_RATE, target, root, &weight)`, then
   `transcript.finish()`.

`Layout` mirrors the Rust struct field by field (`opening.rs:104-115`), `Layout.new` and
`Layout.hidden` its two constructors (`opening.rs:119-203`, the latter `hidden_with`), and
`Layout.check L R claims` is steps 1, 3 and 4 as a program of mumbai's language (`Prog`), each
definition below transcribing the Rust it names. Step 2 is `WhirBridge/Verifier.lean`
(`openingVerifyWithHash`); `placed` (the pruned Merkle form's zero prefix, which mumbai's full-leaf
`Proof` does not have) is not modelled.

`Layout.check_eq`: the program **is** mumbai's `verifyStackedOpening L.logN R (L.stacking.claims
claims)` after the length check (a `Stacking.check`): the same challenge, target and weight, each
claim's weight `Layout.claimWeight L c` being the Rust's per-claim term with its power of `λ` pulled
out, and a hidden layout's gadget (`Layout.gadgetWeight`, its power `λ^m` pulled out) one more stack
claim, of value zero, after the claims' (`Layout.extra`). `isMultiaffine_layoutClaimWeight`,
`isMultiaffine_gadgetWeight`: every such weight is multiaffine on the stack's `log_n` coordinates,
the hypothesis of mumbai's `stackedSpec`.

`Blocks` is the public stacking of a list of blocks (lane `l` holds block `blocks[l]`), with the
public claim weight `claimWeight`; `Table.lean` proves what a claim on it means for the table, and a
public `Layout` is one (`Layout.toBlocks`, `Table.lean`).
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)

/-- `LANE_FOLD` (`opening.rs:50`): the first fold of leanVM's WHIR, `2^6` lanes. -/
def laneFold : ℕ := 6

/-- `LOG_INV_RATE` (`opening.rs:590`): rate `1/2`. -/
def logInvRate : ℕ := 1

/-- A claim (`opening.rs:84-89`): the table's multilinear extension at `point` is `value`. The
Rust holds `F192` limbs; `ext` (`opening.rs:749-751`) reads them as the verifier's `E`, the same
field `K[y]/(y^3 + y + 1)`, `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`. -/
structure Claim where
  point : List E
  value : E

/-- `eq_bits(point, index)` (`opening.rs:400-404`), and the verifier's `eq_index`
(`opening.rs:836-840`): `Π_k (bit k of index ? p_k : 1 + p_k)`. -/
def eqBits (point : List E) (index : ℕ) : E :=
  point.zipIdx.foldl (fun w pk ↦ w * if (index >>> pk.2) % 2 = 1 then pk.1 else 1 + pk.1) 1

/-- The powers `verify` builds (`opening.rs:798-802`): `[1]`, then `last · λ` while there are at
most as many as claims: one per claim and one more, the gadget's (`opening.rs:824`). -/
def lambdas (lam : E) (n : ℕ) : List E := powers lam (n + 1)

/-- The target (`opening.rs:803-806`): `Σ λ_i v_i`, the claims zipped with the powers. -/
def target (ls : List E) (claims : List Claim) : E :=
  (claims.zip ls).foldl (fun acc cl ↦ acc + cl.2 * cl.1.value) 0

/-! ## A stacking: what mumbai's stacked opening needs of a layout -/

/-- **A stacking**: a table of `vars` variables committed as a stack of `logN` variables, one
claim's weight on the stack, multiaffine (the hypothesis of mumbai's `stackedSpec`), and the stack
claims the opening adds after the claims' (a hidden layout's gadget, of value zero), multiaffine
too. -/
structure Stacking where
  vars : ℕ
  logN : ℕ
  weight : Claim → List E → E
  multiaffine : ∀ c, IsMultiaffine logN (weight c)
  extra : List StackClaim
  extra_multiaffine : ∀ c ∈ extra, IsMultiaffine logN c.1

/-- The claims as mumbai's stack claims (`StackClaim`: a weight on the stack and a value), then the
stacking's own. -/
def Stacking.claims (S : Stacking) (cs : List Claim) : List StackClaim :=
  cs.map (fun c ↦ (S.weight c, c.value)) ++ S.extra

/-- **The opening of a stacking**: the length check, then mumbai's stacked opening of the claims. -/
def Stacking.check (S : Stacking) (R : ℕ) (cs : List Claim) : Prog Unit :=
  (Prog.require (∀ c ∈ cs, c.point.length = S.vars)).bind fun _ ↦
    verifyStackedOpening S.logN R (S.claims cs)

theorem Stacking.check_eq_ite (S : Stacking) (R : ℕ) (cs : List Claim) :
    S.check R cs =
      if ∀ c ∈ cs, c.point.length = S.vars then verifyStackedOpening S.logN R (S.claims cs)
      else Prog.fail := by
  rw [Stacking.check, Prog.require]
  split_ifs <;> rfl

theorem Stacking.length_claims (S : Stacking) (cs : List Claim) :
    (S.claims cs).length = cs.length + S.extra.length := by
  simp [Stacking.claims]

theorem Stacking.isMultiaffine_claims (S : Stacking) (cs : List Claim) :
    ∀ c ∈ S.claims cs, IsMultiaffine S.logN c.1 := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨c', -, rfl⟩ := List.mem_map.1 hc
    exact S.multiaffine c'
  · exact S.extra_multiaffine c hc

/-! ## The public stacking of a list of blocks -/

/-- A public stacking (`Layout::new`'s layouts): a table of `vars` variables, committed as a stack
of `log_n` variables whose lane `l` holds the table's block `blocks[l]` of `2^(log_n − 6)`
entries. -/
structure Blocks where
  vars : ℕ
  logN : ℕ
  blocks : List ℕ
  deriving DecidableEq, Repr

namespace Blocks

/-- `log_lane`. -/
def logLane (L : Blocks) : ℕ := L.logN - laneFold

/-- The lanes. -/
def lanes (L : Blocks) : ℕ := L.blocks.length

/-- Each lane's weight in a claim at `point`, `eq` of the point's high coordinates at the lane's
block (`Layout::scales` of a public layout, `opening.rs:284-292`). -/
def laneWeights (L : Blocks) (point : List E) : List E :=
  L.blocks.map fun b ↦ eqBits (point.drop L.logLane) b

end Blocks

/-- **One claim's weight on a public stack**: `eq(p[..ℓ], x[..ℓ]) · Σ_l lane_weight_l ·
eq(bits(l), x[ℓ..])`. -/
def claimWeight (L : Blocks) (c : Claim) (x : List E) : E :=
  ((c.point.take L.logLane).zip (x.take L.logLane)).foldl
      (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) 1 *
    ((L.laneWeights c.point).zip ((List.range L.lanes).map fun l ↦ eqBits (x.drop L.logLane) l)).foldl
      (fun s we ↦ s + we.1 * we.2) 0

/-- The claims as mumbai's stack claims. -/
def stackClaims (L : Blocks) (claims : List Claim) : List StackClaim :=
  claims.map fun c ↦ (claimWeight L c, c.value)

/-! ## The layout (`opening.rs:50-301`) -/

/-- What a lane of the stack holds (`Lane`, `opening.rs:91-101`). -/
inductive Lane where
  /-- The table's block `b` (in a hidden layout, all of it but its first piece). -/
  | block (b : ℕ)
  /-- Pieces of the table, at its pieces `1, 2, ...`. -/
  | overflow
  /-- Randomness. -/
  | random
  deriving DecidableEq, Repr

/-- **`Layout`** (`opening.rs:104-115`), field by field: the table's variables, the stack's, what
each lane holds, a hidden layout's piece `2^log_piece` (`none` for a public layout), and the table's
pieces the overflow lane holds at its pieces `1, 2, ...`. -/
structure Layout where
  vars : ℕ
  logN : ℕ
  lanes : List Lane
  logPiece : Option ℕ
  pieces : List ℕ
  deriving DecidableEq, Repr

/-- `GADGET` (`opening.rs:60`): the gadget's entries, the last of every lane's first piece. -/
def gadget : ℕ := 9

/-- `OVERFLOW_LANE` (`opening.rs:64`): the hidden layouts' overflow lane. -/
def overflowLane : ℕ := 32

/-- `gadget_lanes(g)` (`opening.rs:71-74`): the lanes of gadget pattern `g`, `0` and `31`, `1`
and `30`, the overflow lane alone (none past pattern `2`, where the Rust panics). -/
def gadgetLanes (g : ℕ) : List ℕ := [[0, 31], [1, 30], [overflowLane]].getD g []

/-- `gadget_beta(i)` (`opening.rs:77-81`): the `F192` of limbs `c_i = 1`, the others `0`, as the
verifier's `E` (`ext`): `β = 1, t, t²`. -/
def gadgetBeta (i : ℕ) : E :=
  E.ofLimbs (K.ofLane (if i = 0 then 1 else 0)) (K.ofLane (if i = 1 then 1 else 0))
    (K.ofLane (if i = 2 then 1 else 0))

/-- `Layout::gadget_entry(g, i)` (`opening.rs:247-250`), for pieces of `2^s`: `2^s − 9 + 3g + i`. -/
def gadgetEntry (s g i : ℕ) : ℕ := 2 ^ s - gadget + 3 * g + i

namespace Layout

/-- `log_lane` (`opening.rs:205-207`). -/
def logLane (L : Layout) : ℕ := L.logN - laneFold

/-- `placed` (`opening.rs:219-221`): whole lanes. -/
def placed (L : Layout) : ℕ := L.lanes.length * 2 ^ L.logLane

/-- `Layout::overflow` (`opening.rs:242-244`): the first overflow lane (the lanes' count if there
is none, where the Rust panics). -/
def overflow (L : Layout) : ℕ := L.lanes.findIdx (· == Lane.overflow)

/-- The blocks `Layout::new` lists (`opening.rs:119-128`): for each chunk `(chunk, len)` of
`2^log_chunk` entries, the blocks of `2^(log_n − 6)` entries covering its leading `len`. -/
def newBlocks (logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c ↦
    (List.range ((c.2 + 2 ^ (logN - laneFold) - 1) / 2 ^ (logN - laneFold))).map fun j ↦
      c.1 <<< (logChunk - (logN - laneFold)) ||| j

/-- **`Layout::new`** (`opening.rs:119-142`): a public layout, a lane per block. -/
def new (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) : Layout where
  vars := vars
  logN := logN
  lanes := (newBlocks logChunk logN chunks).map .block
  logPiece := none
  pieces := []

/-- A hidden layout's whole blocks (`opening.rs:168-172`). -/
def hiddenBlocks (logChunk logLane : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c ↦ (List.range (c.2 >>> logLane)).map fun j ↦ (c.1 <<< (logChunk - logLane)) + j

/-- A hidden layout's tails: the pieces of what each chunk holds past its whole blocks
(`opening.rs:173-176`). -/
def hiddenTails (logChunk logLane logPiece : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c ↦
    let first := c.1 <<< (logChunk - logLane)
    let whole := c.2 >>> logLane
    let start := (first + whole) <<< (logLane - logPiece)
    let tail := c.2 - (whole <<< logLane)
    (List.range ((tail + 2 ^ logPiece - 1) / 2 ^ logPiece)).map fun j ↦ start + j

/-- The lanes of a hidden layout (`opening.rs:179-185`): the first `min(32, |blocks|)` blocks on
lanes `0, 1, ...`, random lanes up to the overflow lane `32`, the overflow lane, `random` random
lanes, then the other blocks. -/
def hiddenLanes (blocks : List ℕ) (random : ℕ) : List Lane :=
  let lower := min blocks.length overflowLane
  (blocks.take lower).map .block ++ List.replicate (overflowLane - lower) .random ++ [.overflow] ++
    List.replicate random .random ++ (blocks.drop lower).map .block

/-- **`Layout::hidden_with`** (`opening.rs:153-203`; `Layout::hidden` is `log_piece = LOG_PIECE`):
the lanes `hiddenLanes`; the overflow lane's pieces are each block lane's first piece
(`b << (ℓ − s)`), in lane order, then the chunks' tails. The Rust's assertions
(`GADGET < 2^log_piece`, `random ≥ 7`, at most `64` lanes, fewer pieces than a lane's) are not
transcribed: what the theorems need of them is `HiddenOK`, decided for our layouts
(`Layouts.lean`). -/
def hidden (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) (random logPiece : ℕ) : Layout :=
  let logLane := logN - laneFold
  let lanes := hiddenLanes (hiddenBlocks logChunk logLane chunks) random
  let givenUp := lanes.filterMap fun l ↦ match l with
    | .block b => some (b <<< (logLane - logPiece))
    | _ => none
  { vars := vars
    logN := logN
    lanes := lanes
    logPiece := some logPiece
    pieces := givenUp ++ hiddenTails logChunk logLane logPiece chunks }

/-- `Layout::scales` (`opening.rs:284-301`), the lanes': `eq` of the point's high coordinates at
each block lane's block, zero on the other lanes. -/
def laneScales (L : Layout) (point : List E) : List E :=
  L.lanes.map fun
    | .block b => eqBits (point.drop L.logLane) b
    | _ => 0

/-- `Layout::scales`, the pieces': `eq` of the coordinates above a piece at each overflow piece. -/
def pieceScales (L : Layout) (point : List E) : List E :=
  match L.logPiece with
  | some s => L.pieces.map fun p ↦ eqBits (point.drop s) p
  | none => []

/-- The gadget (`opening.rs:824-833`), in a hidden layout: per pattern, its lanes and its entries
with their weights `scale · β_i`; none in a public layout. -/
def gadgetParts (L : Layout) (scale : E) : List (List ℕ × List (ℕ × E)) :=
  match L.logPiece with
  | some s => (List.range 3).map fun g ↦
      (gadgetLanes g, (List.range 3).map fun i ↦ (gadgetEntry s g i, scale * gadgetBeta i))
  | none => []

end Layout

/-! ## The weight closure (`opening.rs:770-876`) -/

/-- `ClaimWeight` (`opening.rs:770-777`): a claim's lane coordinates, and its lanes' and pieces'
scales. -/
structure Part where
  low : List E
  lanes : List E
  pieces : List E

/-- The scales times `λ_i` (`opening.rs:808-819`). -/
def Part.scale (l : E) (p : Part) : Part := ⟨p.low, p.lanes.map (l * ·), p.pieces.map (l * ·)⟩

/-- A claim's part before its power of `λ`. -/
def Layout.part (L : Layout) (c : Claim) : Part :=
  ⟨c.point.take L.logLane, L.laneScales c.point, L.pieceScales c.point⟩

/-- `parts` (`opening.rs:808-819`). -/
def Layout.parts (L : Layout) (ls : List E) (claims : List Claim) : List Part :=
  (claims.zip ls).map fun cl ↦ (L.part cl.1).scale cl.2

/-- `eq1` (`opening.rs:834`). -/
def eq1 (c p : E) : E := c * p + (1 + c) * (1 + p)

/-- `eq` (`opening.rs:835`): zipping. -/
def eqZ (a b : List E) : E := (a.zip b).foldl (fun w cp ↦ w * eq1 cp.1 cp.2) 1

/-- `Π (1 + p)` (`opening.rs:858-859`). -/
def onePlusProd (l : List E) : E := l.foldl (fun w p ↦ w * (1 + p)) 1

/-- One lane's term of `on_blocks` (`opening.rs:846-849`). -/
def onStep (scales laneEq : List E) (sum : E) (ll : Lane × ℕ) : E :=
  match ll.1 with
  | .block _ => sum + scales.getD ll.2 0 * laneEq.getD ll.2 0
  | _ => sum

/-- `on_blocks` (`opening.rs:846-849`): the block lanes, each its scale times its `eq_index`. -/
def onBlocks (lanes : List Lane) (scales laneEq : List E) : E :=
  lanes.zipIdx.foldl (onStep scales laneEq) 0

/-- `lane_eq` (`opening.rs:844`): `eq_index(high, l)` for each lane. -/
def laneEqs (n : ℕ) (high : List E) : List E := (List.range n).map fun l ↦ eqBits high l

/-- One part's term of the weight (`opening.rs:845-867`): the public branch, or the hidden one. -/
def Layout.term (L : Layout) (laneEq low : List E) (part : Part) : E :=
  let on := onBlocks L.lanes part.lanes laneEq
  match L.logPiece with
  | none => eqZ part.low low * on
  | some s =>
    let below := eqZ (part.low.take s) (low.take s)
    let above := eqZ (part.low.drop s) (low.drop s)
    let firstAbove := onePlusProd (part.low.drop s)
    let firstPiece := onePlusProd (low.drop s)
    let pieces := part.pieces.zipIdx.foldl
      (fun sum wk ↦ sum + wk.1 * eqBits (low.drop s) (wk.2 + 1)) 0
    let onOverflow := laneEq.getD L.overflow 0
    below * ((above + firstAbove * firstPiece) * on + pieces * onOverflow)

/-- The gadget's term of the weight (`opening.rs:868-874`): per pattern, its lanes' `eq_index`
(`lane_eq[l]`, `0` past the lanes, where the Rust panics) times its entries' weighted
`eq_index(low, y)`. -/
def gadgetSum (parts : List (List ℕ × List (ℕ × E))) (laneEq low : List E) : E :=
  parts.foldl (fun acc pe ↦ acc + pe.1.foldl (fun sum l ↦ sum + laneEq.getD l 0) 0 *
    pe.2.foldl (fun sum yb ↦ sum + yb.2 * eqBits low yb.1) 0) 0

/-- **The weight closure** (`opening.rs:841-876`), at a stack point `x`: the lane's coordinates
first, then the lane index's six; the claims' terms, then the gadget's, scaled by the power after
the claims' (`lambdas[claims.len()]`, `opening.rs:824`). -/
def Layout.weight (L : Layout) (ls : List E) (claims : List Claim) (x : List E) : E :=
  let low := x.take L.logLane
  let high := x.drop L.logLane
  let laneEq := laneEqs L.lanes.length high
  (L.parts ls claims).foldl (fun acc part ↦ acc + L.term laneEq low part) 0 +
    gadgetSum (L.gadgetParts (ls.getD claims.length 0)) laneEq low

/-- **The opening check** `opening::verify` (`opening.rs:780-887`) past its transcript's start, as a
program of mumbai's verifier language, at rate exponent `R` (`LOG_INV_RATE = 1`): the length
check, the batching challenge, then `verify_whir` with the target and the weight. -/
def Layout.check (L : Layout) (R : ℕ) (claims : List Claim) : Prog Unit := do
  Prog.require (∀ c ∈ claims, c.point.length = L.vars)
  let lam ← Prog.sampleChallenge
  let ls := lambdas lam claims.length
  verifyWhir L.logN R (target ls claims) (L.weight ls claims)

/-- **One claim's weight on the stack**: the closure's term for the claim with its power of `λ`
pulled out. -/
def Layout.claimWeight (L : Layout) (c : Claim) (x : List E) : E :=
  L.term (laneEqs L.lanes.length (x.drop L.logLane)) (x.take L.logLane) (L.part c)

/-- **The gadget's weight on the stack**: the closure's gadget term with its power of `λ` pulled
out (zero in a public layout). -/
def Layout.gadgetWeight (L : Layout) (x : List E) : E :=
  gadgetSum (L.gadgetParts 1) (laneEqs L.lanes.length (x.drop L.logLane)) (x.take L.logLane)

/-- **The stack claims the opening adds after the claims'**: in a hidden layout the gadget, of
value zero (batched with the power `λ^m` after the claims'); none in a public layout. -/
def Layout.extra (L : Layout) : List StackClaim :=
  match L.logPiece with
  | some _ => [(L.gadgetWeight, 0)]
  | none => []

theorem Layout.extra_of_none {L : Layout} (h : L.logPiece = none) : L.extra = [] := by
  unfold Layout.extra
  rw [h]

theorem Layout.extra_of_some {L : Layout} {s : ℕ} (h : L.logPiece = some s) :
    L.extra = [(L.gadgetWeight, 0)] := by
  unfold Layout.extra
  rw [h]

/-! ### List lemmas -/

section Lists

theorem foldl_zip_eq_foldl_zipWith {α β γ : Type} (op : γ → E → γ) (g : α → β → E) :
    ∀ (l : List α) (r : List β) (s : γ),
      (l.zip r).foldl (fun acc ab ↦ op acc (g ab.1 ab.2)) s = (List.zipWith g l r).foldl op s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l, b :: r, s => by
    simp only [List.zip_cons_cons, List.foldl_cons, List.zipWith_cons_cons]
    exact foldl_zip_eq_foldl_zipWith op g l r _

theorem zipWith_take_left {α β γ : Type} (f : α → β → γ) :
    ∀ (l : List α) (r : List β), List.zipWith f l r = List.zipWith f (l.take r.length) r
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: r => by
    simp only [List.zipWith_cons_cons, List.length_cons, List.take_succ_cons]
    rw [← zipWith_take_left f l r]

theorem take_powersFrom (a b : E) : ∀ n m, (powersFrom a b n).take m = powersFrom a b (min n m)
  | 0, m => by simp [powersFrom]
  | n + 1, 0 => by simp [powersFrom]
  | n + 1, m + 1 => by
    simp only [powersFrom, List.take_succ_cons, Nat.add_min_add_right]
    rw [take_powersFrom (a * b) b n m]

theorem take_lambdas (lam : E) (n : ℕ) : (lambdas lam n).take n = powers lam n := by
  rw [lambdas, powers, take_powersFrom, powers]
  congr 1
  omega

/-- The extra power `verify` builds, the gadget's, is not read by the claims' target. -/
theorem dot_lambdas (lam : E) (vs : List E) {n : ℕ} (hn : vs.length = n) :
    dot (lambdas lam n) vs = dot (powers lam n) vs := by
  rw [dot, dot, zipWith_take_left, hn, take_lambdas]

theorem length_powersFrom (a b : E) : ∀ n, (powersFrom a b n).length = n
  | 0 => rfl
  | n + 1 => by rw [powersFrom, List.length_cons, length_powersFrom (a * b) b n]

/-- The powers end with the last one. -/
theorem powersFrom_succ' (a b : E) : ∀ n, powersFrom a b (n + 1) = powersFrom a b n ++ [a * b ^ n]
  | 0 => by simp [powersFrom]
  | n + 1 => by
    show a :: powersFrom (a * b) b (n + 1) = (a :: powersFrom (a * b) b n) ++ [a * b ^ (n + 1)]
    rw [powersFrom_succ' (a * b) b n, List.cons_append, pow_succ', mul_assoc]

/-- The gadget's power: `λ^m`, the last of `verify`'s `m + 1`. -/
theorem lambdas_getD (lam : E) (n : ℕ) : (lambdas lam n).getD n 0 = lam ^ n := by
  rw [lambdas, powers, powersFrom_succ', List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_powersFrom]), length_powersFrom, Nat.sub_self]
  simp

/-- `Σ_i λ_i v_i` as `verify` folds it is mumbai's `dot`. -/
theorem target_eq_dot : ∀ (claims : List Claim) (ls : List E) (s : E),
    (claims.zip ls).foldl (fun acc cl ↦ acc + cl.2 * cl.1.value) s =
      (List.zipWith (· * ·) ls (claims.map (·.value))).foldl (· + ·) s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | c :: cs, l :: ls, s => by
    simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons, List.zipWith_cons_cons]
    exact target_eq_dot cs ls _

/-- A fold of additions is a sum. -/
theorem foldl_add_map {α : Type} (g : α → E) : ∀ (xs : List α) (s : E),
    xs.foldl (fun acc a ↦ acc + g a) s = s + (xs.map g).sum
  | [], s => by simp
  | a :: xs, s => by
    rw [List.foldl_cons, foldl_add_map g xs, List.map_cons, List.sum_cons, add_assoc]

theorem getD_map_mul (l : E) (xs : List E) (i : ℕ) :
    (xs.map (l * ·)).getD i 0 = l * xs.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> simp

/-- `dot` is the sum of the products. -/
theorem dot_eq_sum (l r : List E) : dot l r = (List.zipWith (· * ·) l r).sum := by
  rw [dot, foldl_add_map (fun x ↦ x) (List.zipWith (· * ·) l r) 0]
  simp

/-- `dot` over two lists of the same length, each extended. -/
theorem dot_append {a c : List E} (b d : List E) (h : a.length = c.length) :
    dot (a ++ b) (c ++ d) = dot a c + dot b d := by
  rw [dot_eq_sum, dot_eq_sum, dot_eq_sum, List.zipWith_append h, List.sum_append]

/-- One more value, with its power. -/
theorem dot_powers_snoc (lam : E) {n : ℕ} (vs : List E) (hn : vs.length = n) (v : E) :
    dot (powers lam (n + 1)) (vs ++ [v]) = dot (powers lam n) vs + lam ^ n * v := by
  rw [powers, powersFrom_succ', dot_append _ _ (by rw [length_powersFrom, hn])]
  simp [dot, powers]

end Lists

/-! ### The program is mumbai's stacked opening -/

/-- **The target is mumbai's batched value** `dot(powers(λ, J), values)`. -/
theorem target_eq (lam : E) (claims : List Claim) :
    target (lambdas lam claims.length) claims =
      dot (powers lam claims.length) (claims.map (·.value)) := by
  rw [target, target_eq_dot, ← dot_lambdas lam _ (List.length_map _)]
  rfl

/-- One lane's term of `on_blocks`, as an addend. -/
def onTerm (scales laneEq : List E) (ll : Lane × ℕ) : E :=
  match ll.1 with
  | .block _ => scales.getD ll.2 0 * laneEq.getD ll.2 0
  | _ => 0

theorem onStep_eq (scales laneEq : List E) (sum : E) (ll : Lane × ℕ) :
    onStep scales laneEq sum ll = sum + onTerm scales laneEq ll := by
  rcases ll with ⟨_ | _ | _, i⟩ <;> simp [onStep, onTerm]

/-- `on_blocks` as a sum. -/
theorem onBlocks_eq_sum (lanes : List Lane) (scales laneEq : List E) :
    onBlocks lanes scales laneEq = (lanes.zipIdx.map (onTerm scales laneEq)).sum := by
  rw [onBlocks, show onStep scales laneEq = fun s ll ↦ s + onTerm scales laneEq ll from
    funext fun s ↦ funext fun ll ↦ onStep_eq _ _ s ll, foldl_add_map, zero_add]

theorem onBlocks_scale (lanes : List Lane) (l : E) (ps laneEq : List E) :
    onBlocks lanes (ps.map (l * ·)) laneEq = l * onBlocks lanes ps laneEq := by
  rw [onBlocks_eq_sum, onBlocks_eq_sum, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun ll _ ↦ ?_
  rcases ll with ⟨_ | _ | _, i⟩ <;> simp only [onTerm]
  · rw [getD_map_mul]
    ring
  · ring
  · ring

/-- The pieces' fold as a sum. -/
theorem pieces_eq_sum (ps low : List E) (s : ℕ) :
    ps.zipIdx.foldl (fun sum wk ↦ sum + wk.1 * eqBits (low.drop s) (wk.2 + 1)) 0 =
      (ps.zipIdx.map fun wk ↦ wk.1 * eqBits (low.drop s) (wk.2 + 1)).sum := by
  rw [foldl_add_map, zero_add]

theorem pieces_scale (l : E) (ps low : List E) (s : ℕ) :
    (ps.map (l * ·)).zipIdx.foldl (fun sum wk ↦ sum + wk.1 * eqBits (low.drop s) (wk.2 + 1)) 0 =
      l * ps.zipIdx.foldl (fun sum wk ↦ sum + wk.1 * eqBits (low.drop s) (wk.2 + 1)) 0 := by
  rw [pieces_eq_sum (ps.map (l * ·)), pieces_eq_sum ps, List.zipIdx_map, List.map_map,
    ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun wk _ ↦ ?_)
  simp only [Function.comp, Prod.map_fst, Prod.map_snd, id]
  ring

/-- **A part's scales pull out of its term.** -/
theorem term_scale (L : Layout) (laneEq low : List E) (l : E) (p : Part) :
    L.term laneEq low (p.scale l) = l * L.term laneEq low p := by
  simp only [Layout.term, Part.scale]
  split
  · rw [onBlocks_scale]
    ring
  · rw [onBlocks_scale, pieces_scale]
    ring

theorem weight_aux (L : Layout) (laneEq low : List E) :
    ∀ (claims : List Claim) (ls : List E) (s : E),
      ((claims.zip ls).map fun cl ↦ (L.part cl.1).scale cl.2).foldl
          (fun acc part ↦ acc + L.term laneEq low part) s =
        (List.zipWith (· * ·) ls (claims.map fun c ↦ L.term laneEq low (L.part c))).foldl
          (· + ·) s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | c :: cs, l :: ls, s => by
    simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons, List.zipWith_cons_cons,
      term_scale]
    exact weight_aux L laneEq low cs ls _

/-- The range of the gadget's patterns and entries. -/
theorem range_three : List.range 3 = [0, 1, 2] := rfl

/-- **The gadget's scale pulls out of its term.** -/
theorem gadgetSum_scale (L : Layout) (c : E) (laneEq low : List E) :
    gadgetSum (L.gadgetParts c) laneEq low = c * gadgetSum (L.gadgetParts 1) laneEq low := by
  unfold Layout.gadgetParts
  split
  · simp only [gadgetSum, range_three, List.map_cons, List.map_nil, List.foldl_cons,
      List.foldl_nil]
    ring
  · simp [gadgetSum]

/-- **The weight is mumbai's batched weight** `dot(powers(λ, J), weights)`: each claim's weight
`Layout.claimWeight`, then a hidden layout's gadget `Layout.gadgetWeight` with the power after the
claims'. -/
theorem Layout.weight_eq (L : Layout) (lam : E) (claims : List Claim) (x : List E) :
    L.weight (lambdas lam claims.length) claims x =
      dot (powers lam (claims.length + L.extra.length))
        (claims.map (fun c ↦ L.claimWeight c x) ++ L.extra.map fun sc ↦ sc.1 x) := by
  have hclaims : (L.parts (lambdas lam claims.length) claims).foldl
      (fun acc part ↦ acc + L.term (laneEqs L.lanes.length (x.drop L.logLane))
        (x.take L.logLane) part) 0 =
      dot (powers lam claims.length) (claims.map fun c ↦ L.claimWeight c x) := by
    rw [← dot_lambdas lam _ (List.length_map _), dot]
    exact weight_aux L _ _ claims _ 0
  dsimp only [Layout.weight]
  rw [hclaims, lambdas_getD, gadgetSum_scale]
  rcases h : L.logPiece with _ | s
  · rw [Layout.extra_of_none h]
    simp [Layout.gadgetParts, h, gadgetSum]
  · rw [Layout.extra_of_some h]
    simp only [List.map_cons, List.map_nil, List.length_singleton]
    rw [dot_powers_snoc lam _ (List.length_map _)]
    rfl

/-- The claims' target, and the gadget's value zero. -/
theorem Layout.dot_extra_values (L : Layout) (lam : E) (claims : List Claim) :
    dot (powers lam (claims.length + L.extra.length))
        (claims.map (·.value) ++ L.extra.map (·.2)) =
      dot (powers lam claims.length) (claims.map (·.value)) := by
  rcases h : L.logPiece with _ | s
  · rw [Layout.extra_of_none h]
    simp
  · rw [Layout.extra_of_some h]
    simp only [List.map_cons, List.map_nil, List.length_singleton]
    rw [dot_powers_snoc lam _ (List.length_map _), mul_zero, add_zero]

/-! ## The weights are multiaffine -/

section Multiaffine

open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd.Sound

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

theorem eqLow_aux : ∀ (a x : List E) (s : E),
    (a.zip x).foldl (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) s =
      (List.zipWith (fun x z ↦ 1 + x + z) a x).foldl (· * ·) s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | c :: a, p :: x, s => by
    simp only [List.zip_cons_cons, List.foldl_cons, List.zipWith_cons_cons]
    rw [show s * (c * p + (1 + c) * (1 + p)) = s * (1 + c + p) by
      linear_combination (s * c * p) * two_eq_zero_E]
    exact eqLow_aux a x _

/-- `eq` as the Rust writes it, `c·p + (1 + c)(1 + p)`, is mumbai's `1 + c + p`. -/
theorem eqLow_eq_eqEval (a x : List E) :
    (a.zip x).foldl (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) 1 = eqEval a x := by
  rw [eqEval]
  exact eqLow_aux a x 1

theorem eqZ_eq_eqEval (a x : List E) : eqZ a x = eqEval a x := eqLow_eq_eqEval a x

theorem eq1_eq (c p : E) : eq1 c p = 1 + c + p := by
  rw [eq1]
  linear_combination (c * p) * two_eq_zero_E

theorem eOfNat_zero_E : eOfNat 0 = 0 := by
  unfold eOfNat
  rw [show K.ofBits 0 = 0 by decide +kernel]
  simp

theorem eOfNat_one_E : eOfNat 1 = 1 := by
  rw [eOfNat, show K.ofBits 1 = 1 from rfl, show ofK = algebraMap K E from rfl, map_one]

theorem bitFactor (n : ℕ) (p : E) :
    (if n % 2 = 1 then p else 1 + p) = 1 + eOfNat (n % 2) + p := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h, eOfNat_zero_E]; simp
  · rw [h, eOfNat_one_E]
    simp only [↓reduceIte]
    linear_combination (-1 : E) * two_eq_zero_E

theorem eqBits_aux (k : ℕ) : ∀ (y : List E) (s : ℕ) (acc : E),
    (y.zipIdx s).foldl (fun w pk ↦ w * if (k >>> pk.2) % 2 = 1 then pk.1 else 1 + pk.1) acc =
      (List.zipWith (fun x z ↦ 1 + x + z)
        ((List.range' s y.length).map fun bit ↦ eOfNat ((k >>> bit) % 2)) y).foldl (· * ·) acc
  | [], _, _ => by simp
  | p :: y, s, acc => by
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons, List.range'_succ,
      List.map_cons, List.zipWith_cons_cons]
    rw [bitFactor]
    exact eqBits_aux k y (s + 1) _

/-- `eq_bits(y, k)` is mumbai's `eq_eval(selector_point(k, |y|), y)`. -/
theorem eqBits_eq_eqEval (k : ℕ) (y : List E) :
    eqBits y k = eqEval (selectorPoint k y.length) y := by
  rw [eqBits, eqBits_aux, eqEval, selectorPoint, List.range_eq_range']

/-- A product of two weights each of which ignores every coordinate the other reads. -/
theorem isMultiaffine_mul_of_split {n : ℕ} {Φ Ψ : List E → E} (hΦ : IsMultiaffine n Φ)
    (hΨ : IsMultiaffine n Ψ)
    (hsplit : ∀ l : List E, l.length = n → ∀ k < n,
      (∀ X, Φ (l.set k X) = Φ l) ∨ (∀ X, Ψ (l.set k X) = Ψ l)) :
    IsMultiaffine n fun l ↦ Φ l * Ψ l := by
  intro l hl k hk X
  show Φ (l.set k X) * Ψ (l.set k X) =
    (1 - X) * (Φ (l.set k 0) * Ψ (l.set k 0)) + X * (Φ (l.set k 1) * Ψ (l.set k 1))
  rcases hsplit l hl k hk with h | h
  · rw [h X, h 0, h 1, hΨ l hl k hk X]; ring
  · rw [h X, h 0, h 1, hΦ l hl k hk X]; ring

theorem isMultiaffine_eqEval_take (a : List E) {n m : ℕ} (hm : m ≤ n) :
    IsMultiaffine n fun x ↦ eqEval a (x.take m) := by
  intro l hl j hj X
  simp only [List.take_set]
  rcases lt_or_ge j m with hjm | hjm
  · exact isMultiaffine_eqEval_any a m (l.take m) (by simp [hl]; omega) j hjm X
  · have hlen : (l.take m).length ≤ j := by simp; omega
    simp only [List.set_eq_of_length_le hlen]
    ring

theorem isMultiaffine_eqBits_drop (k : ℕ) {n m : ℕ} (hm : m ≤ n) :
    IsMultiaffine n fun x ↦ eqBits (x.drop m) k := by
  intro l hl j hj X
  have hlen : ∀ Y, ((l.set j Y).drop m).length = n - m := fun Y ↦ by simp [hl]
  simp only [eqBits_eq_eqEval, hlen]
  simp only [List.drop_set]
  split_ifs with hjm
  · ring
  · exact isMultiaffine_eqEval_any (selectorPoint k (n - m)) (n - m) (l.drop m) (by simp [hl])
      (j - m) (by omega) X

/-- The lane sum `Σ_l w_l · eq(bits(l), y)` as a list sum. -/
theorem lanes_eq_sum (ws : List E) (ks : List ℕ) (y : List E) :
    (ws.zip (ks.map fun l ↦ eqBits y l)).foldl (fun s we ↦ s + we.1 * we.2) 0 =
      ((ws.zip ks).map fun p ↦ p.1 * eqBits y p.2).sum := by
  rw [show (fun s (we : E × E) ↦ s + we.1 * we.2) = (fun s (we : E × E) ↦ s + (· * ·) we.1 we.2)
      from rfl, foldl_zip_eq_foldl_zipWith, foldl_add_eq, zero_add]
  induction ws generalizing ks with
  | nil => simp
  | cons w ws ih =>
    cases ks with
    | nil => simp
    | cons k ks =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.zip_cons_cons, List.sum_cons]
      rw [ih]

/-- **A public claim's weight is multiaffine** on the stack's `log_n` coordinates. -/
theorem isMultiaffine_claimWeight (L : Blocks) (c : Claim) :
    IsMultiaffine L.logN (claimWeight L c) := by
  have hm : L.logLane ≤ L.logN := Nat.sub_le _ _
  have hfun : claimWeight L c = fun x ↦ eqEval (c.point.take L.logLane) (x.take L.logLane) *
      (((L.laneWeights c.point).zip (List.range L.lanes)).map fun p ↦
        p.1 * eqBits (x.drop L.logLane) p.2).sum := by
    funext x
    rw [claimWeight, eqLow_eq_eqEval, lanes_eq_sum]
  rw [hfun]
  refine isMultiaffine_mul_of_split (isMultiaffine_eqEval_take _ hm)
    (isMultiaffine_listSum_mem _ _ fun p _ ↦ (isMultiaffine_eqBits_drop p.2 hm).const_mul p.1)
    fun l hl j hj ↦ ?_
  rcases lt_or_ge j L.logLane with hjm | hjm
  · right
    intro X
    simp only [List.drop_set, hjm, ↓reduceIte]
  · left
    intro X
    have hlen : (l.take L.logLane).length ≤ j := by simp; omega
    simp only [List.take_set, List.set_eq_of_length_le hlen]

/-! ### Combinators -/

/-- `f` ignores coordinate `k`. -/
def Ign (f : List E → E) (k : ℕ) : Prop := ∀ (l : List E) (X : E), f (l.set k X) = f l

theorem Ign.mul {f g : List E → E} {k : ℕ} (hf : Ign f k) (hg : Ign g k) :
    Ign (fun x ↦ f x * g x) k := fun l X ↦ by simp only [hf l X, hg l X]

theorem Ign.add {f g : List E → E} {k : ℕ} (hf : Ign f k) (hg : Ign g k) :
    Ign (fun x ↦ f x + g x) k := fun l X ↦ by simp only [hf l X, hg l X]

theorem isMultiaffine_mul' {n : ℕ} {f g : List E → E} (hf : IsMultiaffine n f)
    (hg : IsMultiaffine n g) (h : ∀ k < n, Ign f k ∨ Ign g k) :
    IsMultiaffine n fun x ↦ f x * g x :=
  isMultiaffine_mul_of_split hf hg fun l _ k hk ↦
    (h k hk).imp (fun h X ↦ h l X) (fun h X ↦ h l X)

theorem isMultiaffine_const (n : ℕ) (a : E) : IsMultiaffine n fun _ ↦ a := by
  intro l hl k hk X
  ring

theorem isMultiaffine_congr {n : ℕ} {f g : List E → E} (hf : IsMultiaffine n f)
    (h : ∀ l : List E, l.length = n → g l = f l) : IsMultiaffine n g := by
  intro l hl k hk X
  rw [h _ (by simp [hl]), h _ (by simp [hl]), h _ (by simp [hl])]
  exact hf l hl k hk X

/-- A weight of the first `m` coordinates. -/
theorem isMultiaffine_take' {n m : ℕ} {g : List E → E} (hm : m ≤ n) (hg : IsMultiaffine m g) :
    IsMultiaffine n fun x ↦ g (x.take m) := by
  intro l hl k hk X
  simp only [List.take_set]
  rcases lt_or_ge k m with hkm | hkm
  · exact hg (l.take m) (by simp [hl]; omega) k hkm X
  · have hlen : (l.take m).length ≤ k := by simp; omega
    simp only [List.set_eq_of_length_le hlen]
    ring

/-- A weight of the coordinates from `m` on. -/
theorem isMultiaffine_drop' {n m : ℕ} {g : List E → E} (hg : IsMultiaffine (n - m) g) :
    IsMultiaffine n fun x ↦ g (x.drop m) := by
  intro l hl k hk X
  simp only [List.drop_set]
  split_ifs with hkm
  · ring
  · exact hg (l.drop m) (by simp [hl]) (k - m) (by omega) X

theorem ign_take {g : List E → E} {m k : ℕ} (hk : m ≤ k) : Ign (fun x ↦ g (x.take m)) k :=
  fun l X ↦ by simp only [List.take_set_of_le hk]

theorem ign_drop {g : List E → E} {m k : ℕ} (hk : k < m) : Ign (fun x ↦ g (x.drop m)) k :=
  fun l X ↦ by simp only [List.drop_set_of_lt hk]

/-- A window `[s, ℓ)` ignores the coordinates outside it. -/
theorem ign_window {g : List E → E} {s ℓ k : ℕ} (hk : k < s ∨ ℓ ≤ k) :
    Ign (fun x ↦ g ((x.take ℓ).drop s)) k := by
  intro l X
  rcases hk with hk | hk
  · simp only [List.take_set, List.drop_set_of_lt hk]
  · simp only [List.take_set_of_le hk]

/-- A weight of the window `[s, ℓ)`. -/
theorem isMultiaffine_window {n s ℓ : ℕ} {g : List E → E} (hℓ : ℓ ≤ n)
    (hg : IsMultiaffine (ℓ - s) g) : IsMultiaffine n fun x ↦ g ((x.take ℓ).drop s) :=
  isMultiaffine_take' (g := fun z ↦ g (z.drop s)) hℓ (isMultiaffine_drop' hg)

/-- A weight of the first `ℓ` coordinates times one of the others. -/
theorem isMultiaffine_take_mul_drop {n ℓ : ℕ} {f g : List E → E} (hℓ : ℓ ≤ n)
    (hf : IsMultiaffine ℓ f) (hg : IsMultiaffine (n - ℓ) g) :
    IsMultiaffine n fun x ↦ f (x.take ℓ) * g (x.drop ℓ) :=
  isMultiaffine_mul' (isMultiaffine_take' hℓ hf) (isMultiaffine_drop' hg) fun k _ ↦ by
    rcases lt_or_ge k ℓ with hk | hk
    · exact Or.inr (ign_drop hk)
    · exact Or.inl (ign_take hk)

theorem isMultiaffine_eqZ (a : List E) (n : ℕ) : IsMultiaffine n (eqZ a) := by
  have : eqZ a = eqEval a := funext (eqZ_eq_eqEval a)
  rw [this]
  exact isMultiaffine_eqEval_any a n

theorem isMultiaffine_eqBits (k n : ℕ) : IsMultiaffine n fun y ↦ eqBits y k := by
  have h := isMultiaffine_eqBits_drop k (n := n) (m := 0) (Nat.zero_le _)
  simpa using h

theorem onePlusProd_aux (a : E) : ∀ l : List E,
    l.foldl (fun w p ↦ w * (1 + p)) a =
      (List.zipWith (fun x z ↦ 1 + x + z) (List.replicate l.length 0) l).foldl (· * ·) a
  | [] => by simp
  | p :: l => by
    simp only [List.foldl_cons, List.length_cons, List.replicate_succ, List.zipWith_cons_cons,
      add_zero]
    exact onePlusProd_aux _ l

theorem onePlusProd_eq (l : List E) : onePlusProd l = eqEval (List.replicate l.length 0) l := by
  rw [onePlusProd, onePlusProd_aux, eqEval]

theorem isMultiaffine_onePlusProd (n : ℕ) : IsMultiaffine n onePlusProd :=
  isMultiaffine_congr (isMultiaffine_eqEval_any (List.replicate n 0) n) fun l hl ↦ by
    rw [onePlusProd_eq, hl]

theorem laneEqs_getD (N i : ℕ) (h : List E) :
    (laneEqs N h).getD i 0 = if i < N then eqBits h i else 0 := by
  by_cases hi : i < N
  · simp [laneEqs, hi, List.getD_eq_getElem?_getD]
  · simp [laneEqs, hi, List.getD_eq_getElem?_getD]

theorem isMultiaffine_laneEq (N i n : ℕ) : IsMultiaffine n fun h ↦ (laneEqs N h).getD i 0 := by
  simp only [laneEqs_getD]
  split_ifs
  · exact isMultiaffine_eqBits i n
  · exact isMultiaffine_const n 0

/-- `on_blocks` is multiaffine in the lane index's coordinates. -/
theorem isMultiaffine_onBlocks (lanes : List Lane) (ps : List E) (N n : ℕ) :
    IsMultiaffine n fun h ↦ onBlocks lanes ps (laneEqs N h) := by
  simp only [onBlocks_eq_sum]
  refine isMultiaffine_listSum_mem _ _ fun ll _ ↦ ?_
  rcases ll with ⟨_ | _ | _, i⟩ <;> simp only [onTerm]
  · exact (isMultiaffine_laneEq N i n).const_mul _
  · exact isMultiaffine_const n 0
  · exact isMultiaffine_const n 0

/-- The pieces' term is multiaffine in the window's coordinates. -/
theorem isMultiaffine_pieces (ps : List E) (n : ℕ) :
    IsMultiaffine n fun y ↦ (ps.zipIdx.map fun wk ↦ wk.1 * eqBits y (wk.2 + 1)).sum :=
  isMultiaffine_listSum ps.zipIdx (fun wk ↦ wk.1) (fun wk y ↦ eqBits y (wk.2 + 1))
    fun _ ↦ isMultiaffine_eqBits _ n

/-- The block term of the hidden branch, in the window `y = low[s..]`: `eq(a, y)` with the first
piece's share `eq(a, 0)·eq(0, y)` taken out (added, in characteristic two). -/
def blockTerm (a : List E) (fa : E) (y : List E) : E :=
  eqZ a y + fa * onePlusProd y

theorem isMultiaffine_blockTerm (a : List E) (fa : E) (n : ℕ) :
    IsMultiaffine n (blockTerm a fa) :=
  (isMultiaffine_eqZ a n).add ((isMultiaffine_onePlusProd n).const_mul _)

/-- **The hidden branch's claim weight**, the window `y = x[s..ℓ]` and the lane index's
coordinates `x[ℓ..]` read apart. -/
theorem claimWeight_hidden (L : Layout) (c : Claim) {s : ℕ} (hs : L.logPiece = some s)
    (x : List E) :
    L.claimWeight c x =
      eqZ ((c.point.take L.logLane).take s) (x.take (min s L.logLane)) *
        (blockTerm ((c.point.take L.logLane).drop s)
            (onePlusProd ((c.point.take L.logLane).drop s)) ((x.take L.logLane).drop s) *
          onBlocks L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) +
         (((L.pieceScales c.point).zipIdx.map fun wk ↦
            wk.1 * eqBits ((x.take L.logLane).drop s) (wk.2 + 1)).sum) *
          (laneEqs L.lanes.length (x.drop L.logLane)).getD L.overflow 0) := by
  rw [Layout.claimWeight, Layout.term, hs]
  simp only [Layout.part, blockTerm, pieces_eq_sum, List.take_take]

/-- The public branch's claim weight. -/
theorem claimWeight_public (L : Layout) (c : Claim) (hs : L.logPiece = none) (x : List E) :
    L.claimWeight c x =
      eqZ (c.point.take L.logLane) (x.take L.logLane) *
        onBlocks L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) := by
  rw [Layout.claimWeight, Layout.term, hs]
  rfl

/-- **Every claim's weight is multiaffine**, for every layout, public or hidden: the hypothesis of
mumbai's `stackedSpec`. -/
theorem isMultiaffine_layoutClaimWeight (L : Layout) (c : Claim) :
    IsMultiaffine L.logN (L.claimWeight c) := by
  have hℓ : L.logLane ≤ L.logN := Nat.sub_le _ _
  have hon : IsMultiaffine L.logN fun x ↦
      onBlocks L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) :=
    isMultiaffine_drop' (g := fun h ↦ onBlocks L.lanes (L.laneScales c.point)
      (laneEqs L.lanes.length h)) (isMultiaffine_onBlocks _ _ _ _)
  have hon_ign : ∀ k, k < L.logLane → Ign (fun x ↦ onBlocks L.lanes (L.laneScales c.point)
      (laneEqs L.lanes.length (x.drop L.logLane))) k :=
    fun k hk ↦ ign_drop (g := fun h ↦ onBlocks L.lanes (L.laneScales c.point)
      (laneEqs L.lanes.length h)) hk
  rcases hs : L.logPiece with _ | s
  · have hf : L.claimWeight c = fun x ↦ eqZ (c.point.take L.logLane) (x.take L.logLane) *
        onBlocks L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) :=
      funext (claimWeight_public L c hs)
    rw [hf]
    refine isMultiaffine_mul' (isMultiaffine_take' hℓ (isMultiaffine_eqZ _ _)) hon fun k _ ↦ ?_
    rcases lt_or_ge k L.logLane with hk | hk
    · exact Or.inr (hon_ign k hk)
    · exact Or.inl (ign_take hk)
  · have hf := funext (claimWeight_hidden L c hs)
    rw [hf]
    -- the overflow lane's `eq`
    have hov : IsMultiaffine L.logN fun x ↦
        (laneEqs L.lanes.length (x.drop L.logLane)).getD L.overflow 0 :=
      isMultiaffine_drop' (g := fun h ↦ (laneEqs L.lanes.length h).getD L.overflow 0)
        (isMultiaffine_laneEq _ _ _)
    have hov_ign : ∀ k, k < L.logLane → Ign (fun x ↦
        (laneEqs L.lanes.length (x.drop L.logLane)).getD L.overflow 0) k :=
      fun k hk ↦ ign_drop (g := fun h ↦ (laneEqs L.lanes.length h).getD L.overflow 0) hk
    -- a window term times a lane term
    have hprod : ∀ (g : List E → E) (G : List E → E), IsMultiaffine (L.logLane - s) g →
        IsMultiaffine L.logN G → (∀ k, k < L.logLane → Ign G k) →
        IsMultiaffine L.logN (fun x ↦ g ((x.take L.logLane).drop s) * G x) ∧
          ∀ k, k < min s L.logLane → Ign (fun x ↦ g ((x.take L.logLane).drop s) * G x) k := by
      intro g G hg hG hGi
      refine ⟨isMultiaffine_mul' (isMultiaffine_window hℓ hg) hG fun k _ ↦ ?_, fun k hk ↦
        (ign_window (Or.inl (lt_of_lt_of_le hk (min_le_left _ _)))).mul
          (hGi k (lt_of_lt_of_le hk (min_le_right _ _)))⟩
      rcases lt_or_ge k L.logLane with hk | hk
      · exact Or.inr (hGi k hk)
      · exact Or.inl (ign_window (Or.inr hk))
    obtain ⟨h1, i1⟩ := hprod _ _ (isMultiaffine_blockTerm _ _ _) hon hon_ign
    obtain ⟨h3, i3⟩ := hprod _ _ (isMultiaffine_pieces _ _) hov hov_ign
    refine isMultiaffine_mul' (isMultiaffine_take' (le_trans (min_le_right _ _) hℓ)
      (isMultiaffine_eqZ _ _)) (h1.add h3) fun k _ ↦ ?_
    rcases lt_or_ge k (min s L.logLane) with hk | hk
    · exact Or.inr ((i1 k hk).add (i3 k hk))
    · exact Or.inl (ign_take hk)

/-- The gadget's term as a sum over its patterns: each its lanes' `eq_index` times its entries'. -/
theorem gadgetSum_eq_sum (parts : List (List ℕ × List (ℕ × E))) (laneEq low : List E) :
    gadgetSum parts laneEq low =
      (parts.map fun pe ↦ (pe.2.map fun yb ↦ yb.2 * eqBits low yb.1).sum *
        (pe.1.map fun l ↦ laneEq.getD l 0).sum).sum := by
  have h : ∀ (xs : List (List ℕ × List (ℕ × E))) (s : E),
      xs.foldl (fun acc pe ↦ acc + pe.1.foldl (fun sum l ↦ sum + laneEq.getD l 0) 0 *
        pe.2.foldl (fun sum yb ↦ sum + yb.2 * eqBits low yb.1) 0) s =
      s + (xs.map fun pe ↦ (pe.2.map fun yb ↦ yb.2 * eqBits low yb.1).sum *
        (pe.1.map fun l ↦ laneEq.getD l 0).sum).sum := by
    intro xs
    induction xs with
    | nil => intro s; simp
    | cons pe xs ih =>
      intro s
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons,
        foldl_add_map (fun l : ℕ ↦ laneEq.getD l 0),
        foldl_add_map (fun yb : ℕ × E ↦ yb.2 * eqBits low yb.1)]
      ring
  rw [gadgetSum, h, zero_add]

/-- **The gadget's term is multiaffine**, for any patterns. -/
theorem isMultiaffine_gadgetSum (parts : List (List ℕ × List (ℕ × E))) (N : ℕ) {n ℓ : ℕ}
    (hℓ : ℓ ≤ n) :
    IsMultiaffine n fun x ↦ gadgetSum parts (laneEqs N (x.drop ℓ)) (x.take ℓ) := by
  have hfun : (fun x : List E ↦ gadgetSum parts (laneEqs N (x.drop ℓ)) (x.take ℓ)) = fun x ↦
      (parts.map fun pe ↦ (pe.2.map fun yb ↦ yb.2 * eqBits (x.take ℓ) yb.1).sum *
        (pe.1.map fun l ↦ (laneEqs N (x.drop ℓ)).getD l 0).sum).sum :=
    funext fun x ↦ gadgetSum_eq_sum _ _ _
  rw [hfun]
  refine isMultiaffine_listSum_mem _ _ fun pe _ ↦ ?_
  have h1 : IsMultiaffine ℓ fun y ↦ (pe.2.map fun yb ↦ yb.2 * eqBits y yb.1).sum :=
    isMultiaffine_listSum pe.2 (fun yb ↦ yb.2) (fun yb y ↦ eqBits y yb.1)
      fun yb ↦ isMultiaffine_eqBits _ _
  have h2 : IsMultiaffine (n - ℓ) fun h ↦ (pe.1.map fun l ↦ (laneEqs N h).getD l 0).sum :=
    isMultiaffine_listSum_mem pe.1 (fun l h ↦ (laneEqs N h).getD l 0)
      fun l _ ↦ isMultiaffine_laneEq N l _
  have h3 := isMultiaffine_take_mul_drop hℓ h1 h2
  exact h3

/-- **The gadget's weight is multiaffine** on the stack's `log_n` coordinates. -/
theorem isMultiaffine_gadgetWeight (L : Layout) : IsMultiaffine L.logN L.gadgetWeight :=
  isMultiaffine_gadgetSum (L.gadgetParts 1) L.lanes.length (Nat.sub_le _ _)

theorem Layout.extra_multiaffine (L : Layout) : ∀ c ∈ L.extra, IsMultiaffine L.logN c.1 := by
  intro c hc
  rcases h : L.logPiece with _ | s
  · rw [Layout.extra_of_none h] at hc
    cases hc
  · rw [Layout.extra_of_some h, List.mem_singleton] at hc
    rw [hc]
    exact isMultiaffine_gadgetWeight L

end Multiaffine

/-! ## The stackings -/

/-- A public stacking's: no stack claim of its own. -/
def Blocks.stacking (L : Blocks) : Stacking :=
  ⟨L.vars, L.logN, claimWeight L, isMultiaffine_claimWeight L, [], fun _ h ↦ by cases h⟩

/-- **A layout's stacking**: its claims' weights as `verify` evaluates them, and a hidden
layout's gadget. -/
def Layout.stacking (L : Layout) : Stacking :=
  ⟨L.vars, L.logN, L.claimWeight, isMultiaffine_layoutClaimWeight L, L.extra,
    L.extra_multiaffine⟩

/-- **The opening check is mumbai's stacked opening** on the claims' stack claims, then a hidden
layout's gadget, after the length check. -/
theorem Layout.check_eq (L : Layout) (R : ℕ) (claims : List Claim) :
    L.check R claims = L.stacking.check R claims := by
  have h1 : (L.stacking.claims claims).length = claims.length + L.extra.length :=
    Stacking.length_claims _ _
  have h2 : (L.stacking.claims claims).map (·.2) = claims.map (·.value) ++ L.extra.map (·.2) := by
    simp [Stacking.claims, Layout.stacking]
  have h3 : ∀ x, (L.stacking.claims claims).map (fun c ↦ c.1 x) =
      claims.map (fun c ↦ L.claimWeight c x) ++ L.extra.map fun sc ↦ sc.1 x := fun x ↦ by
    simp [Stacking.claims, Layout.stacking]
  have key : ∀ lam : E, verifyWhir L.logN R (target (lambdas lam claims.length) claims)
        (L.weight (lambdas lam claims.length) claims) =
      verifyWhir L.logN R
        (dot (powers lam (L.stacking.claims claims).length)
          ((L.stacking.claims claims).map (·.2)))
        (fun point ↦ dot (powers lam (L.stacking.claims claims).length)
          ((L.stacking.claims claims).map fun c ↦ c.1 point)) := fun lam ↦
    congrArg₂ (verifyWhir L.logN R) (by rw [h1, h2, target_eq, L.dot_extra_values])
      (funext fun x ↦ by rw [h1, h3, Layout.weight_eq])
  unfold Layout.check Stacking.check verifyStackedOpening
  simp only [key]
  rfl

end WhirBridge
