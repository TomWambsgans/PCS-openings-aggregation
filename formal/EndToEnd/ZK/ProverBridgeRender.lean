-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The WHIR prover is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- `levelTailA` is `Statement/Prover/Whir.lean`'s `levelsA` with its level's fold rounds taken out
-- (verbatim otherwise), `hybridScript` its `openingFast` (this repository's `openingScript`) with the
-- first level's lane rounds read from the view; the script's moves (`Script.msgOf`, `afterSend`,
-- `afterSample`, `afterGrind`, `wordOf`, `afterCommit`, `afterQuery`) are `Statement/Prover/Run.lean`'s.
import ZK.Format
import QuotientZk.Instance.Prover

/-!
# The deployed renderer: WHIR's honest prover on the available view

`QuotientZk`'s deployed prover `Pb R` (`QuotientZk/Instance/Prover.lean`) sends, after `k` challenges,
the claims' bytes at the openings' starts and then `R k h (avail k v)`: any public function `R` of the
step, the answers `h` so far and the part of the joint view drawn for by then. **`whirRenderer`** is
the one the deployed prover is: WHIR's honest prover (mumbai's script, `Statement/Prover/Whir.lean`)
driven in the skeleton's order (`Deployed.opening`).

* **Step 4**: the five values (the joint view's `v.1`), as the skeleton reads them.
* **The wiring opening** (steps `129 … 241`): the honest script on the circuit's public wiring table
  (`openingScript`, the statement's own), commitment `0` that table's codeword.
* **A secret opening** (witness, steps `6 … 127`; quotient, steps `243 … 393`): the honest script with
  its first level's lane rounds replaced by the view's (`hybridScript`): the round messages of the view's
  lane rounds (`laneFoldsH`; the weight table folded alongside, public), then from the folded table `f¹`
  of the view everything mumbai's `levelsA` computes after the lane folds (`levelTailA`: the next
  commitment, the out-of-domain answer, the queries' rounds, the later levels); commitment `0`'s
  opened rows from the view (`word0`: the `64`-word leaf image, the absent lanes' zeros first, the
  committed lanes from the last).

**The drive** (`evRun`): the opening's events (`openingEv`, read off the skeleton's `opening`: draws,
`k` scalars sent as one item, a commitment's rows, grinding, a query phase's opened rows at the
positions its draws give); each draw feeds the challenge of the next answer (`drawChal`: the state's
lanes `0 .. 2`, `Dx.draw`) to the script; the run stops at the draw no answer is known for, its last
message the one after the last challenge. The claims are the verifier's (`claimsAt`) at the chain's
challenges (`chainChal`: a state's low 192 bits) and the view's values.

`whirRenderer` reads nothing but its arguments: it is the simulator's renderer as well.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete
open QuotientZk.Deployed (Out Msg Item)
open QuotientRpm (Limbs)

namespace PcsQuotient.EndToEnd.Render

set_option linter.unusedSectionVars false

/-! ## Encodings -/

/-- An element of `E` as the skeleton's scalar: its three limbs' lanes. -/
def limbsOf (x : E) : Limbs := ((x.limb 0).lane, (x.limb 1).lane, (x.limb 2).lane)

/-- **A draw's challenge** (`Dx.draw`, mumbai's `squeeze`): the permutation's output, lanes `0 .. 2`. -/
def drawChal (o : Out) : E := Compile.challengeOf o.2

/-- **A chain challenge** (`Chain.squeezeWith`): the new state's low 192 bits. -/
def chainChal (o : Out) : E := Transcript.challengeOf (digestOfBytes o.1)

/-! ## The WHIR prover past its lane rounds -/

/-- **A level of `levelsA` after its fold rounds** (mumbai's `levelsA`, the body after
`foldRoundsA`): the next commitment and its out-of-domain answer, or the residual; grinding, the
query positions, the queries' batching and round; then the tail rounds or the next level. -/
def levelTailA (μ index : ℕ) (level : Whir.Level) (rest : List Whir.Level) (s : WhirState)
    (levelFolds : List E) (W g : Array E) : Script Unit := do
  let messageLog := μ - s.folds.length
  let (residual, pending, tables) ← match rest with
    | [] => do
      Script.sendList g.toList
      pure (g, ([] : List (List E × (List E → E))), ([] : List (Array E)))
    | next :: _ => do
      Script.commitS (levelWordFast (messageLog - next.fold) next.fold next.logInvRate g)
      let oodPoint ← Script.sampleN messageLog
      let oodValue := multilinearEvalA g oodPoint
      Script.sendE oodValue
      let T := eqKernelA oodPoint
      let quad ← roundA oodValue T g
      pure (#[], [(quad, fun x ↦ eqEval oodPoint x)], [T])
  Script.grindS
  let queries ← sampleQueriesS (messageLog + level.logInvRate) level.queries level.queries
  let lam ← Script.sampleE
  let queryWeights := powers lam queries.length
  let words ← Script.queryS
  let rows : List (List E) :=
    if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
  let enforced := enforcedSum rows levelFolds queryWeights
  let T := queryTableA messageLog queries queryWeights
  let quad ← roundA enforced T g
  let pending := pending ++ [(quad, fun x ↦ inducedWeight messageLog queries queryWeights x)]
  let s := glue lam s pending
  let W := glueTablesA lam W (tables ++ [T])
  match rest with
  | [] => tailRoundsA messageLog s.quad W residual
  | _ :: _ => levelsA μ (index + 1) rest s W g

/-- A round's message given (`h(0)` and the quadratic coefficient), sent as `roundA` sends it; the
verifier's quadratic for the running claim `claim`. -/
def roundMsgA (claim : E) (m : E × E) : Script (List E) := do
  Script.sendE m.1
  Script.sendList [m.2]
  return [m.1, claim + sumE [m.2], m.2]

/-- **Lane rounds from given messages**: receive the fold challenge, fold the (public) weight table,
send the next given round message (`foldRoundsA` with the stack's table replaced by the messages). -/
def laneFoldsH (lane : ℕ → E × E) : ℕ → ℕ → WhirState → List E → Array E →
    Script (WhirState × List E × Array E)
  | 0, _, s, levelFolds, W => return (s, levelFolds, W)
  | n + 1, j, s, levelFolds, W => do
    let challenge ← Script.sampleE
    let W' := foldPairsW challenge W
    let quad ← roundMsgA (polyEval s.quad challenge) (lane j)
    laneFoldsH lane n (j + 1) { s with quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge]) W'

/-- **The honest opening from the lane rounds' messages and the folded table** (`openingScript` with
the first level's rounds `0 … fold − 1` the given messages `lane`, the last of its fold rounds and every
later move computed from the folded table `f1`). -/
def hybridScript (L : Layout) (claims : List Claim) (lane : ℕ → E × E) (f1 : Array E) :
    Script Unit := do
  let c ← Script.sampleE
  let scales := powers c (stackClaims L claims).length
  match Whir.ladder L.logN logInvRate with
  | none => return ()
  | some [] => return ()
  | some (level :: rest) =>
    let W₀ := weightTable L scales claims
    let target := dot scales ((stackClaims L claims).map (·.2))
    let quad ← roundMsgA target (lane 0)
    let (s, levelFolds, W) ← laneFoldsH lane (level.fold - 1) 1 ⟨quad, [], []⟩ [] W₀
    let φ ← Script.sampleE
    let W' := foldPairsW φ W
    let quad ← roundA (polyEval s.quad φ) W' f1
    levelTailA L.logN 0 level rest { s with quad, folds := s.folds ++ [φ] } (levelFolds ++ [φ]) W' f1

/-! ## The skeleton's order -/

/-- The events of an opening, as the skeleton's `opening` meets them. -/
inductive Ev where
  /-- A draw. -/
  | draw
  /-- A draw whose limbs give query positions. -/
  | posDraw
  /-- `k` scalars sent, one item. -/
  | send (k : ℕ)
  /-- A commitment of `2^depth` rows. -/
  | commit (depth : ℕ)
  /-- A proof of work. -/
  | grind
  /-- The rows of commitment `lvl` (depth `b`) at the first `q` positions drawn. -/
  | opened (lvl q b : ℕ)

/-- `k` rounds: draw, two scalars. -/
def roundsEv : ℕ → List Ev
  | 0 => []
  | k + 1 => .draw :: .send 2 :: roundsEv k

/-- The out-of-domain sample: `m` draws, three scalars. -/
def oodEv (m : ℕ) : List Ev := List.replicate m .draw ++ [.send 3]

/-- A query phase on commitment `lvl` of depth `b` with `q` queries (`queryPhase`). -/
def queryEv (lvl q b : ℕ) : List Ev :=
  .grind :: List.replicate ((q + 192 / max b 1 - 1) / (192 / max b 1)) .posDraw ++
    [.draw, .opened lvl q b, .send 2]

/-- The later levels (`middle`), commitment `lvl` of depth `b` being queried. -/
def middleEv : ℕ → ℕ → List (ℕ × ℕ × ℕ) → List ℕ → List Ev
  | _, _, [], _ => []
  | lvl, b, (folds, depth, oodN) :: rest, q :: qs =>
    roundsEv folds ++ [.commit depth] ++ oodEv oodN ++ queryEv lvl q b ++ middleEv (lvl + 1) depth rest qs
  | _, _, _ :: _, [] => []

/-- **An opening's events** (`Deployed.opening` from `λ` on). -/
def openingEv (sh : QuotientZk.Deployed.OpenShape) : List Ev :=
  [.draw, .send 2] ++ roundsEv 6 ++ [.commit sh.depth₁] ++ oodEv sh.ood₀ ++
    queryEv 0 (sh.queries.headD 0) sh.depth₀ ++ middleEv 1 sh.depth₁ sh.levels (sh.queries.drop 1) ++
    roundsEv sh.lastFolds ++ [.send (2 ^ sh.residualVars)] ++
    queryEv (sh.levels.length + 1) (sh.queries.getLastD 0)
      (QuotientZk.Instance.lastDepth sh.depth₁ sh.levels) ++
    roundsEv (sh.residualVars - 1) ++ [.draw]

/-- The drive's state: the script, the commitments (height and rows), the limbs of the position draws
not yet used, the current message, the messages so far. -/
structure RunSt where
  script : Option (Script Unit)
  comms : List (ℕ × Word)
  posLimbs : List Limbs
  acc : Msg
  done : List Msg

/-- The next `n` scalars a script sends. -/
def sendsN : ℕ → Option (Script Unit) → List E × Option (Script Unit)
  | 0, S => ([], S)
  | n + 1, S =>
    let r := sendsN n (Script.afterSend S)
    (Script.msgOf S :: r.1, r.2)

/-- **The drive**: the events with the challenges of the answers `chs`; the messages after each
draw, up to the draw no answer is known for. -/
def evRun : List Ev → List Out → RunSt → List Msg
  | [], _, st => st.done ++ [st.acc]
  | .draw :: evs, chs, st =>
    match chs with
    | [] => st.done ++ [st.acc]
    | o :: chs =>
      evRun evs chs ⟨Script.afterSample (drawChal o) st.script, st.comms, st.posLimbs, [],
        st.done ++ [st.acc]⟩
  | .posDraw :: evs, chs, st =>
    match chs with
    | [] => st.done ++ [st.acc]
    | o :: chs =>
      evRun evs chs ⟨Script.afterSample (drawChal o) st.script, st.comms,
        st.posLimbs ++ [(o.2[0], o.2[1], o.2[2])], [], st.done ++ [st.acc]⟩
  | .send k :: evs, chs, st =>
    let r := sendsN k st.script
    evRun evs chs ⟨r.2, st.comms, st.posLimbs, st.acc ++ [.scalars (r.1.map limbsOf)], st.done⟩
  | .commit d :: evs, chs, st =>
    let word := Script.wordOf st.script
    let rows := (List.range (2 ^ d)).map fun i ↦ (word i).flatMap kBytes
    evRun evs chs ⟨Script.afterCommit st.script, st.comms ++ [(d, word)], st.posLimbs,
      st.acc ++ [.rows rows], st.done⟩
  | .grind :: evs, chs, st =>
    evRun evs chs ⟨Script.afterGrind st.script, st.comms, st.posLimbs, st.acc, st.done⟩
  | .opened lvl q b :: evs, chs, st =>
    let ps := (st.posLimbs.flatMap (QuotientZk.Deployed.positionsOf (max b 1))).take q
    let c := st.comms.getD lvl (0, fun _ ↦ [])
    let rows := ps.map fun p ↦ c.2 (p % 2 ^ c.1)
    let opened := (QuotientZk.Deployed.sortedUnique ps).map fun p ↦ (c.2 (p % 2 ^ c.1)).map K.lane
    evRun evs chs ⟨Script.afterQuery rows st.script, st.comms, [], st.acc ++ [.opened opened],
      st.done⟩

/-- The message after the last challenge of a drive. -/
def lastMsg (ms : List Msg) : Msg := ms.getLastD []

/-- **An opening's message after the challenges `chs`**: the drive from `λ` with the script and
commitment `0` (`depth₀`, `word0`). -/
def openingMsg (sh : QuotientZk.Deployed.OpenShape) (S : Script Unit) (word0 : Word)
    (chs : List Out) : Msg :=
  lastMsg (evRun (openingEv sh) chs ⟨some S, [(sh.depth₀, word0)], [], [], []⟩)

/-! ## The renderer -/

section Renderer

open QuotientZk.Instance

variable (rep : QuotientZk.Instance.Rep K E)

/-- **The verifier's claims** at the chain's challenges (answers `0 … 4`) and the values. -/
def chainClaims (stmt : Statement) (h : List Out) (v : Vals E) : Option Claims :=
  claimsAt logRows stmt (chainChal (h.getD 0 default)) (chainChal (h.getD 1 default))
    (chainChal (h.getD 2 default)) (chainChal (h.getD 3 default)) (chainChal (h.getD 4 default))
    (Vector.ofFn v.1) v.2

/-- A lane round's message from the view, by index. -/
def laneAt (lr : Fin 6 → E × E) (j : ℕ) : E × E := if h : j < 6 then lr ⟨j, h⟩ else (0, 0)

/-- **A leaf's words** (the `64`-word image the tree hashes): the absent lanes' zeros, then the
committed lanes from the last. -/
def leafWords {n : ℕ} (row : Fin n → K) : List K :=
  List.replicate (64 - n) 0 ++ (List.ofFn row).reverse

/-- **The witness table's level-0 rows from the view**: at a position, the opened row of its slot. -/
noncomputable def word0W (h : List Out) (va : JV K E) : Word := fun p ↦
  leafWords (va.2.2.1.2.2 (slotOf 20 224 (drawsW (chOf rep.limbs h)) p))

/-- **The quotient table's level-0 rows from the view.** -/
noncomputable def word0Q (h : List Out) (va : JV K E) : Word := fun p ↦
  leafWords (va.2.2.2.2.2 (slotOf 23 225 (drawsQ (chOf rep.limbs h)) p))

/-- **The circuit's wiring table's level-0 rows** (public). -/
noncomputable def word0σ : Word :=
  stackWordFast (cellVars logRows) 1 (membership logRows).wiringTable

/-- **The deployed renderer**: WHIR's honest prover on the available view (`QuotientZk`'s `Renderer`
at `K = GF(2^64)`, `E = GF(2^192)`). -/
noncomputable def whirRenderer (stmt : Statement) : Renderer K E := fun k h va ↦
  if k = 4 then [.scalars ((List.ofFn va.1.1 ++ [va.1.2]).map limbsOf)]
  else
    match chainClaims stmt h va.1 with
    | none => []
    | some cl =>
      if 6 ≤ k ∧ k < 128 then
        openingMsg (QuotientZk.Deployed.witnessShape default)
          (hybridScript (witnessLayout logRows) [cl.witness] (laneAt va.2.2.1.1)
            (Array.ofFn va.2.2.1.2.1))
          (word0W rep h va) (h.drop 5)
      else if 129 ≤ k ∧ k < 242 then
        openingMsg (QuotientZk.Deployed.wiringShape default [])
          (openingScript (wiringLayout logRows) (membership logRows).wiringTable [cl.wiring])
          word0σ (h.drop 128)
      else if 243 ≤ k ∧ k < 394 then
        openingMsg (QuotientZk.Deployed.quotientShape default)
          (hybridScript (quotientLayout logRows) [cl.quotient, cl.sum] (laneAt va.2.2.2.1)
            (Array.ofFn va.2.2.2.2.1))
          (word0Q rep h va) (h.drop 242)
      else []

end Renderer

end PcsQuotient.EndToEnd.Render
