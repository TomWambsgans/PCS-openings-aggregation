-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM `mumbai`'s Merkle trees and stack words (https://github.com/Verified-zkEVM/leanerVM,
-- commit 6175f1a0, MIT OR Apache-2.0): `buildTreeWithHash`, `simulateQ_buildTreeM`,
-- `leafDigestsM_id`, `parentsM_id`, `parentsM_id_toArray`, `root_buildTreeM_id`, `openingAt`,
-- `MerkleTree.pathOfLevel`, `openOne_eq_some_true_iff`, `extract_eq_of_openOne`, `climb_mod`,
-- `stackWord`, `wellShaped_stackWord`, `stackWord_agrees`.
import Compose.WiredDecoded
import LeanVM.Protocol.Compile.Rom.Prover
import LeanVM.Protocol.Whir.Complete.Encoding

/-!
# The setup's word: the circuit's commitment commits to the wiring stack

The setup computes the circuit's commitment with the oracle: the Merkle tree of the wiring
stack's word (`stackWord`, mumbai's level-0 encoding of a stack), `wiringSetup`. Here, on every
table of the oracles and every history that holds the setup's Keccak-256 queries without collision,
the word mumbai's `extract` reads under the setup's root is that word (`extract_wiringSetup`):

* the setup's run through the history's (partial) answers succeeds and is its run through the table
  (`simulateQ_option_of_log`), so building the tree through the history's answers succeeds;
* then every climb of the tree's authentication paths succeeds through the history's answers
  (`climb_of_levels`: each step's input is the input of one of the parents the build hashed), so
  the honest opening at each position is accepted (`openOne_eq_some_true_iff`), and through injective
  answers `extract` reads its leaf (`extract_eq_of_openOne`).

So **`wiringMatch`**: `WiringMatch` for the setup of a stack `q₀` (the word honest by
`stackWord_agrees`), with only the claim condition (`WiringClaims`: the stack's table satisfies the
wiring opening's claims only if F1's wiring claim holds) left; and
**`knowledgeSoundness_wired_setup`**: the composition with that setup, at most `2^(ht+1)` queries.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.KeccakHash
open LeanVM.Prover (Tree buildTreeWithHash leafDigestsWithHash parentsWithHash levelsWithHash)

/-! ## Maps in `Option` -/

theorem list_mapM_option {α β : Type} (f : α → Option β) (g : α → β)
    (hfg : ∀ a b, f a = some b → g a = b) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ys = l.map g ∧ ∀ a ∈ l, f a = some (g a)
  | [], ys, h => by
    simp only [List.mapM_nil] at h
    cases h
    exact ⟨rfl, by simp⟩
  | a :: l, ys, h => by
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨e, hall⟩ := list_mapM_option f g hfg l bs hbs
    have hab := hfg a b hb
    refine ⟨by rw [List.map_cons, hab, e], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hab]
      exact hb
    · exact hall x hx

theorem array_mapM_option {α β : Type} (f : α → Option β) (g : α → β)
    (hfg : ∀ a b, f a = some b → g a = b) (xs : Array α) (ys : Array β)
    (h : xs.mapM f = some ys) : ys = xs.map g ∧ ∀ a ∈ xs, f a = some (g a) := by
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨e, hall⟩ := list_mapM_option f g hfg xs.toList l hl
  refine ⟨?_, fun a ha => hall a (Array.mem_toList_iff.mpr ha)⟩
  subst e
  apply Array.toList_inj.mp
  simp

/-! ## A run through partial answers that hold its queries -/

/-- **A run through partial answers that hold every query of its run through a table** returns
what the run through the table returns. -/
theorem simulateQ_option_of_log {D : Type} {R : D → Type} {α : Type} (T : ∀ d, R d)
    (impl : QueryImpl (OracleSpec.ofFn R) Option) (oa : OracleComp (OracleSpec.ofFn R) α)
    (h : ∀ q ∈ tableQueryLog oa T, impl q.1 = some (T q.1)) :
    simulateQ impl oa = some (evalWithAnswerFn (QueryImpl.ofFn T) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind] at h
    have ht : impl t = some (T t) := h ⟨t, T t⟩ List.mem_cons_self
    have hk := ih (T t) fun q hq => h q (List.mem_cons_of_mem _ hq)
    rw [simulateQ_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      QueryImpl.ofFn_apply]
    show (impl t).bind (fun u => simulateQ impl (k u)) = _
    rw [ht]
    exact hk

/-- Keccak-256 answered by a history's answers, Keccak-f by the table. -/
def partImpl (H : Hist) (T : KTable) : QueryImpl KeccakCalls Option
  | .inl x => ansOf H (viewT T) x
  | .inr s => some (T (.inr s))

theorem ansOf_viewT {H : Hist} {T : KTable} {x : List UInt8} (hx : x ∈ H) :
    ansOf H (viewT T) x = some (T (.inl x)) := by
  simp only [ansOf, hx, ↓reduceIte]
  exact congrArg some (LeanVM.Rpm.digestOfRpm_toRpm _)

theorem ansOf_viewT_eq {H : Hist} {T : KTable} {x : List UInt8} {v : Digest}
    (h : ansOf H (viewT T) x = some v) : T (.inl x) = v := by
  unfold ansOf at h
  split at h
  · rename_i hx
    rw [← Option.some.inj h]
    exact (LeanVM.Rpm.digestOfRpm_toRpm _).symm
  · cases h

theorem simulateQ_partImpl {α : Type} (H : Hist) (T : KTable) (oa : OracleComp KeccakCalls α)
    (h : ∀ x, Sum.inl x ∈ (tableQueryLog oa T).map Sigma.fst → x ∈ H) :
    simulateQ (partImpl H T) oa = some (evalWithAnswerFn (QueryImpl.ofFn T) oa) := by
  refine simulateQ_option_of_log (R := KeccakCalls) T (partImpl H T) oa fun q hq => ?_
  obtain ⟨d, u⟩ := q
  rcases d with x | s
  · exact ansOf_viewT (h x (List.mem_map.mpr ⟨_, hq, rfl⟩))
  · rfl

/-! ## The tree's climbs through partial answers -/

/-- **Every climb of a tree's authentication paths succeeds through answers that build its
levels**: each step's input is one of the parents' inputs. -/
theorem climb_of_levels (Hp : List UInt8 → Option Digest) (h : List UInt8 → Digest)
    (hH : ∀ x v, Hp x = some v → h x = v) :
    ∀ (k : ℕ) (level : Vector Digest (2 ^ k)) (lv : List (Array Digest)),
      levelsWithHash (m := Option) Hp k level.toArray = some lv → ∀ i : Fin (2 ^ k),
        climbWithHash (m := Option) Hp level[i] i.val
          (MerkleTree.pathOfLevel (nodeHash h) k level i) =
          some (MerkleTree.rootOfLevel (nodeHash h) k level)
  | 0, level, _, _, i => by
    obtain ⟨i, hi⟩ := i
    have : i = 0 := by simp at hi; omega
    subst this
    rfl
  | k + 1, level, lv, hl, i => by
    simp only [levelsWithHash, bind, Option.bind_eq_some_iff] at hl
    obtain ⟨up, hup, rest, hrest, -⟩ := hl
    have hpar := array_mapM_option _ (fun j => h (digestBytes (level.toArray.getD (2 * j) default) ++
        digestBytes (level.toArray.getD (2 * j + 1) default)))
      (fun j v hv => hH _ v hv) _ up hup
    have hupI : up = (MerkleTree.parents (nodeHash h) level).toArray := by
      rw [hpar.1, ← parentsM_id_toArray h level, parentsM_id]
    subst hupI
    have hi2 : i.val / 2 < 2 ^ k := MerkleTree.div_two_lt i.isLt
    have hih := climb_of_levels Hp h hH k (MerkleTree.parents (nodeHash h) level) rest hrest
      ⟨i.val / 2, hi2⟩
    have h2j : 2 * (i.val / 2) < 2 ^ (k + 1) := by
      have hi : i.val < 2 ^ k * 2 := lt_of_lt_of_eq i.isLt (Nat.pow_succ 2 k)
      exact lt_of_lt_of_eq (by omega : 2 * (i.val / 2) < 2 ^ k * 2) (Nat.pow_succ 2 k).symm
    have h2j1 : 2 * (i.val / 2) + 1 < 2 ^ (k + 1) := by
      have hi : i.val < 2 ^ k * 2 := lt_of_lt_of_eq i.isLt (Nat.pow_succ 2 k)
      exact lt_of_lt_of_eq (by omega : 2 * (i.val / 2) + 1 < 2 ^ k * 2) (Nat.pow_succ 2 k).symm
    have hget : ∀ j (hj : j < 2 ^ (k + 1)), level.toArray.getD j default = level[j] :=
      fun j hj => by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj),
          Option.getD_some, Vector.getElem_toArray]
    have hq : Hp (digestBytes level[2 * (i.val / 2)] ++ digestBytes level[2 * (i.val / 2) + 1]) =
        some (h (digestBytes level[2 * (i.val / 2)] ++ digestBytes level[2 * (i.val / 2) + 1])) := by
      have := hpar.2 (i.val / 2) (Array.mem_range.mpr hi2)
      simp only [hget _ h2j, hget _ h2j1] at this
      exact this
    have hidx : ∀ a b (ha : a < 2 ^ (k + 1)) (hb : b < 2 ^ (k + 1)), a = b →
        level[a] = level[b] := by
      intro a b ha hb e
      subst e
      rfl
    rw [MerkleTree.pathOfLevel, MerkleTree.rootOfLevel, climb_cons]
    have hinput : nodeInput level[i] (level[MerkleTree.sibling i.val]'(MerkleTree.sibling_lt i.isLt))
        i.val = digestBytes level[2 * (i.val / 2)] ++ digestBytes level[2 * (i.val / 2) + 1] := by
      rw [Fin.getElem_fin]
      rcases Nat.mod_two_eq_zero_or_one i.val with he | he
      · have hs : MerkleTree.sibling i.val = i.val + 1 := by
          unfold MerkleTree.sibling
          split <;> omega
        unfold nodeInput
        split
        · rw [hidx i.val (2 * (i.val / 2)) i.isLt h2j (by omega),
            hidx (MerkleTree.sibling i.val) (2 * (i.val / 2) + 1) _ h2j1 (by rw [hs]; omega)]
        · exfalso
          omega
      · have hs : MerkleTree.sibling i.val = i.val - 1 := by
          unfold MerkleTree.sibling
          split <;> omega
        unfold nodeInput
        split
        · exfalso
          omega
        · rw [hidx i.val (2 * (i.val / 2) + 1) i.isLt h2j1 (by omega),
            hidx (MerkleTree.sibling i.val) (2 * (i.val / 2)) _ h2j (by rw [hs]; omega)]
    rw [hinput, hq, Option.bind_some]
    have hpe : (MerkleTree.parents (nodeHash h) level)[i.val / 2]'hi2 =
        h (digestBytes level[2 * (i.val / 2)] ++ digestBytes level[2 * (i.val / 2) + 1]) := by
      rw [MerkleTree.getElem_parents]
      rfl
    rw [← hpe]
    exact hih

/-! ## The setup's word -/

theorem tableQueryLog_map {D : Type} {R : D → Type} {α β : Type} (T : ∀ d, R d) (f : α → β)
    (oa : OracleComp (OracleSpec.ofFn R) α) : tableQueryLog (f <$> oa) T = tableQueryLog oa T := by
  rw [map_eq_bind_pure_comp, tableQueryLog_bind]
  simp only [Function.comp_apply, tableQueryLog_pure, List.append_nil]

/-- **The setup's word**: through a history that holds the setup's Keccak-256 queries without
collision, the word `extract` reads under the setup's root is the committed word. -/
theorem extract_wiringSetup (ht w : ℕ) (word : Word) (hws : WellShaped w word) (T : KTable)
    (H : Hist)
    (hsub : ∀ x, Sum.inl x ∈ (tableQueryLog (wiringSetup ht word) T).map Sigma.fst → x ∈ H)
    (hinj : Set.InjOn (viewT T) ↑H) (p : ℕ) (hp : p < 2 ^ ht) :
    Rom.extract (ansOf H (viewT T)) (ofB (evalWithAnswerFn (QueryImpl.ofFn T) (wiringSetup ht word)))
      ht w p = word p := by
  set h : List UInt8 → Digest := fun x => T (.inl x)
  set Hp := ansOf H (viewT T)
  have hH : ∀ x v, Hp x = some v → h x = v := fun x v hv => ansOf_viewT_eq hv
  -- The build, through the table and through the history's answers.
  have hsub' : ∀ x, Sum.inl x ∈ (tableQueryLog (buildTreeWithHash callKeccak256 ht word) T).map
      Sigma.fst → x ∈ H := by
    intro x hx
    refine hsub x ?_
    rw [wiringSetup, tableQueryLog_map]
    exact hx
  have hopt := simulateQ_partImpl H T _ hsub'
  rw [simulateQ_buildTreeM] at hopt
  have hid : evalWithAnswerFn (QueryImpl.ofFn T) (buildTreeWithHash callKeccak256 ht word) =
      buildTreeWithHash (m := Id) h ht word := simulateQ_buildTreeM (QueryImpl.ofFn T) ht word
  rw [hid] at hopt
  have hroot : ofB (evalWithAnswerFn (QueryImpl.ofFn T) (wiringSetup ht word)) =
      treeRoot h ht word := by
    rw [wiringSetup, evalWithAnswerFn_map, hid, root_buildTreeM_id]
    exact LeanVM.Rpm.digestOfRpm_toRpm _
  rw [hroot]
  -- The leaves and the levels through the history's answers.
  change (leafDigestsWithHash (m := Option) Hp ht word).bind (fun leaves =>
    (levelsWithHash (m := Option) Hp ht leaves).bind fun levels =>
      some (⟨ht, word, levels.toArray⟩ : Tree)) = _ at hopt
  obtain ⟨lv, hlv, hopt2⟩ := Option.bind_eq_some_iff.mp hopt
  obtain ⟨lvls, hlvls, -⟩ := Option.bind_eq_some_iff.mp hopt2
  have hleaf := array_mapM_option _ (fun i => h ((word i).flatMap kBytes))
    (fun i v hv => hH _ v hv) _ lv hlv
  set lvV := (leavesOf ht word).map (leafHash h)
  have hlvV : lv = lvV.toArray := by
    rw [hleaf.1]
    have := leafDigestsM_id h ht word
    rw [← this]
    exact (Array.idRun_mapM).symm
  rw [hlvV] at hlvls
  have hp' : p % 2 ^ ht < 2 ^ ht := Nat.mod_lt _ (Nat.two_pow_pos ht)
  have hcl := climb_of_levels Hp h hH ht lvV lvls hlvls ⟨p % 2 ^ ht, hp'⟩
  -- The honest opening at `p` is accepted through the history's answers.
  have hacc : openOneWithHash (m := Option) Hp (treeRoot h ht word) ht w p
      (openingAt h ht word p) = some true := by
    have hlen : (openingAt h ht word p).path.length = ht := MerkleTree.length_path _ _ _ _
    rw [openOne_eq_some_true_iff]
    refine ⟨hws _, hlen, h ((word (p % 2 ^ ht)).flatMap kBytes),
      hleaf.2 _ (Array.mem_range.mpr hp'), ?_⟩
    rw [Rom.climb_mod, hlen]
    have hlv : lvV[p % 2 ^ ht]'hp' = h ((word (p % 2 ^ ht)).flatMap kBytes) := by
      simp [lvV, leavesOf, leafHash]
    rw [← hlv]
    exact hcl
  have he := extract_eq_of_openOne (answersInj_ansOf hinj) hacc
  rw [Nat.mod_eq_of_lt hp] at he
  rw [he]
  show word (p % 2 ^ ht) = word p
  rw [Nat.mod_eq_of_lt hp]

/-! ## The setup of the wiring stack -/

/-- **The stack's word is honest**: every lane of every column is the encoding of its block
(`stackWord_agrees`). -/
theorem honest_stackWord (μ R : ℕ) (q : Column μ) :
    HonestWord μ R (LeanVM.Protocol.Whir.Complete.stackWord μ q) q :=
  fun u v => LeanVM.Protocol.Whir.Complete.stackWord_agrees μ R q v (Finset.mem_univ _) u

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds}
variable (W : Wire P B) (D : Deploy F)

/-- **The wiring claims, on the wiring stack**: the stack's table satisfies the wiring opening's
claims only if F1's wiring claim holds (what is left of `WiringMatch`). -/
def WiringClaims (q₀ : Column D.Lσ.logN) : Prop :=
  ∀ (π : RootProof F) (ch : Chals F),
    (∀ cl ∈ (D.clσ π ch).claims, D.Lσ.tableEval q₀ cl.point = cl.value) →
      wiringClaim P ch.t π.v.2

/-- **The setup of the wiring stack `q₀`**: the Merkle tree of its word (`stackWord`, the encoding
`commitStack` commits), at the wiring opening's height. -/
def stackSetup (q₀ : Column D.Lσ.logN) : OracleComp KeccakCalls Bytes32 :=
  wiringSetup (rootHeight D.Lσ.logN D.R) (LeanVM.Protocol.Whir.Complete.stackWord D.Lσ.logN q₀)

/-- The setup's queries: `2^(ht+1)` (`isTotalQueryBound_buildTreeM`). -/
abbrev setupQueries : ℕ := 2 ^ (rootHeight D.Lσ.logN D.R + 1)

theorem isTotalQueryBound_stackSetup (q₀ : Column D.Lσ.logN) :
    IsTotalQueryBound (stackSetup D q₀) (setupQueries D) :=
  (isQueryBound_map_iff _ (fun t : Tree => toB t.root) _ _ _).mpr
    (isTotalQueryBound_buildTreeM _ _)

/-- **`WiringMatch` for the setup of a stack**, but for the claims: the word is the stack's
(`honest_stackWord`), and the setup's queries make it the word the setup's root commits to
(`extract_wiringSetup`). -/
def wiringMatch (q₀ : Column D.Lσ.logN) (hcl : WiringClaims (P := P) D q₀) :
    WiringMatch (P := P) D (stackSetup D q₀) where
  q₀ := q₀
  word := LeanVM.Protocol.Whir.Complete.stackWord D.Lσ.logN q₀
  honest := honest_stackWord _ _ q₀
  setupWord T H hsub hinj p hp := extract_wiringSetup _ _ _
    (LeanVM.Protocol.Whir.Complete.wellShaped_stackWord _ q₀) T H hsub hinj p hp
  claims := hcl

/-- **Knowledge soundness of the deployed verifier, the circuit's commitment the wiring stack's
tree computed with the oracle**: `knowledgeSoundness_wired_decoded` with the setup of `q₀`
(`QS = 2^(ht+1)` queries, `ht` the wiring tree's height); what remains is `WitnessClaims`,
`QuotientClaims` and `WiringClaims`. -/
theorem knowledgeSoundness_wired_setup (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows) (hLw : D.Lw = witnessLayout r)
    (hLσ : D.Lσ = wiringLayout r) (hLQ : D.LQ = quotientLayout r) (hR : D.R = logInvRate)
    (read₁ : Tab D.Lw → B.Msg₁) (read₂ : Tab D.LQ → B.Msg₂)
    (hcl₁ : WitnessClaims D read₁) (hcl₂ : QuotientClaims W D read₂)
    (q₀ : Column D.Lσ.logN) (hclσ : WiringClaims (P := P) D q₀)
    (A : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : ∀ ir, IsTotalQueryBound (A ir) Q) :
    Pr{let z ← (simulateQ randomOracle (wiredExp W D (withSetup (stackSetup D q₀) A))).run' ∅}[
        BreaksW W (tableCode D.Lw D.R
          (admissible_of_eq hLw hR (layouts_ok r h1 h2).1) read₁) z] ≤
      openingBound (setupQueries D + Q + 6) + openingBound (setupQueries D + Q + 6 + 10122) +
        openingBound (setupQueries D + Q + 6 + 10122 + 10122) +
        ((setupQueries D + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) *
          ((listFactor (Whir.Params.certOf D.Lw.logN D.R 0).listHi
              (Whir.Params.certOf D.LQ.logN D.R 0).listHi : ℝ≥0∞) * (roundError P B : ℝ≥0∞) +
          5 * ((setupQueries D + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  knowledgeSoundness_wired_decoded W D r h1 h2 hLw hLσ hLQ hR read₁ read₂ hcl₁ hcl₂
    (stackSetup D q₀) A (wiringMatch D q₀ hclσ) (setupQueries D) Q
    (isTotalQueryBound_stackSetup D q₀) hQ

/-- **The same at the sizes of `quotient::protocol`**: the list term at most `2^-128`. -/
theorem knowledgeSoundness_wired_setup_bits (hq : Fintype.card F = 2 ^ 192)
    (hN : P.nCells = 2 ^ 24) (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28)
    (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows)
    (hLw : D.Lw = witnessLayout r) (hLσ : D.Lσ = wiringLayout r)
    (hLQ : D.LQ = quotientLayout r) (hR : D.R = logInvRate)
    (read₁ : Tab D.Lw → B.Msg₁) (read₂ : Tab D.LQ → B.Msg₂)
    (hcl₁ : WitnessClaims D read₁) (hcl₂ : QuotientClaims W D read₂)
    (q₀ : Column D.Lσ.logN) (hclσ : WiringClaims (P := P) D q₀)
    (A : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : ∀ ir, IsTotalQueryBound (A ir) Q) :
    Pr{let z ← (simulateQ randomOracle (wiredExp W D (withSetup (stackSetup D q₀) A))).run' ∅}[
        BreaksW W (tableCode D.Lw D.R
          (admissible_of_eq hLw hR (layouts_ok r h1 h2).1) read₁) z] ≤
      openingBound (setupQueries D + Q + 6) + openingBound (setupQueries D + Q + 6 + 10122) +
        openingBound (setupQueries D + Q + 6 + 10122 + 10122) +
        ((setupQueries D + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) *
          (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
          5 * ((setupQueries D + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  knowledgeSoundness_wired_decoded_bits W D hq hN hw hd r h1 h2 hLw hLσ hLQ hR read₁ read₂ hcl₁
    hcl₂ (stackSetup D q₀) A (wiringMatch D q₀ hclσ) (setupQueries D) Q
    (isTotalQueryBound_stackSetup D q₀) hQ

/-- At the deployed wiring layout, the setup makes `2^(ht+1)` queries, `ht = log_rows - 3`:
`2^20` at `log_rows = 22`. -/
theorem setupQueries_eq (r : ℕ) (hLσ : D.Lσ = wiringLayout r) (hR : D.R = logInvRate) :
    setupQueries D = 2 ^ (r + 2 - laneFold + logInvRate + 1) := by
  simp only [setupQueries, hLσ, hR, rootHeight]
  rfl

end Compose
