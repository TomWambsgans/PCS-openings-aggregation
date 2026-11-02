-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.Skeleton

/-!
# The skeleton's number of operations

`skel_queryBound`: the deployed skeleton makes at most `skelBound sh` operations on every path,
whatever the oracle and the messages answer (grinding counted at its worst case, `2^64` tries of
two permutations each, at every level). `skelBound_le`: at most `2^72` for shapes of at most
`2^23`-leaf trees, seven levels of at most `256` queries and `2^23` public rows.
-/

open OracleComp OracleSpec QuotientRpm

namespace QuotientZk.Deployed

/-- One query then a pure continuation. -/
theorem qb_query_pure {α : Type} (t : (DSpec).Domain) (f : (DSpec).Range t → α) :
    IsTotalQueryBound (liftM (DSpec.query t) >>= fun a => (pure (f a) : OracleComp DSpec α)) 1 := by
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by norm_num, fun _ => trivial⟩

theorem qb_hashH (m : List UInt8) : IsTotalQueryBound (hashH m) 1 := qb_query_pure _ _
theorem qb_perm (x : KSt) : IsTotalQueryBound (perm x) 1 := qb_query_pure _ _
theorem qb_chalH (m : List UInt8) : IsTotalQueryBound (chalH m) 1 := qb_query_pure _ _
theorem qb_chalF (x : KSt) : IsTotalQueryBound (chalF x) 1 := qb_query_pure _ _
theorem qb_leafH (k : Tbl) (x : ℕ) : IsTotalQueryBound (leafH k x) 1 := qb_query_pure _ _

theorem qb_getMsg : IsTotalQueryBound getMsg 1 := by
  unfold getMsg
  have := qb_query_pure (α := Msg) .msg id
  simpa using this

theorem qb_pure {α : Type} (a : α) (n : ℕ) : IsTotalQueryBound (pure a : OracleComp DSpec α) n :=
  trivial

theorem qb_bind {α β : Type} {oa : OracleComp DSpec α} {ob : α → OracleComp DSpec β} {n₁ n₂ : ℕ}
    (h1 : IsTotalQueryBound oa n₁) (h2 : ∀ x, IsTotalQueryBound (ob x) n₂) :
    IsTotalQueryBound (oa >>= ob) (n₁ + n₂) := isTotalQueryBound_bind h1 h2

theorem qb_mono {α : Type} {oa : OracleComp DSpec α} {n₁ n₂ : ℕ} (h : IsTotalQueryBound oa n₁)
    (hle : n₁ ≤ n₂) : IsTotalQueryBound oa n₂ := h.mono hle

theorem qb_mapM {α β : Type} (f : α → OracleComp DSpec β) (c : ℕ)
    (hf : ∀ a, IsTotalQueryBound (f a) c) :
    ∀ l : List α, IsTotalQueryBound (l.mapM f) (l.length * c)
  | [] => trivial
  | a :: l => by
    rw [List.mapM_cons]
    have := qb_bind (hf a) fun b => qb_bind (qb_mapM f c hf l) fun bs =>
      qb_pure (n := 0) (b :: bs)
    refine qb_mono this ?_
    simp [Nat.succ_mul, Nat.add_comm]

theorem mapM_length {α β : Type} (f : α → OracleComp DSpec β) :
    ∀ (l : List α), ∀ r ∈ support (l.mapM f), r.length = l.length
  | [] => by simp
  | a :: l => by
    intro r hr
    rw [List.mapM_cons] at hr
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨b, -, bs, hbs, rfl⟩ := hr
    simp [mapM_length f l bs hbs]

theorem qb_levelUp : ∀ l : List Bytes32, IsTotalQueryBound (levelUp l) l.length
  | a :: b :: rest => by
    unfold levelUp
    refine qb_mono (qb_bind (qb_hashH _) fun _ => qb_bind (qb_levelUp rest) fun _ =>
      qb_pure (n := 0) _) ?_
    simp; omega
  | [a] => by simp [levelUp]; exact trivial
  | [] => by simp [levelUp]; exact trivial

theorem levelUp_length : ∀ l : List Bytes32, ∀ r ∈ support (levelUp l), r.length ≤ l.length
  | a :: b :: rest => by
    intro r hr
    unfold levelUp at hr
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨h, -, t, ht, rfl⟩ := hr
    have := levelUp_length rest t ht
    simp; omega
  | [a] => by intro r hr; simp [levelUp] at hr; simp [hr]
  | [] => by intro r hr; simp [levelUp] at hr; simp [hr]

theorem qb_levels : ∀ (d : ℕ) (l : List Bytes32), IsTotalQueryBound (levels d l) (d * l.length)
  | 0, l => trivial
  | d + 1, l => by
    unfold levels
    refine qb_mono (isTotalQueryBound_bind_of_mem_support (qb_levelUp l) fun up hup =>
      qb_mono (qb_bind (qb_levels d up) fun _ => qb_pure (n := 0) _)
        (show d * up.length + 0 ≤ d * l.length by
          have := levelUp_length l up hup
          simp only [Nat.add_zero]
          exact Nat.mul_le_mul_left d this)) ?_
    rw [Nat.succ_mul, Nat.add_comm]

/-! ## The duplex -/

theorem qb_absorb (d : Dx) (x : Limbs) (tag : UInt64) : IsTotalQueryBound (d.absorb x tag) 1 := by
  unfold Dx.absorb
  split_ifs
  · exact qb_mono (qb_bind (qb_perm _) fun _ => qb_pure (n := 0) _) (by norm_num)
  · exact trivial

theorem qb_absorbAll : ∀ (d : Dx) (xs : List Limbs), IsTotalQueryBound (d.absorbAll xs) xs.length
  | d, [] => trivial
  | d, x :: xs => by
    unfold Dx.absorbAll
    exact qb_mono (qb_bind (qb_absorb d x _) fun d' => qb_absorbAll d' xs) (by simp; omega)

theorem qb_draw (d : Dx) : IsTotalQueryBound d.draw 1 := by
  unfold Dx.draw
  exact qb_mono (qb_bind (qb_chalF _) fun _ => qb_pure (n := 0) _) (by norm_num)

theorem qb_seed (iv : Bytes32) : IsTotalQueryBound (seed iv) 1 := by
  unfold seed
  exact qb_mono (qb_bind (qb_perm _) fun _ => qb_pure (n := 0) _) (by norm_num)

theorem qb_tryNonce (d : Dx) (n : UInt64) : IsTotalQueryBound (tryNonce d n) 2 := by
  unfold tryNonce
  exact qb_mono (qb_bind (qb_absorb d _ _) fun _ => qb_bind (qb_perm _) fun _ =>
    qb_pure (n := 0) _) (by norm_num)

theorem qb_grind (d : Dx) : ∀ (fuel : ℕ) (n : UInt64), IsTotalQueryBound (grind d fuel n) (2 * fuel)
  | 0, n => trivial
  | fuel + 1, n => by
    unfold grind
    refine qb_mono (qb_bind (qb_tryNonce d n) fun r => ?_) (by omega : 2 + 2 * fuel ≤ 2 * (fuel + 1))
    obtain ⟨ok, d'⟩ := r
    simp only
    split_ifs
    · exact trivial
    · exact qb_grind d fuel (n + 1)

/-! ## The opening's steps -/

theorem takeScalars_length (items : Msg) (k : ℕ) : (takeScalars items k).1.length = k := by
  unfold takeScalars
  split <;> simp

theorem qb_sendK (o : OSt) (k : ℕ) : IsTotalQueryBound (sendK o k) k := by
  unfold sendK
  refine qb_mono (qb_bind (qb_absorbAll o.dx _) fun _ => qb_pure (n := 0) _) ?_
  have := takeScalars_length o.items k
  unfold takeScalars at this
  omega

theorem qb_drawO (o : OSt) : IsTotalQueryBound (drawO o) 2 := by
  unfold drawO
  refine qb_mono (qb_bind (n₂ := 1) (qb_draw o.dx) fun r => ?_) (by norm_num)
  obtain ⟨c, dx⟩ := r
  exact qb_mono (qb_bind qb_getMsg fun _ => qb_pure (n := 0) _) (by norm_num)

theorem qb_rounds : ∀ (o : OSt) (k : ℕ), IsTotalQueryBound (rounds o k) (4 * k)
  | o, 0 => trivial
  | o, k + 1 => by
    unfold rounds
    refine qb_mono (qb_bind (qb_drawO o) fun r => ?_) (by omega : 2 + (2 + 4 * k) ≤ 4 * (k + 1))
    obtain ⟨c, o'⟩ := r
    exact qb_bind (qb_sendK o' 2) fun o'' => qb_rounds o'' k

theorem qb_drawMany : ∀ (o : OSt) (m : ℕ), IsTotalQueryBound (drawMany o m) (2 * m)
  | o, 0 => trivial
  | o, m + 1 => by
    unfold drawMany
    refine qb_mono (qb_bind (qb_drawO o) fun r => ?_) (by omega : 2 + (2 * m + 0) ≤ 2 * (m + 1))
    obtain ⟨c, o'⟩ := r
    exact qb_bind (qb_drawMany o' m) fun r' => by obtain ⟨cs, o''⟩ := r'; exact trivial

/-- The operations of a commitment of depth `d`. -/
def commitBound (d : ℕ) : ℕ := 2 ^ d + d * 2 ^ d + 2

theorem qb_commitNext (o : OSt) (d : ℕ) : IsTotalQueryBound (commitNext o d) (commitBound d) := by
  unfold commitNext commitBound
  have hm := qb_mapM (fun i => hashH ((takeRows o.items).1.getD i [])) 1 (fun _ => qb_hashH _)
    (List.range (2 ^ d))
  rw [List.length_range, Nat.mul_one] at hm
  refine qb_mono (isTotalQueryBound_bind_of_mem_support (suffixBound := d * 2 ^ d + 2) hm
    fun leaves hl => ?_) (by omega)
  have hlen := mapM_length _ _ leaves hl
  rw [List.length_range] at hlen
  refine qb_mono (qb_bind (qb_levels d leaves) fun lv =>
    qb_bind (n₁ := 2) (qb_mono (qb_absorbAll _ _) (by simp [rootLimbs])) fun _ =>
      qb_pure (n := 0) _) ?_
  simp [rootLimbs, hlen]

theorem qb_ood (o : OSt) (m : ℕ) : IsTotalQueryBound (ood o m) (2 * m + 3) := by
  unfold ood
  refine qb_bind (qb_drawMany o m) fun r => ?_
  obtain ⟨cs, o'⟩ := r
  exact qb_sendK o' 3

theorem div_le_self' (q per : ℕ) : (q + per - 1) / per ≤ q := by
  rcases Nat.eq_zero_or_pos per with h | h
  · simp [h]
  · rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; exact Nat.le_of_eq (Nat.div_eq_of_lt (by omega))
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      obtain ⟨p', rfl⟩ : ∃ p', per = p' + 1 := ⟨per - 1, by omega⟩
      refine Nat.div_le_of_le_mul ?_
      have e : q' + 1 + (p' + 1) - 1 = q' + p' + 1 := by omega
      rw [e]
      nlinarith [Nat.zero_le (q' * p')]

/-- The operations of a query phase of `q` queries: grinding at its worst, the draws, `λ`, the
intro message. -/
def qpBound (q : ℕ) : ℕ := 2 * 2 ^ 64 + 2 * q + 4

theorem qb_queryPhase (o : OSt) (lvl q : ℕ) : IsTotalQueryBound (queryPhase o lvl q) (qpBound q) := by
  unfold queryPhase qpBound
  refine qb_mono (qb_bind (n₂ := 2 * q + 4) (qb_grind o.dx (2 ^ 64) 0) fun r => ?_) (by omega)
  obtain ⟨nonce, dx⟩ := r
  simp only
  refine qb_mono (qb_bind (qb_drawMany _ _) fun r' => ?_)
    (show 2 * ((q + _ - 1) / _) + (2 + 2) ≤ 2 * q + 4 by
      have := div_le_self' q (192 / max ((o.trees.getD lvl []).length - 1) 1)
      omega)
  obtain ⟨cs, o'⟩ := r'
  refine qb_bind (qb_drawO o') fun r'' => ?_
  obtain ⟨c, o''⟩ := r''
  exact qb_sendK _ 2

/-- The operations of the levels between the first and the last. -/
def middleBound : List (ℕ × ℕ × ℕ) → List ℕ → ℕ
  | [], _ => 0
  | (folds, depth, oodN) :: rest, q :: qs =>
    4 * folds + commitBound depth + (2 * oodN + 3) + qpBound q + middleBound rest qs
  | _ :: _, [] => 0

theorem qb_middle : ∀ (o : OSt) (lvl : ℕ) (ls : List (ℕ × ℕ × ℕ)) (qs : List ℕ),
    IsTotalQueryBound (middle o lvl ls qs) (middleBound ls qs)
  | o, lvl, [], qs => by unfold middle; exact trivial
  | o, lvl, (folds, depth, oodN) :: rest, q :: qs => by
    unfold middle middleBound
    exact qb_mono (qb_bind (qb_rounds o folds) fun o1 => qb_bind (qb_commitNext o1 depth) fun o2 =>
      qb_bind (qb_ood o2 oodN) fun o3 => qb_bind (qb_queryPhase o3 lvl q) fun o4 =>
        qb_middle o4 (lvl + 1) rest qs) (by omega)
  | o, lvl, _ :: _, [] => by unfold middle; exact trivial

/-! ## The trees, the openings, the skeleton -/

/-- The operations of a level-0 tree. -/
def tree0Bound (sh : OpenShape) : ℕ :=
  match sh.secret with
  | some _ => 2 ^ sh.depth₀ + sh.depth₀ * 2 ^ sh.depth₀
  | none => sh.pubRows.length + sh.depth₀ * sh.pubRows.length

theorem qb_tree₀ (sh : OpenShape) : IsTotalQueryBound (tree₀ sh) (tree0Bound sh) := by
  unfold tree₀ tree0Bound
  cases sh.secret with
  | some k =>
    simp only
    have hm := qb_mapM (leafH k) 1 (fun _ => qb_leafH _ _) (List.range (2 ^ sh.depth₀))
    rw [List.length_range, Nat.mul_one] at hm
    refine isTotalQueryBound_bind_of_mem_support hm fun leaves hl => ?_
    have hlen := mapM_length _ _ leaves hl
    rw [List.length_range] at hlen
    have := qb_levels sh.depth₀ leaves
    rwa [hlen] at this
  | none =>
    simp only
    have hm := qb_mapM hashH 1 (fun _ => qb_hashH _) sh.pubRows
    rw [Nat.mul_one] at hm
    refine isTotalQueryBound_bind_of_mem_support hm fun leaves hl => ?_
    have hlen := mapM_length _ _ leaves hl
    have := qb_levels sh.depth₀ leaves
    rwa [hlen] at this

/-- The operations of an opening. -/
def openBound (sh : OpenShape) : ℕ :=
  1 + (1 + (1 + (2 + (2 + (2 + (4 * 6 + (commitBound sh.depth₁ +
    ((2 * sh.ood₀ + 3) + (qpBound (sh.queries.headD 0) +
    (middleBound sh.levels (sh.queries.drop 1) + (4 * sh.lastFolds + (2 ^ sh.residualVars +
    (qpBound (sh.queries.getLastD 0) + (4 * (sh.residualVars - 1) + 2))))))))))))))

theorem qb_opening (sh : OpenShape) (lv₀ : List (List Bytes32)) :
    IsTotalQueryBound (opening sh lv₀) (openBound sh) := by
  unfold opening openBound
  refine qb_bind qb_getMsg fun m => ?_
  generalize (match m with
    | .bytes b :: rest => (b, rest)
    | rest => ([], rest)) = cm
  obtain ⟨claims, m'⟩ := cm
  refine qb_bind (qb_hashH _) fun iv => qb_bind (qb_seed iv) fun dx => ?_
  refine qb_bind (n₁ := 2) (qb_mono (qb_absorbAll _ _) (by simp [rootLimbs])) fun dx' => ?_
  refine qb_bind (qb_drawO _) fun r => ?_
  obtain ⟨_, o1⟩ := r
  refine qb_bind (qb_sendK o1 2) fun o2 => qb_bind (qb_rounds o2 6) fun o3 => ?_
  refine qb_bind (qb_commitNext o3 _) fun o4 => qb_bind (qb_ood o4 _) fun o5 => ?_
  refine qb_bind (qb_queryPhase o5 0 _) fun o6 => qb_bind (qb_middle o6 1 _ _) fun o7 => ?_
  refine qb_bind (qb_rounds o7 _) fun o8 => qb_bind (qb_sendK o8 _) fun o9 => ?_
  refine qb_bind (qb_queryPhase o9 _ _) fun o10 => qb_bind (qb_rounds o10 _) fun o11 => ?_
  refine qb_mono (qb_bind (n₂ := 0) (qb_drawO o11) fun r' => ?_) (by norm_num)
  obtain ⟨_, o12⟩ := r'
  exact qb_pure (n := 0) _

/-- **The skeleton's operations**: the three level-0 trees, the chain's six hashes and the message
of the values, the three openings. -/
def skelBound (sh : Shape) : ℕ :=
  tree0Bound sh.witness + tree0Bound sh.quotient + tree0Bound sh.wiring + 8 +
    openBound sh.witness + openBound sh.wiring + openBound sh.quotient

theorem skel_queryBound (sh : Shape) : IsTotalQueryBound (skel sh) (skelBound sh) := by
  unfold skel
  refine qb_mono (qb_bind (qb_tree₀ _) fun lvW => qb_bind (qb_hashH _) fun st₀ =>
    qb_bind (qb_chalH _) fun st₁ => qb_bind (qb_chalH _) fun st₂ =>
    qb_bind (qb_chalH _) fun st₃ => qb_bind (qb_tree₀ _) fun lvQ =>
    qb_bind (qb_chalH _) fun st₄ => qb_bind qb_getMsg fun m =>
    qb_bind (qb_chalH _) fun _ => qb_bind (qb_tree₀ _) fun lvσ =>
    qb_bind (qb_opening _ _) fun oW => qb_bind (qb_opening _ _) fun oσ =>
    qb_bind (qb_opening _ _) fun oQ => qb_pure (n := 0) _) ?_
  unfold skelBound
  omega

set_option exponentiation.threshold 300 in
/-- **At the deployed shape**: at most `2^70` operations (grinding at its worst case dominates:
sixteen levels of `2^65` permutations), for the wiring codeword's `2^19` rows. -/
theorem skelBound_deployed (st : Statement) (idW idσ idQ : Bytes32) (rows : List (List UInt8))
    (hrows : rows.length = 2 ^ 19) :
    skelBound (deployedShape st idW idσ idQ rows) ≤ 2 ^ 70 := by
  simp only [skelBound, deployedShape, tree0Bound, openBound, witnessShape, wiringShape,
    quotientShape, middleBound, commitBound, qpBound, hrows, List.headD, List.drop, List.getLastD,
    List.length_cons, List.length_nil]
  norm_num

end QuotientZk.Deployed
