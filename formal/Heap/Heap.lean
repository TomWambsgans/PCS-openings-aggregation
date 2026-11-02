-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Heap.Tree
import Heap.Cantor
import Heap.Leaf
import Heap.Bus
import Heap.Balanced
import Heap.Realize
import Heap.LeanIsa
import Heap.Deployed
import Heap.Honest

/-!
# Heap: the univariate PIOP's bus, a product heap, implies `Balanced`

The univariate PIOP for leanVM 42422001 (`crates/leanvm_univariate/SPEC.md` §2, §5, branch
`leanvm-univariate`, at `56ea040`) proves leanVM's bus balance with a **grand product**, not
logUp (in characteristic two, `Σ 1/(β + f)` sees each tuple's multiplicity only mod 2): the push
and pull fingerprint products are compared through a committed binary tree on Cantor cosets, the
heap `T`. This library proves, generically and then at leanISA's instance, that the heap's
identities give `Lv42.Protocol.M3Instance.Balanced` (the push and pull tuples one multiset, a
`List.Perm`) outside an event of probability at most `4·N/|E|`.

## The chain

1. **The tree** (`Heap.Tree`, `Heap.Cantor`). On positions, `TreeHolds n T`:
   `T(i >>> 1) = T(i)·T(i ^^^ 1)` for `2 ≤ i < 2^n`; then `T(1) = Π_{2^(n-1) ≤ i < 2^n} T(i)`
   (`root_eq_prod_leaves`). On points of a Cantor basis, `ω_i = Σ_{bit k of i} β_k`,
   `V_r = {ω_i : i < 2^r}`, the facts `s(ω_i) = ω_{i >> 1}` (`sq_omega`),
   `ω_i + 1 = ω_{i xor 1}` (`omega_xor_one`), `ω_1 = 1` (`omega_one`) and injectivity on
   `[0, 2^n)` (`omega_injOn`) turn the tree identity on `V_n \ V_1` into the one on positions
   (`root_eq_prod_leaves_omega`); `tree_of_quotient` reads it off the verifier's quotient form
   `w_1·(T(s(t)) + T(t)·T(t + 1)) + w_n·Q_tree = 0`. Generic in `n`; at the deployed basis for
   every `n ≤ 24` (`Heap.Deployed`, no evaluation: Bridge's kernel-checked Cantor property).
2. **The leaves** (`Heap.Leaf`). The leaf lemma `prod_leaves_eq_div` (`Π leaves = Π P'/Π P` when no
   pull fingerprint vanishes) and its multiplied-out form `prod_leaves_mul` (no hypothesis); leaves
   in blocks laid end to end (`LeafBlock`, `LeavesHold`; a table's padding rows have leaf `1`,
   `LeafBlock.ofRows`; aligned when largest first, `alignedFrom_of_sorted`); and **`heap_prod_eq`**:
   tree, leaves and root `T(1)·fp(init) = fp(fin)` give `Π_push fp · fp(init) = Π_pull fp · fp(fin)`,
   by multiplications only.
3. **The fingerprint** (`Heap.Bus`). `fp α β τ = β + Σ_s eq(α, s)·τ_s` is leanerVM 6175f1a0's
   `β − fingerprint α τ` (characteristic two), so its Theorem 5.1 (`sideProduct_collision`, one
   Schwartz–Zippel bound over `E⁵`, total degree `4` per factor) gives **`prob_fpProd_eq_le`**:
   lists that are not permutations of each other, of at most `N` tuples each, have equal products
   at a uniform `(α, β)` with probability at most `busError N = 4·N/|E| = 4·N/2^192`. Hence
   `HeapData.prob_sat_le`: the heap holds (`HeapData.Sat`: **some** `T` meets the identities) with
   at most that probability when its push and pull tuples differ as multisets.
4. **`Balanced`** (`Heap.Balanced`, `Heap.Realize`, `Heap.LeanIsa`). A layout `Realizes` the bus of
   a stack `q` when its tuples are `I.tuples q` up to order; then **`prob_sat_not_balanced`**:
   `Pr[Sat ∧ ¬ Balanced q] ≤ busError N`, `N ≥ busCount` (the instance's tuple counts); and
   **`prob_exists_candidate_le`**: union-bounded over a list `L` of candidate stacks (a WHIR root's
   level-0 Johnson list), at most `busError (L.length · N)`. `tableBlock` and `pairBlock` build the
   blocks of any `M3Instance`; **`LeanIsa.realizes`**: SPEC §5.2's heap (memory and bytecode pairs,
   the six opcode tables, unused blocks, the state boundary at the root), in any block order,
   realizes `leanIsaInstance`'s bus for every stack, and `LeanIsa.prob_sat_not_balanced` follows.
5. **Not vacuous** (`Heap.Honest`): the honest heap satisfies `Sat` whenever the bus balances and no
   pull fingerprint vanishes (`HeapData.sat_of_perm`).

## Zero fingerprints

No exclusion is needed. The tree, leaf and root identities are multiplied out, never divided
(`heap_prod_eq`): a zero pull fingerprint on a row makes a push fingerprint of that row zero (its
leaf identity), so both products vanish and are equal, and a zero state fingerprint at the root does
the same. The bound counts every challenge, those at which some fingerprint vanishes included.

## What is left to the end-to-end proof

That the verifier's checks at the random point `t` make the identities hold on the domain (a
Schwartz–Zippel step per identity, over the Johnson lists of `C1` and `C2`), that the restriction
`R_b` agrees with `T` on its aligned coset (`omega_add_of_dvd` gives `o_b + ω_k = ω_{pos_b + k}`),
that the products `P_b(ω_k)`, `P'_b(ω_k)` of the committed columns are row `k`'s fingerprints, and
that `Z_act`, `Z_pad` vanish on the executed and padding rows: these produce `HeapData.Sat` for the
layout `LeanIsa.heapData`, to which `LeanIsa.prob_sat_not_balanced` and
`prob_exists_candidate_le` apply.

The build fails if the axiom footprint of the headline theorems grows beyond Lean's three standard
axioms.
-/

-- 1. The tree.
/-- info: 'Heap.root_eq_prod_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.root_eq_prod_leaves

/-- info: 'Heap.sq_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.sq_omega

/-- info: 'Heap.omega_xor_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.omega_xor_one

/-- info: 'Heap.omega_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.omega_injOn

/-- info: 'Heap.root_eq_prod_leaves_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.root_eq_prod_leaves_omega

/-- info: 'Heap.tree_of_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.tree_of_quotient

/-- info: 'Heap.omega_add_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.omega_add_of_dvd

/-- info: 'Heap.Deployed.root_eq_prod_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.Deployed.root_eq_prod_leaves

-- 2. The leaves.
/-- info: 'Heap.prod_leaves_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.prod_leaves_eq_div

/-- info: 'Heap.prod_leaves_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.prod_leaves_mul

/-- info: 'Heap.heap_prod_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.heap_prod_eq

-- 3. The fingerprint.
/-- info: 'Heap.prob_fpProd_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.prob_fpProd_eq_le

/-- info: 'Heap.card_fpProd_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.card_fpProd_eq_le

/-- info: 'Heap.HeapData.prob_sat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.HeapData.prob_sat_le

-- 4. `Balanced`.
/-- info: 'Heap.prob_sat_not_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.prob_sat_not_balanced

/-- info: 'Heap.card_sat_not_balanced_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.card_sat_not_balanced_le

/-- info: 'Heap.prob_exists_candidate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.prob_exists_candidate_le

/-- info: 'Heap.card_exists_candidate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.card_exists_candidate_le

/-- info: 'Heap.LeanIsa.realizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.LeanIsa.realizes

/-- info: 'Heap.LeanIsa.prob_sat_not_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.LeanIsa.prob_sat_not_balanced

-- 5. Not vacuous.
/-- info: 'Heap.HeapData.sat_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Heap.HeapData.sat_of_perm
