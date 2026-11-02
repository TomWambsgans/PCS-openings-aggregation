<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# WhirBridge: our WHIR openings under leanerVM `mumbai`'s proofs

`crates/quotient/src/opening.rs` opens every claim on a committed table with leanVM's WHIR, unchanged.
[leanerVM](https://github.com/Verified-zkEVM/leanerVM) `mumbai` (commit `6175f1a0`, MIT OR Apache-2.0;
its `leanvm-rev` is leanVM `c445e3d5`, the commit our `crates/verifier` is vendored from) proves leanVM's
verifier knowledge sound. This package transcribes `opening::verify` into mumbai's verifier language,
**its transcript included**, and proves its Fiat–Shamir soundness in the random-oracle model for the
three openings the protocol makes (the wiring table's, public; the witness and quotient tables',
hidden, in the layout redesigned for condition (R) of `crates/quotient/HIDING.md`: the overflow lane
`32`, seven random lanes after it, and the **gadget**), at every supported size, in table terms.
Everything here is sorry-free and depends on `propext`, `Classical.choice` and `Quot.sound` only
(`#guard_msgs` checks in `WhirBridge.lean`; the review's sweep `formal/Review/WhirBridgeAxioms.lean`:
589 declarations, no other axiom, no `opaque`, no `implemented_by`). No `native_decide`: the facts
about our layouts are `decide +kernel`.

## What is proved

**`ours_sound`** (`WhirBridge/Verifier.lean`): for every supported size `17 ≤ log_rows ≤ 22` and each of
`witnessLayout r`, `wiringLayout r`, `quotientLayout r` (the layouts of `protocol.rs`, built by the Lean
`Layout.hidden` / `Layout.new`), an adversary `A` making at most `QA` queries to Keccak-256 and
Keccak-f[1600] (two independent random oracles) that outputs a root, claims on the layout and a proof
makes `opening::verify` (`openingVerifyWithHash`, rate `1/2`) accept while **every candidate table** of
the word extracted for that root violates one of the claims with probability at most

```
(QA + 10122) · (2^-128 + 5 (QA + 10122) / 2^256)        ≤ 2^-63 for QA ≤ 2^64   (opening_bound_le)
```

In Lean:

```lean
theorem ours_sound (r : ℕ) (h1 : minLogRows ≤ r) (h2 : r ≤ maxLogRows) (L : Layout)
    (hLr : L = witnessLayout r ∨ L = wiringLayout r ∨ L = quotientLayout r)
    (A : OracleComp KeccakCalls ((Digest × Stmt L.stacking) × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier L logInvRate)}[
        z.1.2 = true ∧ OpeningDoomed L logInvRate z.1.1 z.2] ≤ openingBound QA

def OpeningDoomed (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof)
    (cache : KeccakCalls.QueryCache) : Prop :=
  ∀ q ∈ Candidates L.logN R (code₀ L.logN R).thr
      (extract (fun x ↦ cache (.inl x)) w.1.1 (rootHeight L.logN R) (2 ^ laneFold)),
    ∃ cl ∈ w.1.2.claims, L.tableEval q cl.point ≠ cl.value

openingBound QA = (QA + 10122) * ((2⁻¹)^128 + 5 * (QA + 10122) / 2^256)
```

`ourVerifier L R w` is `openingVerifyWithHash callKeccak256 callKeccakF1600 L R root claims π`, the
Lean `opening::verify` (which, like the Rust, rejects an empty claim list before anything else);
`extract` is mumbai's straight-line extraction of the word a root commits to from the oracle's
answers; `Candidates` the stacks within level 0's Johnson radius of it (at most `9952`, `7908`, `3564`
at our three shapes); `L.tableEval q p` the multilinear extension at `p` of the table `Table::read`
reads back from the stack `q`. It is `opening_sound` (every valid layout at an admissible shape) at
our layouts.

**The gadget and the event.** A hidden layout's opening batches one more claim after the `m` claims,
with the power `λ^m`: the gadget, of value zero, a fixed weight on nine entries of the random first
pieces (`opening.rs:827-838`, `873-879`). In mumbai's terms it is one more stack claim
(`Layout.extra`), so the doom mumbai's specification starts from is "every candidate violates **a
claim or the gadget**" (`Layout.openingDoom_iff`). `OpeningDoomed` is still about the claims only:
every candidate's table violates a claim, which implies that doom (the proof of `family_sound`), so the
statement of `ours_sound` is unchanged by the redesign. What the gadget claim says of a stack is
`gadget_holds_iff`: `Σ_{g,i} β_i · Σ_{l ∈ pattern g} q[l][2^s − 9 + 3g + i] = 0`, patterns `{0, 31}`,
`{1, 30}`, `{32}`, `β = 1, t, t²` (a condition on the random first pieces, not on the table); an opening
that is not doomed has a candidate whose table satisfies every claim **and** which satisfies the gadget
(`Layout.joint_of_not_doom`). The batch has `m + 1` stack claims, so the lead `eBatch` is that of
`m + 1` (below; still under `2^-128`, statements carry at most `2^46 + 1` stack claims, the gadget
counted).

The pieces:

| Theorem | File | What |
|---|---|---|
| `Layout.check_eq` | `Opening.lean` | `Layout.check` (`opening::verify` past its transcript's start, both branches of the weight closure transcribed line by line, the gadget's term with the power `λ^m` after the claims') **is** mumbai's `verifyStackedOpening` of the claims' stack claims then the gadget's (`Layout.stacking`: claim weights `Layout.claimWeight`, extra stack claims `Layout.extra`), after the length check. |
| `isMultiaffine_layoutClaimWeight`, `isMultiaffine_gadgetWeight` | `Opening.lean` | Each claim's weight, public or hidden, and the gadget's are multiaffine on the stack's `log_n` coordinates (`stackedSpec`'s hypothesis). |
| `holds_iff_hidden`, `Layout.holds_iff` | `Hidden.lean` | A stack satisfies a claim's stack weight **iff the table read back from it** (`Layout.readHidden` = `Table::read`: the overflow lane's piece `k + 1` for the table's piece `pieces[k]`, the blocks' first pieces and the tails; a block's other pieces on its lane; for a public layout its blocks) has the claimed multilinear value, for every `Layout.Valid` layout. |
| `gadget_holds_iff`, `Layout.openingDoom_iff`, `Layout.joint_of_not_doom` | `Hidden.lean` | The gadget's stack claim holds iff its `β`-combination of the pattern lanes at its entries is zero; the doom in table terms (a claim or the gadget violated); joint extraction (every claim and the gadget). |
| `layouts_ok`, `layouts_valid`, `layouts_shape` | `Layouts.lean` | Our 18 layouts are admissible at rate `1/2` and valid (`HiddenOK 8` for witness and quotient, the gadget's entries in the first piece and its lanes among the layout's; a valid public stacking for wiring); `40`, `64`, `63` lanes, the overflow lane `32`, the random lanes `33..39`, the gadget's pair lanes `0, 31, 1, 30` blocks, `33` and `167` overflow pieces. Decided (`decide +kernel`). |
| `family_sound` | `Family.lean` | The theorem for mumbai's transcript shape and claims chosen by the adversary: the seeding `famSeed pre` (IV `H(pre ‖ claims)`, zero public digest, any fixed `pre`), the program `variantProg` reading the root from the proof, the event in stack terms at the proof's root (`FamDoomed`, the claims), for any stacking (claim weights and extra stack claims that are multiaffine). |
| `extracted_root_word` | `Variant.lean` | In an accepted run, the extracted history starts with the commitment of the root the proof's first two scalars encode, holding `extract` of it. |
| `openingVerify_imp` | `Verifier.lean` | **Acceptance by ours implies acceptance by the proven program**: if `opening::verify` accepts, the proof's first two scalars encode the expected root and `variantProg` from `famSeed (openingPrefix L R)` accepts. The empty-claims and root checks only reject more. |
| `romExperiment_le_of_reject` | `Verifier.lean` | So in the random-oracle experiment, ours accepting with the event is at most as likely as the proven verifier accepting with its event. |
| `opening_sound`, `opening_bound_le`, `ours_sound` | `Verifier.lean` | The theorem above, and the numbers. |
| `openingSpec`, `whirEps_le`, `eBatch_*`, `listMax_ours`, `candidates_ours` | `Sound.lean`, `Table.lean` | Round-by-round soundness of a stacking's opening from mumbai's `stackedSpec` with the deployed codes; the numbers. |
| `variant_sound` | `Variant.lean` | The fixed-statement version (a family of one). |

## The transcript

`opening::verify` (`opening.rs:782-892`), version 2 of the opening (`VERSION`, `opening.rs:48`):

* no claim, or a point of the wrong length, is rejected first (`opening.rs:792-794`);
* the IV is `keccak256(prefix ‖ claims)` (`iv`, `opening.rs:635-645`), `prefix` (`opening.rs:616-626`)
  76 bytes: `LABEL` `"pcs-quotient-opening"` (20), `VERSION = 2` (u64 LE), the layout's id
  (`layout_id`, Keccak-256 of every field of the layout and of the gadget, `encode_layout`, 32 bytes),
  `log_n` (u64 LE), `LOG_INV_RATE = 1` (u64 LE); the claims each point's coordinates then its value,
  three 8-byte limbs per scalar, no lengths (under one layout every claim is `24 (vars + 1)` bytes, the
  verifier checks the points' lengths first);
* the public digest is zero (`PUBLIC_DIGEST`): not a hash answer, as mumbai's `Seeds.refs` requires;
* the root is the proof's first two scalars, read (absorbed) and checked against the expected root
  before `λ` is sampled (`opening.rs:797-800`).

The Lean mirror (`openingPrefix`, `encodeLayout`, `gadgetBytes`, `layoutId`, `claimsBytes`,
`openingVerifyWithHash`) transcribes these. `famSeed pre` with `pre = openingPrefix L 1` is exactly this
IV and public digest, and mumbai's `commitStack` reads the root as the Rust does; the Rust's extra
comparison with the expected root is `openingVerify_imp`. The layout's id is a constant of the verifier
(Keccak-256 with the deployed function, not an oracle answer), so the theorem is about the verifier with
its 76-byte prefix fixed. The 18 prefixes are distinct (Check.lean; not needed by the theorem, which is
per layout).

## Building

The package builds against a built checkout of leanerVM placed at `../leanervm` (so `formal/leanervm`
here, gitignored), sharing `lean_vm`'s packages (`packagesDir`), so nothing is fetched or rebuilt:

```sh
git clone https://github.com/Verified-zkEVM/leanerVM ../leanervm
cd ../leanervm && git checkout 6175f1a07f0dc33bd3d640de0063d1006143ee91 && cd lean_vm
lake exe cache get && python3 -I ../lake-build.py . LeanVM     # several CPU-hours
cd ../../WhirBridge && lake build                                # about a minute
```

**The test vectors, one command each** (from the repository root; run again after any change of
`opening.rs` or of the layouts):

```sh
cargo test -p quotient --release --test whir_bridge_vector -- --ignored   # writes target/whir_bridge_vector.txt (5 s)
(cd formal/WhirBridge && lake env lean --run Test/Check.lean ../../target/whir_bridge_vector.txt)   # 1-2 min
```

`whir_bridge_vector.rs` writes three openings, each naming its layout by the constructor's arguments:
a public layout (two claims, lanes out of order and a gap, `placed` short of the stack), and the
**deployed witness and quotient layouts** at `2^17` rows by the real prover (one and two claims), then the
76-byte prefix of each of the 18 layouts the protocol opens. `Test/Check.lean` rebuilds each layout with
the Lean `Layout.new` / `Layout.hidden`, recomputes its prefix with mumbai's Keccak-256 and compares it
with the Rust's, accepts the honest proof, and rejects a wrong claimed value, a wrong expected root, a
changed stream scalar, a changed leaf word and an empty claim list; on the public layout also a wrong
prefix (the same layout with one more overflow piece, which only its id reads), and on the hidden ones
the honest proof against the weight **without the gadget's term** (so the gadget's transcription is what
WHIR's final check reads; on the public layout, which has no gadget, the same verifier accepts, the
control). It recomputes the 18 prefixes from the Lean `witnessLayout`, `wiringLayout`, `quotientLayout`
and checks they are distinct. It prints `all checks: true` and exits `0`. If the Rust layouts change, the
Lean `Layout.hidden` and `Layouts.lean` must be transcribed again (Check.lean fails until they are); the
theorems are stated for every `Layout.Valid` layout, so `layouts_valid` re-decides and nothing else
changes unless the weight's shape does (as it did for the gadget: one more stack claim).

On `h1` the bridge lives at `/root/pcs-quotient-fv/whir-bridge-gadget` (this version;
`whir-bridge-seed` holds the previous one, before the redesign) next to `/root/pcs-quotient-fv/leanervm`.
It needs only `lean_vm`'s protocol modules: `python3 -I ../lake-build.py . LeanVM.Protocol.Whir.Sound.Spec
LeanVM.Protocol.Whir.Params.Deployed LeanVM.Protocol.EndToEnd.Sound.Assemble LeanVM.Protocol.LeanVMSound`
builds them in about 6.5 minutes from mumbai's Mathlib cache.

## The Rust against mumbai's model

mumbai's `verifyWhir` (`Statement/LeanVmVerifier.lean:1505-1553`, a transcription of `verifier.py` at
`c445e3d5`) against the vendored `crates/verifier/src/whir.rs`, and `Layout.check` against
`crates/quotient/src/opening.rs`. The vendored `whir.rs`, `transcript.rs`, `merkle.rs`, `multilinear.rs`,
`field.rs` and `hash.rs` are byte-identical, past their two-line headers, to leanVM `c445e3d5`'s (checked
against a fetch of that commit, mumbai's `leanvm-tree.sh`), so what mumbai's fuzzing establishes of leanVM's
Rust verifier holds of ours.

* **Parameters.** `derive_config` (`whir.rs:34-60`) is `Whir.ladder` (`LeanVmVerifier.lean:110-161`): the
  same folds (6, then 4 or what remains while more than 5 variables remain), rate rule, window `15..28`,
  rates `1..4`; the query table `WHIR_QUERIES` (`whir.rs:20-25`) is `queryTable` (`:126`), checked equal
  entry by entry (56 rows). `QUERY_GRINDING_BITS = 17` is `queryGrindingBits`.
* **The level loop** (`whir.rs:154-269` / `whirLevels`, `:1505-1546`): the same operations in the same
  order. **No mismatch** in the WHIR verifier beyond these, none of which matters for soundness:
  - **`placed` and pruned paths.** The Rust level-0 rows carry `ceil(placed / 2^(log_n-6))` words, the rest
    of each 64-word leaf a zero prefix rebuilt by `PrunedMerklePaths::expand`; mumbai's `Proof` has one full
    path per query and no `placed`. The expansion checks the same roots, so it only restricts what is
    accepted; it is not formalised (mumbai says the same of leanVM: `Statement/LeanVm.lean:60`).
  - **A final level with no tail round** (`message_log = 0`): no ladder reaches it.
  - The Rust `eq_eval`/`dot` assert equal lengths where mumbai's truncate; every call site passes equal
    lengths.
* **The layout** (`opening.rs:51-301` / `Layout`, `Lane`): every field (`vars`, `log_n`, the lanes as
  `Block(b)` / `Overflow` / `Random`, `log_piece`, `pieces`; no share lane since the redesign), the
  gadget's constants (`GADGET`, `OVERFLOW_LANE`, `gadget_lanes`, `gadget_beta`, `gadget_entry`);
  `Layout::new` and `Layout::hidden_with` transcribed step by step (`Layout.new`, `Layout.hidden`: the
  whole blocks, the tails, the first `min(32, |blocks|)` blocks on lanes `0..32` and random lanes up to
  `32`, the overflow lane, the random lanes, the other blocks; the overflow pieces each block lane's first
  piece in lane order, then the tails). The Rust's assertions (`GADGET < 2^log_piece`, `random ≥ 7`, at
  most `64` lanes, fewer pieces than a lane's) are not transcribed: what the theorems need of them is
  `HiddenOK`, decided for our layouts.
* **The opening** (`opening.rs:782-892` / `openingVerifyWithHash`, `Layout.check`): the empty-claims and
  length check, the transcript's start, the root, `λ`, `λ_i = λ^i` for `i ≤ m` (`lambdas`, one power more
  than the claims, the gadget's), the target (`dot_lambdas`: the last power is not read by it), and the
  weight closure, **both branches**: the public one, `eq(p[..ℓ], low) · on_blocks`, and the hidden one,
  `below · ((above + first_above · first_piece) · on_blocks + pieces · on_overflow)` with the first-piece
  cancellation and the overflow lane's pieces (`Layout.term`, `opening.rs:850-872`), and the **gadget's
  term** `λ^m Σ_{g,i} β_i eq_index(low, D + 3g + i) Σ_{l ∈ pattern g} lane_eq[l]` (`gadgetSum`,
  `Layout.gadgetParts`, `opening.rs:873-879`). Its `F192` scales lifted by `ext` are the verifier's `E`:
  both fields are `K[y]/(y^3+y+1)`, `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` (`β_i` the limbs `E.ofLimbs`).
* **Executed**: the Lean mirror with the deployed Keccak accepts proofs of the Rust prover on a public
  layout and on the deployed witness and quotient layouts, rejects the hidden ones without the gadget's
  term, and recomputes the prefixes (so `LABEL`, the layout encoding and id with the gadget,
  `Layout.hidden`, the seed, `λ`, the target, both branches of the weight closure, the gadget and
  mumbai's `verifyWhir` agree with the Rust on them); test evidence, as mumbai's for leanVM.

## What covers us

**mumbai's `stackedSpec`** (`lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean:273`) is stated for **any** list of
stack claims `(w, v)` whose weights are multiaffine on the stack's `μ` coordinates. Its hypotheses and how
they are met:

| Hypothesis | Met by |
|---|---|
| `Whir.ladder μ R = some (level :: rest)`, `level.fold = 6`, `6 ≤ μ` | admissible `(μ, R)`: `15 ≤ μ ≤ 28`, `1 ≤ R ≤ 4`; ours `μ = log_rows + 2, +3, +6` (`19..24`, `20..25`, `23..28`), `R = 1`, for every `17 ≤ log_rows ≤ 22` (`layouts_ok`) |
| `(codes 0).κ = μ − 6`, `(codes 0).R = R`, `LadderArith`, `whirEps ≤ εmax` | the deployed codes, certified for all 56 shapes by kernel evaluation (`Params/Deployed.lean:179`, `shapeOK_all`) |
| every stack claim's weight multiaffine on `μ` coordinates | `isMultiaffine_layoutClaimWeight` (both branches), `isMultiaffine_gadgetWeight` (the gadget) |
| the doom `StackedPre`: the level-0 commitment has the stack's shape and every candidate of its word violates a stack claim | `Layout.openingDoom_iff`: every candidate's **table** (`Table::read`) violates a claim (`Layout.holds_iff`) or the candidate violates the gadget (`gadget_holds_iff`); the event of `ours_sound` (a claim violated) implies it |

`openingSpec` packages it for a stacking's opening; `family_sound` composes it into mumbai's `romSound`
(`Compile/Rom/Sound.lean:196`) for claims the adversary chooses; `opening_sound` moves it to
`opening::verify` itself.

## Errors at our sizes (rate 1/2)

| | witness | wiring | quotient |
|---|---|---|---|
| table variables / `log_n` / lanes (at `LOG_ROWS = 22`) | 25 / 25 / 40 (hidden) | 24 / 24 / 64 (public) | 30 / 28 / 63 (hidden) |
| WHIR levels, queries | 5: 224, 56, 32, 23, 17 | 5: 224, 56, 32, 23, 17 | 6: 225, 56, 32, 23, 18, 14 |
| per-group escape `εmax` (every group after `λ`, discounted by its proof of work) | `2^-128` | `2^-128` | `2^-128` |
| stack claims batched (`J`) | 2 (one claim, the gadget) | 1 (one claim) | 3 (two claims, the gadget) |
| batching challenge `λ` (the lead, `(J−1)·L₀/2^192`) | `≤ 2^-174` (`eBatch_two`; `≤ 7908/2^192 ≈ 2^-179.0` with the shape's own list bound) | `0` (`eBatch_one`) | `≤ 2^-173` (`eBatch_three`; `≤ 2·3564/2^192 ≈ 2^-179.2`) |
| level-0 Johnson list `L₀` (candidates per root, `candidates_ours`) | `≤ 7908` | `≤ 9952` | `≤ 3564` |
| weakest group, bits (leanerVM's certificate, evaluated in `Float`) | 128.96 (level 0, queries) | 128.97 (level 0, queries) | 128.98 (level 1, queries) |

The WHIR numbers depend on `log_n` only, so hiding the witness and quotient tables changed none of them;
the gadget adds one stack claim to their batches, which moves the lead (below `2^-173`) and nothing else.
The `2^-128` is mumbai's certificate (`whirEps (deployedCodes μ R) config ≤ 2^-128`): at our three shapes
it certifies at `2^-128` and not at `2^-129` (`shapeOK 129 μ 1 = false`, evaluated), the query counts
being tuned to it. **These are leanerVM's certified codes, not `whir_config.rs`'s**: the level-0 slack is
`η = e/2^22` with `e = 298, 375, 832` at `log_n = 24, 25, 28` (`Params/Deployed.lean`, `certTable`), which
gives the lists `9952, 7908, 3564`. `whir_config.rs`'s own slack search (lists 323 and 216) omits the fold
group's row-union factor `2^(ℓ−1)` (32 at level 0) that leanerVM's proved fold bound carries
(`(2·L + 2^(ℓ−1)·E)/|E|`, `eFold`); under the proved bound only leanerVM's slacks make the deployed query
counts reach `2^-128`. Every group of our three shapes, with those slacks, in bits (the certificate's
`Nat` bounds, `listHi`, `excHi`, `thrHi`, read as floats: an evaluation, the theorem being `≥ 128`):

| `log_n` | level: fold / out-of-domain / queries (after 17 bits of grinding) |
|---|---|
| 24 | 0: 128.97 / 155.0 / 128.97; 1: 129.02 / 150.6 / 129.00; 2: 129.06 / 148.5 / 129.02; 3: 132.27 / 143.3 / 132.26; 4 (final): 131.21 / — / 131.07 |
| 25 | 0: 128.97 / 155.6 / 128.96; 1: 129.02 / 151.1 / 128.99; 2: 129.03 / 148.9 / 129.00; 3: 132.17 / 142.8 / 132.11; 4 (final): 129.34 / — / 129.15 |
| 28 | 0: 129.41 / 157.4 / 129.41; 1: 128.98 / 152.9 / 128.98; 2: 129.00 / 150.5 / 128.99; 3: 131.98 / 147.7 / 131.98; 4: 134.14 / 141.8 / 134.13; 5 (final): 131.95 / — / 131.86 |

The tail rounds escape at `2/2^192` each. In the random-oracle model the per-group `2^-128` and the
collision term give `opening_sound`'s `(QA + 10122) · (2^-128 + 5 (QA + 10122)/2^256)`, about
`QA · 2^-128`, at most `2^-63` for `QA ≤ 2^64`; `10122` bounds the verifier's queries over every
admissible shape (the IV's hash, the seed's permutation, mumbai's `whirBound`), `5` is mumbai's
`failBound` for a seeding with no embedded answers.

## What the bridge exports to the composition

* **The list bound**: `candidates_ours`: for every word, the candidates the doom quantifies over (the stacks
  agreeing with the root's word on level 0's Johnson threshold of the **certified** code) number at most
  **9952** (`log_n = 24`), **7908** (`25`), **3564** (`28`); `candidates_count` gives `≤ listMax` at any
  admissible shape, and mumbai's global bound is `2^18`. A reduction drawing challenges before any claim
  pins a list member union-bounds over these.
* **One opening per root**: the guarantee is joint only within one opening. An opening that is not doomed
  has **one** candidate whose table satisfies **all** its claims (and which satisfies the gadget,
  `Layout.joint_of_not_doom`); claims on one root split over two openings would get one list member each,
  possibly different (a split opening of the quotient table's two claims is forgeable, about `2^111` by
  the review's count). So every statement here is about one opening holding all the claims on its root, as
  `protocol::verify_openings` does.
* **Table terms**: the candidates are tables as `Table::read` reads them back (the hidden layouts: the
  overflow lane at the held pieces, the blocks' other pieces on their lanes, the random first pieces left
  out), so the composition's claims are on the tables the protocol commits to.

## Public layouts at `2^24 ..= 2^28` (a univariate leanVM PIOP)

`WhirBridge/Large*.lean` (imported by `WhirBridge.lean`, axioms checked in `WhirBridge/Large.lean`) extend the
bridge to the commitments of a univariate leanVM PIOP: **public** stacks (no hiding) of `2^24 ..= 2^28` words,
any shape `Layout::new` accepts, rate `1/2`. Nothing above changes; the new theorems are corollaries of
`opening_sound` (and of `family_sound`'s proof, with the query count a parameter).

| Theorem | File | What |
|---|---|---|
| `admissible_large`, `ladder_large`, `residual_large`, `grinding_large` | `LargeParams.lean` | `(μ, 1)` admissible for `24 ≤ μ ≤ 28`; `Whir.ladder μ 1 = some (largeLadder μ)` (decided); residuals `2, 3, 4, 5, 2`; `17` bits of grinding |
| `shapeOK_large` | `LargeParams.lean` | the certified codes check at `2^-128` per group and **not** at `2^-129`, at each of the five shapes (decided) |
| `listHi_large`, `listMax_large`, `candidates_large` | `LargeParams.lean` | level 0's Johnson list `L₀ = largeList μ`: **9952, 7908, 6296, 4473, 3564** |
| `largeQueries_eq`, `isTotalQueryBound_large` | `LargeParams.lean` | `ourVerifier` makes at most **`QO = 7183, 7546, 7928, 8318, 9018`** queries (mumbai's cost calculus at the commitments' height `μ − 5`; `≤ 10122`, `largeQueries_le`) |
| `NewOK`, `Layout.new_valid` | `LargeLayout.lean` | **every** `Layout.new vars log_chunk log_n chunks` whose `(table, height)` chunks pass `Layout::new`'s assertions (`NewOK`: `ℓ ≤ log_chunk ≤ vars`, chunk indices `< 2^(vars − log_chunk)`, heights `≤ 2^log_chunk`, `Σ ⌈height/2^ℓ⌉ ≤ 64`; decidable on the chunks' numbers) is `Layout.Valid`: one generic proof (`mem_newBlocks`, `newBlocks_lt`, `newBlocks_length`), no lane enumerated |
| `newBlocks_nodup`, `Blocks.table_eq_lane`, `Blocks.table_eq_zero`, `mem_newBlocks_iff`, `Layout.new_table_eq_zero` | `LargeLayout.lean` | distinct chunks give distinct blocks; the table read back is the stack's lanes on each listed chunk's first `⌈height/2^ℓ⌉` lanes, **zero elsewhere** (a chunk's entries past its height inside its last lane are read back from the stack, not forced to zero) |
| `ours_sound_public`, `ours_sound_public_le`, `ours_sound_public_layout` | `LargeSound.lean` | `opening::verify` on such a layout with `24 ≤ log_n ≤ 28`: accepting while every candidate table of the root's word violates a claim has probability at most `openingBound QA = (QA + 10122)(2^-128 + 5(QA + 10122)/2^256) ≤ 2^-63` (`QA ≤ 2^64`); the same for any public layout whose blocks are a valid stacking |
| `ours_sound_public_at` (`family_sound_q`, `opening_sound_q`) | `LargeSound.lean` | the same with the shape's `QO`: `openingBoundAt QO QA` |
| `joint_public_large` | `LargeSound.lean` | an opening not doomed has a candidate, among at most `L₀`, whose table satisfies **all** its claims |
| `exampleChunks_ok`, `example_sound` | `LargeSound.lean` | how a fixed shape is covered: `NewOK` by `decide +kernel` (43 lanes of a `2^28` stack), then the theorem |
| `eBatch_large`, `eBatch_large_le` | `LargeMargins.lean` | one opening's batching lead `(J − 1)·L₀/2^192`, `≤ 2^-164` for `J ≤ 2^14` claims |
| `ncard_bad_pairs_le`, `ncard_bad_candidates_le` | `LargeMargins.lean` | the union bound after two roots as a count: `≤ L₁ L₂ · d` bad challenges |
| `union_one_root_le`, `union_two_roots_le`, `union_three_roots_le`, `largeList_pairs` | `LargeMargins.lean` | `L₁ d/2^192 ≤ 2^-(178−k)`, `L₁L₂ d/2^192 ≤ 2^-(165−k)`, `L₁L₂L₃ d/2^192 ≤ 2^-(152−k)` for `d ≤ 2^k`; `L₁L₂ ∈ [3564², 9952²] = [2^23.60, 2^26.56]` |

**The parameters** (rate `1/2`; queries per level after `17` bits of grinding; `L₀` the certified level-0 list;
the weakest group of the certificate, its `Nat` bounds read as bits by `review/whir_params.py --large`, which
computes them exactly as `Params/Check.lean` does and reproduces the table of the previous section at `24`,
`25`, `28`):

| `log_n` | folds | queries | residual | `L₀` | `QO` | weakest group | after root 1 / roots 1, 2 (worst partner `2^24`) |
|---|---|---|---|---|---|---|---|
| 24 | 6, 4, 4, 4, 4 | 224, 56, 32, 23, 17 | 2 | 9952 (`2^13.28`) | 7183 | 128.97 (level 0) | 178.72 / 165.44 |
| 25 | 6, 4, 4, 4, 4 | 224, 56, 32, 23, 17 | 3 | 7908 (`2^12.95`) | 7546 | 128.96 (level 0) | 179.05 / 165.77 |
| 26 | 6, 4, 4, 4, 4 | 224, 56, 32, 23, 18 | 4 | 6296 (`2^12.62`) | 7928 | 128.95 (level 0) | 179.38 / 166.10 |
| 27 | 6, 4, 4, 4, 4 | 225, 56, 32, 23, 18 | 5 | 4473 (`2^12.13`) | 8318 | 128.99 (levels 1, 2) | 179.87 / 166.59 |
| 28 | 6, 4, 4, 4, 4, 4 | 225, 56, 32, 23, 18, 14 | 2 | 3564 (`2^11.80`) | 9018 | 128.98 (level 1) | 180.20 / 166.92 |

The rate exponents are `1, 4, 7, 10, 13 (, 16)`; level 0 takes no out-of-domain sample, every later level one.
The last column is `192 − log2 L₁` and `192 − log2 (L₁ L₂)`: what is left, after the union over the lists,
for a challenge's own error (a degree-`2^k` identity keeps `165.44 − k` bits after two roots of `2^24`;
`union_two_roots_le` proves `165 − k`; three roots of `2^24` leave `152.16 − k`).

**Against the Rust** (on h1): `cargo test --release -p quotient --test whir_large_params` checks that the
prover's configuration (`pcs::whir::config_for_rate`, `whir_config.rs`'s eta search), the verifier's
`WHIR_QUERIES` (read from `crates/verifier/src/whir.rs`) and its ladder rule equal `largeLadder` level by level
(folds, rates, queries, grinding `17`, out-of-domain samples `0, 1, 1, ...`, residual), and prints the code's own
level-0 lists (`323, 323, 323, 216, 216`: its search omits the fold group's row-union factor, so it is not the
certified accounting). The ignored `large_public_openings` (`WHIR_LARGE_MAX=28`) commits and opens, with the
real prover, a PIOP-like public layout at each size (`32` chunks of heights `2^(ℓ+1)`, `2^ℓ + 5`, `2^ℓ/3`, `1`,
out of order with gaps: `62` lanes), verifies it in Rust, rejects a wrong value, and writes the openings;
`lake env lean --run Test/CheckLarge.lean ../../target/whir_large_vector.txt` rebuilds each layout with the
Lean `Layout.new`, evaluates `NewOK` on it, recomputes its prefix, accepts the honest proof with the Lean
verifier and rejects a wrong value, a wrong root, a changed stream scalar, a changed leaf word, no claim and a
wrong prefix.

What this does not cover, beyond the gaps below: the PIOP's own layouts are not fixed yet (any one is covered
once its `NewOK` is decided); `Layout::new` = `Layout.new` is checked by execution (`Check.lean`,
`CheckLarge.lean`), not proved; the composition with the PIOP's reduction (the union over the lists,
`LargeMargins.lean` gives the counting and the numbers) is the PIOP's.

## Assumptions

Keccak-256 and Keccak-f[1600] are independent random oracles (mumbai's two-oracle model; leanVM's own
theorem then moves to one random permutation). The adversary is classical and its code is fixed before
the oracles are sampled. The layout's id inside the prefix is computed with the deployed Keccak-256 (a
constant of the verifier). Statements carry at most `2^46 + 1` stack claims, a hidden layout's gadget
counted (`Stmt.short`; the protocol opens one or two claims per root). The Rust verifier is the Lean
mirror (test evidence, not proof), and the pruned paths expand as `expand` says (not formalised).
Extraction is mumbai's straight-line `extract` (the word a root commits to, read off the oracle's
answers) and Guruswami–Sudan list decoding of the level-0 word (`Statement/Extractor.lean`): the
extractor returns the list, its running time read off its loops.

## Gaps

What mumbai's proofs and this package do not cover of our openings (`Gaps.lean`):

1. **The model**: two random oracles, not leanVM's one random permutation (mumbai's `LeanVMRpm.lean`, at
   `q²/2^508`); the prefix's layout id a constant; at most `2^46 + 1` stack claims.
2. **The Rust is the model**: the transcriptions of `opening.rs` (`Layout`, `Layout::new`,
   `Layout::hidden_with`, `Table::read`, `prefix`, `encode_layout`, `verify` with its gadget), of
   `protocol.rs`'s layouts and mumbai's of the Python verifier are checked by execution
   (`Test/Check.lean`), not proved equal to the Rust. A further redesign of the hidden layout must be
   transcribed again; the theorems need only `Layout.Valid` and multiaffine weights.
3. **Pruned paths and `placed`**, not formalised (they only restrict what is accepted).
4. **List decoding, no out-of-domain sample at level 0**: an accepted opening yields a candidate among
   the up to `L₀` tables of the root's Johnson list satisfying all its claims jointly, not a unique table:
   the reduction's soundness must hold for each of the `L₀ ≤ 2^13.3` candidates fixed by each root
   (`candidates_ours`), a union bound, and claims on one root must not be split over openings.
5. **Composition of the three transcripts with the reduction's**: the reduction must read the words
   extracted when each root entered its transcript (mumbai's `extract_take_eq`).
6. **Extraction from the adversary's queries only**: the extracted word is read off the final cache (the
   verifier's answers included), as in mumbai's `romSound`; mumbai's further step for leanVM
   (`Sound.extractor_of_extracted`, `LeanVMSound.lean`, at `Q_V/2^256`) is not taken here.
7. **Hiding** (zero knowledge of the openings) is layer F3 of `formal/README.md`.

## Build on h1

leanerVM `6175f1a0` cloned at `/root/pcs-quotient-fv/leanervm`, built with `run-build.sh` there (10 jobs within
36 GB, the machine shared): `lake exe cache get` (1 min 26 s), then `lake-build.py` of the WHIR and soundness
modules, **931 modules in 6 min 30 s** (0.97 CPU-hours), then the whole `LeanVM` target, **3920 modules in
1 h 52 min** (14.66 CPU-hours). The bridge (`/root/pcs-quotient-fv/whir-bridge-gadget`, 10 modules) builds from
a clean `.lake` in 1 min 19 s on the shared machine (`Layouts.lean`'s kernel decisions of the 18 layouts
28 s of it); the vectors are written in 5 s and `Test/Check.lean` runs in 1 min 54 s (`all checks: true`;
it now also runs every opening against the weight without the gadget's term).

The `Large*` files were built at `/root/pcs-quotient-fv/whir-large` (a copy of `whir-bridge-gadget`, the same
`../leanervm`): the five modules build in about 20 s (their kernel decisions, `shapeOK` at `128` and `129` for
the five shapes included, a few seconds each); `Review/WhirBridgeAxioms.lean` sweeps 676 declarations, none
outside the three axioms, no opaque, axiom or `implemented_by` constant. The Rust check is in the same directory
(`rust/`, the workspace without `formal/`).
