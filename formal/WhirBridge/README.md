<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# WhirBridge: our WHIR openings under leanerVM `mumbai`'s proofs

`crates/quotient/src/opening.rs` opens every claim on a committed table with leanVM's WHIR, unchanged.
[leanerVM](https://github.com/Verified-zkEVM/leanerVM) `mumbai` (commit `6175f1a0`, MIT OR Apache-2.0;
its `leanvm-rev` is leanVM `c445e3d5`, the commit our `crates/verifier` is vendored from) proves leanVM's
verifier knowledge sound. This package transcribes `opening::verify` into mumbai's verifier language,
**its transcript included**, and proves its Fiat–Shamir soundness in the random-oracle model for the
three openings the protocol makes (the wiring table's, public; the witness and quotient tables',
hidden), at every supported size, in table terms. Everything here is sorry-free and depends on
`propext`, `Classical.choice` and `Quot.sound` only (`#guard_msgs` checks in `WhirBridge.lean`; the
review's sweep `formal/Review/WhirBridgeAxioms.lean`: 556 declarations, no other axiom, no `opaque`,
no `implemented_by`). No `native_decide`: the facts about our layouts are `decide +kernel`.

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
Lean `opening::verify`; `extract` is mumbai's straight-line extraction of the word a root commits to
from the oracle's answers; `Candidates` the stacks within level 0's Johnson radius of it (at most
`9952`, `7908`, `3564` at our three shapes); `L.tableEval q p` the multilinear extension at `p` of the
table `Table::read` reads back from the stack `q`. It is `opening_sound` (every valid layout at an
admissible shape) at our layouts. The pieces:

| Theorem | File | What |
|---|---|---|
| `Layout.check_eq` | `Opening.lean` | `Layout.check` (`opening::verify` past its transcript's start, both branches of the weight closure transcribed line by line) **is** mumbai's `verifyStackedOpening` of the claims' stack claims, after the length check. |
| `isMultiaffine_layoutClaimWeight` | `Opening.lean` | Each claim's weight, public or hidden, is multiaffine on the stack's `log_n` coordinates (`stackedSpec`'s hypothesis). |
| `holds_iff_hidden`, `Layout.holds_iff` | `Hidden.lean` | A stack satisfies a claim's stack weight **iff the table read back from it** (`Layout.readHidden` = `Table::read`: the overflow and share lanes summed at the held pieces, the odd lanes' pieces swapped, the first pieces left out; for a public layout its blocks) has the claimed multilinear value, for every `Layout.Valid` layout. |
| `layouts_ok`, `layouts_valid`, `layouts_shape` | `Layouts.lean` | Our 18 layouts are admissible at rate `1/2` and valid (`HiddenOK 8` for witness and quotient, a valid public stacking for wiring); `40`, `64`, `63` lanes, overflow/share `38, 39` and `61, 62`, `33` and `167` pieces. Decided (`decide +kernel`, 30 s). |
| `family_sound` | `Family.lean` | The theorem for mumbai's transcript shape and claims chosen by the adversary: the seeding `famSeed pre` (IV `H(pre ‖ claims)`, zero public digest, any fixed `pre`), the program `variantProg` reading the root from the proof, the event in stack terms at the proof's root (`FamDoomed`), for any stacking (a claim weight that is multiaffine). |
| `extracted_root_word` | `Variant.lean` | In an accepted run, the extracted history starts with the commitment of the root the proof's first two scalars encode, holding `extract` of it. |
| `openingVerify_imp` | `Verifier.lean` | **Acceptance by ours implies acceptance by the proven program**: if `opening::verify` accepts, the proof's first two scalars encode the expected root and `variantProg` from `famSeed (openingPrefix L R)` accepts. The root check only rejects more. |
| `romExperiment_le_of_reject` | `Verifier.lean` | So in the random-oracle experiment, ours accepting with the event is at most as likely as the proven verifier accepting with its event. |
| `opening_sound`, `opening_bound_le`, `ours_sound` | `Verifier.lean` | The theorem above, and the numbers. |
| `openingSpec`, `whirEps_le`, `eBatch_*`, `listMax_ours`, `candidates_ours` | `Sound.lean`, `Table.lean` | Round-by-round soundness of a stacking's opening from mumbai's `stackedSpec` with the deployed codes; the numbers. |
| `variant_sound` | `Variant.lean` | The fixed-statement version (a family of one). |

## The transcript

`opening::verify` (`opening.rs:728-819`), version 2 of the opening (`VERSION`, `opening.rs:45`):

* the IV is `keccak256(prefix ‖ claims)` (`iv`, `opening.rs:592-602`), `prefix` (`opening.rs:573-584`)
  76 bytes: `LABEL` `"pcs-quotient-opening"` (20), `VERSION = 2` (u64 LE), the layout's id
  (`layout_id`, Keccak-256 of every field of the layout, `encode_layout`, 32 bytes), `log_n` (u64 LE),
  `LOG_INV_RATE = 1` (u64 LE); the claims each point's coordinates then its value, three 8-byte limbs
  per scalar, no lengths (under one layout every claim is `24 (vars + 1)` bytes, the verifier checks the
  points' lengths first);
* the public digest is zero (`PUBLIC_DIGEST`): not a hash answer, as mumbai's `Seeds.refs` requires;
* the root is the proof's first two scalars, read (absorbed) and checked against the expected root
  before `λ` is sampled (`opening.rs:742-745`).

The Lean mirror (`openingPrefix`, `encodeLayout`, `layoutId`, `claimsBytes`, `openingVerifyWithHash`)
transcribes these. `famSeed pre` with `pre = openingPrefix L 1` is exactly this IV and public digest, and
mumbai's `commitStack` reads the root as the Rust does; the Rust's extra comparison with the expected
root is `openingVerify_imp`. The layout's id is a constant of the verifier (Keccak-256 with the deployed
function, not an oracle answer), so the theorem is about the verifier with its 76-byte prefix fixed. The
18 prefixes are distinct (Check.lean; not needed by the theorem, which is per layout).

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
`opening.rs` or of the layouts, e.g. the hidden layout's redesign for condition (R)):

```sh
cargo test -p quotient --release --test whir_bridge_vector -- --ignored   # writes target/whir_bridge_vector.txt (5 s)
(cd formal/WhirBridge && lake env lean --run Test/Check.lean ../../target/whir_bridge_vector.txt)   # 33 s
```

`whir_bridge_vector.rs` writes three openings, each naming its layout by the constructor's arguments:
a public layout (two claims, lanes out of order and a gap, `placed` short of the stack), and the
**deployed witness and quotient layouts** at `2^17` rows by the real prover (one and two claims), then the
76-byte prefix of each of the 18 layouts the protocol opens. `Test/Check.lean` rebuilds each layout with
the Lean `Layout.new` / `Layout.hidden`, recomputes its prefix with mumbai's Keccak-256 and compares it
with the Rust's, accepts the honest proof, and rejects a wrong claimed value, a wrong expected root, a
changed stream scalar and a changed leaf word (and, on the public layout, a wrong prefix: the same layout
with one more overflow piece, which only its id reads); it recomputes the 18 prefixes from the Lean
`witnessLayout`, `wiringLayout`, `quotientLayout` and checks they are distinct. It prints
`all checks: true` and exits `0`. If the Rust layouts change, the Lean `Layout.hidden` and
`Layouts.lean` must be transcribed again (Check.lean fails until they are); the theorems are stated for
every `Layout.Valid` layout, so `layouts_valid` re-decides and nothing else changes unless the weight's
shape does.

On `h1` the bridge lives at `/root/pcs-quotient-fv/whir-bridge-seed` (this version; `whir-bridge` holds
the previous one) next to `/root/pcs-quotient-fv/leanervm`. It needs only `lean_vm`'s protocol modules:
`python3 -I ../lake-build.py . LeanVM.Protocol.Whir.Sound.Spec LeanVM.Protocol.Whir.Params.Deployed
LeanVM.Protocol.EndToEnd.Sound.Assemble LeanVM.Protocol.LeanVMSound` builds them in about 6.5 minutes from
mumbai's Mathlib cache.

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
* **The layout** (`opening.rs:61-243` / `Layout`, `Lane`): every field (`vars`, `log_n`, the lanes as
  `Block(b)` / `Overflow` / `Random`, `log_piece`, `pieces`, `share`); `Layout::new` and `Layout::hidden_with`
  transcribed step by step (`Layout.new`, `Layout.hidden`: the whole blocks, the tails, the random lanes'
  slots, the blocks filling the free lanes, the given-up pieces).
* **The opening** (`opening.rs:728-819` / `openingVerifyWithHash`, `Layout.check`): the length check, the
  transcript's start, the root, `λ`, `λ_i = λ^i` (the Rust builds one power for no claim, never read:
  `dot_lambdas`), the target, and the weight closure, **both branches**: the public one,
  `eq(p[..ℓ], low) · (on(0) + on(1))`, and the hidden one, `below · (even · on(0) + odd · on(1) + pieces ·
  on_overflow)` with the first-piece cancellation, the odd lanes' flip of coordinate `s` and the overflow
  and share lanes' pieces (`Layout.term`, `opening.rs:777-807`). Its `F192` scales lifted by `ext` are the
  verifier's `E`: both fields are `K[y]/(y^3+y+1)`, `K = GF(2)[x]/(x^64+x^4+x^3+x+1)`.
* **Executed**: the Lean mirror with the deployed Keccak accepts proofs of the Rust prover on a public
  layout and on the deployed witness and quotient layouts, and recomputes the prefixes (so `LABEL`, the
  layout encoding and id, `Layout.hidden`, the seed, `λ`, the target, both branches of the weight closure
  and mumbai's `verifyWhir` agree with the Rust on them); test evidence, as mumbai's for leanVM.

## What covers us

**mumbai's `stackedSpec`** (`lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean:273`) is stated for **any** list of
stack claims `(w, v)` whose weights are multiaffine on the stack's `μ` coordinates. Its hypotheses and how
they are met:

| Hypothesis | Met by |
|---|---|
| `Whir.ladder μ R = some (level :: rest)`, `level.fold = 6`, `6 ≤ μ` | admissible `(μ, R)`: `15 ≤ μ ≤ 28`, `1 ≤ R ≤ 4`; ours `μ = log_rows + 2, +3, +6` (`19..24`, `20..25`, `23..28`), `R = 1`, for every `17 ≤ log_rows ≤ 22` (`layouts_ok`) |
| `(codes 0).κ = μ − 6`, `(codes 0).R = R`, `LadderArith`, `whirEps ≤ εmax` | the deployed codes, certified for all 56 shapes by kernel evaluation (`Params/Deployed.lean:179`, `shapeOK_all`) |
| every claim's weight multiaffine on `μ` coordinates | `isMultiaffine_layoutClaimWeight`, both branches |
| the doom `StackedPre`: the level-0 commitment has the stack's shape and every candidate of its word violates a claim | `Layout.openingDoom_iff`: every candidate's **table** (`Table::read`) violates a claim (`Layout.holds_iff`) |

`openingSpec` packages it for a stacking's opening; `family_sound` composes it into mumbai's `romSound`
(`Compile/Rom/Sound.lean:196`) for claims the adversary chooses; `opening_sound` moves it to
`opening::verify` itself.

## Errors at our sizes (rate 1/2)

| | witness | wiring | quotient |
|---|---|---|---|
| table variables / `log_n` / lanes (at `LOG_ROWS = 22`) | 25 / 25 / 40 (hidden) | 24 / 24 / 64 (public) | 30 / 28 / 63 (hidden) |
| WHIR levels, queries | 5: 224, 56, 32, 23, 17 | 5: 224, 56, 32, 23, 17 | 6: 225, 56, 32, 23, 18, 14 |
| per-group escape `εmax` (every group after `λ`, discounted by its proof of work) | `2^-128` | `2^-128` | `2^-128` |
| batching challenge `λ` (the lead, `(J−1)·L₀/2^192`) | `0` (one claim) | `0` (one claim) | `≤ 2^-174` (two claims; `≤ 3564/2^192 ≈ 2^-180.2` with the shape's own list bound) |
| level-0 Johnson list `L₀` (candidates per root, `candidates_ours`) | `≤ 7908` | `≤ 9952` | `≤ 3564` |
| weakest group, bits (leanerVM's certificate, evaluated in `Float`) | 128.96 (level 0, queries) | 128.97 (level 0, queries) | 128.98 (level 1, queries) |

The WHIR numbers depend on `log_n` only, so hiding the witness and quotient tables changed none of them.
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
  has **one** candidate whose table satisfies **all** its claims (`Layout.joint_of_not_doom`); claims on one
  root split over two openings would get one list member each, possibly different (a split opening of the
  quotient table's two claims is forgeable, about `2^111` by the review's count). So every statement here
  is about one opening holding all the claims on its root, as `protocol::verify_openings` does.
* **Table terms**: the candidates are tables as `Table::read` reads them back (the hidden layouts: the
  overflow and share lanes summed at the held pieces, the odd lanes' pieces swapped, the random first
  pieces left out), so the composition's claims are on the tables the protocol commits to.

## Assumptions

Keccak-256 and Keccak-f[1600] are independent random oracles (mumbai's two-oracle model; leanVM's own
theorem then moves to one random permutation). The adversary is classical and its code is fixed before
the oracles are sampled. The layout's id inside the prefix is computed with the deployed Keccak-256 (a
constant of the verifier). Statements carry at most `2^46 + 1` claims (`Stmt.short`; the protocol opens
one or two per root). The Rust verifier is the Lean mirror (test evidence, not proof), and the pruned paths
expand as `expand` says (not formalised). Extraction is mumbai's straight-line `extract` (the word a root
commits to, read off the oracle's answers) and Guruswami–Sudan list decoding of the level-0 word
(`Statement/Extractor.lean`): the extractor returns the list, its running time read off its loops.

## Gaps

What mumbai's proofs and this package do not cover of our openings (`Gaps.lean`):

1. **The model**: two random oracles, not leanVM's one random permutation (mumbai's `LeanVMRpm.lean`, at
   `q²/2^508`); the prefix's layout id a constant; at most `2^46 + 1` claims.
2. **The Rust is the model**: the transcriptions of `opening.rs` (`Layout`, `Layout::new`,
   `Layout::hidden_with`, `prefix`, `encode_layout`, `verify`), of `protocol.rs`'s layouts and mumbai's of
   the Python verifier are checked by execution (`Test/Check.lean`), not proved equal to the Rust. A
   redesign of the hidden layout must be transcribed again; the theorems need only `Layout.Valid`.
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
1 h 52 min** (14.66 CPU-hours). The bridge (`/root/pcs-quotient-fv/whir-bridge-seed`, 10 modules) builds from
a clean `.lake` in 57 s, of which `Layouts.lean`'s kernel decisions of the 18 layouts take 30 s; the
vectors are written in 5 s and `Test/Check.lean` runs in 33 s (`all checks: true`).
