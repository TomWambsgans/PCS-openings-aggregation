<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The structure follows formal/UniStatement/README.md. -->

# RecStatement

The recursion's outer proof π2 (`crates/leanvm_rec`, `PI2.md` §2, §8–§9; branch `leanvm-rec` @ 2b22581, the final
protocol: the setup committed as `κ` and `κ + σ`, `ξ = κ(t) + βσ(t)` sent, no `h(t)`, the zero checks as an aligned
coset of ports in closed form `β^15/F(Y)`, the row fold's siblings, the normalised `Q` claim
`(1 + ρ')h + ρ'q = X/(S_d Y)`, one inversion, every `PCS_OPEN` call in `machine.rs`'s one ABI, π1's claims at points the
contract derives from π1-rec3's 14 narrow pair challenges), in the files a reviewer reads:

* **π2's verifier as computable Lean**, step by step as `pi2/verifier.rs` and the contract's order;
* the circuit's tables as **data the Rust emits** (`Data.lean`, with a staleness test; never `σ`);
* the **differential test** against the Rust (the real π1-rec3 + π2 proof and 63 other streams);
* the **verifier-arithmetic lemmas** that `RecPiop`'s rounds and copy argument consume, proved;
* the **end statements** of the whole recursive verifier, `RecKnowledgeSoundness` and `RecCompleteness`, against leanVM
  42422001's relation (`Lv42.Protocol.M3Holds`), stated, not proved.

No `sorry`, no `native_decide`, every headline definition and theorem on Lean's three axioms (`RecStatement.lean`'s
`#guard_msgs`). It is a library of `formal/EndToEnd` (`RecStatement`, `srcDir = "../RecStatement"`, `warningAsError`),
as `UniStatement` is, whose definitions it reuses (the channel, `E`, the layout words of π1, π1-rec3's contract IV, the
extractor's pieces).

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=10G lake build RecStatement            # the library; the axiom guards
# the data and the vectors (from the repository root, on h1; ~14 s, 11.6 GB: the real circuit compiled, its setup
# committed, π2's prover on π1-rec3's real witness):
UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_statement -- --ignored statement_data_is_current
REC_STATEMENT_OUT=$PWD/rec_statement_vectors.txt \
  cargo test --release -p leanvm_rec --test lean_statement -- --ignored --nocapture lean_statement_vectors
REC_STATEMENT_VECTORS=$PWD/rec_statement_vectors.txt lake env lean ../RecStatement/RecStatementTest/Runner.lean
```
(`RUSTFLAGS="-C target-cpu=native"` for the Rust; without `UPDATE_LEAN` the first command fails when `Data.lean` is
stale.)

## Reading order

1. [`Basic.lean`](RecStatement/Basic.lean): the circuit as the verifier reads it (`Coeff`, `Lin`, `Formula`, `Pair`,
   `Read`, `PublicTerm`, `Circuit`) and π1's call words (`CallWord`).
2. [`Data.lean`](RecStatement/Data.lean) (generated): π2's circuit for π1-rec3's real proof, D16v: `2^24` positions,
   rows of 16, 55 formulas, 156 pairs (4 pull-less) in 66 groups, 19 reads, 36 public terms (16 the zero coset); π1's
   contract IV, the setup's root, the circuit's digest; π1's three calls.
3. [`Core.lean`](RecStatement/Core.lean): **the arithmetic at `t`, over any field** (`CoreSpec.run`), every
   intermediate value a field of `Out`.
4. [`Spec.lean`](RecStatement/Spec.lean): `Spec::of` (the blocks' constants in `K`, the groups, the zero coset, the
   highest power of `γ`, the walk).
5. [`Verifier.lean`](RecStatement/Verifier.lean): the norm's inverse, the extension, `Spec.core` (the constants over
   `E`), the layouts and layout words, **the IV**, `pairPoint`, **`reduceWith`**, `runWith`/`run`.
6. [`Calls.lean`](RecStatement/Calls.lean): **the six `PCS_OPEN` calls word for word** (`pcsCalls`), π1-rec3's contract
   IV (`pi1IvWith`).
7. [`Security.lean`](RecStatement/Security.lean): π2's circuit with `σ`, `κ` (`Pi2Circuit`: its digest and setup table
   over `F`), the deployment and `RecDeployment.Real`, `PCS_OPEN` decoded under the registry and opened, the recursive
   verifier, the extractor, the experiments, **`RecKnowledgeSoundness`**, **`RecCompleteness`**.
8. [`Lemmas/`](RecStatement/Lemmas): `Arith` (fractions, digits, the fold, the siblings' fold), `Side` (the pushes'
   sums, the walk), `Subspace` (the indicators' closed form), `Coset` (the zero coset's), `SpecOf` (the transcription's
   hypothesis), `Push`, `Public`, **`Main`** (`checks_claims_iff`), `SpecLink` (`Spec::of`'s constants are `SpecOf`'s).
9. [`RecStatementTest/Runner.lean`](RecStatementTest/Runner.lean): the differential runner.

## Rust → Lean

| Rust (`crates/leanvm_rec/src/pi2`, `leanvm-rec` @ 2b22581) | Lean (`RecStatement.`) |
|---|---|
| `circuit.rs`: `Coeff`, `Lin`, `Formula`, `Pair`, `Read`, `PublicTerm`, `Circuit` (but `σ`, `κ`), `max_gamma`, `coset_constants`, `vanishing`, `pair_constants`, `digest` | `Coeff`, `Lin`, `Formula`, `Pair`, `Read`, `PublicTerm`, `Circuit`, `Circuit.maxGamma`, `cosetConstants` (`cosetConstantsF`), `vanishing` (`vanishingF`), `pairConstants`, `Pi2Circuit.digestWith` |
| `verifier.rs`: `NAME`, `Spec::of`, `subspace_coefficients`, `zero_coset`, `normalised_constants`, `tag_walk`, `frobenius`, `inverse`, `extension`, `reduce`, `Reduced`, `verify`, `statement_words` | `name`, `Spec.of`, `subspaceCoefficients` (`subspaceCoeffsF`), `zeroCosetOf`, `normalisedConstants`, `tagWalk`, `frobenius`, `normInverse`, `extension`, `reduceWith` (+ `CoreSpec.run`), `Reduced`, `runWith`/`run`, `UniStatement.publicWordsOf` |
| `verifier.rs` (`reduce`'s steps) | `digitsList`, `cellsList`/`foldLevel`, `zHat`, `fraction`, `groupDens`, `walkDens`/`betaTagNext`, `cosetSum`/`bRestList`, `publicSide`, `pushStep`/`pushSums`, `wInvsList`, `foldW` |
| `prover.rs`: `quotient_chunks`, `layouts`, `layout_word`, `layout_words`, `iv`, `Setup::new`'s table | `quotientChunks`, `layoutsOf`, `layoutWord`, `layoutWords`, `ivWith`/`iv`, `Pi2Circuit.setupStack` |
| `contract.rs`: `read_indices`, `number`, `root_word`, `call_words`/`expected_calls`, `registry`; `machine.rs`: `decode`, `root_of_word` | `elementIndices`, `UniStatement.numberWord`, `rootWordOfBytes`, `pcsCalls`, `registryOf`, `decodeWith`, `rootOfWord` |
| `transcript.rs`: `cantor_beta1`, `pair_point`; `circuit/spec.rs`: `CallWord` | `cantorBeta1` (`UniStatement.cantorBeta1`), `pairPoint`, `CallWord` |
| `leanvm_univariate/contract.rs`: `variant_bytes`, `contract_iv_for` | `rec3VariantBytes`, `pi1IvWith` (`UniStatement.variantBytes`, `contractIvForWith`) |

**Deviations, none changing a value**: a `List` stands for a `Vec`, an out-of-range read gives a default (the Rust
would panic; it never does on the circuits tested); the Rust skips a product by a coefficient equal to one, a zero
coefficient of `w_k` and, for a one-pair group, its numerator `1` (here the products are taken); `γ^0` is read from
the powers (`gammas[0] = 1`); the arithmetic's inverse is the field's (the Rust's is the norm's, `normInverse`,
transcribed and checked equal on every vector); the Rust's trace hook (`reduce_traced`) only reads values (the
contract's graph is unchanged: `tests/pi2.rs`'s parity holds).

## The data

`crates/leanvm_rec/src/lean_statement.rs` (`render`) writes `Data.lean` from π2's circuit for π1-rec3's real proof
(`circuit::compile::pi2(record_verifier(REFERENCE, Flock(FLOCK_REC3), Point), D16v)`, then `pi2::adapt`): the shape,
the formulas, the pairs, the reads, the public terms; π1's contract IV (`Compiled::pi1_iv`), the setup's root
(`Setup::new(circuit).root()`), the circuit's digest (`Circuit::digest`); π1's three calls (`spec::Circuit::calls`).
**Not `σ`, not `κ`**: the verifier reads neither; the setup's root and the digest bind them (`RecDeployment.Real`).
`tests/lean_statement.rs`'s `statement_data_is_current` fails when the file is stale. The runner checks, against the
Rust, every constant the Lean derives from it: `Spec.of`'s pairs (`s`, `Ẑ_s(c_p)`), recursion constants, groups,
pull-less pairs, public terms, zero coset, walk, highest power of `γ`; the IV; the layout words; `β_1`; the extension;
the stream's length; π1's contract IV (`pi1Iv` at `UniStatement.reference`, `programIv`, `referenceRoots`) and π1's
calls' constants (the reference layout words, one claim each, `F`'s root word).

## The statements (`Security.lean`, verbatim)

```lean
structure Pi2Circuit where
  circuit : Circuit
  sigma : ℕ → ℕ
  kappa : ℕ → K

structure RecDeployment where
  pi1 : UniStatement.Deployment
  pi2 : Pi2Circuit
  pi1Calls : List (List CallWord)
  pi1Rows : (ℕ → K) → List ℕ

def RecDeployment.Real (D : RecDeployment) : Prop :=
  D.pi2.circuit = Data.circuit ∧ D.pi1Calls = Data.pi1Calls ∧ D.pi1.shape = UniStatement.reference ∧
    D.pi1.programIv = UniStatement.programIv ∧
    Id.run (D.pi2.digestWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) = Data.digest ∧
    digestBytes (Id.run (D.pi2.setupTreeWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))).root =
      Data.setupRoot

noncomputable def recSoundnessExperiment (D : RecDeployment) (A : RecAdversary) : ProbComp RecOutcome :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots)).run []
    let accepted ← D.verifierWith queryPermutation trees.roots z.1 z.2
    return ((z, accepted), trees.evaluations, transcript)

def RecBreaksKnowledgeSoundness (D : RecDeployment) (ext : RecExtractor D) (z : RecOutcome) : Prop :=
  z.1.2 = true ∧ ¬ ∃ w, ext z.1.1.1 z.2.1 z.2.2 z.1.1.2 = some w ∧ D.pi1.Relation w.1 z.1.1.1 w.2

def RecKnowledgeSoundnessWith (D : RecDeployment) (ext : RecExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D ext z] ≤ ε Q

def RecKnowledgeSoundness (D : RecDeployment) (ε : ℕ → ℝ≥0∞) : Prop :=
  RecKnowledgeSoundnessWith D (recExtractor D) ε

noncomputable def recCompletenessExperiment (D : RecDeployment) (P : RecProver D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.pi1.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← P input rows q with
    | none => return false
    | some proof => D.verifierWith queryPermutation trees.roots input proof

def RecCompletenessWith (D : RecDeployment) (P : RecProver D) (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let v ← recCompletenessExperiment D P input rows q}[v = false] ≤ δ

def RecCompleteness (D : RecDeployment) (P : RecProver D) (δ : ℝ≥0∞) : Prop := RecCompletenessWith D P δ
```

`RecAdversary := RecSetupRoots → OracleComp RandomPermutationOracles (Vector UInt8 32 × RecProof)`; `RecProof` is the
stream and the six opening proofs (π1's `C1`, `C2`, `F`; π2's `W`, the setup, `Q`); `RecExtractor D := Vector UInt8 32 →
List (List UInt8 × Digest) → OracleQueryLog → RecProof → Option ((rows : List ℕ) × D.pi1.Stack rows)`;
`D.pi1.Relation rows input q` is UniStatement's (`M3Holds (leanIsaInstance blake2sFlockSpec prog (sizes rows))
(publicInputOf input) q`). **The verifier** `D.verifierWith F roots input proof`: π2's IV over `F`
(`D.ivWith`: π1-rec3's contract IV at π1's setup roots, the circuit's digest, π2's setup root, π2's layout words), the
run (`runWith`, its verdict `all ≠ 0`), then the six calls (`pcsCalls`, π1's `F` root word and π2's setup root the
setup's), each decoded under the registry (`decodeWith`) and opened: π1's by `UniStatement.pcsOpenWith` (the plain
layout), π2's by `PcsQuotient.openingWith` (π2's layouts). **The setup** (`D.setupTreesWith`): π1's three trees
(`UniStatement.setupTreesWith`) and π2's (`PcsQuotient.commitWith` of `κ`, `κ + σ` in the basis `B`). **The extractor**
`recExtractor` (explicit, computable): the setup's and the transcript's evaluations replayed; π2's `W` inverted under the
root the stream names and decoded (fast path, unique decoder, list decoder), each candidate's witness values read
(`basisValue`) and **π1's row counts** read off them (`D.pi1Rows`: π1's stream is π2's witness, not calldata); π1's `C1`
inverted under π2's stream's first public root and decoded; each `C1` candidate read as Lv42's stack at those counts
(`lv42Stack`), the first satisfying `M3Holds`. The bounds `ε`, `δ` and the prover `P` are parameters.

## The verifier-arithmetic lemmas (`Lemmas/`, proved)

Over any field of characteristic two, for `RecPiop`'s circuit `G` on a Cantor basis `B` (`ω = Heap.omega B`), under
**`SpecOf S G B pairOf portOf nz pubOf`** (the arithmetic's constants are `Spec::of` of `G`: the normalised recursion's
constants, the pairs enumerating `G.pairs` with their `s` and `Ẑ_s(c_p)`, the groups partitioning them with their
role, pull flag and formula, the zero coset the first `2^k` ports, the other terms the other ports with their tags and
public fingerprints):

* **`ind_eval_closed`** (`Subspace`): at `t ∉ V_m`, `Ẑ_s(t) + Ẑ_s(c_p) ≠ 0` and
  `(G.ind ω p).eval t = w_m(t)/(Ẑ_s(t) + Ẑ_s(c_p))`;
* **`coset_closed`** (`Coset`): `F(Y) = Π_{u<2^k} (Y + β ω_u)` and `Σ_u 1/(Y + βω_u) = β^(2^k−1)/F(Y)`;
* **`cellsList_eq_cellsOf`** (`Arith`): the siblings' fold is `RecPiop.cellsOf` (`ω_{2k+1} = ω_{2k} + 1`);
  **`foldW_eq_foldAt`**: `W`'s fold is `RecPiop.foldAt`;
* **`push_side`** (`Push`): `B ≠ 0`, `S_d ≠ 0`, `Σ_p I_p(t)(E_p + v_0) = w_m A/B`, `1_S(t) = w_m S_n/S_d`;
  **`publicSide_eq`** (`Public`): `D = Π_j d_pub(j)`, and `N = D · T` where no `d_pub` vanishes;
* **`all_ne_zero_iff`** (`Main`): the one inversion carries the two nonzero conditions:
  `all ≠ 0 ↔ w_{m+2}(t) ≠ 0 ∧ c_h + c_q ≠ 0 ∧ PubOK`;
* **`checks_claims_iff`** (`Main`):
  ```lean
  ((S.run inp).all ≠ 0 ∧ (S.run inp).combination = (1 + (S.run inp).rhoQ) * ht + (S.run inp).rhoQ * qt ∧
      (S.run inp).target = sumH ∧ inp.ξ = κt + inp.β * σt ∧ (S.run inp).fold = foldTrue) ↔
    (sq^[G.logN + 2] inp.t ≠ 0 ∧ dPullAt v α β t * G.dPushAt ω v ξ α γ t + (G.zV ω).eval t ≠ 0 ∧
      (∀ j < G.nP, G.dPub ω (pubOf inp.scalars) α β γ j ≠ 0) ∧ sumH = G.target ω (pubOf inp.scalars) α β γ ∧
      ξ = κt + β * σt ∧ G.QClaim ω v ξ α β γ t ht qt ∧ foldAt G.logW (fun k ↦ inp.a.getD k 0) ρ = foldTrue)
  ```
  (`v = cellsOf G.logW ω (fun k ↦ inp.a.getD k 0) t`): the verifier's check passes and its claims hold at the true
  values iff `t ∉ V_{m+2}`, `c_h + c_q ≠ 0` and `RecPiop`'s state after `ρ` holds; **`checks_claims_iff_post2`** states
  the right side with `RecPiop.Post2 G ω Mo pubOf' s cW [α, β, γ] cQ [t] (a ++ [ξ]) [ρ]` itself, for any tables' model
  `Mo` (its `h(t)`, `q(t)`, `Σ_V h`, `κ(t)`, `σ(t)`, `W`'s true fold);
* the claims' points (`Main`): `run_u` (`u_l = w_l/(1 + w_l)`), `run_digitsScale` (`t/w_{m+2} = Π (1 + w_l)^{-1}`), for
  the tables' layer;
* **`normConsts_of_spec`**, **`pairZ_eq_zHat`** (`SpecLink`): `Spec::of`'s constants (`coset_constants`,
  `normalised_constants`, `pair_constants`) are `SpecOf`'s; they commute with a field homomorphism (`K → E`).

## What is tested, what is defined

**Tested** (`RecStatementTest/Runner.lean`, `lake env lean`: compiled evaluation, not the kernel), on **64 vectors** of
the Rust (`crates/leanvm_rec/tests/lean_statement.rs`): **the real proof** (π1-rec3's 1,000-signature proof, then π2's
real proof on its circuit), **31 flips** (one bit of a byte of π1's roots, its elements, `W`'s and `Q`'s roots, every
fold value and `ξ`, the last byte), **3 other public inputs**, **3 truncated and 2 extended streams**, **24 random**
streams and public inputs. On each, the Lean and the Rust agree on every value: the verdict (the stream's error, or the
value required nonzero), the 16 trace steps (every intermediate value of `reduce`), the public scalars and their pair
points, the roots, the four claims, **the six `PCS_OPEN` inputs word for word**, and the compiled contract (revm, every
call attested) calls `PCS_OPEN` with exactly these inputs (the Rust writer asserts it). On every accepted vector the
Lean also decodes each call under the registry (π1's three by π1's layouts, π2's three by π2's), re-encodes it to its
words, and finds π2's decoded claims the reduction's; and the norm's inverse is the field's. The self-tests: the norm's
inverse; the zero coset's closed form (`k ≤ 5`) and `w_k` vanishing on `V_k`; the indicators' cosets at `m = 10`
(`Ẑ_s(ω_i) + Ẑ_s(c_p) = 0` exactly on the coset, every alignment) and the normalised recursion; `β_1`; π1's contract IV
and π1's calls' constants. **Results: 64/64 agree on every value; 59 accepted by both, 5 rejected by both** (the
truncated and extended streams); about 85 s.

The flipped, other-input and random streams are accepted by both: the contract's only check before `PCS_OPEN` is the
one inversion (`all ≠ 0`), which fails only on a degenerate challenge; everything else rests on the openings.

**Defined, not tested**: `PCS_OPEN`'s WHIR (the Rust has a mock), the setup's commitment (`setupTreeWith`) and the
circuit's digest over `F` (`σ` is not in Lean: `RecDeployment.Real` binds them to the Rust's values), the extractor,
the experiments, the Props.

## Open points

1. **The Props are not proved** (the composition's): it needs `SpecOf` for the real circuit (from the circuit compiler,
   `RecCircuit`, and `SpecLink`), the tables' layer (`W`'s and `Q`'s claims as their tables' values: `run_u`,
   `run_digitsScale`, `RecPiop.sum_tablePoly_omega`), the Fiat–Shamir layer and the openings, π1's verifier in π2's
   circuit (`RecGraph`, `RecCircuit`) and π1's soundness (`UniSound`'s rec3 instance).
2. **`pi1Rows`** is a field of the deployment: where π2's witness holds π1's row counts is the circuit compiler's (the
   stream's first 24 bytes are free bits of π2's witness, `circuit::compile`); the composition instantiates it.
3. **`PCS_OPEN`'s WHIR instance is a choice**, as in UniStatement: π1's calls on the plain layout of `2^vars` words
   (the layout word's byte 24), π2's on π2's public layouts (`quotient::opening`); the registry decodes as
   `machine::decode`.
4. **The degenerate events** (`all = 0`: `t ∈ V_{m+2}`, `c_h + c_q = 0`, a vanishing public denominator) reject; they
   matter for completeness only (`all_ne_zero_iff` names them).
