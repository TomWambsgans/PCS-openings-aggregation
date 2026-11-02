/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

What the bridge does not prove of this repository's openings, given leanerVM `mumbai`'s theorems
(https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0).
-/
import WhirBridge.Verifier

/-!
# The gaps

`opening_sound` (`Verifier.lean`) is the random-oracle soundness of `opening::verify` itself, its
transcript included (the IV `keccak256(prefix ‖ claims)`, a zero public digest, the root the proof's
first two scalars, checked against the expected one), for every valid layout, and `ours_sound`
for the witness, wiring and quotient layouts at every supported size. What it does not cover:

1. **The model.** Keccak-256 and Keccak-f[1600] are two independent random oracles; the adversary
   is classical and fixed before they are sampled. mumbai moves leanVM's theorem to one random
   permutation (`LeanVMRpm.lean`, at `q²/2^508`); this bridge stops at the two-oracle model. The
   layout's id in the prefix is a constant of the verifier, computed with the deployed Keccak-256,
   not an oracle answer. Statements carry at most `2^46 + 1` claims (`Stmt.short`; the protocol
   opens one or two per root).
2. **The Rust is the model** (test evidence, not proof): `Layout.check` and
   `openingVerifyWithHash` transcribe `opening.rs`, `Layout.new`, `Layout.hidden` and the protocol's
   layouts transcribe `opening.rs` and `protocol.rs`, mumbai's `verifyWhir` transcribes the Python
   verifier at `c445e3d5`, of which the vendored `verify_whir` is a byte-identical copy of leanVM's
   Rust (mumbai fuzzes the two). `Test/Check.lean` runs `openingVerifyWithHash` with the deployed
   Keccak on openings of the Rust prover (a public layout, the deployed witness and quotient
   layouts) and recomputes the 76-byte prefix of all 18 layouts. A change of the hidden layout
   (condition (R) of the hiding layer) changes `Layout.hidden` and the protocol's layouts, which
   must be transcribed again; the theorems are stated for every layout with `Layout.Valid`, so the
   proofs do not change unless the weight's shape does.
3. **Pruned Merkle paths and `placed`**: the Rust verifier reads pruned batches whose level-0 rows
   leave out the zero lanes past `placed`; mumbai's `Proof` has one full path per query. The
   expansion (`PrunedMerklePaths::expand`, `crates/verifier/src/merkle.rs`) checks the same roots,
   so it only restricts what is accepted; it is not formalised (as for leanVM).
4. **List decoding, no out-of-domain sample at level 0**: an accepted opening yields a candidate
   among the up to `L₀` tables of the root's Johnson list satisfying all its claims jointly
   (`Layout.joint_of_not_doom`), not a unique table: the reduction's soundness must hold for each
   of the `L₀ ≤ 9952` candidates fixed by each root (`candidates_ours`; mumbai's global bound
   `2^18`), a union bound, and claims on one root must not be split over openings.
5. **Composition** of the three openings' transcripts with the reduction's: the reduction must read
   the words extracted when each root entered its transcript (mumbai's `extract_take_eq`).
6. **Extraction from the adversary's queries only**: the extracted word is read off the final
   cache (the verifier's answers included), as in mumbai's `romSound`; mumbai's further step to an
   extractor reading the adversary's transcript alone (`Sound.extractor_of_extracted`,
   `LeanVMSound.lean`, at `Q_V/2^256`) is not taken.
7. **Hiding** (zero knowledge of the openings) is layer F3 (`formal/QuotientSecurity/Hiding`).
-/
