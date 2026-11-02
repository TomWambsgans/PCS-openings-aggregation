<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Issues to report upstream (leanVM)

Issues found in code this repository vendors from [leanVM](https://github.com/leanEthereum/leanVM) (commit
`c445e3d51a5a85031df47240595698f3b24897bf`, see NOTICE.md) that affect leanVM itself, written so that each can be
forwarded as it stands. Paths are leanVM's, which this repository keeps. Line numbers are those of this
repository's copy before the fix, at commit `f6e68a5` (items 1 and 2) or `25d06ea` (items 3 to 5). That copy
carries local additions, so its line numbers differ from leanVM's.

## 1. Aliasing UB in the in-place Reed-Solomon encodes (medium)

**File.** `crates/pcs/src/ntt/additive_ntt_f64.rs`. It was vendored at this repository's `d940553`, unchanged
except for its header. The branch `PCS-openings-aggregation` (at `651453c6`) has the same three pointer
derivations.

**Functions.** `AdditiveNttF64::encode_interleaved_in_place` and `AdditiveNttF64::encode_interleaved_in_place_with`
create the bad pointer. `AdditiveNttF64::transform` passes it on, and `AdditiveNttF64::gathered_pass` and `replicate`
read through it. (This repository's `encode_interleaved_rows_in_place` copied the pattern and had the same bug.)

**What happens.** Each in-place encode takes a raw pointer to the message, which is the buffer's own first replica.
It then lends the buffer to `transform` as a `&mut [F64]`:

```rust
pub fn encode_interleaved_in_place(&self, data: &mut [F64], num_ntts: usize, log_inv_rate: usize) {
    // The message is the buffer's own first replica.
    let msg = parallel::SendPtr(data.as_mut_ptr());
    self.transform(data, num_ntts, log_inv_rate, Some(msg), None);
}
```

A `&mut` function argument is protected for the whole call. LLVM marks it `noalias`, so within the call it is the
only way to access those words. `transform` writes the buffer through pointers it derives from its own `data`:
`gathered_pass`'s `base`, `replicate`'s `dst`, and the deep pass's chunks. Meanwhile the first gathered pass, or
`replicate`, reads the message through `msg`. That pointer was derived before the reborrow, so it is not derived
from the argument. Under Stacked Borrows, the function-entry retag of `data` invalidates `msg` at once, and the
first read through `msg` is UB. Under Tree Borrows, that read is a foreign read of the protected argument. It makes
the argument "Reserved (conflicted)", and the argument's next child write is UB.

The outputs are correct today. Every test passes. With `-Zmiri-disable-stacked-borrows`, Miri reports nothing: no
out-of-bounds access, no uninitialized read, no data race. But the compiler is allowed to rely on `noalias`. For
example, it could move the message reads after the writes of block 0, which `transform` orders deliberately ("Why
block 0 goes last"). So this is a latent miscompilation.

**Miri report.** Toolchain `nightly-2026-10-03` (rustc 1.101.0-nightly 0abfedbc7), with
`cargo miri test --target x86_64-unknown-linux-gnu`. The shape is a 2^5-row codeword of 3 lanes at rate 1/2, as in
`ntt::additive_ntt_f64::adversarial::miri_replica_and_rows_only_encodes`. At x86's cache budgets that shape takes
`replicate` and then the deep pass.

Stacked Borrows:

```text
error: Undefined Behavior: trying to retag from <327175> for SharedReadOnly permission at alloc120238[0x0], but that
tag does not exist in the borrow stack for this location
   --> crates/pcs/src/ntt/additive_ntt_f64.rs:920:23        (replicate)
920 |             let src = std::slice::from_raw_parts(msg.add(start), len);
help: <327175> was created by a SharedReadWrite retag at offsets [0x0..0x300]
   --> crates/pcs/src/ntt/additive_ntt_f64.rs:174:37
174 |         let msg = parallel::SendPtr(data.as_mut_ptr());
help: <327175> was later invalidated at offsets [0x0..0x300] by a Unique function-entry retag inside this call
   --> crates/pcs/src/ntt/additive_ntt_f64.rs:175:9
175 |         self.transform(data, num_ntts, log_inv_rate, Some(msg), None, None);
```

Tree Borrows (`MIRIFLAGS=-Zmiri-tree-borrows`):

```text
error: Undefined Behavior: write access through <322458> at alloc120234[0x0] is forbidden
    --> crates/pcs/src/ntt/additive_ntt_f64.rs:1066:9        (butterfly_lanes, in the deep pass)
1066 |         top[lane] = new_u;
     = help: the accessed tag <322458> is a child of the conflicting tag <319406>
     = help: the conflicting tag <319406> has state Reserved (conflicted) which forbids this child write access
help: the conflicting tag <319406> was created here, in the initial state Reserved
    --> crates/pcs/src/ntt/additive_ntt_f64.rs:298:9
 298 |         data: &mut [F64],                                  (transform's argument)
help: the conflicting tag <319406> later transitioned to Reserved (conflicted) due to a reborrow (acting as a
      foreign read access) at offsets [0x0..0x180]
    --> crates/pcs/src/ntt/additive_ntt_f64.rs:920:23        (replicate's read through `msg`)
```

The first gathered pass has the same bug. Shrinking the cache budgets to `L2_WORDS = 16` and `L3_WORDS = 32` makes
tiny shapes take gathered passes from the message. Miri then reports the read in `gathered_pass`'s `gather`
(`std::slice::from_raw_parts(src_row(i), num_ntts)`, line 499) under Stacked Borrows. Under Tree Borrows, it reports
the scatter's write back to block 0 (`dst.copy_from_slice(src)`, line 511), after that read made `gathered_pass`'s
`data` "Reserved (conflicted)".

**To reproduce in leanVM.** On a 2^5-row domain, this triggers the bug. Run as a test on this repository's copy
before the fix, it gives the two reports above:

```rust
let ntt = AdditiveNttF64::standard(5);
let mut data = vec![F64::ZERO; 3 << 5];
data[..3 << 4].iter_mut().enumerate().for_each(|(i, w)| *w = F64(i as u64 + 1));
ntt.encode_interleaved_in_place(&mut data, 3, 1);
```

Run it under `cargo +nightly miri test --target x86_64-unknown-linux-gnu`. On aarch64, the NEON field and
butterfly paths use intrinsics Miri may not support, hence the x86 target, where the default target features take
the portable paths. Two local edits were needed:

- Drop the `bench` dev-dependency: jemalloc does not cross-build.
- Use plain copies in `primitives::stream` under `cfg(miri)`: `_mm_stream_si128` is inline assembly, which Miri
  does not run.

**Fix (applied here).** The fix stops taking the message pointer before the buffer is lent out. A private
`enum Message<'a> { InPlace, Separate(&'a [F64]) }` replaces `Option<SendPtr<F64>>` as the message argument of
`transform`, `gathered_pass` and `replicate`:

- The in-place encodes pass `Message::InPlace`. The separate-message encodes pass `Message::Separate(msg)`.
- `gathered_pass` derives the in-place message pointer from its own `data`, as the same `base` its tasks write
  through. `replicate` likewise reads an in-place message through `dst`. Reads and writes now all derive from the
  `&mut` that the function holds.
- In `transform`, `msg.take_if(|m| std::ptr::eq(m.0, data.as_mut_ptr()) || ..)` becomes
  `matches!(m, Message::InPlace) || ..`.
- The deep pass reads a separate message as `&m[off..off + sub_len]`, which removes one `unsafe` block.

The schedule and the arithmetic are unchanged. The codewords are the same, word for word:

- Every NTT test passes, along with this repository's adversarial ones (replica, rows-only and whole encodes
  against the untouched whole encode).
- The proofs are byte-identical: `protocol::tests::proofs_are_pinned`, 18 pinned whole-protocol digests, and the
  full-size membership benchmark's proof digest.

Under Miri, after the fix, these tests pass under both Stacked Borrows and Tree Borrows:

- The `ntt::additive_ntt_f64::adversarial` tests, scaled down under `cfg(miri)`, at x86's budgets and at the shrunk
  budgets (one or two gathered passes from an in-place message).
- `whir::adversarial::miri_commit_tree_rows_and_lean_level` and `whir::adversarial::miri_lane_tensor_prover`, which
  run commitments and a whole WHIR proof that use the in-place encodes.

## 2. The pass planner divides by zero on very wide rows (low)

**File.** `crates/pcs/src/ntt/additive_ntt_f64.rs`, in `AdditiveNttF64::transform` at `c445e3d5`:

```rust
let fit = |words: usize| (words / num_ntts).max(1).ilog2() as usize;
let (fit2, fit3) = (fit(L2_WORDS), fit(L3_WORDS));
// ...
let deep = if rest <= fit3 {
    fit3
} else {
    fit2.max(rest.saturating_sub((rest - fit3).div_ceil(fit2) * fit2))
};
```

A row wider than half the L2 budget makes `fit2 = 0`. That is `num_ntts > 2^15` words on x86 and `num_ntts > 2^20`
words on Apple silicon. If more than `fit3` layers then remain, `div_ceil(0)` panics with "attempt to divide by
zero". This was checked natively on Apple silicon: `encode_interleaved_in_place` on `2^21` lanes of 4 rows at rate
1/2 (a 2-row message) panics at that line. (The same call on 2 rows does not panic, because no layer is left.)

The planner on `PCS-openings-aggregation` is different: `deep = if log_d - start <= fit3 { fit3 } else { fit2 }`.
By reading (not run), `fit2 = 0` there gives `deep_start = log_d` and gathered passes of `g = 0` layers. The loop
`layer += g` never advances, so the call hangs instead of panicking.

No WHIR commitment here comes near such widths. They have at most a few hundred words a row. So this is a latent
edge case of a public API, and it is not fixed here. One fix: floor the row-group budget at one layer
(`fit(L2_WORDS).max(1)`). That leaves every plan with `fit2 >= 1`, which covers every current use. Another: assert
`num_ntts <= L2_WORDS / 2` with a clear message.

## 3. The level-0 query grinding comment says 0 bits; it is 17 (documentation)

**File.** `crates/pcs/src/whir.rs`, in `recursive_prover_with_basis` (line 1804 of this repository's copy at
`25d06ea`, before the fix):

```rust
// Query-phase PoW grinding for L0 (0 bits in the production profile; the
// canonical 0 nonce is still absorbed to keep the transcript in lockstep).
ps.grind(config.grinding_bits[0] as u32);
```

The production profile grinds `QUERY_GRINDING_BITS = 17` bits at every level, level 0 included
(`crates/pcs/src/whir_config.rs:62`, and the verifier's `const QUERY_GRINDING_BITS: u32 = 17` in
`crates/verifier/src/whir.rs:17`, which `grind_check` requires at level 0 too). Only the test-only
`default_config` grinds 0 bits. The code is right; the comment would mislead an auditor counting the query bits
(level 0's 222 to 225 queries close `128 - 17 = 111` bits, not 128). **Fix (applied here):** the comment says
17 bits in the production profile, 0 only in `default_config`.

## 4. The level-0 OOD row's comment omits its assumptions (documentation)

**File.** `crates/pcs/src/whir_config.rs`, the security schema's comment (line 321 at `25d06ea`) and
`paper_ood_bits`'s doc (line 565):

> Binding to a single codeword of the (Johnson-bounded) interleaved list is via `ood_samples` explicit
> multilinear OOD evaluations, except at L0, where the opening's own post-commit random evaluation claim plays
> the OOD role (union over the list, `L*mu/q`), so `ood_samples = 0`.

At level 0 the PCS takes no OOD sample, so a root binds only to a Johnson list; the row's bits
(`192 - log2 L - log2 mu`) are a property of the protocol that uses the PCS, and hold only if:

- **the outer protocol binds the list**: it opens all the claims on one root together, in one opening (two
  openings of one root can be of two list members: for a table with two claims, splitting them into two
  openings is forgeable at about `2^111` work at these parameters), and it union-bounds over the list every
  challenge it draws after the commitment and before the claims (each of the `L` members may be the one later
  opened);
- **the claim point is uniform in `E^mu`**, drawn after the commitment: then two distinct list members agree at
  it with probability at most `mu/q`, and `L*mu/q` over the list. A point that is a degree-`D` image of fewer
  challenges (for instance built from one field element, as in a univariate-to-multilinear reduction) costs
  `L*D/q` instead;
- **a fixed point binds nothing** (a claim at a point known before the commitment, such as a "top coefficient"
  claim, distinguishes no list members chosen with it in mind).

**Fix (applied here, comments only):** both comments state these assumptions.

## 5. The proximity-gap accounting omits the fold's `2^(ℓ-1)` factor (documentation, parameters)

**File.** `crates/pcs/src/whir_config.rs`, `paper_thm_ca_johnson_log_a` (line 436 at `25d06ea`), whose doc says the
two-row MCA error `a/|F|` "is also the fold error of a `2^ℓ`-row word". leanerVM's proof of the fold error
(`mumbai`, the theorems that certify these WHIR levels) carries a factor `2^(ℓ-1)` on it, which this accounting
omits: 5 bits at the first fold of `2^6` lanes. leanerVM certifies the deployed parameters (the query counts and
grinding) with a smaller `η` of its own (`LeanVM/Protocol/Whir/Params/Deployed.lean`, `certTable`), so the
deployed configuration is covered there, but the per-level proximity-gap bits this file computes (and that
`validate` checks against 128) are not the certified ones. **Not changed here** (flagged in the comment): the fix
is to carry the factor in `paper_thm_ca_johnson_log_a`, or to cite leanerVM's certified `η` instead of the
search's.
