// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/pcs/src/ring_switch.rs.
// MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and NOTICE.md at the repository root).
// Part of this repository: leanVM's `crates/pcs/src/ring_switch.rs` at commit 42422001 keeps more; flock's
// prover needs only this function of it, copied unchanged. MIT OR Apache-2.0; see NOTICE.md.
use primitives::field::F192;

/// Standard inner product `sum_i a[i] * b[i]` over E.
pub fn inner_product_ext(a: &[F192], b: &[F192]) -> F192 {
    assert_eq!(a.len(), b.len());
    let mut acc = F192::ZERO;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc += x * y;
    }
    acc
}
