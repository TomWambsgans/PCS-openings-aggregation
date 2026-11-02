// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The prover's kernels timed alone, to see where its time goes:
//! `cargo test --release -p leanvm_univariate --test prove_kernels -- --ignored --nocapture`.

use leanvm_univariate::prover::poly::{novel_from_extension, on_coset, subset_sums};
use primitives::field::{F64, F192};

fn time<R>(name: &str, reps: usize, mut f: impl FnMut() -> R) -> R {
    let started = std::time::Instant::now();
    let mut out = None;
    for _ in 0..reps {
        out = Some(f());
    }
    println!("{:>10.3} ms  {name}", started.elapsed().as_secs_f64() * 1e3 / reps as f64);
    out.expect("one run")
}

#[test]
#[ignore]
fn kernels() {
    parallel::init();
    let mut state = 7u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for r in [18usize, 21, 23] {
        let k: Vec<F64> = (0..1 << r).map(|_| F64(next())).collect();
        let e: Vec<F192> = (0..1 << r).map(|_| F192::new(next(), next(), next())).collect();
        time(&format!("K NTT on a coset, 2^{r}"), 8, || on_coset(&k, 1 << 25));
        time(&format!("E NTT on a coset, 2^{r}"), 4, || on_coset(&e, 1 << 25));
        let mut e2 = e.clone();
        time(&format!("E inverse NTT on D_{r}, 2^{r}"), 2, || novel_from_extension(&mut e2, r));
        let mut k2 = k.clone();
        time(&format!("K subset sums, 2^{r}"), 4, || subset_sums(&mut k2));
    }
}
