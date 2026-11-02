// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The prover's kernels timed alone, to see where its time goes:
//! `cargo test --release -p leanvm_univariate --test prove_kernels -- --ignored --nocapture`.

use leanvm_univariate::prover::poly::{novel_from_extension, on_coset, subset_sums};
use primitives::field::{F64, F192};
use quotient::ntt::{self, K8};

fn time<R>(name: &str, reps: usize, mut f: impl FnMut() -> R) -> R {
    let started = std::time::Instant::now();
    let mut out = None;
    for _ in 0..reps {
        out = Some(f());
    }
    println!(
        "{:>10.3} ms  {name}",
        started.elapsed().as_secs_f64() * 1e3 / reps as f64
    );
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
    let offset = quotient::domain::point(1 << 25);
    for r in [18usize, 21, 23] {
        let k: Vec<F64> = (0..1 << r).map(|_| F64(next())).collect();
        let e: Vec<F192> = (0..1 << r).map(|_| F192::new(next(), next(), next())).collect();
        time(&format!("K NTT on a coset, 2^{r} (quotient::domain)"), 8, || {
            on_coset(&k, 1 << 25)
        });
        time(&format!("E NTT on a coset, 2^{r} (quotient::domain)"), 4, || {
            on_coset(&e, 1 << 25)
        });
        let mut e2 = e.clone();
        time(&format!("E inverse NTT on D_{r}, 2^{r} (quotient::domain)"), 2, || {
            novel_from_extension(&mut e2, r)
        });
        let mut k2 = k.clone();
        time(&format!("K NTT, 2^{r} (ntt, one column)"), 8, || {
            ntt::values(&mut k2, offset)
        });
        time(&format!("K inverse NTT, 2^{r} (ntt, one column)"), 8, || {
            ntt::coefficients(&mut k2, offset)
        });
        time(&format!("K subset sums, 2^{r}"), 8, || subset_sums(&mut k2));
        time(&format!("K fold 2^{r} -> 2^{} and NTT (ntt)", r - 2), 8, || {
            ntt::on_coset_prefix(&k, 1 << 25, r - 2)
        });
        time(&format!("K fold 2^{r} -> 2 (ntt)"), 8, || {
            ntt::on_coset_prefix(&k, 1 << 25, 1)
        });
        if r == 18 {
            let batch: Vec<K8> = (0..1 << r).map(|_| K8(std::array::from_fn(|_| F64(next())))).collect();
            let mut out = vec![K8::ZERO; 1 << r];
            time(&format!("8 K NTTs, 2^{r} (ntt, a batch)"), 8, || {
                ntt::values_batch_from(&batch, &mut out, offset, true)
            });
            let mut quarter = vec![K8::ZERO; 1 << (r - 2)];
            time(&format!("8 K folds 2^{r} -> 2^{} (ntt, a batch)", r - 2), 8, || {
                ntt::fold_batch(&batch, 1 << 25, &mut quarter)
            });
            let delta: Vec<F64> = (0..r).map(|_| F64(next())).collect();
            time(&format!("K shifted cube, 2^{r}"), 8, || {
                ntt::shifted_cube(&k, &delta, r)
            });
        }
    }
}
