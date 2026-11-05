// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π1's prover on a real SLH-DSA-SHAKE-128s signature: each phase's seconds (median of 3 runs) and the process's
//! peak memory, with jemalloc as `crates/leanvm_univariate`'s proving runs.
//!
//! `cargo test --release -p slh_fast --test bench -- --ignored --nocapture`

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

use fips205::{Shake128s, SigningKey, VerifyingKey};
use leanvm_flock_gas::keccak_flock::Keccak;
use primitives::test_rng::Rng;
use slh_dsa::{MSG_BYTES, SHAKE_128S, glue};
use slh_fast::Params;
use slh_fast::prover::{Config, Setup, prove, verify};

const P: Params = Params::SLH_128S;
const RUNS: usize = 3;

fn median(mut x: Vec<f64>) -> f64 {
    x.sort_by(f64::total_cmp);
    x[x.len() / 2]
}

#[test]
#[ignore]
fn bench_pi1() {
    let p = SHAKE_128S;
    let glue = glue::build(&p);
    let setup = Setup::new(&P, &glue.circuit);
    let mut rng = Rng::new(0xBE_5C);
    let mut bytes16 = || -> [u8; 16] { std::array::from_fn(|_| rng.next_u64() as u8) };
    let (sk_seed, sk_prf, pk_seed, opt_rand) = (bytes16(), bytes16(), bytes16(), bytes16());
    let msg: [u8; MSG_BYTES] = [bytes16(), bytes16()].concat().try_into().unwrap();
    let sk = SigningKey::<Shake128s>::slh_keygen_internal(&sk_seed, &sk_prf, &pk_seed);
    let vk: &VerifyingKey<Shake128s> = sk.as_ref();
    let pk: [u8; 32] = vk.to_bytes().as_slice().try_into().unwrap();
    let sig = sk.try_sign_with_context(&msg, &[], Some(&opt_rand)).unwrap().to_bytes().to_vec();
    let (bits, lanes) = glue::inputs(&p, &pk, &msg, &sig);

    // Warm up once, then RUNS runs.
    let cells = glue.witness(&bits, &lanes).expect("the honest witness");
    let (proof, _) = prove(&setup, &pk, &msg, &cells, Config::default()).expect("a proof");
    verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).expect("accepted");
    drop((cells, proof));
    let mut phases: Vec<(&'static str, Vec<f64>)> = Vec::new();
    let mut totals = Vec::new();
    for _ in 0..RUNS {
        let started = std::time::Instant::now();
        let cells = glue.witness(&bits, &lanes).expect("the honest witness");
        let glue_secs = started.elapsed().as_secs_f64();
        let (proof, report) = prove(&setup, &pk, &msg, &cells, Config::default()).expect("a proof");
        totals.push(started.elapsed().as_secs_f64());
        let all = std::iter::once(("witness: the glue's cells (evaluated, checked)", glue_secs)).chain(report.phases.iter().copied());
        for (k, (name, secs)) in all.enumerate() {
            if phases.len() <= k {
                phases.push((name, Vec::new()));
            }
            phases[k].1.push(secs);
        }
        drop((cells, proof));
    }
    println!("BENCH π1, SLH-DSA-SHAKE-128s ({RUNS} runs, medians), threads {}:", parallel::num_threads());
    for (name, secs) in &phases {
        println!("  {name:<56} {:.4} s", median(secs.clone()));
    }
    println!(
        "  {:<56} {:.3} s (runs {:?})",
        "total (glue witness + prove)",
        median(totals.clone()),
        totals.iter().map(|t| format!("{t:.3}")).collect::<Vec<_>>()
    );
    println!("  peak RSS {:.2} GB", bench::peak_rss_bytes() as f64 / 1e9);
}
