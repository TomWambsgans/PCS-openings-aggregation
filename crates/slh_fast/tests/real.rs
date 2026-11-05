// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π1 on real SLH-DSA-SHAKE-128s signatures (RustCrypto's FIPS 205 implementation, as `slh_dsa`'s tests): three
//! proofs verify with their WHIR openings (the structured Keccak terminal; the first also with the walked one), and
//! are rejected after a changed stream byte (sampled), opening root or value, message or public key; a tampered
//! signature (the reference rejects it) makes the prover refuse, and a forced proof of it is rejected; so is a port
//! the glue holds but Flock does not.
//!
//! `cargo test --release -p slh_fast --test real -- --nocapture`

use fips205::{Shake128s, SigningKey, VerifyingKey};
use leanvm_flock_gas::keccak_flock::{Keccak, KeccakWalked};
use primitives::field::F64;
use primitives::test_rng::Rng;
use slh_dsa::{MSG_BYTES, SHAKE_128S, glue};
use slh_fast::Params;
use slh_fast::prover::{Config, Setup, prove, verify};

const P: Params = Params::SLH_128S;

#[test]
fn real_signatures() {
    let p = SHAKE_128S;
    let started = std::time::Instant::now();
    let glue = glue::build(&p);
    let setup = Setup::new(&P, &glue.circuit);
    println!("glue and setup (σ committed): {:.2} s", started.elapsed().as_secs_f64());

    let mut rng = Rng::new(0x5_1D5A_F457);
    let mut bytes16 = || -> [u8; 16] { std::array::from_fn(|_| rng.next_u64() as u8) };
    for round in 0..3 {
        let (sk_seed, sk_prf, pk_seed, opt_rand) = (bytes16(), bytes16(), bytes16(), bytes16());
        let msg: [u8; MSG_BYTES] = [bytes16(), bytes16()].concat().try_into().unwrap();
        let sk = SigningKey::<Shake128s>::slh_keygen_internal(&sk_seed, &sk_prf, &pk_seed);
        let vk: &VerifyingKey<Shake128s> = sk.as_ref();
        let pk: [u8; 32] = vk.to_bytes().as_slice().try_into().unwrap();
        let sig = sk.try_sign_with_context(&msg, &[], Some(&opt_rand)).unwrap();
        vk.try_verify_with_context(&msg, &[], &sig).expect("the reference verifies its signature");
        let sig = sig.to_bytes().to_vec();

        let (bits, lanes) = glue::inputs(&p, &pk, &msg, &sig);
        let cells = glue.witness(&bits, &lanes).expect("the honest witness");
        let started = std::time::Instant::now();
        let config = Config { check: round == 0, force: false };
        let (proof, report) = prove(&setup, &pk, &msg, &cells, config).expect("a proof");
        let secs = started.elapsed().as_secs_f64();
        for (check, holds) in &report.checks {
            assert!(holds, "round {round}: {check}");
        }
        let started = std::time::Instant::now();
        verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).expect("accepted");
        let verify_secs = started.elapsed().as_secs_f64();
        println!(
            "round {round}: proved in {secs:.3} s (stream {} B, openings {:?} B), verified in {verify_secs:.3} s",
            report.stream_bytes, report.opening_bytes
        );
        if round == 0 {
            for (name, secs) in &report.phases {
                println!("  {name:<56} {secs:.4} s");
            }
            for (c, placed, vars) in &report.stacks {
                println!("  {c:?}: {placed} words of 2^{vars} ({:.1}%)", 100.0 * *placed as f64 / (1u64 << vars) as f64);
            }
            verify::<KeccakWalked>(&P, &setup.root, &pk, &msg, &proof).expect("accepted (walked terminal)");
        }

        // A wrong statement.
        let mut other = msg;
        other[31] ^= 0x80;
        assert!(verify::<Keccak>(&P, &setup.root, &pk, &other, &proof).is_err(), "round {round}: another M");
        let mut other = pk;
        other[20] ^= 0x01;
        assert!(verify::<Keccak>(&P, &setup.root, &other, &msg, &proof).is_err(), "round {round}: another PK.root");
        // Stream bytes, sampled; each opening's root and value.
        let mut proof = proof;
        let len = proof.stream.len();
        for k in 0..24 {
            let at = (k * 104_729 + 31 * round + 5) % len;
            proof.stream[at] ^= 1 << ((k + round) % 8);
            assert!(verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).is_err(), "round {round}: stream byte {at}");
            proof.stream[at] ^= 1 << ((k + round) % 8);
        }
        for k in 0..3 {
            proof.openings[k].root[7] ^= 4;
            assert!(verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).is_err(), "round {round}: root {k}");
            proof.openings[k].root[7] ^= 4;
            proof.openings[k].value.c0 ^= 1;
            assert!(verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).is_err(), "round {round}: value {k}");
            proof.openings[k].value.c0 ^= 1;
        }

        // A tampered signature (a WOTS+ chain of layer 3, as tests/real.rs): the reference rejects it; its glue
        // witness holds but for word 6, so the prover refuses, and a forced proof is rejected.
        let n = p.n;
        let fors = n * p.k * (1 + p.a);
        let xmss = n * (p.len() + p.hp);
        let mut bad = sig.clone();
        bad[n + fors + xmss * 3 + n * 17 + 4] ^= 1 << (round + 2);
        let reference = fips205::Signature::<Shake128s>::try_from(&bad[..]).unwrap();
        assert!(vk.try_verify_with_context(&msg, &[], &reference).is_err());
        let (bits, lanes) = glue::inputs(&p, &pk, &msg, &bad);
        let bad_cells = glue.witness(&bits, &lanes).expect("the glue's gates, wires and ports hold");
        assert!(prove(&setup, &pk, &msg, &bad_cells, Config::default()).is_err(), "round {round}: the prover refuses");
        if round == 0 {
            let (forced, _) = prove(&setup, &pk, &msg, &bad_cells, Config { check: false, force: true }).expect("forced");
            assert!(verify::<Keccak>(&P, &setup.root, &pk, &msg, &forced).is_err(), "a tampered signature is rejected");
            // A port the glue holds but Flock does not: block 4,000 (Keccak-f(0) padding, read by nothing), lane 7.
            let mut bad = cells.clone();
            let row = P.port_start() + glue::port_index(4000, 7);
            for role in [0, 3] {
                bad[4 * row + role] += F64(1 << 40);
            }
            glue.circuit.check_k(&bad).expect("the glue's gates and wires hold");
            let (forced, _) = prove(&setup, &pk, &msg, &bad, Config { check: false, force: true }).expect("forced");
            assert!(verify::<Keccak>(&P, &setup.root, &pk, &msg, &forced).is_err(), "a wrong port is rejected");
        }
        println!("round {round}: the statement (2), 24 stream bytes, 3 roots, 3 values, a tampered signature rejected");
    }
}
