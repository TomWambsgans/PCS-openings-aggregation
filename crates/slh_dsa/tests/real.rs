// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The SLH-DSA-SHAKE-128s circuit on real signatures of RustCrypto's FIPS 205 implementation: it accepts them
//! and rejects tampered ones. About 30 GB and a few minutes:
//! `cargo test --release -p slh_dsa --test real -- --ignored --nocapture`.

use fips205::{Shake128s, SigningKey, VerifyingKey};
use primitives::test_rng::Rng;
use quotient::circuit::{Circuit, PUBLIC_ROWS, WORD_BITS, read};
use slh_dsa::{MSG_BYTES, SHAKE_128S, circuit, inputs, statement};

/// The bit public row `r`'s X (even `j`) or Y (odd `j`) cell holds, for bit `j` of public word `word`.
fn public_bit(circuit: &Circuit, v: &[u8], word: usize, j: usize) -> u64 {
    let row = circuit.rows[word * (WORD_BITS / 2) + j / 2];
    read(v, if j % 2 == 0 { row.x } else { row.y }) as u64
}

/// Whether the circuit's public words hold the statement of `(pk, msg)` and word 6 is zero: the verifier's
/// public check, bit by bit.
fn accepts(circuit: &Circuit, pk: &[u8; 32], msg: &[u8; MSG_BYTES], sig: &[u8]) -> (bool, bool) {
    let v = circuit.outputs(&inputs(&SHAKE_128S, pk, msg, sig));
    let halves = statement(pk, msg).halves();
    let public = (0..4).all(|word| {
        (0..WORD_BITS).all(|j| {
            let limb = if j < 64 { halves[word].c0 >> j } else { halves[word].c1 >> (j - 64) };
            public_bit(circuit, &v, word, j) == limb & 1
        })
    });
    let zero = (0..WORD_BITS).all(|j| public_bit(circuit, &v, 6, j) == 0);
    (public, zero)
}

#[test]
#[ignore]
fn verifies_real_signatures() {
    let p = SHAKE_128S;
    let start = std::time::Instant::now();
    let (circuit, keccak_f) = circuit(&p);
    println!(
        "{}: {} rows used of 2^{} ({:.2} bits), {} free inputs, {} Keccak-f; built in {:.1} s",
        p.name,
        circuit.used_rows,
        circuit.log_rows,
        (circuit.used_rows as f64).log2(),
        circuit.n_inputs(),
        keccak_f,
        start.elapsed().as_secs_f64()
    );
    assert_eq!(keccak_f, p.keccak_f());
    assert_eq!(circuit.log_rows, slh_dsa::SHAKE_128S_LOG_ROWS);
    assert_eq!(circuit.n_inputs(), 8 * (32 + MSG_BYTES + p.sig_bytes()));
    assert!(PUBLIC_ROWS == 8 * WORD_BITS / 2);

    let mut rng = Rng::new(0x5_1D5A);
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
        assert_eq!(sig.len(), p.sig_bytes());

        let start = std::time::Instant::now();
        assert_eq!(accepts(&circuit, &pk, &msg, &sig), (true, true), "round {round}: an honest signature");
        println!("round {round}: honest signature accepted ({:.1} s)", start.elapsed().as_secs_f64());

        // A flipped bit of R, of a FORS secret, of a FORS path, of a WOTS+ chain value in layer 3, and of the
        // last layer's path: the reference rejects each, and the circuit's root differs from PK.root.
        let n = p.n;
        let fors = n * p.k * (1 + p.a);
        let xmss = n * (p.len() + p.hp);
        for (what, at) in [
            ("R", 3),
            ("FORS secret 5", n + n * (1 + p.a) * 5 + 2),
            ("FORS path 9, level 7", n + n * (1 + p.a) * 9 + n * 8 + 11),
            ("WOTS+ chain 17, layer 3", n + fors + xmss * 3 + n * 17 + 4),
            ("XMSS path, layer 6, level 8", n + fors + xmss * 6 + n * (p.len() + 8) + 15),
        ] {
            let mut bad = sig.clone();
            bad[at] ^= 1 << (round + 2);
            let reference = fips205::Signature::<Shake128s>::try_from(&bad[..]).unwrap();
            assert!(vk.try_verify_with_context(&msg, &[], &reference).is_err(), "{what}");
            assert_eq!(accepts(&circuit, &pk, &msg, &bad), (true, false), "round {round}: {what}");
        }
        // Another message under the same signature, and another key.
        let mut other = msg;
        other[31] ^= 0x80;
        assert_eq!(accepts(&circuit, &pk, &other, &sig), (true, false), "round {round}: another message");
        let mut other_pk = pk;
        other_pk[20] ^= 0x01;
        assert_eq!(accepts(&circuit, &other_pk, &msg, &sig).1, false, "round {round}: another PK.root");
        println!("round {round}: 7 tamperings rejected");
    }
}
