// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The lane-level glue of SLH-DSA-SHAKE-128s (`slh_dsa::glue`, `SPEC-FAST.md` §4.3–4.5) on real signatures of
//! RustCrypto's FIPS 205 implementation, with real Keccak-f outputs in its ports: the gates, the wires and the
//! ports hold, the public words hold the statement, and word 6 is zero exactly when the reference verifies (the
//! 21 tamperings of `tests/real.rs`). And, on a small parameter set, the glue computes what `lib.rs`'s bit circuit
//! computes, value by value.

use fips205::{Shake128s, SigningKey, VerifyingKey};
use primitives::field::F64;
use primitives::test_rng::Rng;
use quotient::circuit::{WORD_BITS, read};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use slh_dsa::glue::{self, Glue};
use slh_dsa::{MSG_BYTES, Params, SHAKE_128S, statement};

/// Whether the public words hold the statement of `(pk, msg)`, and whether word 6 is zero, from the cells.
fn public(cells: &[F64], pk: &[u8; 32], msg: &[u8; MSG_BYTES]) -> (bool, bool) {
    let halves = statement(pk, msg).halves();
    let holds = (0..4).all(|word| {
        (0..WORD_BITS).all(|j| {
            let limb = if j < 64 { halves[word].c0 >> j } else { halves[word].c1 >> (j - 64) };
            Glue::public_bit(cells, word, j) == limb & 1
        })
    });
    (holds, (0..WORD_BITS).all(|j| Glue::public_bit(cells, 6, j) == 0))
}

/// The honest witness of `(pk, msg, sig)`: its gates, wires and ports hold; the public words; the row outputs.
fn evaluate(glue: &Glue, pk: &[u8; 32], msg: &[u8; MSG_BYTES], sig: &[u8]) -> ((bool, bool), Vec<F64>) {
    let (bits, lanes) = glue::inputs(&SHAKE_128S, pk, msg, sig);
    let cells = glue.witness(&bits, &lanes).expect("the honest witness holds");
    (public(&cells, pk, msg), glue.outputs(&bits, &lanes))
}

fn shake256(bytes: &[u8], out: usize) -> Vec<u8> {
    let mut h = sha3::Shake256::default();
    h.update(bytes);
    let mut digest = vec![0; out];
    h.finalize_xof().read(&mut digest);
    digest
}

#[test]
fn glue_verifies_real_signatures() {
    let p = SHAKE_128S;
    let start = std::time::Instant::now();
    let glue = glue::build(&p);
    println!(
        "{} glue: {} rows below the ports + {} port rows = {} of 2^{}; {} Keccak-f of {} blocks; built in {:.2} s",
        p.name,
        glue.main_rows,
        glue::QUADS * glue::BLOCKS,
        glue.main_rows + glue::QUADS * glue::BLOCKS,
        glue.circuit.log_rows,
        glue.used_calls,
        glue::BLOCKS,
        start.elapsed().as_secs_f64()
    );
    for (gadget, rows) in &glue.rows {
        println!("  {gadget:<48} {rows:>7}");
    }
    assert_eq!(glue.used_calls, p.keccak_f());
    assert_eq!(glue.circuit.log_rows, glue::LOG_ROWS);
    assert!(glue.main_rows <= glue::PORT_START);
    assert_eq!(glue.rows.iter().map(|(_, rows)| rows).sum::<usize>(), glue.main_rows);

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

        let start = std::time::Instant::now();
        let (accepted, v) = evaluate(&glue, &pk, &msg, &sig);
        assert_eq!(accepted, (true, true), "round {round}: an honest signature");
        // The taps: `H_msg`'s digest is SHAKE256's, and the last root is `PK.root`.
        let h_msg = [&sig[..16], &pk[..], &[0, 0], &msg[..]].concat();
        assert_eq!(glue::read_bytes(&v, &glue.digest), shake256(&h_msg, p.m));
        assert_eq!(glue::read_bytes(&v, glue.roots.last().unwrap()), pk[16..]);
        println!("round {round}: honest signature accepted ({:.3} s)", start.elapsed().as_secs_f64());

        // The tamperings of `tests/real.rs`: the reference rejects each, the glue's word 6 is nonzero.
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
            assert_eq!(evaluate(&glue, &pk, &msg, &bad).0, (true, false), "round {round}: {what}");
        }
        let mut other = msg;
        other[31] ^= 0x80;
        assert_eq!(evaluate(&glue, &pk, &other, &sig).0, (true, false), "round {round}: another message");
        let mut other_pk = pk;
        other_pk[20] ^= 0x01;
        assert!(!evaluate(&glue, &other_pk, &msg, &sig).0.1, "round {round}: another PK.root");
        println!("round {round}: 7 tamperings rejected");
    }
}

/// A small parameter set with every gadget of 128s: two layers (the tree bits shift), multi-block `T_len`, a
/// three-block `T_k` (`k = 14`), several FORS levels.
const TOY: Params = Params { name: "toy", n: 16, h: 6, d: 2, hp: 3, a: 3, k: 14, m: 8 };

/// The glue and `lib.rs`'s bit circuit compute the same values on the same inputs (random, so not signatures):
/// the digest, the FORS public key, every layer's root, word 6. About 2^27 rows of bit circuit: run with
/// `cargo test --release -p slh_dsa --test glue -- --ignored --nocapture`.
#[test]
#[ignore]
fn glue_agrees_with_the_bit_circuit() {
    let p = TOY;
    let start = std::time::Instant::now();
    let glue = glue::build(&p);
    let built = slh_dsa::build(&p);
    let (digest, roots, zero) = (built.digest.clone(), built.roots.clone(), built.zero.clone());
    let log_rows = built.builder.len().next_power_of_two().trailing_zeros() as usize;
    let bits = built.builder.finish_with_zeros(log_rows, &built.public, &[built.zero]);
    println!(
        "toy: glue {} rows below the ports, bit circuit {} rows; {} Keccak-f; built in {:.1} s",
        glue.main_rows,
        bits.used_rows,
        glue.used_calls,
        start.elapsed().as_secs_f64()
    );
    assert_eq!(glue.used_calls, p.keccak_f());
    let mut rng = Rng::new(0x70);
    for round in 0..3 {
        let pk: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let msg: [u8; MSG_BYTES] = std::array::from_fn(|_| rng.next_u64() as u8);
        let sig: Vec<u8> = (0..p.sig_bytes()).map(|_| rng.next_u64() as u8).collect();
        let (public_bits, lanes) = glue::inputs(&p, &pk, &msg, &sig);
        glue.witness(&public_bits, &lanes).expect("the honest witness holds");
        let v = glue.outputs(&public_bits, &lanes);
        let w = bits.outputs(&slh_dsa::inputs(&p, &pk, &msg, &sig));
        let bit_bytes = |wires: &[quotient::circuit::Src]| -> Vec<u8> {
            wires.chunks(8).map(|byte| byte.iter().enumerate().fold(0u8, |acc, (i, &s)| acc | read(&w, s) << i)).collect()
        };
        assert_eq!(glue::read_bytes(&v, &glue.digest), bit_bytes(&digest), "round {round}: the digest");
        let h_msg = [&sig[..16], &pk[..], &[0, 0], &msg[..]].concat();
        assert_eq!(bit_bytes(&digest), shake256(&h_msg, p.m));
        assert_eq!(glue.roots.len(), roots.len());
        for (layer, (ours, theirs)) in glue.roots.iter().zip(&roots).enumerate() {
            assert_eq!(glue::read_bytes(&v, ours), bit_bytes(theirs), "round {round}: root {layer}");
        }
        assert_eq!(glue::read_bytes(&v, &glue.zero), bit_bytes(&zero), "round {round}: word 6");
        println!("round {round}: digest, {} roots and word 6 agree", roots.len());
    }
}
