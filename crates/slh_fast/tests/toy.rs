// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π1 end to end on a small glue (`Params::TOY`: `2^13` rows, 128 Keccak-f blocks): a few chained calls on free
//! lanes and the public bits, one output unpacked. The proof verifies (both Keccak terminals, the WHIR openings);
//! every combined claim holds on the stacks; a changed stream byte, root, statement or port is rejected.
//!
//! `cargo test --release -p slh_fast --test toy -- --nocapture`

use leanvm_flock_gas::keccak_flock::{Keccak, KeccakWalked};
use primitives::field::F64;
use primitives::test_rng::Rng;
use quotient::circuit::{Src, public_words};
use slh_dsa::glue::{G, Glue, Hint};
use slh_fast::Params;
use slh_fast::prover::{Config, Setup, prove, verify};

const P: Params = Params::TOY;

/// The toy glue: 512 public bits (`PK ‖ M`), 8 free lanes, four chained Keccak-f calls (lanes 0..4 the free lanes,
/// 4..8 packings of public bits; each next call's input the previous output, its lanes 0..4 XORed with free lanes),
/// the last call's lane 1 unpacked.
fn toy() -> Glue {
    let mut g = G::new(P.port_start(), P.blocks());
    let public: Vec<Src> = (0..512).map(|k| g.bit(Hint::Public(k))).collect();
    let lanes: Vec<Src> = (0..8).map(|k| g.lane(Hint::Lane(k))).collect();
    let mut input = [Src::Zero; 25];
    input[..4].copy_from_slice(&lanes[..4]);
    for l in 0..4 {
        input[4 + l] = g.pack(&public[64 * l..64 * (l + 1)]);
    }
    input[24] = g.kconst(0x0123_4567_89ab_cdef);
    for call in 0..4 {
        let unpack: &[usize] = if call == 3 { &[1] } else { &[] };
        let (out, _) = g.keccak(input, unpack);
        input = out;
        for l in 0..4 {
            input[l] = g.b.xor(input[l], lanes[4 + l]);
        }
    }
    let words = public_words(&public[..256], &public[256..]);
    g.finish(P.log_rows, &words, &[])
}

fn statement(rng: &mut Rng) -> ([u8; 32], [u8; 32], Vec<bool>, Vec<u64>) {
    let pk: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let msg: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let bits = [&pk[..], &msg[..]].concat().iter().flat_map(|&b| (0..8).map(move |i| (b >> i) & 1 == 1)).collect();
    let lanes = (0..8).map(|_| rng.next_u64()).collect();
    (pk, msg, bits, lanes)
}

#[test]
fn toy_pi1_end_to_end() {
    let glue = toy();
    let setup = Setup::new(&P, &glue.circuit);
    let mut rng = Rng::new(0x70_1E);
    let (pk, msg, bits, lanes) = statement(&mut rng);
    let cells = glue.witness(&bits, &lanes).expect("the honest witness");
    let started = std::time::Instant::now();
    let (proof, report) = prove(&setup, &pk, &msg, &cells, Config { check: true, force: false }).expect("a proof");
    println!("toy: proved in {:.3} s, stream {} B", started.elapsed().as_secs_f64(), report.stream_bytes);
    for (name, secs) in &report.phases {
        println!("  {name:<56} {secs:.4} s");
    }
    for (check, holds) in &report.checks {
        println!("  {check}: {holds}");
        assert!(holds, "{check}");
    }
    verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).expect("accepted (structured terminal)");
    verify::<KeccakWalked>(&P, &setup.root, &pk, &msg, &proof).expect("accepted (walked terminal)");

    // A wrong statement.
    let mut other = msg;
    other[5] ^= 1;
    assert!(verify::<Keccak>(&P, &setup.root, &pk, &other, &proof).is_err(), "another M");
    let mut other = pk;
    other[30] ^= 0x10;
    assert!(verify::<Keccak>(&P, &setup.root, &other, &msg, &proof).is_err(), "another PK");
    // The prover refuses a statement the cells do not hold.
    assert!(prove(&setup, &pk, &other, &cells, Config::default()).is_err(), "the prover refuses another PK");

    // Stream bytes, sampled.
    let len = proof.stream.len();
    let mut proof = proof;
    for k in 0..48 {
        let at = (k * 7919 + 13) % len;
        proof.stream[at] ^= 1 << (k % 8);
        assert!(verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).is_err(), "stream byte {at} of {len}");
        proof.stream[at] ^= 1 << (k % 8);
    }
    // Each opening's root, point, value.
    for k in 0..3 {
        proof.openings[k].root[3] ^= 1;
        assert!(verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).is_err(), "root {k}");
        proof.openings[k].root[3] ^= 1;
        proof.openings[k].value.c1 ^= 1;
        assert!(verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).is_err(), "value {k}");
        proof.openings[k].value.c1 ^= 1;
    }
    let mut setup_root = setup.root;
    setup_root[0] ^= 1;
    assert!(verify::<Keccak>(&P, &setup_root, &pk, &msg, &proof).is_err(), "another setup");
    verify::<Keccak>(&P, &setup.root, &pk, &msg, &proof).expect("restored");

    // A port the glue holds but Flock does not: block 100 (Keccak-f(0) padding, its outputs read by nothing), lane 7's
    // X and V changed together (its gate and its wires still hold).
    let mut bad = cells.clone();
    let row = P.port_start() + slh_dsa::glue::port_index(100, 7);
    for role in [0, 3] {
        bad[4 * row + role] += F64(1 << 33);
    }
    glue.circuit.check_k(&bad).expect("the glue's gates and wires hold");
    assert!(prove(&setup, &pk, &msg, &bad, Config::default()).is_err(), "the prover refuses a wrong port");
    let (forced, report) = prove(&setup, &pk, &msg, &bad, Config { check: false, force: true }).expect("forced");
    assert!(report.checks.iter().any(|(_, holds)| !holds));
    assert!(verify::<Keccak>(&P, &setup.root, &pk, &msg, &forced).is_err(), "a wrong port is rejected");
    println!("toy: accepted; 48 stream bytes, 3 roots, 3 values, the statement, the setup and a port rejected");
}
