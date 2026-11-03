// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Review of π2's PIOP (REVIEW-REC.md): experiments, no fixes.
//!
//! - `review_hole_is_unconstrained` (E3): PI2.md §4.1's pull-less holes. A witness whose hole holds garbage (which
//!   `spec::Circuit::check` rejects, `Failure::Hole`) gives a proof whose four claims hold: π2 proves
//!   `spec::Circuit::check`'s (1), (2), (4), not (3). Harmless while no formula reads a hole, which only `adapt` (at
//!   circuit construction) and `pi2::circuit::Circuit::validate` (called by tests) check: `Spec::of`, the prover and
//!   the contract's generator do not.
//! - `review_hole_read_is_forgeable` (E3b): the same circuit with role 1's formula reading the hole (built directly as
//!   the PIOP's `Circuit`, as `adapt` would refuse): the verifier's `Spec::of` and the prover take it, and a witness
//!   whose role-1 push is computed from a garbage hole value is accepted — the push it carries is then whatever the
//!   prover chose. The verifier does not itself guarantee the property `adapt` checks.
//!
//! `cargo test --release -p leanvm_rec --test review_pi2 -- --nocapture`

#[global_allocator]
static ALLOC: bench::Jemalloc = bench::Jemalloc;

use leanvm_rec::circuit::spec::{self, Failure};
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::circuit::{Circuit, Lin};
use leanvm_rec::pi2::prover::{self, PublicValue, Setup, claims_hold, open, prove_with, public_scalars, verify_openings};
use leanvm_rec::pi2::verifier::Spec;
use primitives::field::{F64, F192};

const PI1_IV: [u8; 32] = [0x11; 32];

/// `tests/pi2.rs`'s padding of the interface's example to `2^log_n` positions.
fn padded_example(log_n: u8) -> (spec::Circuit, spec::Witness, spec::PublicInputs) {
    let (mut c, mut w, public) = spec::example();
    let (old, n) = (c.n(), 1usize << log_n);
    c.sigma = c
        .sigma
        .iter()
        .map(|&s| if (s as usize) < old { s } else { s - old as u32 + n as u32 })
        .chain(old as u32..n as u32)
        .collect();
    c.log_n = log_n;
    w.resize(n, leanvm_flock_gas::field::K(0));
    (c, w, public)
}

/// Prove `witness` (no prover-side check) and report whether the four claims hold and the openings verify.
fn accepted(circuit: &Circuit, public_input: &[u8; 32], values: &[PublicValue], witness: &[F64]) -> bool {
    let spec = Spec::of(circuit);
    let setup = Setup::new(circuit);
    let iv = prover::iv(&PI1_IV, &circuit.digest(), &setup.root(), circuit.log_n);
    let proved = prove_with(circuit, &spec, &setup, &iv, public_input, values, witness, false);
    let holds = claims_hold(&proved, &setup);
    let (reduced, roots, openings) = open(proved, &setup);
    let opened = verify_openings(circuit.log_n, &reduced, &roots, &setup.root(), &openings).is_ok();
    println!("  claims hold {holds:?}, openings verify {opened}");
    holds == [true; 4] && opened
}

#[test]
fn review_hole_is_unconstrained() {
    let (c, mut w, public) = padded_example(11);
    assert_eq!(c.check(&w, &public), Ok(()));
    let hole = c.ports[0].position as usize;
    w[hole] = leanvm_flock_gas::field::K(0xdead_beef_0bad_f00d);
    assert_eq!(c.check(&w, &public), Err(Failure::Hole { position: hole as u32 }));
    let circuit = adapt::adapt(&c);
    let (public_input, values) = adapt::public_values(&public);
    println!("hole {hole} set to garbage:");
    assert!(
        accepted(&circuit, &public_input, &values, &adapt::witness(&w)),
        "π2 accepts a witness spec::Circuit::check rejects (a garbage hole)"
    );
}

#[test]
fn review_hole_read_is_forgeable() {
    let (c, w, public) = padded_example(11);
    let hole = c.ports[0].position as usize; // row 1, role 15
    let mut circuit = adapt::adapt(&c);
    // The port's fingerprint `cell 0 + Y cell 2 + Y² cell 4` (row 1) made to read cell 15, the port's own position
    // (the hole), for its first limb: a circuit `adapt` would refuse, built directly as the PIOP's.
    let port_pair = circuit.pairs.iter().position(|p| !p.pulls).expect("the port pair");
    let f = circuit.pairs[port_pair].formula;
    let mut formula = circuit.formulas[f].clone();
    assert_eq!(formula.lin.terms[0].1, 0);
    formula.lin.terms[0].1 = 15;
    let _ = Lin::default();
    circuit.formulas.push(formula);
    circuit.pairs[port_pair].formula = circuit.formulas.len() - 1;
    assert!(circuit.validate().is_err(), "validate refuses a formula reading a pull-less cell");
    // The public element is now whatever the hole holds (plus Y, Y² parts from cells 2 and 4): put the target's limb
    // 0 in the hole, the original cell 0 left as it is.
    let (public_input, mut values) = adapt::public_values(&public);
    let target = 0x1234_5678_9abc_def0u64;
    if let PublicValue::Scalar(x) = &mut values[0] {
        *x = F192::new(target, x.c1, x.c2);
    }
    let mut witness = adapt::witness(&w);
    witness[hole] = F64(target);
    let _ = public_scalars(&public_input, &values);
    println!("a port reading its own hole, the hole set to the forged limb {target:#x}:");
    assert!(
        accepted(&circuit, &public_input, &values, &witness),
        "the verifier accepts a public element the circuit never computed"
    );
}
