// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The vectors of the Lean honest prover's differential test (`formal/RecCompose/RecComposeTest/Pi2Prover.lean`): the
//! circuit compiler's example (`circuit::spec::example`), padded to `2^log_n` positions as `tests/pi2.rs` pads it,
//! through `pi2::adapt`; its witness, public input and values, π2's IV; and the Rust prover's stream and roots
//! (`pi2::prover::prove`). The Lean runner reads the interface's circuit as `RecCircuit.Circuit`, runs its prover on
//! the same inputs and compares the stream byte for byte, `W`'s, `Q`'s and the setup's roots.
//!
//! `PI2_PROVER_OUT=$PWD/pi2_prover.txt cargo test --release -p leanvm_rec --test lean_pi2_prover -- --ignored --nocapture`

use std::fmt::Write as _;

use leanvm_rec::circuit::spec::{self, Formula, Source};
use leanvm_rec::pi2::adapt;
use leanvm_rec::pi2::circuit::Read;
use leanvm_rec::pi2::prover::{self, PublicValue, Setup, claims_hold, prove};
use leanvm_rec::pi2::verifier::Spec;

/// The example on `2^log_n` positions (`tests/pi2.rs`'s `padded_example`).
fn padded_example(log_n: u8) -> (spec::Circuit, spec::Witness, spec::PublicInputs) {
    let (mut c, mut w, public) = spec::example();
    let (old, n) = (c.n(), 1usize << log_n);
    c.sigma = c
        .sigma
        .iter()
        .map(|&s| {
            if (s as usize) < old {
                s
            } else {
                s - old as u32 + n as u32
            }
        })
        .chain(old as u32..n as u32)
        .collect();
    c.log_n = log_n;
    w.resize(n, leanvm_flock_gas::field::K(0));
    (c, w, public)
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn vector(log_n: u8, out: &mut String) {
    let (c, w, public) = padded_example(log_n);
    assert_eq!(c.check(&w, &public), Ok(()));
    let circuit = adapt::adapt(&c);
    let (public_input, values) = adapt::public_values(&public);
    let spec = Spec::of(&circuit);
    let setup = Setup::new(&circuit);
    let iv = prover::iv(&[0x11; 32], &circuit.digest(), &setup.root(), circuit.log_n);
    let witness = adapt::witness(&w);
    let proved = prove(&circuit, &spec, &setup, &iv, &public_input, &values, &witness);
    assert_eq!(claims_hold(&proved, &setup), [true; 4]);
    writeln!(out, "VECTOR example {log_n}").unwrap();
    writeln!(out, "SHAPE {} {}", c.log_n, c.log_width).unwrap();
    for region in &c.regions {
        let roles: Vec<String> = region
            .roles
            .iter()
            .map(|f| match f {
                Formula::Forward => "F".to_string(),
                Formula::Expr(p) => {
                    let lin: Vec<String> = p.linear.iter().map(|(c, k)| format!("{c}:{:x}", k.0)).collect();
                    let quad: Vec<String> =
                        p.quadratic.iter().map(|(a, b, k)| format!("{a}:{b}:{:x}", k.0)).collect();
                    format!("E{};{}", lin.join(","), quad.join(","))
                }
                Formula::Port(limbs) => {
                    let ls: Vec<String> = limbs.iter().map(|l| l.to_string()).collect();
                    format!("P{}", ls.join(","))
                }
            })
            .collect();
        writeln!(out, "REGION {}", roles.join(" ")).unwrap();
    }
    for b in &c.blocks {
        writeln!(out, "BLOCK {} {} {}", b.row, b.log_rows, b.region).unwrap();
    }
    let sigma: Vec<String> = c.sigma.iter().map(|s| s.to_string()).collect();
    writeln!(out, "SIGMA {}", sigma.join(" ")).unwrap();
    for (i, k) in &c.kappa {
        writeln!(out, "KAPPA {i} {:x}", k.0).unwrap();
    }
    for p in &c.ports {
        let source = match p.source {
            Source::Statement => "S".to_string(),
            Source::Root(i) => format!("R{i}"),
            Source::Element(i) => format!("L{i}"),
            Source::Zero => "Z".to_string(),
            Source::Pad => "D".to_string(),
        };
        writeln!(out, "PORT {} {source}", p.position).unwrap();
    }
    let reads: Vec<String> = circuit
        .reads
        .iter()
        .map(|r| match r {
            Read::Integer(b) => format!("I{b}"),
            Read::Root => "R".to_string(),
            Read::Scalar => "S".to_string(),
        })
        .collect();
    writeln!(out, "READS {}", reads.join(" ")).unwrap();
    let vals: Vec<String> = values
        .iter()
        .map(|v| match v {
            PublicValue::Integer(x) => format!("I{x:x}"),
            PublicValue::Root(b) => format!("R{}", hex(b)),
            PublicValue::Scalar(x) => format!("S{:x}:{:x}:{:x}", x.c0, x.c1, x.c2),
        })
        .collect();
    writeln!(out, "VALUES {}", vals.join(" ")).unwrap();
    writeln!(out, "IV {}", hex(&iv)).unwrap();
    writeln!(out, "INPUT {}", hex(&public_input)).unwrap();
    let ws: Vec<String> = witness.iter().map(|x| format!("{:x}", x.0)).collect();
    writeln!(out, "WITNESS {}", ws.join(" ")).unwrap();
    writeln!(out, "SETUPROOT {}", hex(&setup.root())).unwrap();
    writeln!(out, "WROOT {}", hex(&proved.roots[0])).unwrap();
    writeln!(out, "QROOT {}", hex(&proved.roots[1])).unwrap();
    writeln!(out, "STREAM {}", hex(&proved.stream)).unwrap();
    writeln!(out, "END").unwrap();
}

#[test]
#[ignore]
fn lean_pi2_prover_vectors() {
    let path = std::env::var("PI2_PROVER_OUT").unwrap_or_else(|_| "pi2_prover.txt".into());
    let mut out = String::new();
    for log_n in [9u8, 10] {
        vector(log_n, &mut out);
    }
    std::fs::write(&path, out).expect("the vectors are written");
    eprintln!("wrote {path}");
}
