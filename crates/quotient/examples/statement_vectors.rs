// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Test vectors for the differential test of `formal/Statement` (its `lake exe differential`): statements and
//! proofs, honest and tampered, with what the Rust verifier makes of them.
//!
//! `cargo run --release -p quotient --example statement_vectors -- OUT [--full]`
//!
//! - `R` lines: the reduction alone ([`protocol::verify`]) on random nine-scalar streams (and a few of other
//!   lengths, or with a root that is not two halves) at `2^16` to `2^23` rows (the layouts take `2^17` to `2^22`,
//!   [`protocol::supported`]), and on the honest proofs below: the two roots and the four claims, or the rejection.
//! - `Q` lines: the honest prover's inputs (input bits, the tables' seed, the masks) and the stream it sends.
//! - `P` lines: whole proofs (the reduction and the three openings) on a small circuit of `2^17` rows, honest and
//!   tampered, the openings in their raw form (one full Merkle path per query, [`opening::verify_paths`]), with
//!   the Rust verifier's verdict on that raw form. With `--full`, also the membership circuit (`2^22` rows).
//! - `I` lines: a circuit's size, its number of inputs and its commitment (the root of its wiring table), for the
//!   small circuit and a circuit of one Keccak-256 (`2^17` rows), and with `--index` (or `--full`) the membership
//!   circuit: the Lean builder and commitment must reproduce them.
//!
//! Tokens are separated by spaces: a hash is 64 hex digits (its bytes in order), an element of `E` its three limbs
//! `c0:c1:c2` in hex, a word of `K` 16 hex digits.

use std::fmt::Write as _;

use fiat_shamir::merkle::Hash;
use primitives::field::{F64, F192};
use primitives::test_rng::Rng;
use quotient::circuit::{Builder, Circuit, Src, membership, membership_inputs, public_words};
use quotient::opening::{self, Claim, Layout, commit, wire_proof};
use quotient::protocol::{
    Claims, Index, Openings, Randomness, open, prove_with_seed, quotient_layout, verify, wiring_layout, witness_layout,
};
use quotient::statement::{DEPTH, Secret, Statement};
use quotient::transcript::Proof;
use verifier::{MerkleOpenings, MerklePath};

fn hex_hash(h: &Hash) -> String {
    h.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_e(x: F192) -> String {
    format!("{:016x}:{:016x}:{:016x}", x.c0, x.c1, x.c2)
}

fn hex_ve(x: verifier::E) -> String {
    format!("{:016x}:{:016x}:{:016x}", x.c0, x.c1, x.c2)
}

fn random_e(rng: &mut Rng) -> F192 {
    F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64())
}

fn random_hash(rng: &mut Rng) -> Hash {
    std::array::from_fn(|_| rng.next_u64() as u8)
}

fn claim_tokens(out: &mut String, claim: &Claim) {
    write!(out, " {}", claim.point.len()).unwrap();
    for &x in &claim.point {
        write!(out, " {}", hex_e(x)).unwrap();
    }
    write!(out, " {}", hex_e(claim.value)).unwrap();
}

fn head(out: &mut String, tag: &str, log_rows: usize, index_root: &Hash, statement: &Statement, stream: &[F192]) {
    write!(
        out,
        "{tag} {log_rows} {} {} {} {}",
        hex_hash(index_root),
        hex_hash(&statement.y),
        hex_hash(&statement.root),
        stream.len()
    )
    .unwrap();
    for &x in stream {
        write!(out, " {}", hex_e(x)).unwrap();
    }
}

/// An `R` line: the reduction's verdict on a stream.
fn reduction_line(log_rows: usize, index_root: &Hash, statement: &Statement, stream: &[F192]) -> String {
    let mut out = String::new();
    head(&mut out, "R", log_rows, index_root, statement, stream);
    let proof = Proof {
        stream: stream.to_vec(),
    };
    match verify(index_root, statement, &proof, log_rows) {
        Ok((roots, claims)) => {
            write!(out, " ACCEPT {} {}", hex_hash(&roots[0]), hex_hash(&roots[1])).unwrap();
            for claim in [&claims.witness, &claims.wiring, &claims.quotient, &claims.sum] {
                claim_tokens(&mut out, claim);
            }
        }
        Err(_) => out.push_str(" REJECT"),
    }
    out
}

/// An opening in its raw form: the WHIR stream and every query's path.
#[derive(Clone)]
struct RawOpening {
    stream: Vec<verifier::E>,
    paths: Vec<MerklePath>,
}

impl RawOpening {
    fn proof(&self) -> verifier::Proof {
        let mut bytes = Vec::new();
        for path in &self.paths {
            for word in &path.leaf {
                bytes.extend_from_slice(&word.to_bytes());
            }
            for sibling in &path.siblings {
                bytes.extend_from_slice(sibling);
            }
        }
        verifier::Proof {
            stream: self.stream.clone(),
            merkle_openings: MerkleOpenings::Raw(bytes),
        }
    }

    fn tokens(&self, out: &mut String) {
        write!(out, " {}", self.stream.len()).unwrap();
        for &x in &self.stream {
            write!(out, " {}", hex_ve(x)).unwrap();
        }
        write!(out, " {}", self.paths.len()).unwrap();
        for path in &self.paths {
            write!(out, " {}", path.leaf.len()).unwrap();
            for word in &path.leaf {
                write!(out, " {:016x}", word.0).unwrap();
            }
            write!(out, " {}", path.siblings.len()).unwrap();
            for sibling in &path.siblings {
                write!(out, " {}", hex_hash(sibling)).unwrap();
            }
        }
    }
}

/// The raw form of an honest (pruned) opening: the paths the Rust verifier expands it into.
fn raw(layout: &Layout, root: &Hash, claims: &[Claim], proof: &fiat_shamir::transcript::Proof) -> RawOpening {
    let wired = wire_proof(proof);
    let paths = opening::verify_paths(layout, root, claims, &wired).expect("an honest opening holds");
    let raw = RawOpening {
        stream: wired.stream.clone(),
        paths,
    };
    opening::verify(layout, root, claims, &raw.proof()).expect("its raw form holds");
    raw
}

/// A whole proof: the reduction's stream and the three openings in raw form.
#[derive(Clone)]
struct Whole {
    log_rows: usize,
    index_root: Hash,
    statement: Statement,
    stream: Vec<F192>,
    openings: [RawOpening; 3],
}

impl Whole {
    fn of(
        log_rows: usize,
        index_root: &Hash,
        statement: &Statement,
        stream: &[F192],
        roots: &[Hash; 2],
        claims: &Claims,
        openings: &Openings,
    ) -> Self {
        Self {
            log_rows,
            index_root: *index_root,
            statement: *statement,
            stream: stream.to_vec(),
            openings: [
                raw(
                    &witness_layout(log_rows),
                    &roots[0],
                    std::slice::from_ref(&claims.witness),
                    &openings.witness,
                ),
                raw(
                    &wiring_layout(log_rows),
                    index_root,
                    std::slice::from_ref(&claims.wiring),
                    &openings.wiring,
                ),
                raw(
                    &quotient_layout(log_rows),
                    &roots[1],
                    &[claims.quotient.clone(), claims.sum.clone()],
                    &openings.quotient,
                ),
            ],
        }
    }

    /// The Rust verifier on the raw form: the reduction, then the three openings.
    fn accepts(&self) -> bool {
        let proof = Proof {
            stream: self.stream.clone(),
        };
        let Ok((roots, claims)) = verify(&self.index_root, &self.statement, &proof, self.log_rows) else {
            return false;
        };
        let Claims {
            witness,
            wiring,
            quotient,
            sum,
        } = claims;
        opening::verify(
            &witness_layout(self.log_rows),
            &roots[0],
            &[witness],
            &self.openings[0].proof(),
        )
        .is_ok()
            && opening::verify(
                &wiring_layout(self.log_rows),
                &self.index_root,
                &[wiring],
                &self.openings[1].proof(),
            )
            .is_ok()
            && opening::verify(
                &quotient_layout(self.log_rows),
                &roots[1],
                &[quotient, sum],
                &self.openings[2].proof(),
            )
            .is_ok()
    }

    fn line(&self) -> String {
        let mut out = String::new();
        head(
            &mut out,
            "P",
            self.log_rows,
            &self.index_root,
            &self.statement,
            &self.stream,
        );
        for opening in &self.openings {
            opening.tokens(&mut out);
        }
        out.push_str(if self.accepts() { " ACCEPT" } else { " REJECT" });
        out
    }
}

/// The tampered variants of an honest proof, each named.
fn tampered(honest: &Whole) -> Vec<(&'static str, Whole)> {
    let mut cases: Vec<(&'static str, Whole)> = Vec::new();
    let mut add = |name, f: &dyn Fn(&mut Whole)| {
        let mut w = honest.clone();
        f(&mut w);
        cases.push((name, w));
    };
    add("value", &|w| w.stream[4] += F192::ONE);
    add("next", &|w| w.stream[8] += F192::Y);
    add("witness root", &|w| w.stream[0].c0 ^= 1);
    add("root not two halves", &|w| w.stream[3].c2 = 1);
    add("statement", &|w| w.statement.root[3] ^= 0x10);
    add("index root", &|w| w.index_root[0] ^= 1);
    add("whir scalar", &|w| w.openings[0].stream[5].c1 ^= 1 << 7);
    add("whir trailing scalar", &|w| {
        w.openings[2].stream.push(verifier::E::new(0, 0, 0))
    });
    add("whir truncated", &|w| {
        w.openings[1].stream.pop();
    });
    add("leaf word", &|w| w.openings[2].paths[3].leaf[7].0 ^= 1 << 40);
    add("sibling", &|w| w.openings[1].paths[0].siblings[2][5] ^= 0x01);
    add("missing path", &|w| {
        w.openings[0].paths.pop();
    });
    add("extra path", &|w| {
        let p = w.openings[2].paths[0].clone();
        w.openings[2].paths.push(p)
    });
    add("short leaf", &|w| {
        w.openings[0].paths[1].leaf.pop();
    });
    cases
}

/// A small circuit with the membership statement's shape: 256 input bits, some rows of XORs, and the inputs as
/// both public values, `y = root = x`.
fn small() -> Circuit {
    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let mut acc = x[0];
    for (i, &bit) in x.iter().enumerate().skip(1) {
        acc = if i % 3 == 0 {
            b.chi(acc, bit, x[(i * 7) % 256])
        } else {
            b.xor(acc, bit)
        };
    }
    let _ = b.not(acc);
    b.finish(17, &public_words(&x, &x))
}

/// A circuit of one Keccak-256 of a 64-byte block, `root = H(x ‖ x)` (as `protocol.rs`'s test `toy`).
fn toy() -> Circuit {
    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
    b.finish(17, &public_words(&x, &digest))
}

/// An `I` line: a circuit's size, its inputs and its commitment, which the Lean builder must reproduce.
fn index_line(name: &str, circuit: &Circuit) -> String {
    let root = commit(&Index::new(circuit).table).root;
    format!(
        "I {name} {} {} {} {}",
        circuit.log_rows,
        circuit.used_rows,
        circuit.n_inputs(),
        hex_hash(&root)
    )
}

/// A `Q` line: the honest prover's inputs (the circuit by name, its input bits as bytes, the tables' seed, the
/// masks) and the reduction's stream it sends, which the Lean prover must reproduce.
fn prover_line(name: &str, inputs: &[bool], seed: &[u8; 32], masks: &[[F64; 3]; 4], stream: &[F192]) -> String {
    let mut out = format!("Q {name} {}", inputs.len());
    for byte in inputs.chunks(8) {
        let value = byte
            .iter()
            .enumerate()
            .fold(0u8, |acc, (i, &bit)| acc | (bit as u8) << i);
        write!(out, " {value:02x}").unwrap();
    }
    write!(out, " {}", hex_hash(seed)).unwrap();
    for coeffs in masks {
        for coeff in coeffs {
            write!(out, " {:016x}", coeff.0).unwrap();
        }
    }
    write!(out, " {}", stream.len()).unwrap();
    for &x in stream {
        write!(out, " {}", hex_e(x)).unwrap();
    }
    out
}

fn proofs(lines: &mut Vec<String>, rng: &mut Rng, name: &str, circuit: &Circuit, cases: &[(Statement, Vec<bool>)]) {
    let index = Index::new(circuit);
    let index_committed = commit(&index.table);
    for (statement, inputs) in cases {
        let cells = circuit.cells(inputs);
        // The proof's seed; the masks and the tables' padding seed are derived from it (`Randomness::derive`).
        let seed = random_hash(rng);
        let randomness = Randomness::derive(&seed, &index_committed.root, statement, &cells);
        let proved = prove_with_seed(circuit, &index, &index_committed.root, statement, &cells, &seed);
        assert!(proved.fits);
        lines.push(prover_line(
            name,
            inputs,
            &randomness.padding,
            &randomness.masks,
            &proved.proof.stream,
        ));
        let (stream, roots, claims) = (proved.proof.stream.clone(), proved.roots, proved.claims.clone());
        let openings = open(proved.tables, &claims, &index, &index_committed);
        let honest = Whole::of(
            circuit.log_rows,
            &index_committed.root,
            statement,
            &stream,
            &roots,
            &claims,
            &openings,
        );
        assert!(honest.accepts(), "the honest proof is accepted");
        lines.push(reduction_line(
            circuit.log_rows,
            &index_committed.root,
            statement,
            &stream,
        ));
        lines.push(honest.line());
        for (name, case) in tampered(&honest) {
            assert!(!case.accepts(), "the tampered proof ({name}) is rejected");
            lines.push(case.line());
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out = args.get(1).cloned().unwrap_or_else(|| "vectors.txt".into());
    let full = args.iter().any(|a| a == "--full");
    let mut rng = Rng::new(0x5747_A7E5);
    let mut lines = Vec::new();

    // The reduction on random streams, at sizes the layouts take (`2^17` to `2^22` rows) and two they do not.
    for (log_rows, count) in [(16usize, 10), (17, 40), (20, 20), (22, 40), (23, 10)] {
        for case in 0..count {
            let index_root = random_hash(&mut rng);
            let statement = Statement {
                y: random_hash(&mut rng),
                root: random_hash(&mut rng),
            };
            let mut stream: Vec<F192> = (0..9).map(|_| random_e(&mut rng)).collect();
            for root in [0, 2] {
                stream[root].c2 = 0;
                stream[root + 1].c2 = 0;
            }
            match case % 10 {
                3 => stream[1].c2 = 5,
                6 => stream[2].c2 = 1,
                7 => {
                    stream.pop();
                }
                8 => stream.push(random_e(&mut rng)),
                9 => stream.truncate(3),
                _ => {}
            }
            lines.push(reduction_line(log_rows, &index_root, &statement, &stream));
        }
    }

    // Whole proofs on a small circuit.
    let circuit = small();
    let cases: Vec<(Statement, Vec<bool>)> = (0..1)
        .map(|_| {
            let x = random_hash(&mut rng);
            let inputs = (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect();
            (Statement { y: x, root: x }, inputs)
        })
        .collect();
    proofs(&mut lines, &mut rng, "small", &circuit, &cases);

    // The circuits' commitments, which the Lean builder must reproduce.
    lines.push(index_line("small", &circuit));
    lines.push(index_line("toy", &toy()));
    if args.iter().any(|a| a == "--index") || full {
        lines.push(index_line("membership", &membership()));
    }

    // The membership circuit itself.
    if full {
        let circuit = membership();
        let secret = Secret {
            x: random_hash(&mut rng),
            siblings: std::array::from_fn::<_, DEPTH, _>(|_| random_hash(&mut rng)),
            directions: rng.next_u64() as u32,
        };
        proofs(
            &mut lines,
            &mut rng,
            "membership",
            &circuit,
            &[(secret.statement(), membership_inputs(&secret))],
        );
    }

    std::fs::write(&out, lines.join("\n") + "\n").expect("the vectors are written");
    println!("{} vectors written to {out}", lines.len());
}
