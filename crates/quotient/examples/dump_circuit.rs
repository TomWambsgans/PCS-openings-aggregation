// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The membership circuit as bytes, for the differential test against its Lean transcription
//! (`formal/Circuit`, `lake exe dump-circuit`, which writes the same format): `cargo run --release -p quotient
//! --example dump_circuit -- OUT`, then compare the two files' SHA-256.
//!
//! The format, little-endian `u32`s: the number of rows, the rows used, the number of inputs; each row's `X, Y, C`
//! sources (`0` zero, `1` one, `2 + r` row `r`); the input rows; σ. It then prints the public words the circuit
//! computes for a fixed secret, next to the statement's.

use quotient::circuit::{PUBLIC_ROWS, Src, WORD_BITS, membership, membership_inputs, read};
use quotient::statement::Secret;

fn code(src: Src) -> u32 {
    match src {
        Src::Zero => 0,
        Src::One => 1,
        Src::Row(r) => r + 2,
    }
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: dump_circuit OUT");
    let circuit = membership();
    println!(
        "rows {} used {} inputs {} sigma {}",
        circuit.rows.len(),
        circuit.used_rows,
        circuit.inputs.len(),
        circuit.sigma.len()
    );
    let mut out: Vec<u8> = Vec::with_capacity(4 * (3 + 3 * circuit.rows.len() + circuit.inputs.len() + circuit.sigma.len()));
    let mut push = |x: u32| out.extend_from_slice(&x.to_le_bytes());
    push(circuit.rows.len() as u32);
    push(circuit.used_rows as u32);
    push(circuit.inputs.len() as u32);
    for row in &circuit.rows {
        push(code(row.x));
        push(code(row.y));
        push(code(row.c));
    }
    for &r in &circuit.inputs {
        push(r);
    }
    for &s in &circuit.sigma {
        push(s);
    }
    std::fs::write(&path, &out).expect("write");

    // The secret `CircuitTest/Dump.lean` uses.
    let secret = Secret {
        x: std::array::from_fn(|i| (i * 37 + 11) as u8),
        siblings: std::array::from_fn(|l| std::array::from_fn(|i| (l * 101 + i * 13 + 5) as u8)),
        directions: 0xA5C3_1E77,
    };
    let v = circuit.outputs(&membership_inputs(&secret));
    let halves = secret.statement().halves();
    for (word, half) in halves.iter().enumerate() {
        let mut w: u128 = 0;
        for j in 0..WORD_BITS {
            let r = word * (WORD_BITS / 2) + j / 2;
            let src = if j % 2 == 0 { circuit.rows[r].x } else { circuit.rows[r].y };
            w |= (read(&v, src) as u128) << j;
        }
        let expected = (half.c0 as u128) | ((half.c1 as u128) << 64);
        println!("word {word}: circuit {w:032x} statement {expected:032x}");
    }
    let _ = PUBLIC_ROWS;
}
