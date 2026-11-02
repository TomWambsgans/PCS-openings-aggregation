//! Gas study (`leanvm_flock_gas` in PCS-openings-aggregation): not part of leanVM. Prove one leaf aggregate and write
//! what the gas study reads: the bytecode, the public input, the proof's stream and raw openings, and its shape.

use std::io::Write;

pub fn run(xmss: usize, sphincs: usize, log_inv_rate: usize, out: &std::path::Path) {
    leanvm_core::init_prover();
    rec_aggregation::warm_up();
    let raw: Vec<_> = if xmss == 0 {
        Vec::new()
    } else {
        rec_aggregation::signers_cache::get_signers(xmss)[..xmss]
            .iter()
            .map(|(pk, sig)| (*pk, rec_aggregation::signers_cache::message(), sig.clone()))
            .collect()
    };
    let raw_sphincs = if sphincs == 0 {
        Vec::new()
    } else {
        rec_aggregation::signers_cache::get_lean_sphincs_signers(sphincs)[..sphincs].to_vec()
    };
    let started = std::time::Instant::now();
    let (sig, stats) =
        rec_aggregation::aggregate_with_stats(&[], raw, raw_sphincs, &[], None, log_inv_rate).expect("leaf aggregates");
    let proving = started.elapsed();
    sig.verify().expect("verifies");
    let (bytecode, public_input, stream, merkle, summary) = sig.export_for_gas();
    std::fs::create_dir_all(out).unwrap();
    let words: Vec<u8> = bytecode.iter().flat_map(|w| w.to_le_bytes()).collect();
    std::fs::write(out.join("bytecode.bin"), words).unwrap();
    std::fs::write(out.join("public_input.bin"), public_input).unwrap();
    std::fs::write(out.join("stream.bin"), &stream).unwrap();
    std::fs::write(out.join("merkle.bin"), &merkle).unwrap();
    let mut shape = std::fs::File::create(out.join("shape.txt")).unwrap();
    writeln!(shape, "xmss {xmss}").unwrap();
    writeln!(shape, "sphincs {sphincs}").unwrap();
    writeln!(shape, "log_inv_rate {}", summary.log_inv_rate).unwrap();
    writeln!(shape, "log_memory {}", summary.log_memory).unwrap();
    writeln!(shape, "table_rows {:?}", summary.table_rows).unwrap();
    writeln!(shape, "bytecode_words {}", bytecode.len()).unwrap();
    writeln!(shape, "stream_elements {}", stream.len() / 24).unwrap();
    writeln!(shape, "flock_stream_end {}", summary.flock_stream_end).unwrap();
    writeln!(shape, "merkle_bytes {}", merkle.len()).unwrap();
    writeln!(shape, "cycles {}", stats.cycles).unwrap();
    writeln!(shape, "details {}", stats.details()).unwrap();
    writeln!(shape, "proving_seconds {:.3}", proving.as_secs_f64()).unwrap();
    println!("{}", std::fs::read_to_string(out.join("shape.txt")).unwrap());
}
