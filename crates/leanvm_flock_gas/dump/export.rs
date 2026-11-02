
// Part of PCS-openings-aggregation (crates/leanvm_flock_gas/dump), appended to leanVM's
// crates/rec_aggregation/src/aggregation.rs by apply.sh. MIT OR Apache-2.0.
/// Gas study (`leanvm_flock_gas` in PCS-openings-aggregation): not part of leanVM.
impl EthereumProof {
    /// The stacked bytecode's words, the public input as the `verifier` crate takes it, the proof in that crate's
    /// raw transport (the stream as 24-byte little-endian elements; the openings as every query's leaf words then its
    /// siblings, in the order the verifier reads them), and the verifier's summary.
    pub fn export_for_gas(&self) -> (Vec<u64>, [u8; 32], Vec<u8>, Vec<u8>, verifier::Summary) {
        let bytecode: Vec<u64> = stacked_bytecode().iter().map(|word| word.0).collect();
        let public_input = public_input_bytes(&self.public_input());
        let proof = scalar_proof(&self.proof);
        let summary = verifier::verify_execution(scalar_bytecode(), &public_input, &proof).expect("the proof verifies");
        let stream: Vec<u8> = proof
            .stream
            .iter()
            .flat_map(|e| [e.c0, e.c1, e.c2])
            .flat_map(u64::to_le_bytes)
            .collect();
        let mut raw = Vec::new();
        for path in &summary.merkle_paths {
            for word in &path.leaf {
                raw.extend(word.0.to_le_bytes());
            }
            for sibling in &path.siblings {
                raw.extend(sibling);
            }
        }
        let reloaded = verifier::Proof::load(&stream, &raw).expect("whole elements");
        let again = verifier::verify_execution(scalar_bytecode(), &public_input, &reloaded).expect("the raw form verifies");
        assert_eq!(again.table_rows, summary.table_rows);
        (bytecode, public_input, stream, raw, summary)
    }
}
