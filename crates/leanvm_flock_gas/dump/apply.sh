#!/bin/sh
# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
# Adds `leanvm gas-dump` to a checkout of leanVM (https://github.com/leanEthereum/leanVM) at commit 42422001:
# `sh apply.sh <leanVM checkout>`, then, in the checkout,
# `cargo run --release -p leanvm-cli -- --log-inv-rate 1 gas-dump --xmss 1290 --out <dir>/xmss1290`.
# (At 4af2cddd, the Keccak version, `dump.rs`'s `flock_stream_end` line prints `summary.keccak_scalars` instead.)
set -e
here=$(cd "$(dirname "$0")" && pwd)
cd "$1"
cat "$here/export.rs" >> crates/rec_aggregation/src/aggregation.rs
cp "$here/dump.rs" bins/leanvm/src/dump.rs
python3 - <<'PY'
p = 'bins/leanvm/src/main.rs'
s = open(p).read()
s = s.replace("mod benchmark;\n", "mod benchmark;\nmod dump;\n", 1)
s = s.replace("""    /// Prove and verify Fibonacci in the exponent (demo).""", """    /// Gas study: prove one leaf aggregate and dump it.
    GasDump {
        #[arg(long, default_value = "0")]
        xmss: usize,
        #[arg(long, default_value = "0")]
        sphincs: usize,
        #[arg(long)]
        out: std::path::PathBuf,
    },
    /// Prove and verify Fibonacci in the exponent (demo).""", 1)
s = s.replace("""        Command::Fibonacci { n } => {""", """        Command::GasDump { xmss, sphincs, out } => {
            dump::run(xmss, sphincs, cli.log_inv_rate, &out);
        }
        Command::Fibonacci { n } => {""", 1)
open(p, 'w').write(s)
PY
grep -n "GasDump\|mod dump" bins/leanvm/src/main.rs
