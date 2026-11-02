#!/bin/sh
# Applies the gas-study dump to the copy of leanVM 42422001 in /root/pcs-quotient-fv/leanvm-flock-gas/leanvm-42422001.
set -e
cd /root/pcs-quotient-fv/leanvm-flock-gas/leanvm-42422001
cat ../patch/export.rs >> crates/rec_aggregation/src/aggregation.rs
cp ../patch/dump.rs bins/leanvm/src/dump.rs
python3 - <<'PY'
import re
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
