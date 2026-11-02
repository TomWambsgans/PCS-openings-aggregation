#!/bin/sh
# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
# Makes a checkout of leanVM (https://github.com/leanEthereum/leanVM) at commit 42422001 write its execution trace for
# the univariate prover: `sh apply.sh <leanVM checkout>`. Then any proof leanVM makes with `LEANVM_TRACE_DUMP=<dir>`
# set writes the trace to <dir> (trace_dump.rs) and goes on unchanged, e.g. with the gas-dump command of
# crates/leanvm_flock_gas/dump (applied first):
#   LEANVM_TRACE_DUMP=<dir>/xmss1000 cargo run --release -p leanvm-cli -- --log-inv-rate 1 gas-dump --xmss 1000 --out <dir>/proof1000
set -e
here=$(cd "$(dirname "$0")" && pwd)
cd "$1"
cp "$here/trace_dump.rs" crates/leanvm_core/src/cpu/trace_dump.rs
python3 - <<'PY'
p = 'crates/leanvm_core/src/cpu/mod.rs'
s = open(p).read()
assert 'mod trace_dump;' not in s, 'already applied'
s = s.replace("mod trace;\n", "mod trace;\nmod trace_dump;\n", 1)
anchor = '    let w = crate::stage!("Build witness", || program.build(&exec));\n'
assert anchor in s
s = s.replace(anchor, anchor + "    trace_dump::maybe_dump(program, &w);\n", 1)
open(p, 'w').write(s)
p = 'crates/leanvm_core/src/hash_flock.rs'
s = open(p).read()
s += '''
/// Trace dump (PCS-openings-aggregation's univariate prover), not leanVM: the reduction's inputs as they are.
impl PreparedReductionWitness {
    pub(crate) fn dump_parts(&self) -> (usize, &[u64], &[u64], &[u64], &[u8]) {
        (self.n_blocks, &self.z_packed, &self.a_packed, &self.b_packed, &self.z_lincheck)
    }
}
'''
open(p, 'w').write(s)
PY
grep -n "trace_dump" crates/leanvm_core/src/cpu/mod.rs
