// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! A probe of pi1-rec's graph for the compiler (temporary).
use leanvm_flock_gas::evm::codegen::Word;
use leanvm_flock_gas::evm::record::Node;
use leanvm_rec::REFERENCE;
use leanvm_rec::count::{live, outputs};
use leanvm_univariate::contract::{calls, record_verifier};
use leanvm_univariate::{Blake2s, Claims, FLOCK_REC};
use std::collections::BTreeMap;

fn main() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            let r = record_verifier(&REFERENCE, Blake2s::Flock(FLOCK_REC), Claims::Point);
            let g = &r.graph;
            let l = live(g, outputs(&r));
            let mut bits: BTreeMap<(u8, u8), usize> = BTreeMap::new();
            let mut inputs: BTreeMap<u8, (usize, usize)> = BTreeMap::new();
            let mut bits_of_bits = 0;
            let mut statements = 0;
            for (id, n) in g.nodes.iter().enumerate() {
                match *n {
                    Node::Bits(v, s, w) => {
                        if l[id] {
                            *bits.entry((s, w)).or_default() += 1;
                        }
                        if matches!(g.nodes[v as usize], Node::Bits(..)) {
                            bits_of_bits += 1;
                        }
                    }
                    Node::Input { len, .. } => {
                        let e = inputs.entry(len).or_default();
                        e.0 += 1;
                        if l[id] {
                            e.1 += 1;
                        }
                    }
                    Node::Statement(_) if l[id] => statements += 1,
                    _ => {}
                }
            }
            println!("bits (shift,width)->count {bits:?}");
            println!("bits of bits {bits_of_bits}; inputs len->(all,live) {inputs:?}; live statements {statements}");
            let (mut consts_in_calls, mut nodes_in_calls, mut streams) = (0, 0, vec![]);
            for call in calls(&r) {
                for w in call {
                    match w {
                        Word::Node(id) => {
                            nodes_in_calls += 1;
                            if matches!(g.nodes[id as usize], Node::Const(_)) {
                                consts_in_calls += 1;
                            }
                        }
                        Word::Stream(at) => streams.push(at),
                        _ => {}
                    }
                }
            }
            println!(
                "call nodes {nodes_in_calls}, consts {consts_in_calls}; stream words {streams:?}; roots_at {:?}; stream_len {}",
                r.roots_at, r.stream_len
            );
            let hashes: Vec<(u32, u32)> = g
                .nodes
                .iter()
                .filter_map(|n| if let Node::Hash(_, f, t) = *n { Some((f, t)) } else { None })
                .collect();
            println!("hashes {} first {:?} last {:?}", hashes.len(), &hashes[..3], hashes.last());
            println!("kernels {}, zero checks {}, nonzero {}", g.kernels.len(), g.zero.len(), g.nonzero.len());
            let mut direct = 0;
            for (id, n) in g.nodes.iter().enumerate() {
                if !l[id] {
                    continue;
                }
                if let Node::Add(a, b) | Node::Mul(a, b) = *n {
                    for x in [a, b] {
                        if let Node::Input { len, .. } = g.nodes[x as usize]
                            && len < 16
                        {
                            direct += 1;
                        }
                    }
                }
            }
            println!("integer inputs used directly in Add/Mul: {direct}");
        })
        .unwrap()
        .join()
        .unwrap();
}
