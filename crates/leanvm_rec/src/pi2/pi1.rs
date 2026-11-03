// Part of this repository. The mapping of π1's call words follows `crate::circuit::compile` (the ports). MIT OR
// Apache-2.0; see NOTICE.md.
//! π1's five `PCS_OPEN` calls as the circuit's interface names their words (`circuit::spec::CallWord`), from π1-rec's
//! recorded verifier (`leanvm_univariate::contract`, 1,000-signature reference shape): constants, π1's two roots
//! (`C1`, `C2`), and its claims' distinct elements in first appearance. The contract of a synthetic circuit appends
//! these, its words from calldata, as the real circuit's contract does.

use std::collections::BTreeMap;

use leanvm_flock_gas::evm::codegen::Word;
use leanvm_flock_gas::evm::record::Node;
use leanvm_flock_gas::field::E;
use leanvm_univariate::contract::{calls, record_verifier};
use leanvm_univariate::{Blake2s, Claims, FLOCK_REC};

use crate::REFERENCE;
use crate::circuit::spec::{CallWord, element_word};

/// π1's calls, and how many roots and elements their words name.
#[derive(Clone, Debug)]
pub struct Pi1Calls {
    pub calls: Vec<Vec<CallWord>>,
    pub roots: usize,
    pub elements: usize,
}

/// π1-rec's calls at the reference shape. Records π1's verifier: run it on a thread with a deep stack.
pub fn pi1_calls() -> Pi1Calls {
    let recorded = record_verifier(&REFERENCE, Blake2s::Flock(FLOCK_REC), Claims::Point);
    let graph = &recorded.graph;
    let roots: BTreeMap<usize, u32> = recorded
        .roots_at
        .iter()
        .enumerate()
        .map(|(i, &at)| (at, i as u32))
        .collect();
    let mut element_of: BTreeMap<u32, u32> = BTreeMap::new();
    let out: Vec<Vec<CallWord>> = calls(&recorded)
        .iter()
        .map(|call| {
            call.iter()
                .map(|w| match *w {
                    Word::Const(bytes) => CallWord::Const(bytes),
                    Word::Stream(at) => CallWord::Root(roots[&at]),
                    Word::Node(id) => match graph.nodes[id as usize] {
                        Node::Const([c0, c1, c2]) => CallWord::Const(element_word(E::new(c0, c1, c2))),
                        _ => {
                            let next = element_of.len() as u32;
                            CallWord::Element(*element_of.entry(id).or_insert(next))
                        }
                    },
                    Word::Stored(_) => panic!("π1's contract stores nothing"),
                })
                .collect()
        })
        .collect();
    Pi1Calls {
        calls: out,
        roots: roots.len(),
        elements: element_of.len(),
    }
}
