// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/evm/src/contract.rs: its `Recorder`. MIT OR Apache-2.0; see NOTICE.md.
//! The proof as the recorder reads it: every read and every challenge is a node of the graph the contract is
//! compiled from.

use quotient::protocol::Channel;
use quotient::transcript::TranscriptError;

use crate::record::{MAX_ABSORBED, Node, Sym};

pub(crate) struct Recorder {
    state: Sym,
    /// Read since the last challenge.
    pending: Vec<Sym>,
    roots: u8,
    pub(crate) read: u16,
}

impl Recorder {
    pub(crate) fn new() -> Self {
        Self {
            state: Sym::new(Node::Seed),
            pending: Vec::new(),
            roots: 0,
            read: 0,
        }
    }
}

impl Channel<Sym> for Recorder {
    fn statement(&mut self) -> [Sym; 4] {
        std::array::from_fn(|k| Sym::new(Node::Statement(k as u8)))
    }

    fn next_root(&mut self) -> Result<[Sym; 2], TranscriptError> {
        let scalars = std::array::from_fn(|k| Sym::new(Node::Root(2 * self.roots + k as u8)));
        self.roots += 1;
        self.pending.extend(scalars);
        Ok(scalars)
    }

    fn next(&mut self) -> Result<Sym, TranscriptError> {
        let scalar = Sym::new(Node::Input(self.read));
        self.read += 1;
        self.pending.push(scalar);
        Ok(scalar)
    }

    fn sample(&mut self) -> Sym {
        let mut scalars = [0; MAX_ABSORBED];
        for (slot, scalar) in scalars.iter_mut().zip(&self.pending) {
            *slot = scalar.0;
        }
        assert!(
            self.pending.len() <= MAX_ABSORBED,
            "a challenge follows too many scalars"
        );
        self.state = Sym::new(Node::Hash(self.state.0, scalars, self.pending.len() as u8));
        self.pending.clear();
        Sym::new(Node::Low(self.state.0))
    }

    fn finish(&mut self) -> Result<(), TranscriptError> {
        Ok(())
    }
}
