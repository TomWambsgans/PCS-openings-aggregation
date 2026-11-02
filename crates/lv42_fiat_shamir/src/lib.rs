// Part of this repository. The method names and `add_round_poly`'s body are leanVM's (https://github.com/leanEthereum/
// leanVM), commit 42422001, file crates/fiat_shamir/src/transcript.rs; the transcript is a trait here, so that flock's
// prover writes to whatever chain implements it (the univariate PIOP's Keccak-256 chain). MIT OR Apache-2.0; see
// NOTICE.md.
//! The transcript flock's prover (`crates/lv42_flock`) writes to.

pub mod transcript {
    use primitives::field::F192;

    /// What flock's prover does with a transcript: send scalars, draw challenges.
    pub trait Transcript {
        fn add_scalar(&mut self, x: F192);

        fn sample(&mut self) -> F192;

        fn sample_vec(&mut self, n: usize) -> Vec<F192> {
            (0..n).map(|_| self.sample()).collect()
        }

        fn add_scalars(&mut self, xs: &[F192]) {
            for &x in xs {
                self.add_scalar(x);
            }
        }

        /// leanVM's: a round polynomial's coefficients but the one the verifier derives (the constant with an eq
        /// factor, the linear one without).
        fn add_round_poly(&mut self, coeffs: &[F192], eq: bool) {
            assert!(coeffs.len() >= 2, "a round polynomial has at least two coefficients");
            let fixed = usize::from(!eq);
            for (i, &c) in coeffs.iter().enumerate() {
                if i != fixed {
                    self.add_scalar(c);
                }
            }
        }
    }

    /// leanVM's name for the prover's transcript, here any [`Transcript`] (which may borrow: the lifetime is elided
    /// where flock names it).
    pub type ProverState<'a> = dyn Transcript + 'a;
}
