// Part of this repository. The round constants, rotations and lane permutation are Keccak's (FIPS 202), as in this
// repository's crates/primitives/src/hash.rs (vendored from leanVM) and used by crates/quotient/src/circuit.rs, whose
// Keccak-f wiring (lane `x + 5y`, bit `z` at index `z`, lane `i` rotated by `RHO[i]` to `PI[i]`) this follows. MIT OR
// Apache-2.0; see NOTICE.md.
//! Keccak-f\[1600\] and Keccak-256 as rows (SPEC-REC.md §2.4.1, §2.4.2, §2.6).
//!
//! - [`D32`]: D32v's template (§2.6). One row per `(round, z)` slice, 32 positions: the 25 lanes' χ inputs
//!   `b_j[·][z]` and the next θ's column parities of the slice before, `C_(j+1)[·][z−1]`, all pulled by expression
//!   slots. A row pushes `a'_(j+1) = A_j + C_(j+1)[x−1][z] + C_(j+1)[x+1][z−1]` (θ of the next round applied to χ's
//!   output, `A_j = χ(b) + RC`) to the next round's row `z + ρ`, role `π`, and its own parities `C_(j+1)[·][z]` to
//!   row `z + 1`. A preparation round applies the first θ, the last round is χ and ι only. No forwards: every value
//!   has one consumer. 25 rows of 64 a permutation, 51,200 positions.
//! - [`sponge`]: Keccak-256 over any [`Permutation`]: the first block's rate from the input bits and the padding
//!   (fresh constants), its capacity known zero; later blocks XORed into the rate; the digest the first four lanes.

use leanvm_flock_gas::field::K;

use super::layout::{Builder, PolyBuilder, Units, Value, forwards};
use super::spec::{Formula, Poly};

/// The round constants.
pub const RC: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// ρ's left rotation of lane `x + 5y`.
pub const RHO: [usize; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// Where π sends lane `x + 5y`: lane `y + 5·((2x + 3y) mod 5)`.
pub const PI: [usize; 25] = {
    let mut p = [0usize; 25];
    let mut i = 0;
    while i < 25 {
        let (x, y) = (i % 5, i / 5);
        p[i] = y + 5 * ((2 * x + 3 * y) % 5);
        i += 1;
    }
    p
};

/// Keccak-256's rate, in lanes and bits.
pub const RATE_LANES: usize = 17;
pub const RATE_BITS: usize = 64 * RATE_LANES;

/// Keccak-f\[1600\] in rows.
pub trait Permutation {
    /// The permutation of `input` (index `64·lane + z`), whose constant bits it makes from `constants` (after
    /// offering its rows' spare slots to it). Returns the output's 1600 values.
    fn permute(&mut self, b: &mut Builder, constants: &mut Constants, input: &[Bit]) -> Vec<Value>;
}

/// Fresh constants: one expression slot each, pushing `κ` (its pull is a free end). The slots are other regions'
/// spare roles (formula 0) when offered, else rows of their own.
pub struct Constants {
    units: Option<Units>,
    spare: Vec<(u32, usize)>,
    /// Constants made, and the rows of their own.
    pub made: usize,
    pub own_rows: usize,
}

/// A spare role: an expression slot pushing 0, which a constant may take (`κ`) or which stays dead.
pub fn spare() -> Formula {
    Formula::Expr(Poly::default())
}

impl Constants {
    pub fn new() -> Self {
        Self {
            units: None,
            spare: Vec::new(),
            made: 0,
            own_rows: 0,
        }
    }

    /// Offer a spare role (its formula [`spare`]).
    pub fn offer(&mut self, row: u32, role: usize) {
        self.spare.push((row, role));
    }

    /// A new value of word `k`.
    pub fn fresh(&mut self, b: &mut Builder, k: K) -> Value {
        self.made += 1;
        let (row, role) = match self.spare.pop() {
            Some(slot) => slot,
            None => {
                let units = self.units.get_or_insert_with(|| {
                    let w = b.width();
                    let r = b.region("const", (0..w).map(|_| spare()).collect());
                    Units::new(r, 1, w)
                });
                let (row, role) = units.next(b);
                if role == 0 {
                    self.own_rows += 1;
                }
                (row, role)
            }
        };
        b.set_kappa(row, role, k);
        b.produce(row, role)
    }
}

impl Default for Constants {
    fn default() -> Self {
        Self::new()
    }
}

/// χ's output at lane `l` as a polynomial of the row's χ inputs (`cell l` = `b[l]`): `b + b₂ + b₁·b₂`.
fn chi(l: usize) -> PolyBuilder {
    let (x, y) = (l % 5, l / 5);
    let (l1, l2) = ((x + 1) % 5 + 5 * y, (x + 2) % 5 + 5 * y);
    PolyBuilder::new().linear(l, 1).linear(l2, 1).quadratic(l1, l2, 1)
}

/// The identity at lane `l` (the preparation round), zero on a known-zero lane.
fn identity(l: usize, zero: bool) -> PolyBuilder {
    if zero {
        PolyBuilder::new()
    } else {
        PolyBuilder::new().linear(l, 1)
    }
}

/// D32v's Keccak-f (SPEC-REC.md §2.6).
pub struct D32 {
    prep: u16,
    prep_first: u16,
    round: u16,
    last: u16,
}

/// The column-parity roles of a D32v row.
const C_ROLE: usize = 25;

impl D32 {
    pub fn new(b: &mut Builder) -> Self {
        assert_eq!(b.width(), 32, "D32v's rows are 32 positions");
        // A row: `A(l)` the lane function (χ, or the identity in preparation), its parities `C[x]`, the pulled parities
        // `cell 25 + x` = `C[x][z−1]`. Roles `l`: `A(l) + C[x−1] + Cp[x+1]`; roles `25 + x`: `C[x]`.
        let theta = |a: &dyn Fn(usize) -> PolyBuilder| -> Vec<Formula> {
            let c = |x: usize| {
                let mut p = PolyBuilder::new();
                for y in 0..5 {
                    p.add(&a(x + 5 * y));
                }
                p
            };
            let mut roles = forwards(32);
            for (l, role) in roles.iter_mut().enumerate().take(25) {
                let x = l % 5;
                let mut p = a(l);
                p.add(&c((x + 4) % 5));
                p.add_linear(C_ROLE + (x + 1) % 5, 1);
                *role = Formula::Expr(p.build());
            }
            for x in 0..5 {
                roles[C_ROLE + x] = Formula::Expr(c(x).build());
            }
            roles[30] = spare();
            roles[31] = spare();
            roles
        };
        let prep = b.region("keccak32/prep", theta(&|l| identity(l, false)));
        let prep_first = b.region("keccak32/prep-first", theta(&|l| identity(l, l >= 25 - 8)));
        let round = b.region("keccak32/round", theta(&chi));
        let mut last: Vec<Formula> = (0..32).map(|_| spare()).collect();
        for (l, role) in last.iter_mut().enumerate().take(25) {
            *role = Formula::Expr(chi(l).build());
        }
        let last = b.region("keccak32/last", last);
        Self {
            prep,
            prep_first,
            round,
            last,
        }
    }

    /// The roles a round constant's one at the row's `z` adds to: those whose push has `A[0,0]`.
    fn rc_roles() -> [usize; 7] {
        [0, 1, 6, 11, 16, 21, C_ROLE]
    }
}

impl Permutation for D32 {
    fn permute(&mut self, b: &mut Builder, constants: &mut Constants, input: &[Bit]) -> Vec<Value> {
        assert_eq!(input.len(), 1600);
        let capacity_zero = input[64 * RATE_LANES..].iter().all(|&x| x == Bit::Zero);
        let region = if capacity_zero { self.prep_first } else { self.prep };
        // Every round's rows first, their spare roles offered to the constants (the input's among them).
        let rows: Vec<u32> = (0..64).map(|_| b.row(region)).collect();
        let mut rounds: Vec<Vec<u32>> = (0..24)
            .map(|j| {
                (0..64)
                    .map(|_| b.row(if j == 23 { self.last } else { self.round }))
                    .collect()
            })
            .collect();
        for &row in &rows {
            constants.offer(row, 30);
            constants.offer(row, 31);
        }
        for (j, round) in rounds.iter().enumerate() {
            for &row in round {
                for role in if j == 23 { 25..32 } else { 30..32 } {
                    constants.offer(row, role);
                }
            }
        }
        rounds.reverse();
        for l in 0..25 {
            if capacity_zero && l >= RATE_LANES {
                continue;
            }
            for z in 0..64 {
                let v = match input[64 * l + z] {
                    Bit::V(v) => v,
                    Bit::Zero => constants.fresh(b, K(0)),
                    Bit::One => constants.fresh(b, K(1)),
                };
                b.place(rows[z], l, v);
            }
        }
        let mut pushed = self.theta_round(b, &rows, None);
        for (j, &rc) in RC.iter().enumerate() {
            let last = j == 23;
            let rows = rounds.pop().expect("a round's rows");
            // ρ and π: lane `l`'s bit `z` goes to row `z + ρ_l`, role `π_l`.
            for l in 0..25 {
                for (z, &v) in pushed[l].iter().enumerate() {
                    b.place(rows[(z + RHO[l]) % 64], PI[l], v);
                }
            }
            if last {
                let mut out = vec![0; 1600];
                for (z, &row) in rows.iter().enumerate() {
                    if rc >> z & 1 == 1 {
                        b.set_kappa(row, 0, K(1));
                    }
                    for l in 0..25 {
                        out[64 * l + z] = b.produce(row, l);
                    }
                }
                return out;
            }
            pushed = self.theta_round(b, &rows, Some(rc));
        }
        unreachable!()
    }
}

impl D32 {
    /// A round's rows with their lane cells placed: the parities, wired to the next slice, then the lanes' pushes.
    /// Returns each lane's 64 pushed values.
    fn theta_round(&self, b: &mut Builder, rows: &[u32], rc: Option<u64>) -> Vec<Vec<Value>> {
        if let Some(rc) = rc {
            for (z, &row) in rows.iter().enumerate() {
                if rc >> z & 1 == 1 {
                    for role in Self::rc_roles() {
                        b.set_kappa(row, role, K(1));
                    }
                }
            }
        }
        let c: Vec<[Value; 5]> = rows
            .iter()
            .map(|&row| std::array::from_fn(|x| b.produce(row, C_ROLE + x)))
            .collect();
        for z in 0..64 {
            for x in 0..5 {
                b.place(rows[(z + 1) % 64], C_ROLE + x, c[z][x]);
            }
        }
        (0..25)
            .map(|l| rows.iter().map(|&row| b.produce(row, l)).collect())
            .collect()
    }
}

/// One input bit of a Keccak-256 call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bit {
    /// A value that may end at the permutation's slot (it has no other slot placement).
    V(Value),
    Zero,
    One,
}

/// XOR units for the later blocks: `a ⊕ b` at the slot reading its own pull `a` and the forward `b`.
pub struct Xors {
    units: Units,
}

impl Xors {
    pub fn new(b: &mut Builder) -> Self {
        let w = b.width();
        let mut roles = forwards(w);
        for u in 0..w / 2 {
            roles[2 * u] = Formula::Expr(PolyBuilder::new().linear(2 * u, 1).linear(2 * u + 1, 1).build());
        }
        let r = b.region("xor", roles);
        Self {
            units: Units::new(r, 2, w / 2),
        }
    }

    /// `a ⊕ b`: `a` ends here, `b` is forwarded.
    pub fn xor(&mut self, bld: &mut Builder, a: Value, b: Value) -> Value {
        let (row, base) = self.units.next(bld);
        bld.place(row, base, a);
        bld.place(row, base + 1, b);
        bld.produce(row, base)
    }
}

/// Keccak-256's sponge on rows.
pub struct Sponge<P: Permutation> {
    pub permutation: P,
    pub constants: Constants,
    pub xors: Xors,
    /// Permutations run.
    pub permutations: usize,
}

impl<P: Permutation> Sponge<P> {
    pub fn new(b: &mut Builder, permutation: P) -> Self {
        Self {
            permutation,
            constants: Constants::new(),
            xors: Xors::new(b),
            permutations: 0,
        }
    }

    /// Keccak-256 of `message` (bits in byte order, low bit first): the digest's 256 bits, likewise.
    pub fn keccak256(&mut self, b: &mut Builder, message: &[Bit]) -> Vec<Value> {
        assert!(message.len().is_multiple_of(8), "whole bytes");
        let blocks = message.len() / RATE_BITS + 1;
        let padded_len = blocks * RATE_BITS;
        // pad10*1: 0x01 after the message, 0x80 in the last byte.
        let bit_of = |i: usize| -> Bit {
            if i < message.len() {
                message[i]
            } else if i == message.len() || i == padded_len - 1 {
                Bit::One
            } else {
                Bit::Zero
            }
        };
        let mut state: Vec<Value> = Vec::new();
        for block in 0..blocks {
            let mut input: Vec<Bit> = vec![Bit::Zero; 1600];
            for (i, slot) in input.iter_mut().enumerate().take(RATE_BITS) {
                let bit = bit_of(block * RATE_BITS + i);
                *slot = if block == 0 {
                    bit
                } else {
                    Bit::V(match bit {
                        Bit::V(v) => self.xors.xor(b, state[i], v),
                        Bit::Zero => state[i],
                        Bit::One => {
                            let one = self.constants.fresh(b, K(1));
                            self.xors.xor(b, state[i], one)
                        }
                    })
                };
            }
            if block > 0 {
                for i in RATE_BITS..1600 {
                    input[i] = Bit::V(state[i]);
                }
            }
            state = self.permutation.permute(b, &mut self.constants, &input);
            self.permutations += 1;
        }
        state[..256].to_vec()
    }
}

/// Keccak-f\[1600\] on lanes, the reference.
pub fn keccak_f(a: &mut [u64; 25]) {
    for &rc in &RC {
        let c: [u64; 5] = std::array::from_fn(|x| (0..5).fold(0, |acc, y| acc ^ a[x + 5 * y]));
        for i in 0..25 {
            a[i] ^= c[(i + 4) % 5] ^ c[(i + 1) % 5].rotate_left(1);
        }
        let mut b = [0u64; 25];
        for i in 0..25 {
            b[PI[i]] = a[i].rotate_left(RHO[i] as u32);
        }
        for y in 0..5 {
            for x in 0..5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
            }
        }
        a[0] ^= rc;
    }
}
