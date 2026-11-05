// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6, crates/flock/src/quotient/circuit.rs: the wiring and the public rows
// are the same; the gate (one χ on bits instead of a full adder on GF(4)) and the hash (Keccak-256 instead of
// BLAKE2s) are new. MIT OR Apache-2.0; see NOTICE.md.
//! Rows of one gate and the permutation that wires them, and the circuit of the membership statement.
//!
//! **The gate.** A row has four cells, `X, Y, C, V`, and says `V = X + C + Y·C`. On bits that is
//! `X ⊕ (C ∧ ¬Y)`: Keccak's χ when `(X, Y, C)` are `(a[x], a[x+1], a[x+2])`, an XOR when `Y = 0`, a NOT when
//! `X = 1, Y = 0`. A free input bit is a row whose three inputs are wired to its own output, so the gate reads
//! `v = v + v + v^2`, that is `v^2 = v`. Every other row reads constants or rows before it, and the gate sends
//! bits to bits: by induction every cell is a bit, and the one the circuit computes.
//!
//! **Lane circuits** (`crates/slh_dsa/SPEC-FAST.md`, §4.3). The gate is an identity of `K = GF(2^64)`, and the
//! argument does not need the cells to be bits. A lane circuit has `K`-valued cells besides its bits:
//! - a **free-`K` row** ([`Builder::free_k`]) reads its own output as `X` and `1` as `Y`, so the gate reads
//!   `v = v + C + C`: any value;
//! - a product is one row ([`Builder::mul`]: `(X, Y, C) = (b, a, b)`, `V = a·b`), and with `Y` a bit `s`, `χ` is a
//!   lane mux: `X + C·(1 + s)`;
//! - a **port** ([`Builder::port`]) is a row at a reserved index of the port region, `(X, Y, C, V) = (O, 1, I, O)`:
//!   `O` free (or read from a row), `I` read from its source. Another argument (Flock, for Keccak-f) is to prove
//!   the region's cells; here they are only rows.
//!
//! Bits stay Boolean by the free-bit row's `v = v^2`, whose roots in `K` are `0` and `1`. The rows are evaluated
//! over `K` by [`Circuit::outputs_k`], in the order they were built.

use primitives::field::F64;
use primitives::hash::{PI, RC, RHO, ROUNDS, STATE_LANES};

use crate::statement::{DEPTH, LEAF_PAD, Secret, Y_PAD};

/// The rows holding the public bits: eight words of 128, two bits a row.
pub const PUBLIC_ROWS: usize = 512;
pub const WORD_BITS: usize = 128;
/// The membership circuit's rows: `2^LOG_ROWS`.
pub const LOG_ROWS: usize = 22;

/// What a cell reads: a constant, or row `r`'s `V` cell.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Src {
    Zero,
    One,
    Row(u32),
}

/// One gate: `V = X + C + Y·C`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Row {
    pub x: Src,
    pub y: Src,
    pub c: Src,
}

const IDLE: Row = Row {
    x: Src::Zero,
    y: Src::Zero,
    c: Src::Zero,
};

/// The gate on bits: `x ⊕ (c ∧ ¬y)`.
pub fn gate_bits(x: u8, y: u8, c: u8) -> u8 {
    x ^ (c & !y & 1)
}

/// A lane of 64 wires, bit `z` at index `z`.
type Lane = [Src; 64];
type State = [Lane; STATE_LANES];

pub struct Circuit {
    pub log_rows: usize,
    /// Rows the gates use, the public ones included; the rest are idle.
    pub used_rows: usize,
    pub rows: Vec<Row>,
    /// The rows that are free input bits, in the order [`Circuit::cells`] takes them.
    pub inputs: Vec<u32>,
    /// Each cell's successor on its cycle. Cell `4 r + role`, the roles `X, Y, C, V`.
    pub sigma: Vec<u32>,
    /// The port region's rows `[start, start + len)` ([`Builder::with_ports`]); `(0, 0)` without one.
    pub port_region: (usize, usize),
    /// The placed ports in the order they were placed: `(row, rows built before it)`, which is where
    /// [`Circuit::outputs_k`] evaluates them. Empty without a port region.
    pub ports: Vec<(u32, u32)>,
}

pub struct Builder {
    rows: Vec<Row>,
    inputs: Vec<u32>,
    /// The port region's first row, its rows, and when each placed one was placed.
    port_start: usize,
    port_rows: Vec<Option<Row>>,
    placed: Vec<(u32, u32)>,
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder {
    pub fn new() -> Self {
        Self::with_capacity(PUBLIC_ROWS)
    }

    /// A builder with room for `rows` rows, so that a large circuit's rows are not copied as they grow.
    pub fn with_capacity(rows: usize) -> Self {
        let mut all = Vec::with_capacity(rows.max(PUBLIC_ROWS));
        all.resize(PUBLIC_ROWS, IDLE);
        Self {
            rows: all,
            inputs: Vec::new(),
            port_start: usize::MAX,
            port_rows: Vec::new(),
            placed: Vec::new(),
        }
    }

    /// A builder whose rows `[start, start + len)` are a port region: the built rows must stay below `start`,
    /// and [`Builder::port`] places the region's rows by index.
    pub fn with_ports(rows: usize, start: usize, len: usize) -> Self {
        assert!(start >= PUBLIC_ROWS);
        let mut b = Self::with_capacity(rows.min(start));
        b.port_start = start;
        b.port_rows = vec![None; len];
        b
    }

    /// A free `K` value: a row reading its own output as `X`, `1` as `Y` and `0` as `C`, so `V = V + 0 + 0`.
    pub fn free_k(&mut self) -> Src {
        let at = Src::Row(self.rows.len() as u32);
        self.row(at, Src::One, Src::Zero)
    }

    /// `a · b` in `K`, one row `(X, Y, C) = (b, a, b)`: `V = b + b + a·b`.
    pub fn mul(&mut self, a: Src, b: Src) -> Src {
        match (a, b) {
            (Src::Zero, _) | (_, Src::Zero) => Src::Zero,
            (Src::One, v) | (v, Src::One) => v,
            _ => self.row(b, a, b),
        }
    }

    /// Port `index` of the region: the row `(X, Y, C) = (out, 1, input)`, `out` its own output where `None` (a
    /// free value). The gate reads `V = X + C + C = X`, so the four cells are `(O, 1, I, O)`. Returns `V`.
    pub fn port(&mut self, index: usize, out: Option<Src>, input: Src) -> Src {
        let row = self.port_start + index;
        assert!(self.port_rows[index].is_none(), "port {index} placed twice");
        let at = Src::Row(row as u32);
        self.port_rows[index] = Some(Row {
            x: out.unwrap_or(at),
            y: Src::One,
            c: input,
        });
        self.placed.push((row as u32, self.rows.len() as u32));
        at
    }

    /// The row a port index is at.
    pub fn port_row(&self, index: usize) -> u32 {
        assert!(index < self.port_rows.len());
        (self.port_start + index) as u32
    }

    /// Rows used so far, the public ones included.
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn row(&mut self, x: Src, y: Src, c: Src) -> Src {
        debug_assert!(self.rows.len() < self.port_start, "the rows reach the port region");
        self.rows.push(Row { x, y, c });
        Src::Row(self.rows.len() as u32 - 1)
    }

    /// A free bit: a row reading its own output three times, which the gate then makes `0` or `1`.
    pub fn input(&mut self) -> Src {
        let at = Src::Row(self.rows.len() as u32);
        self.inputs.push(self.rows.len() as u32);
        self.row(at, at, at)
    }

    pub fn not(&mut self, a: Src) -> Src {
        match a {
            Src::Zero => Src::One,
            Src::One => Src::Zero,
            _ => self.row(Src::One, Src::Zero, a),
        }
    }

    pub fn xor(&mut self, a: Src, b: Src) -> Src {
        match (a, b) {
            (Src::Zero, v) | (v, Src::Zero) => v,
            (Src::One, v) | (v, Src::One) => self.not(v),
            _ => self.row(a, Src::Zero, b),
        }
    }

    /// `a ⊕ (¬b ∧ c)`, Keccak's χ, in one row unless a constant makes it cheaper.
    pub fn chi(&mut self, a: Src, b: Src, c: Src) -> Src {
        match (b, c) {
            (Src::One, _) | (_, Src::Zero) => a,
            (Src::Zero, _) => self.xor(a, c),
            (_, Src::One) => {
                let not_b = self.not(b);
                self.xor(a, not_b)
            }
            _ => self.row(a, b, c),
        }
    }

    /// Keccak-f\[1600\]: lane `x + 5y`, bit `z` of a lane at index `z`.
    pub fn keccak_f(&mut self, mut a: State) -> State {
        for &rc in RC.iter().take(ROUNDS) {
            // θ: the column parities, then each lane XORed with its two neighbours' columns.
            let mut c = [[Src::Zero; 64]; 5];
            for x in 0..5 {
                for z in 0..64 {
                    let mut acc = a[x][z];
                    for y in 1..5 {
                        acc = self.xor(acc, a[x + 5 * y][z]);
                    }
                    c[x][z] = acc;
                }
            }
            let mut d = [[Src::Zero; 64]; 5];
            for x in 0..5 {
                for z in 0..64 {
                    d[x][z] = self.xor(c[(x + 4) % 5][z], c[(x + 1) % 5][(z + 63) % 64]);
                }
            }
            for (i, lane) in a.iter_mut().enumerate() {
                for z in 0..64 {
                    lane[z] = self.xor(lane[z], d[i % 5][z]);
                }
            }
            // ρ and π: wiring only. Lane `i`, rotated left by `RHO[i]`, goes to `PI[i]`.
            let mut b = [[Src::Zero; 64]; STATE_LANES];
            for i in 0..STATE_LANES {
                let r = RHO[i] as usize;
                for z in 0..64 {
                    b[PI[i]][(z + r) % 64] = a[i][z];
                }
            }
            // χ: one row a bit.
            for y in 0..5 {
                for x in 0..5 {
                    for z in 0..64 {
                        a[x + 5 * y][z] =
                            self.chi(b[x + 5 * y][z], b[(x + 1) % 5 + 5 * y][z], b[(x + 2) % 5 + 5 * y][z]);
                    }
                }
            }
            // ι: a NOT where the round constant has a one.
            for z in 0..64 {
                if (rc >> z) & 1 == 1 {
                    a[0][z] = self.not(a[0][z]);
                }
            }
        }
        a
    }

    /// Keccak-256 of a 64-byte block, its bits in byte order and low bit first; the digest likewise.
    pub fn keccak256_64(&mut self, message: &[Src]) -> Vec<Src> {
        assert_eq!(message.len(), 512);
        let mut state: State = [[Src::Zero; 64]; STATE_LANES];
        for (b, &bit) in message.iter().enumerate() {
            state[b / 64][b % 64] = bit;
        }
        // Keccak's padding of a 64-byte message in one 136-byte block: 0x01 at byte 64, 0x80 at byte 135.
        state[8][0] = Src::One;
        state[16][63] = Src::One;
        let out = self.keccak_f(state);
        (0..256).map(|b| out[b / 64][b % 64]).collect()
    }

    /// Close the circuit on `2^log_rows` rows, `public[J][j]` being bit `j` of public word `J`.
    pub fn finish(self, log_rows: usize, public: &[Vec<Src>; 4]) -> Circuit {
        self.finish_with_zeros(log_rows, public, &[])
    }

    /// As [`Builder::finish`], with public words `6` and `7` reading `zeros[0]` and `zeros[1]` (128 wires each)
    /// instead of constant zeros. The verifier takes every word past `4` to be zero, so an accepted proof has
    /// these wires at `0`: an equality `a = b` of computed bits is `a ⊕ b` here. Word `5` stays the zero anchor.
    pub fn finish_with_zeros(mut self, log_rows: usize, public: &[Vec<Src>; 4], zeros: &[Vec<Src>]) -> Circuit {
        assert!(zeros.len() <= 2 && zeros.iter().all(|word| word.len() == WORD_BITS));
        let n = 1 << log_rows;
        let used_rows = self.rows.len();
        assert!(used_rows <= n, "{used_rows} rows");
        let port_region = if self.port_rows.is_empty() {
            (0, 0)
        } else {
            assert!(used_rows <= self.port_start, "{used_rows} rows reach the port region");
            assert!(self.port_start + self.port_rows.len() <= n, "the port region past the rows");
            (self.port_start, self.port_rows.len())
        };
        let bit = |word: usize, j: usize| match word {
            0..4 => public[word][j],
            4 if j == 0 => Src::One,
            6 | 7 if word - 6 < zeros.len() => zeros[word - 6][j],
            _ => Src::Zero,
        };
        for (r, row) in self.rows[..PUBLIC_ROWS].iter_mut().enumerate() {
            let (word, pair) = (r / (WORD_BITS / 2), r % (WORD_BITS / 2));
            *row = Row {
                x: bit(word, 2 * pair),
                y: bit(word, 2 * pair + 1),
                c: Src::Zero,
            };
        }
        self.rows.resize(n, IDLE);
        for (i, row) in self.port_rows.iter().enumerate() {
            if let Some(row) = row {
                self.rows[port_region.0 + i] = *row;
            }
        }

        // A cycle is a source and the cells reading it, in cell order.
        const NONE: u32 = u32::MAX;
        let slot = |src: Src| match src {
            Src::Zero => 0,
            Src::One => 1,
            Src::Row(r) => 2 + r as usize,
        };
        let mut first = vec![NONE; n + 2];
        let mut last = vec![NONE; n + 2];
        let mut sigma: Vec<u32> = (0..4 * n as u32).collect();
        let mut join = |at: usize, cell: u32, sigma: &mut Vec<u32>| {
            if first[at] == NONE {
                first[at] = cell;
            } else {
                sigma[last[at] as usize] = cell;
            }
            last[at] = cell;
            sigma[cell as usize] = first[at];
        };
        for r in 0..n {
            join(2 + r, 4 * r as u32 + 3, &mut sigma);
        }
        for (r, row) in self.rows.iter().enumerate() {
            for (role, src) in [row.x, row.y, row.c].into_iter().enumerate() {
                join(slot(src), (4 * r + role) as u32, &mut sigma);
            }
        }
        Circuit {
            log_rows,
            used_rows,
            rows: self.rows,
            inputs: self.inputs,
            sigma,
            port_region,
            ports: self.placed,
        }
    }
}

/// The bit a source holds, given every row's output.
pub fn read(v: &[u8], src: Src) -> u8 {
    match src {
        Src::Zero => 0,
        Src::One => 1,
        Src::Row(r) => v[r as usize],
    }
}

impl Circuit {
    pub fn n_inputs(&self) -> usize {
        self.inputs.len()
    }

    /// Every row's output bit, from the free inputs.
    pub fn outputs(&self, inputs: &[bool]) -> Vec<u8> {
        assert_eq!(inputs.len(), self.inputs.len());
        assert!(self.ports.is_empty(), "a lane circuit: use outputs_k");
        let mut v = vec![0u8; self.rows.len()];
        for (&row, &input) in self.inputs.iter().zip(inputs) {
            v[row as usize] = input as u8;
        }
        // A row reads rows before it, or itself; the public rows read the outputs.
        for r in (PUBLIC_ROWS..self.rows.len()).chain(0..PUBLIC_ROWS) {
            let row = self.rows[r];
            v[r] = gate_bits(read(&v, row.x), read(&v, row.y), read(&v, row.c));
        }
        v
    }

    /// Every cell's value, from the free inputs.
    pub fn cells(&self, inputs: &[bool]) -> Vec<F64> {
        let v = self.outputs(inputs);
        parallel::map_collect(4 * self.rows.len(), |cell| {
            let (r, row) = (cell / 4, self.rows[cell / 4]);
            let bit = match cell % 4 {
                0 => read(&v, row.x),
                1 => read(&v, row.y),
                2 => read(&v, row.c),
                _ => v[r],
            };
            F64(bit as u64)
        })
    }
}

/// The `K` value a source holds, given every row's output.
pub fn read_k(v: &[F64], src: Src) -> F64 {
    match src {
        Src::Zero => F64::ZERO,
        Src::One => F64::ONE,
        Src::Row(r) => v[r as usize],
    }
}

/// The gate over `K`: `x + c + y·c`.
pub fn gate_k(x: F64, y: F64, c: F64) -> F64 {
    x + c + y * c
}

impl Circuit {
    /// Every row's output over `K`. The rows are evaluated in the order they were built (the ports where they
    /// were placed, the public rows last); a free row (one whose `X` reads itself: a free bit or a free `K`
    /// value) takes `free(row, outputs so far)`, and every other row its gate.
    pub fn outputs_k(&self, mut free: impl FnMut(u32, &[F64]) -> F64) -> Vec<F64> {
        let mut v = vec![F64::ZERO; self.rows.len()];
        let mut eval = |r: usize, v: &mut Vec<F64>| {
            let row = self.rows[r];
            v[r] = if row.x == Src::Row(r as u32) {
                free(r as u32, v)
            } else {
                gate_k(read_k(v, row.x), read_k(v, row.y), read_k(v, row.c))
            };
        };
        let mut ports = self.ports.iter().peekable();
        for r in PUBLIC_ROWS..self.used_rows {
            while let Some(&(port, _)) = ports.next_if(|&&(_, before)| before as usize <= r) {
                eval(port as usize, &mut v);
            }
            eval(r, &mut v);
        }
        for &(port, _) in ports {
            eval(port as usize, &mut v);
        }
        let (start, len) = self.port_region;
        for r in self.used_rows..self.rows.len() {
            let placed = (start..start + len).contains(&r) && self.rows[r] != IDLE;
            if !placed {
                eval(r, &mut v);
            }
        }
        for r in 0..PUBLIC_ROWS {
            eval(r, &mut v);
        }
        v
    }

    /// Every cell's value over `K`, from every row's output.
    pub fn cells_k(&self, v: &[F64]) -> Vec<F64> {
        assert_eq!(v.len(), self.rows.len());
        parallel::map_collect(4 * self.rows.len(), |cell| {
            let row = self.rows[cell / 4];
            match cell % 4 {
                0 => read_k(v, row.x),
                1 => read_k(v, row.y),
                2 => read_k(v, row.c),
                _ => v[cell / 4],
            }
        })
    }

    /// Whether `cells` satisfy every row's gate and are constant on every cycle of the wiring; else the first
    /// row whose gate fails, or the first cell that differs from its successor.
    pub fn check_k(&self, cells: &[F64]) -> Result<(), CheckError> {
        assert_eq!(cells.len(), 4 * self.rows.len());
        if let Some(r) = (0..self.rows.len()).find(|&r| {
            let [x, y, c, v] = std::array::from_fn(|role| cells[4 * r + role]);
            gate_k(x, y, c) != v
        }) {
            return Err(CheckError::Gate(r));
        }
        if let Some(cell) = (0..cells.len()).find(|&i| cells[self.sigma[i] as usize] != cells[i]) {
            return Err(CheckError::Wiring(cell));
        }
        Ok(())
    }
}

/// Why cells are not a witness of a circuit ([`Circuit::check_k`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckError {
    /// The row's gate fails.
    Gate(usize),
    /// The cell differs from its successor on its cycle.
    Wiring(usize),
}

/// The 256 wires of 32 bytes to the four public words they are read as: a word is sixteen bytes, big-endian.
pub fn public_words(y: &[Src], root: &[Src]) -> [Vec<Src>; 4] {
    std::array::from_fn(|word| {
        let (bytes, half) = (if word < 2 { y } else { root }, word % 2);
        (0..WORD_BITS)
            .map(|j| bytes[8 * (16 * half + 15 - j / 8) + j % 8])
            .collect()
    })
}

fn constant_block(byte: u8) -> Vec<Src> {
    (0..256)
        .map(|i| {
            if (byte >> (i % 8)) & 1 == 1 {
                Src::One
            } else {
                Src::Zero
            }
        })
        .collect()
}

/// The membership statement: `y = H(x | 0x11..)`, and the path from `H(x | 0x22..)` up to `root`.
pub fn membership() -> Circuit {
    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let y = b.keccak256_64(&[&x[..], &constant_block(Y_PAD)].concat());
    let mut node = b.keccak256_64(&[&x[..], &constant_block(LEAF_PAD)].concat());
    for _ in 0..DEPTH {
        let sibling: Vec<Src> = (0..256).map(|_| b.input()).collect();
        let direction = b.input();
        // χ negates its middle input, so `left = node ⊕ (direction ∧ differ)` reads `¬direction` there.
        let keep = b.not(direction);
        let (mut left, mut right) = (Vec::with_capacity(256), Vec::with_capacity(256));
        for i in 0..256 {
            let differ = b.xor(node[i], sibling[i]);
            let l = b.chi(node[i], keep, differ);
            right.push(b.xor(l, differ));
            left.push(l);
        }
        node = b.keccak256_64(&[left, right].concat());
    }
    b.finish(LOG_ROWS, &public_words(&y, &node))
}

/// The free inputs of [`membership`] for a secret.
pub fn membership_inputs(secret: &Secret) -> Vec<bool> {
    let bits = |bytes: &[u8; 32]| -> Vec<bool> { (0..256).map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1).collect() };
    let mut inputs = bits(&secret.x);
    for (level, sibling) in secret.siblings.iter().enumerate() {
        inputs.extend(bits(sibling));
        inputs.push((secret.directions >> level) & 1 == 1);
    }
    inputs
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// A lane circuit: free `K` values, a product, a lane mux, ports placed out of row order (one free, one read
    /// from a row) and read back; its `K` evaluation follows the build order, its cells hold every gate and wire,
    /// and a changed cell does not. On a bit circuit the `K` evaluation is the bit one.
    #[test]
    fn lane_cells_and_ports() {
        let mut b = Builder::with_ports(2048, 1024, 8);
        let (a, c) = (b.free_k(), b.free_k());
        let s = b.input();
        let product = b.mul(a, c);
        let not_s = b.not(s);
        let differ = b.xor(a, c);
        let muxed = b.chi(a, not_s, differ);
        let free_port = b.port(3, None, product);
        let read_port = b.port(5, Some(muxed), a);
        let after = b.xor(free_port, a);
        assert_eq!(b.port_row(3), 1027);
        let circuit = b.finish(11, &std::array::from_fn(|_| vec![Src::Zero; WORD_BITS]));
        assert_eq!(circuit.port_region, (1024, 8));
        assert_eq!(circuit.ports, vec![(1027, 519), (1029, 519)]);
        assert_eq!(circuit.rows[1026], IDLE);
        let mut rng = Rng::new(0x4C);
        for bit in [0, 1, 0, 1] {
            let (va, vc, vo) = (F64(rng.next_u64()), F64(rng.next_u64()), F64(rng.next_u64()));
            let v = circuit.outputs_k(|r, _| match Src::Row(r) {
                x if x == a => va,
                x if x == c => vc,
                x if x == s => F64(bit),
                x if x == free_port => vo,
                _ => panic!("row {r} is not free"),
            });
            assert_eq!(read_k(&v, product), va * vc);
            assert_eq!(read_k(&v, muxed), if bit == 1 { vc } else { va });
            assert_eq!(read_k(&v, read_port), read_k(&v, muxed));
            assert_eq!(read_k(&v, after), vo + va);
            let cells = circuit.cells_k(&v);
            assert_eq!(circuit.check_k(&cells), Ok(()));
            let Src::Row(port) = free_port else { unreachable!() };
            assert_eq!(&cells[4 * port as usize..4 * port as usize + 4], [vo, F64::ONE, va * vc, vo]);
            let mut bad = cells.clone();
            bad[4 * port as usize + 2] += F64::ONE;
            assert!(circuit.check_k(&bad).is_err());
        }
        // A bit circuit evaluates over `K` as over bits.
        let mut b = Builder::new();
        let ins: Vec<Src> = (0..8).map(|_| b.input()).collect();
        let mut out = ins[0];
        for w in ins.windows(3) {
            let t = b.chi(w[0], w[1], w[2]);
            out = b.xor(out, t);
        }
        let circuit = b.finish(10, &std::array::from_fn(|j| vec![if j == 0 { out } else { Src::Zero }; WORD_BITS]));
        assert!(circuit.ports.is_empty() && circuit.port_region == (0, 0));
        for _ in 0..8 {
            let inputs: Vec<bool> = (0..8).map(|_| rng.next_u64() & 1 == 1).collect();
            let bits = circuit.outputs(&inputs);
            let v = circuit.outputs_k(|r, _| F64(inputs[circuit.inputs.iter().position(|&i| i == r).unwrap()] as u64));
            assert_eq!(v, bits.iter().map(|&x| F64(x as u64)).collect::<Vec<_>>());
            assert_eq!(circuit.cells_k(&v), circuit.cells(&inputs));
            assert_eq!(circuit.check_k(&circuit.cells_k(&v)), Ok(()));
        }
    }

    /// The circuit's Keccak-256 is Ethereum's, on random blocks.
    #[test]
    fn keccak_matches() {
        let mut b = Builder::new();
        let message: Vec<Src> = (0..512).map(|_| b.input()).collect();
        let digest = b.keccak256_64(&message);
        let rows = b.len() - PUBLIC_ROWS - 512;
        let circuit = b.finish(18, &std::array::from_fn(|_| vec![Src::Zero; WORD_BITS]));
        let mut rng = Rng::new(0x4B);
        for _ in 0..4 {
            let bytes: Vec<u8> = (0..64).map(|_| rng.next_u64() as u8).collect();
            let inputs: Vec<bool> = (0..512).map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1).collect();
            let v = circuit.outputs(&inputs);
            let got: Vec<u8> = (0..32)
                .map(|byte| (0..8).fold(0u8, |acc, i| acc | read(&v, digest[8 * byte + i]) << i))
                .collect();
            let expected = {
                use sha3::Digest;
                sha3::Keccak256::digest(&bytes).to_vec()
            };
            assert_eq!(got, expected);
            assert_eq!(got, primitives::hash::hash(&bytes).to_vec());
        }
        println!("rows per Keccak-256 of a 64-byte block: {rows}");
    }

    /// The membership circuit computes the statement, fits its rows, and is what the soundness argument
    /// assumes: an input row reads its own output three times, every other row reads constants or rows of lower
    /// rank (the public rows ranked last, nothing reading them), every reading cell is on the cycle of the output
    /// cell it reads, and the cells reading a constant are one cycle that holds its public anchor.
    #[test]
    fn membership_is_a_wired_loop_free_circuit() {
        let circuit = membership();
        let n = circuit.rows.len();
        let mut rng = Rng::new(0x3E);
        let secret = Secret {
            x: std::array::from_fn(|_| rng.next_u64() as u8),
            siblings: std::array::from_fn(|_| std::array::from_fn(|_| rng.next_u64() as u8)),
            directions: rng.next_u64() as u32,
        };
        let statement = secret.statement();
        let v = circuit.outputs(&membership_inputs(&secret));
        // The public rows hold the statement's halves, bit by bit.
        let halves = statement.halves();
        for (word, half) in halves.iter().enumerate() {
            for j in 0..WORD_BITS {
                let r = word * (WORD_BITS / 2) + j / 2;
                let src = if j % 2 == 0 {
                    circuit.rows[r].x
                } else {
                    circuit.rows[r].y
                };
                let expected = if j < 64 {
                    (half.c0 >> j) & 1
                } else {
                    (half.c1 >> (j - 64)) & 1
                };
                assert_eq!(read(&v, src) as u64, expected, "word {word} bit {j}");
            }
        }

        let rank = |r: usize| if r < PUBLIC_ROWS { n + r } else { r };
        let mut is_input = vec![false; n];
        circuit.inputs.iter().for_each(|&r| is_input[r as usize] = true);
        for (r, row) in circuit.rows.iter().enumerate() {
            let sources = [row.x, row.y, row.c];
            if is_input[r] {
                assert_eq!(sources, [Src::Row(r as u32); 3]);
                continue;
            }
            for src in sources {
                if let Src::Row(from) = src {
                    assert!(from as usize >= PUBLIC_ROWS, "row {r} reads a public row");
                    assert!(rank(from as usize) < rank(r), "row {r} reads row {from}");
                }
            }
        }
        // Cycles of the wiring, each named by its least cell.
        let mut cycle = vec![u32::MAX; 4 * n];
        for start in 0..4 * n {
            if cycle[start] != u32::MAX {
                continue;
            }
            let mut at = start;
            while cycle[at] == u32::MAX {
                cycle[at] = start as u32;
                at = circuit.sigma[at] as usize;
            }
            assert_eq!(at, start, "the wiring is not a permutation");
        }
        let (zero_anchor, one_anchor) = (4 * (5 * 64), 4 * (4 * 64));
        assert_eq!(circuit.rows[5 * 64].x, Src::Zero);
        assert_eq!(circuit.rows[4 * 64].x, Src::One);
        for (r, row) in circuit.rows.iter().enumerate() {
            for (role, src) in [row.x, row.y, row.c].into_iter().enumerate() {
                let source = match src {
                    Src::Zero => zero_anchor,
                    Src::One => one_anchor,
                    Src::Row(from) => 4 * from as usize + 3,
                };
                assert_eq!(cycle[4 * r + role], cycle[source], "cell {role} of row {r}");
            }
        }
        assert_ne!(cycle[zero_anchor], cycle[one_anchor]);
        assert!((0..n).all(|r| cycle[4 * r + 3] != cycle[zero_anchor] && cycle[4 * r + 3] != cycle[one_anchor]));
        // Word 5 is all zeros, word 4 a one then zeros, and words 0 to 3 read computed rows.
        for r in 0..PUBLIC_ROWS {
            let (word, row) = (r / (WORD_BITS / 2), circuit.rows[r]);
            assert_eq!(row.c, Src::Zero);
            match word {
                0..4 => assert!(matches!((row.x, row.y), (Src::Row(_), Src::Row(_)))),
                4 if r == 4 * 64 => assert_eq!([row.x, row.y], [Src::One, Src::Zero]),
                _ => assert_eq!([row.x, row.y], [Src::Zero, Src::Zero]),
            }
        }
    }
}
