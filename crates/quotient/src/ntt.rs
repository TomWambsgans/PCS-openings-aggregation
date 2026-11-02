// Part of this repository. The additive transform's layers are domain.rs's (adapted there from leanVM's branch
// PCS-openings-aggregation, commit 651453c6), in the same order; the lane-wise carry-less product and its reduction
// are those of crates/primitives/src/field/{x8,gf2_64x3}.rs (vendored from leanVM c445e3d5, credit binius64).
// MIT OR Apache-2.0; see NOTICE.md.
//! [`crate::domain`]'s transforms on rows of eight words, a row's eight products one AVX-512 carry-less product where
//! the build has it (for `crates/leanvm_univariate`'s prover):
//!
//! - a batch ([`K8`]): eight K-columns, row `i` their entries at position `i`, every layer between rows;
//! - one K-column, eight positions a row: its layers from 3 up between rows, layers 0..3 inside a row.
//!
//! The additive transform has `quotient::domain`'s layers in its order, so the same values. Also here: the fold of a
//! polynomial onto a smaller coset, the shifted cube, and the interpolation from the first points of an extension
//! coset (`D_M`'s first `Σ 2^(e_j)` points, for a polynomial of degree below their count).

use std::ops::{Add, Mul};

use parallel::SendPtr;
use primitives::field::{F64, F192};

use crate::domain::{chain, point};

use lanes::{
    U, V, clmul_u, from_array, load, mask_add, mul, reduce_u, splat, store, swap, transpose, xor, xor_u, zero_u,
};

/// Eight K-columns' entries at one position: a row of a batch.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C, align(64))]
pub struct K8(pub [F64; 8]);

impl K8 {
    pub const ZERO: Self = Self([F64::ZERO; 8]);
}

/// Rows one worker transforms whole (256 KiB), and rows one tile of the wider layers holds.
const LEAF_ROWS: usize = 1 << 12;
const TILE_ROWS: usize = 1 << 12;
/// The most of the wider layers one pass over memory takes.
const GROUP: usize = 6;

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
mod lanes {
    use core::arch::x86_64::*;

    /// Eight K elements in one register.
    #[derive(Clone, Copy)]
    pub struct V(__m512i);

    /// # Safety
    /// `p` points to eight readable words.
    #[inline(always)]
    pub unsafe fn load(p: *const u64) -> V {
        // SAFETY: the caller's eight words; the module's cfg enables avx512f.
        unsafe { V(_mm512_loadu_si512(p.cast())) }
    }

    /// # Safety
    /// `p` points to eight writable words.
    #[inline(always)]
    pub unsafe fn store(p: *mut u64, v: V) {
        // SAFETY: the caller's eight words.
        unsafe { _mm512_storeu_si512(p.cast(), v.0) }
    }

    #[inline(always)]
    pub fn splat(x: u64) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { V(_mm512_set1_epi64(x as i64)) }
    }

    #[inline(always)]
    pub fn from_array(x: [u64; 8]) -> V {
        // SAFETY: eight words on the stack.
        unsafe { load(x.as_ptr()) }
    }

    #[inline(always)]
    pub fn xor(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { V(_mm512_xor_si512(a.0, b.0)) }
    }

    /// Lane-wise carry-less products, unreduced: the even lanes' 128-bit products, and the odd lanes'.
    #[derive(Clone, Copy)]
    pub struct U(__m512i, __m512i);

    #[inline(always)]
    pub fn zero_u() -> U {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { U(_mm512_setzero_si512(), _mm512_setzero_si512()) }
    }

    #[inline(always)]
    pub fn clmul_u(a: V, b: V) -> U {
        // SAFETY: the module's cfg enables avx512f and vpclmulqdq.
        unsafe {
            U(
                _mm512_clmulepi64_epi128::<0x00>(a.0, b.0),
                _mm512_clmulepi64_epi128::<0x11>(a.0, b.0),
            )
        }
    }

    #[inline(always)]
    pub fn xor_u(a: U, b: U) -> U {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { U(_mm512_xor_si512(a.0, b.0), _mm512_xor_si512(a.1, b.1)) }
    }

    /// Lane `i` reduced: the reduction of `gf2_64x3::x86_64::reduce_lanes512`.
    #[inline(always)]
    pub fn reduce_u(p: U) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            let (lo, hi) = (_mm512_unpacklo_epi64(p.0, p.1), _mm512_unpackhi_epi64(p.0, p.1));
            // The bits of `hi * 0x1B` past x^63, then lo ^ f(hi ^ spill), f(v) = v ^ v<<1 ^ v<<3 ^ v<<4.
            let spill = _mm512_ternarylogic_epi64::<0x96>(
                _mm512_srli_epi64::<63>(hi),
                _mm512_srli_epi64::<61>(hi),
                _mm512_srli_epi64::<60>(hi),
            );
            let v = _mm512_xor_si512(hi, spill);
            let f = _mm512_ternarylogic_epi64::<0x96>(v, _mm512_slli_epi64::<1>(v), _mm512_slli_epi64::<3>(v));
            V(_mm512_ternarylogic_epi64::<0x96>(lo, f, _mm512_slli_epi64::<4>(v)))
        }
    }

    /// Lane `i` is `a_i b_i` in K.
    #[inline(always)]
    pub fn mul(a: V, b: V) -> V {
        reduce_u(clmul_u(a, b))
    }

    /// The 8 x 8 transpose: lane `p` of output `c` is lane `c` of input `p`.
    #[inline(always)]
    pub fn transpose(r: [V; 8]) -> [V; 8] {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            let pick = |a: __m512i, b: __m512i, i: [i64; 8]| {
                _mm512_permutex2var_epi64(a, _mm512_set_epi64(i[7], i[6], i[5], i[4], i[3], i[2], i[1], i[0]), b)
            };
            let x: [__m512i; 8] = std::array::from_fn(|k| {
                let (a, b) = (r[k & !1].0, r[k | 1].0);
                if k & 1 == 0 {
                    _mm512_unpacklo_epi64(a, b)
                } else {
                    _mm512_unpackhi_epi64(a, b)
                }
            });
            let (lo2, hi2) = ([0, 1, 8, 9, 4, 5, 12, 13], [2, 3, 10, 11, 6, 7, 14, 15]);
            let y = [
                pick(x[0], x[2], lo2),
                pick(x[1], x[3], lo2),
                pick(x[0], x[2], hi2),
                pick(x[1], x[3], hi2),
                pick(x[4], x[6], lo2),
                pick(x[5], x[7], lo2),
                pick(x[4], x[6], hi2),
                pick(x[5], x[7], hi2),
            ];
            let (lo4, hi4) = ([0, 1, 2, 3, 8, 9, 10, 11], [4, 5, 6, 7, 12, 13, 14, 15]);
            std::array::from_fn(|c| V(pick(y[c & 3], y[4 + (c & 3)], if c < 4 { lo4 } else { hi4 })))
        }
    }

    /// Lane `i` is `a_(i ^ S)`.
    #[inline(always)]
    pub fn swap<const S: usize>(a: V) -> V {
        let s = S as i64;
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            let index = _mm512_set_epi64(7 ^ s, 6 ^ s, 5 ^ s, 4 ^ s, 3 ^ s, 2 ^ s, 1 ^ s, s);
            V(_mm512_permutexvar_epi64(index, a.0))
        }
    }

    /// `a`, with `b` added on the lanes of `mask`.
    #[inline(always)]
    pub fn mask_add(a: V, mask: u8, b: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { V(_mm512_mask_xor_epi64(a.0, mask, a.0, b.0)) }
    }
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq")))]
mod lanes {
    use primitives::field::F64;

    /// Eight K elements.
    #[derive(Clone, Copy)]
    pub struct V([u64; 8]);

    /// # Safety
    /// `p` points to eight readable words.
    #[inline(always)]
    pub unsafe fn load(p: *const u64) -> V {
        // SAFETY: the caller's eight words.
        unsafe { V(p.cast::<[u64; 8]>().read_unaligned()) }
    }

    /// # Safety
    /// `p` points to eight writable words.
    #[inline(always)]
    pub unsafe fn store(p: *mut u64, v: V) {
        // SAFETY: the caller's eight words.
        unsafe { p.cast::<[u64; 8]>().write_unaligned(v.0) }
    }

    #[inline(always)]
    pub fn splat(x: u64) -> V {
        V([x; 8])
    }

    #[inline(always)]
    pub fn from_array(x: [u64; 8]) -> V {
        V(x)
    }

    #[inline(always)]
    pub fn xor(a: V, b: V) -> V {
        V(std::array::from_fn(|i| a.0[i] ^ b.0[i]))
    }

    #[inline(always)]
    pub fn mul(a: V, b: V) -> V {
        V(std::array::from_fn(|i| (F64(a.0[i]) * F64(b.0[i])).0))
    }

    /// Products, here reduced at once.
    pub type U = V;

    #[inline(always)]
    pub fn zero_u() -> U {
        V([0; 8])
    }

    #[inline(always)]
    pub fn clmul_u(a: V, b: V) -> U {
        mul(a, b)
    }

    #[inline(always)]
    pub fn xor_u(a: U, b: U) -> U {
        xor(a, b)
    }

    #[inline(always)]
    pub fn reduce_u(p: U) -> V {
        p
    }

    #[inline(always)]
    pub fn transpose(r: [V; 8]) -> [V; 8] {
        std::array::from_fn(|c| V(std::array::from_fn(|p| r[p].0[c])))
    }

    #[inline(always)]
    pub fn swap<const S: usize>(a: V) -> V {
        V(std::array::from_fn(|i| a.0[i ^ S]))
    }

    #[inline(always)]
    pub fn mask_add(a: V, mask: u8, b: V) -> V {
        V(std::array::from_fn(|i| {
            if mask >> i & 1 == 1 { a.0[i] ^ b.0[i] } else { a.0[i] }
        }))
    }
}

/// A transform's layers: the twiddle of a pair of rows, their butterfly, and a row's own layers 0..3 (one column).
trait Kind: Sync {
    /// Whether the layers run from the highest down.
    const DOWN: bool;
    /// The twiddle of position layer `k`'s block `block` (a position `>> (k + 1)`).
    fn twiddle(&self, k: usize, block: usize) -> F64;
    fn butterfly(a: V, b: V, t: V) -> (V, V);
    /// Layers 0..3 of row `row`, eight consecutive positions of one column.
    fn lanes(&self, row: usize, x: V) -> V;
}

/// The additive transform's twiddles: `w_k` of the offset, and a row's lane twiddles' constant parts.
struct Twiddles {
    offsets: Vec<F64>,
    c1: V,
    c0: V,
}

impl Twiddles {
    fn new(offset: F64, layers: usize) -> Self {
        let p = |i: usize| point(i).0;
        Self {
            offsets: chain(offset, layers.max(3)),
            c1: from_array([0, 0, 0, 0, p(2), p(2), p(2), p(2)]),
            c0: from_array([0, 0, p(2), p(2), p(4), p(4), p(6), p(6)]),
        }
    }

    /// Row `row`'s twiddles at layers 2, 1, 0: `w_k` at each pair's low position.
    #[inline(always)]
    fn row(&self, row: usize) -> [V; 3] {
        let o = &self.offsets;
        [
            splat((o[2] + point(2 * row)).0),
            xor(splat((o[1] + point(4 * row)).0), self.c1),
            xor(splat((o[0] + point(8 * row)).0), self.c0),
        ]
    }
}

/// Coefficients to values (`crate::domain::values`): `a += λ b; b += a`, the layers from the highest down.
struct Forward(Twiddles);

impl Kind for Forward {
    const DOWN: bool = true;
    #[inline(always)]
    fn twiddle(&self, k: usize, block: usize) -> F64 {
        self.0.offsets[k] + point(2 * block)
    }
    #[inline(always)]
    fn butterfly(a: V, b: V, t: V) -> (V, V) {
        let a = xor(a, mul(b, t));
        (a, xor(b, a))
    }
    #[inline(always)]
    fn lanes(&self, row: usize, x: V) -> V {
        let [t2, t1, t0] = self.0.row(row);
        let x = mask_add(x, 0x0F, mul(swap::<4>(x), t2));
        let x = mask_add(x, 0xF0, swap::<4>(x));
        let x = mask_add(x, 0x33, mul(swap::<2>(x), t1));
        let x = mask_add(x, 0xCC, swap::<2>(x));
        let x = mask_add(x, 0x55, mul(swap::<1>(x), t0));
        mask_add(x, 0xAA, swap::<1>(x))
    }
}

/// Values to coefficients (`crate::domain::coefficients`): `b += a; a += λ b`, the layers from 0 up.
struct Inverse(Twiddles);

impl Kind for Inverse {
    const DOWN: bool = false;
    #[inline(always)]
    fn twiddle(&self, k: usize, block: usize) -> F64 {
        self.0.offsets[k] + point(2 * block)
    }
    #[inline(always)]
    fn butterfly(a: V, b: V, t: V) -> (V, V) {
        let b = xor(b, a);
        (xor(a, mul(b, t)), b)
    }
    #[inline(always)]
    fn lanes(&self, row: usize, x: V) -> V {
        let [t2, t1, t0] = self.0.row(row);
        let x = mask_add(x, 0xAA, swap::<1>(x));
        let x = mask_add(x, 0x55, mul(swap::<1>(x), t0));
        let x = mask_add(x, 0xCC, swap::<2>(x));
        let x = mask_add(x, 0x33, mul(swap::<2>(x), t1));
        let x = mask_add(x, 0xF0, swap::<4>(x));
        mask_add(x, 0x0F, mul(swap::<4>(x), t2))
    }
}

/// The multilinear extension on a shifted cube: per variable `l`, `(v_0, v_1) ↦ (v_0 + δ_l s, v_1 + δ_l s)`,
/// `s = v_0 + v_1`. The variables' maps commute.
struct Cube {
    delta: Vec<F64>,
}

impl Kind for Cube {
    const DOWN: bool = true;
    #[inline(always)]
    fn twiddle(&self, k: usize, _: usize) -> F64 {
        self.delta[k]
    }
    #[inline(always)]
    fn butterfly(a: V, b: V, t: V) -> (V, V) {
        let s = mul(xor(a, b), t);
        (xor(a, s), xor(b, s))
    }
    #[inline(always)]
    fn lanes(&self, _: usize, x: V) -> V {
        let x = xor(x, mul(xor(x, swap::<1>(x)), splat(self.delta[0].0)));
        let x = xor(x, mul(xor(x, swap::<2>(x)), splat(self.delta[1].0)));
        xor(x, mul(xor(x, swap::<4>(x)), splat(self.delta[2].0)))
    }
}

/// `len` row pairs, `lo` and `hi`, through the butterfly with twiddle `t`.
///
/// # Safety
/// `lo` and `hi` point to `len` rows each, of the caller's own.
#[inline(always)]
unsafe fn pairs<T: Kind>(lo: *mut u64, hi: *mut u64, len: usize, t: V) {
    for i in 0..len {
        // SAFETY: rows `i < len` of the caller's.
        unsafe {
            let (pa, pb) = (lo.add(8 * i), hi.add(8 * i));
            let (a, b) = T::butterfly(load(pa), load(pb), t);
            store(pa, a);
            store(pb, b);
        }
    }
}

/// `kind`'s layers on the `rows` rows of eight words at `data`, read first from `src` if given: position layer `k` is
/// row layer `k - shift`, and the layers below `shift` (0 or 3) are inside the rows. With `runs`, every eight rows
/// are transposed last ([`values_batch`]).
///
/// # Safety
/// `data` holds `8 rows` words, and `src` (if given) as many, disjoint from `data`.
unsafe fn run<T: Kind>(data: *mut u64, src: Option<*const u64>, rows: usize, shift: usize, kind: &T, runs: bool) {
    assert!(rows.is_power_of_two());
    let mr = rows.trailing_zeros() as usize;
    let leaf = mr.min(LEAF_ROWS.trailing_zeros() as usize);
    // The wider layers in groups, the highest first.
    let mut groups = Vec::new();
    let mut top = mr;
    while top > leaf {
        let a = top.saturating_sub(GROUP).max(leaf);
        groups.push((a, top - a));
        top = a;
    }
    let data = SendPtr(data);
    let src = src.map(|s| SendPtr(s.cast_mut()));
    if T::DOWN {
        let mut from = src;
        for &(a, g) in &groups {
            wide(data, from.take(), rows, a, g, shift, kind);
        }
        leaves(data, from, rows, leaf, shift, kind, runs);
    } else {
        leaves(data, src, rows, leaf, shift, kind, runs);
        for &(a, g) in groups.iter().rev() {
            wide(data, None, rows, a, g, shift, kind);
        }
    }
}

/// Row layers `0..leaf`, and the rows' own layers, on each block of `2^leaf` rows by one worker.
fn leaves<T: Kind>(
    data: SendPtr<u64>,
    src: Option<SendPtr<u64>>,
    rows: usize,
    leaf: usize,
    shift: usize,
    kind: &T,
    runs: bool,
) {
    let size = 1usize << leaf;
    parallel::for_each(rows >> leaf, |task| {
        let first = task << leaf;
        // SAFETY: a task touches its own `size` rows from `first`.
        unsafe {
            let base = data.add(8 * first);
            if let Some(s) = src {
                std::ptr::copy_nonoverlapping(s.add(8 * first), base, 8 * size);
            }
            let own = |base: *mut u64| {
                if shift == 3 {
                    for r in 0..size {
                        let p = base.add(8 * r);
                        store(p, kind.lanes(first + r, load(p)));
                    }
                }
            };
            if !T::DOWN {
                own(base);
            }
            let layer = |k: usize| {
                let half = 1usize << k;
                for j in 0..size >> (k + 1) {
                    let row = first + 2 * half * j;
                    let t = splat(kind.twiddle(k + shift, row >> (k + 1)).0);
                    pairs::<T>(data.add(8 * row), data.add(8 * (row + half)), half, t);
                }
            };
            if T::DOWN {
                (0..leaf).rev().for_each(layer);
                own(base);
            } else {
                (0..leaf).for_each(layer);
            }
            if runs {
                for g in 0..size / 8 {
                    let p = base.add(64 * g);
                    let t = transpose(std::array::from_fn(|q| load(p.add(8 * q))));
                    (0..8).for_each(|q| store(p.add(8 * q), t[q]));
                }
            }
        }
    });
}

/// Row layers `a..a + g` in one pass: tiles of `2^g` lines `2^a` rows apart, each line a run of rows.
fn wide<T: Kind>(
    data: SendPtr<u64>,
    src: Option<SendPtr<u64>>,
    rows: usize,
    a: usize,
    g: usize,
    shift: usize,
    kind: &T,
) {
    let lines = 1usize << g;
    let width = (TILE_ROWS >> g).clamp(1, 1 << a);
    let per_group = (1usize << a) / width;
    parallel::for_each((rows >> (a + g)) * per_group, |task| {
        let row0 = ((task / per_group) << (a + g)) + (task % per_group) * width;
        let line = |u: usize| row0 + (u << a);
        // SAFETY: a task touches rows `line(u) + [0, width)`, `u < lines`: its own.
        unsafe {
            if let Some(s) = src {
                for u in 0..lines {
                    std::ptr::copy_nonoverlapping(s.add(8 * line(u)), data.add(8 * line(u)), 8 * width);
                }
            }
            let layer = |j: usize| {
                let k = a + j;
                let hs = 1usize << j;
                for ub in (0..lines).step_by(2 * hs) {
                    let t = splat(kind.twiddle(k + shift, line(ub) >> (k + 1)).0);
                    for u in ub..ub + hs {
                        pairs::<T>(data.add(8 * line(u)), data.add(8 * line(u + hs)), width, t);
                    }
                }
            };
            if T::DOWN {
                (0..g).rev().for_each(layer);
            } else {
                (0..g).for_each(layer);
            }
        }
    });
}

fn words(data: &mut [K8]) -> *mut u64 {
    data.as_mut_ptr().cast()
}

/// `crate::domain::values` on a batch: row `i` becomes the eight columns at `offset + ω_i`; with `runs` (and eight
/// rows or more), each eight rows transposed: row `8 j + l` is column `l` at the points `8 j..8 j + 8` ([`Kx8::row`]).
pub fn values_batch(data: &mut [K8], offset: F64, runs: bool) {
    assert!(!runs || data.len() >= 8);
    let kind = Forward(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    // SAFETY: `data`'s own rows.
    unsafe { run(words(data), None, data.len(), 0, &kind, runs) }
}

/// [`values_batch`] of `src`, written to `dst`.
pub fn values_batch_from(src: &[K8], dst: &mut [K8], offset: F64, runs: bool) {
    assert_eq!(src.len(), dst.len());
    assert!(!runs || dst.len() >= 8);
    let kind = Forward(Twiddles::new(offset, dst.len().trailing_zeros() as usize));
    // SAFETY: `dst`'s own rows, read first from `src`'s.
    unsafe { run(words(dst), Some(src.as_ptr().cast()), dst.len(), 0, &kind, runs) }
}

/// Each eight rows transposed, as [`values_batch`]'s `runs` leaves them (`data.len()` a multiple of 8).
pub fn transpose_runs(data: &mut [K8]) {
    for group in data.chunks_exact_mut(8) {
        let rows: [V; 8] = std::array::from_fn(|q| Kx8::row(&group[q]).0);
        for (row, t) in group.iter_mut().zip(transpose(rows)) {
            *row = Kx8(t).to_row();
        }
    }
}

/// `crate::domain::coefficients` on a batch.
pub fn coefficients_batch(data: &mut [K8], offset: F64) {
    let kind = Inverse(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    // SAFETY: `data`'s own rows.
    unsafe { run(words(data), None, data.len(), 0, &kind, false) }
}

/// `crate::domain::values` on one column.
pub fn values(data: &mut [F64], offset: F64) {
    if data.len() < 8 {
        return crate::domain::values(data, offset);
    }
    let kind = Forward(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    // SAFETY: `data`'s own words, eight a row.
    unsafe { run(data.as_mut_ptr().cast(), None, data.len() / 8, 3, &kind, false) }
}

/// [`values`] of `src`, written to `dst`.
pub fn values_from(src: &[F64], dst: &mut [F64], offset: F64) {
    assert_eq!(src.len(), dst.len());
    if dst.len() < 8 {
        dst.copy_from_slice(src);
        return crate::domain::values(dst, offset);
    }
    let kind = Forward(Twiddles::new(offset, dst.len().trailing_zeros() as usize));
    // SAFETY: `dst`'s own words, eight a row, read first from `src`'s.
    unsafe {
        run(
            dst.as_mut_ptr().cast(),
            Some(src.as_ptr().cast()),
            dst.len() / 8,
            3,
            &kind,
            false,
        )
    }
}

/// [`coefficients`] of `src`, written to `dst`.
pub fn coefficients_from(src: &[F64], dst: &mut [F64], offset: F64) {
    assert_eq!(src.len(), dst.len());
    if dst.len() < 8 {
        dst.copy_from_slice(src);
        return crate::domain::coefficients(dst, offset);
    }
    let kind = Inverse(Twiddles::new(offset, dst.len().trailing_zeros() as usize));
    // SAFETY: `dst`'s own words, eight a row, read first from `src`'s.
    unsafe {
        run(
            dst.as_mut_ptr().cast(),
            Some(src.as_ptr().cast()),
            dst.len() / 8,
            3,
            &kind,
            false,
        )
    }
}

/// `crate::domain::coefficients` on one column.
pub fn coefficients(data: &mut [F64], offset: F64) {
    if data.len() < 8 {
        return crate::domain::coefficients(data, offset);
    }
    let kind = Inverse(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    // SAFETY: `data`'s own words, eight a row.
    unsafe { run(data.as_mut_ptr().cast(), None, data.len() / 8, 3, &kind, false) }
}

/// Eight K elements in a register: a column at eight consecutive points.
#[derive(Clone, Copy)]
pub struct Kx8(V);

impl Kx8 {
    /// A row of a batch, as [`values_batch`]'s `runs` leaves it.
    #[inline(always)]
    pub fn row(x: &K8) -> Self {
        // SAFETY: a row's eight words.
        Self(unsafe { load(x.0.as_ptr().cast()) })
    }

    /// The first eight of `x`.
    #[inline(always)]
    pub fn load(x: &[F64]) -> Self {
        assert!(x.len() >= 8);
        // SAFETY: eight words of `x`.
        Self(unsafe { load(x.as_ptr().cast()) })
    }

    #[inline(always)]
    pub fn new(x: [F64; 8]) -> Self {
        Self(from_array(x.map(|v| v.0)))
    }

    #[inline(always)]
    pub fn splat(x: F64) -> Self {
        Self(splat(x.0))
    }

    #[inline(always)]
    pub fn to_row(self) -> K8 {
        let mut out = K8::ZERO;
        // SAFETY: a row's eight words.
        unsafe { store(out.0.as_mut_ptr().cast(), self.0) };
        out
    }
}

impl Add for Kx8 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self(xor(self.0, rhs.0))
    }
}

impl Mul for Kx8 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        Self(mul(self.0, rhs.0))
    }
}

/// Eight E elements in three registers, limb by limb.
#[derive(Clone, Copy)]
pub struct Ex8([V; 3]);

impl Ex8 {
    #[inline(always)]
    pub fn splat(x: F192) -> Self {
        Self([splat(x.c0), splat(x.c1), splat(x.c2)])
    }

    #[inline(always)]
    pub fn from_limbs(l: [Kx8; 3]) -> Self {
        Self(l.map(|k| k.0))
    }

    /// K lanes as E lanes.
    #[inline(always)]
    pub fn from_k(k: Kx8) -> Self {
        Self([k.0, splat(0), splat(0)])
    }

    #[inline(always)]
    pub fn limbs(self) -> [Kx8; 3] {
        self.0.map(Kx8)
    }

    /// Lane `i` times `k_i` in K.
    #[inline(always)]
    pub fn mul_k(self, k: Kx8) -> Self {
        Self(self.0.map(|l| mul(l, k.0)))
    }
}

impl Add for Ex8 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self([
            xor(self.0[0], rhs.0[0]),
            xor(self.0[1], rhs.0[1]),
            xor(self.0[2], rhs.0[2]),
        ])
    }
}

impl Mul for Ex8 {
    type Output = Self;
    /// Karatsuba's six lane products, then the fold of `y^3 = y + 1` (`gf2_64x3::x86_64::fold`), three reductions.
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        let ([a0, a1, a2], [b0, b1, b2]) = (self.0, rhs.0);
        let (p0, p1, p2) = (clmul_u(a0, b0), clmul_u(a1, b1), clmul_u(a2, b2));
        let p01 = clmul_u(xor(a0, a1), xor(b0, b1));
        let p02 = clmul_u(xor(a0, a2), xor(b0, b2));
        let p12 = clmul_u(xor(a1, a2), xor(b1, b2));
        let d0 = xor_u(xor_u(p0, p1), xor_u(p2, p12));
        let d1 = xor_u(xor_u(p0, p01), p12);
        let d2 = xor_u(xor_u(p0, p1), p02);
        Self([reduce_u(d0), reduce_u(d1), reduce_u(d2)])
    }
}

/// An E constant in every lane, for [`MixedSum::add`].
#[derive(Clone, Copy)]
pub struct ESplat([V; 3]);

impl ESplat {
    pub fn new(c: F192) -> Self {
        Self([splat(c.c0), splat(c.c1), splat(c.c2)])
    }
}

/// `Σ c k` over E constants `c` and K lanes `k`, unreduced until [`MixedSum::reduce`].
#[derive(Clone, Copy)]
pub struct MixedSum([U; 3]);

impl Default for MixedSum {
    fn default() -> Self {
        Self([zero_u(), zero_u(), zero_u()])
    }
}

impl MixedSum {
    #[inline(always)]
    pub fn add(&mut self, c: &ESplat, k: Kx8) {
        for (acc, &l) in self.0.iter_mut().zip(&c.0) {
            *acc = xor_u(*acc, clmul_u(l, k.0));
        }
    }

    #[inline(always)]
    pub fn reduce(self) -> Ex8 {
        Ex8(self.0.map(reduce_u))
    }
}

/// `out[k][8 j + p]` is limb `k` of `f(j)`'s lane `p`, the last run cut at the outputs' length.
pub fn fill_limbs8(out: [&mut [F64]; 3], f: impl Fn(usize) -> Ex8 + Sync) {
    let len = out[0].len();
    assert!(out.iter().all(|o| o.len() == len));
    let ptrs = out.map(|o| SendPtr(o.as_mut_ptr()));
    let runs = len.div_ceil(8);
    const BLOCK: usize = 128;
    parallel::for_each(runs.div_ceil(BLOCK), |b| {
        for j in b * BLOCK..((b + 1) * BLOCK).min(runs) {
            let limbs = f(j).0;
            for (ptr, limb) in ptrs.iter().zip(limbs) {
                // SAFETY: a task writes its own runs of the three outputs, each `len` long.
                unsafe {
                    if 8 * j + 8 <= len {
                        store(ptr.add(8 * j).cast(), limb);
                    } else {
                        let row = Kx8(limb).to_row();
                        std::ptr::copy_nonoverlapping(row.0.as_ptr(), ptr.add(8 * j), len - 8 * j);
                    }
                }
            }
        }
    });
}

/// `out[k][i]` is limb `k` of `f(i)`, in parallel blocks of `block` entries.
pub fn fill_limbs(out: [&mut [F64]; 3], block: usize, f: impl Fn(usize) -> F192 + Sync) {
    let len = out[0].len();
    assert!(out.iter().all(|o| o.len() == len));
    let ptrs = out.map(|o| SendPtr(o.as_mut_ptr()));
    parallel::for_each(len.div_ceil(block), |b| {
        for i in b * block..((b + 1) * block).min(len) {
            let v = f(i);
            // SAFETY: a task writes its own block of the three outputs, each `len` long.
            unsafe {
                *ptrs[0].add(i) = F64(v.c0);
                *ptrs[1].add(i) = F64(v.c1);
                *ptrs[2].add(i) = F64(v.c2);
            }
        }
    });
}

/// Columns (at most eight, of one length) as a batch, the absent lanes zero.
pub fn pack(columns: &[&[F64]]) -> Vec<K8> {
    assert!(columns.len() <= 8);
    let n = columns.first().map_or(0, |c| c.len());
    assert!(columns.iter().all(|c| c.len() == n));
    parallel::map_collect(n, |i| {
        K8(std::array::from_fn(|l| columns.get(l).map_or(F64::ZERO, |c| c[i])))
    })
}

/// `Π_(bits b of h) c[b]` for every `h < len` (the weights of a fold): `c[b]` for the bits of `h`, ...
fn tensor(len: usize, factor: impl Fn(usize, bool) -> F64) -> Vec<F64> {
    let mut out = vec![F64::ONE];
    let mut b = 0;
    while out.len() < len {
        let (zero, one) = (factor(b, false), factor(b, true));
        let half = out.len();
        out.resize(2 * half, F64::ZERO);
        let (low, high) = out.split_at_mut(half);
        parallel::chunks_mut_zip(high, low, 1 << 12, |_, h, l| {
            h.iter_mut().zip(l).for_each(|(h, &l)| *h = l * one)
        });
        if zero != F64::ONE {
            parallel::chunks_mut(low, 1 << 12, |_, l| l.iter_mut().for_each(|x| *x *= zero));
        }
        b += 1;
    }
    out.truncate(len);
    out
}

/// The weights folding a polynomial's novel coefficients (`len` blocks of `2^e`) onto the coset `ω_first + V_e`:
/// `Π w_(e + b)(ω_first)` over the bits `b` of the block, since `w_l` is constant there for `l ≥ e`.
fn novel_weights(len: usize, first: usize, e: usize) -> Vec<F64> {
    tensor(len, |b, bit| if bit { point(first >> (e + b)) } else { F64::ONE })
}

/// `dst` row `i` is `Σ_h weights[h] src[i + h dst_rows]`.
///
/// # Safety
/// `src` holds `weights.len() dst_rows` rows, `dst` `dst_rows`, disjoint.
unsafe fn fold_rows(src: *const u64, dst: *mut u64, dst_rows: usize, weights: &[F64]) {
    let (src, dst) = (SendPtr(src.cast_mut()), SendPtr(dst));
    if dst_rows < 64 {
        // Few rows: the blocks `h` split among the workers, their partial sums added.
        let per = weights.len().div_ceil(64).max(1);
        let sum = parallel::map_reduce(
            weights.len().div_ceil(per),
            || vec![K8::ZERO; dst_rows],
            |task| {
                let mut acc = vec![K8::ZERO; dst_rows];
                for h in task * per..((task + 1) * per).min(weights.len()) {
                    let w = splat(weights[h].0);
                    for (i, a) in acc.iter_mut().enumerate() {
                        let p: *mut u64 = a.0.as_mut_ptr().cast();
                        // SAFETY: row `i + h dst_rows` of `src`, and the accumulator's own row.
                        unsafe { store(p, xor(load(p), mul(load(src.add(8 * (i + h * dst_rows))), w))) }
                    }
                }
                acc
            },
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(&b) {
                    x.0.iter_mut().zip(&y.0).for_each(|(x, &y)| *x += y);
                }
                a
            },
        );
        // SAFETY: `dst_rows` rows of `dst`.
        unsafe { std::ptr::copy_nonoverlapping(sum.as_ptr().cast::<u64>(), dst.add(0), 8 * dst_rows) };
        return;
    }
    let chunk = (dst_rows / 128).clamp(1, 64);
    parallel::for_each(dst_rows / chunk, |task| {
        // SAFETY: a task writes its own `chunk` rows of `dst` and reads `src`.
        unsafe {
            for i in task * chunk..(task + 1) * chunk {
                let mut acc = load(src.add(8 * i));
                if weights[0] != F64::ONE {
                    acc = mul(acc, splat(weights[0].0));
                }
                for (h, &w) in weights.iter().enumerate().skip(1) {
                    acc = xor(acc, mul(load(src.add(8 * (i + h * dst_rows))), splat(w.0)));
                }
                store(dst.add(8 * i), acc);
            }
        }
    });
}

/// A batch of novel coefficients folded onto the coset `ω_first + V_e` (`2^e ≤ src.len()`), into `dst`.
pub fn fold_batch(src: &[K8], first: usize, dst: &mut [K8]) {
    let rows = dst.len();
    assert_eq!(src.len() % rows, 0);
    let weights = novel_weights(src.len() / rows, first, rows.trailing_zeros() as usize);
    // SAFETY: `src` is `weights.len()` blocks of `dst`'s rows.
    unsafe { fold_rows(src.as_ptr().cast(), words(dst), rows, &weights) }
}

/// The column with `weights`' fold onto `2^e` entries: `out[i] = Σ_h weights[h] data[i + h 2^e]`.
fn fold_column(data: &[F64], e: usize, weights: &[F64]) -> Vec<F64> {
    let size = 1usize << e;
    assert_eq!(data.len(), weights.len() * size);
    if size < 8 {
        let per = weights.len().div_ceil(64).max(1);
        return parallel::map_reduce(
            weights.len().div_ceil(per),
            || vec![F64::ZERO; size],
            |task| {
                let mut acc = vec![F64::ZERO; size];
                for h in task * per..((task + 1) * per).min(weights.len()) {
                    acc.iter_mut()
                        .zip(&data[h * size..])
                        .for_each(|(a, &x)| *a += weights[h] * x);
                }
                acc
            },
            |mut a, b| {
                a.iter_mut().zip(&b).for_each(|(x, &y)| *x += y);
                a
            },
        );
    }
    let mut out = vec![F64::ZERO; size];
    // SAFETY: `data` is `weights.len()` blocks of `out`'s rows.
    unsafe { fold_rows(data.as_ptr().cast(), out.as_mut_ptr().cast(), size / 8, weights) }
    out
}

/// The values on the coset `ω_first + V_e` of the column of novel coefficients `novel` (any multiple of `2^e` of
/// them, `2^e | first`).
pub fn on_coset_prefix(novel: &[F64], first: usize, e: usize) -> Vec<F64> {
    let size = 1usize << e;
    if novel.len() == size {
        let mut out = vec![F64::ZERO; size];
        values_from(novel, &mut out, point(first));
        return out;
    }
    let mut out = fold_column(novel, e, &novel_weights(novel.len() / size, first, e));
    values(&mut out, point(first));
    out
}

/// `ṽ(bits(i) + δ)` for every `i < 2^e`, `ṽ` the multilinear of `values` (`2^r` of them, `e ≤ r`): the top `r - e`
/// variables at `δ` (a fold), then the shifted cube of the rest.
pub fn shifted_cube(values: &[F64], delta: &[F64], e: usize) -> Vec<F64> {
    let r = values.len().trailing_zeros() as usize;
    assert!(e <= r && delta.len() >= r);
    let mut out = if e == r {
        values.to_vec()
    } else {
        let weights = tensor(
            1 << (r - e),
            |b, bit| if bit { delta[e + b] } else { F64::ONE + delta[e + b] },
        );
        fold_column(values, e, &weights)
    };
    if out.len() < 8 {
        for (l, &d) in delta[..e].iter().enumerate() {
            let half = 1usize << l;
            for pair in out.chunks_exact_mut(2 * half) {
                let (lo, hi) = pair.split_at_mut(half);
                for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                    let t = d * (*a + *b);
                    *a += t;
                    *b += t;
                }
            }
        }
        return out;
    }
    let kind = Cube {
        delta: delta[..e].to_vec(),
    };
    // SAFETY: `out`'s own words, eight a row.
    unsafe { run(out.as_mut_ptr().cast(), None, out.len() / 8, 3, &kind, false) }
    out
}

/// The interpolation blocks: `count` rounded up to a multiple of `2^grain`, in binary, largest first.
pub fn prefix_sizes(count: u64, grain: usize) -> Vec<usize> {
    let units = count.max(1).div_ceil(1 << grain);
    (0..64)
        .rev()
        .filter(|&b| units >> b & 1 == 1)
        .map(|b| b + grain)
        .collect()
}

/// The first point of each block, from `base`: block `j` is the coset `ω_(starts[j]) + V_(sizes[j])`.
pub fn prefix_starts(sizes: &[usize], base: usize) -> Vec<usize> {
    let mut at = base;
    sizes
        .iter()
        .map(|&e| {
            let s = at;
            at += 1 << e;
            s
        })
        .collect()
}

/// The novel coefficients of the polynomial of degree `< T = Σ 2^(sizes[j])` whose values at `ω_(base + i)`, `i < T`,
/// are `data` (in place). `sizes` decrease strictly and `2^(sizes[0] + 1) | base`.
///
/// With `R_0 = Q` and `R_j = Q_j + w_(e_j) R_(j+1)`, `deg Q_j < 2^(e_j)`: on block `j`, `w_(e_j)` is a constant
/// `λ_j`, so the inverse transform there gives `U_j = Q_j + λ_j R_(j+1)`; on the later blocks `w_(e_j) = λ_j + 1`, so
/// `R_(j+1) = R_j + U_j` there. Last, `Q_j = U_j + λ_j R_(j+1)` from the end, and `Q = [Q_0, Q_1, ...]` (since
/// `X_(2^e + k) = w_e X_k`).
pub fn interpolate_prefix(data: &mut [F64], sizes: &[usize], base: usize) {
    let total: usize = sizes.iter().map(|&e| 1usize << e).sum();
    assert_eq!(data.len(), total);
    assert!(sizes.windows(2).all(|w| w[0] > w[1]) && base % (2 << sizes[0]) == 0);
    let starts = prefix_starts(sizes, base);
    for j in 0..sizes.len() {
        let (at, e) = (starts[j] - base, sizes[j]);
        let (head, tail) = data.split_at_mut(at + (1 << e));
        let u = &mut head[at..];
        coefficients(u, point(starts[j]));
        for l in j + 1..sizes.len() {
            let mut add = on_coset_prefix(u, starts[l], sizes[l]);
            let from = starts[l] - starts[j] - (1 << e);
            let block = &mut tail[from..from + (1 << sizes[l])];
            parallel::chunks_mut_zip(block, &add, 1 << 14, |_, b, a| {
                b.iter_mut().zip(a).for_each(|(x, &y)| *x += y)
            });
            add.clear();
        }
    }
    for j in (0..sizes.len().saturating_sub(1)).rev() {
        let (at, e) = (starts[j] - base, sizes[j]);
        let lambda = point(starts[j] >> e);
        let (q, rest) = data.split_at_mut(at + (1 << e));
        let q = &mut q[at..at + rest.len()];
        parallel::chunks_mut_zip(q, rest, 1 << 14, |_, q, r| {
            q.iter_mut().zip(r).for_each(|(x, &y)| *x += lambda * y)
        });
    }
}

/// Novel to `B` coefficients (or back), in place: `b_k = Σ_(j ⊆ k) a_j`. The low variables on blocks of 256 KiB
/// one worker holds, then the rest a few at a time on tiles. The variables' maps commute.
pub fn subset_sums<M: Copy + Send + Sync + Add<Output = M>>(data: &mut [M]) {
    let n = data.len();
    assert!(n.is_power_of_two());
    let m = n.trailing_zeros() as usize;
    let leaf = m.min(((1usize << 18) / std::mem::size_of::<M>()).max(2).ilog2() as usize);
    parallel::chunks_mut(data, 1 << leaf, |_, block| {
        let mut half = 1;
        while half < block.len() {
            for pair in block.chunks_exact_mut(2 * half) {
                let (lo, hi) = pair.split_at_mut(half);
                for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                    *h = *h + l;
                }
            }
            half *= 2;
        }
    });
    let base = SendPtr(data.as_mut_ptr());
    let mut a = leaf;
    while a < m {
        let g = (m - a).min(8);
        let lines = 1usize << g;
        let width = ((1usize << leaf) >> g).clamp(1, 1 << a);
        let per_group = (1usize << a) / width;
        parallel::for_each((n >> (a + g)) * per_group, |task| {
            let e0 = ((task / per_group) << (a + g)) + (task % per_group) * width;
            for j in 0..g {
                let hs = 1usize << j;
                for ub in (0..lines).step_by(2 * hs) {
                    for u in ub..ub + hs {
                        // SAFETY: a task touches the runs `e0 + (u << a) + [0, width)`, `u < lines`: its own; the
                        // two runs here are distinct.
                        let (lo, hi) = unsafe {
                            (
                                base.slice(e0 + (u << a), width),
                                base.slice(e0 + ((u + hs) << a), width),
                            )
                        };
                        for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                            *h = *h + l;
                        }
                    }
                }
            }
        });
        a += g;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rng(seed: u64) -> impl FnMut() -> u64 {
        let mut state = seed | 1;
        move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        }
    }

    /// The transforms are `quotient::domain`'s, on one column and on a batch, at every size up to two wide passes.
    #[test]
    fn transforms_are_the_domains() {
        let mut next = rng(3);
        for m in [0usize, 1, 2, 3, 4, 5, 9, 12, 13, 17, 19] {
            let offset = point(1 << 21) + point(5 << m);
            let column: Vec<F64> = (0..1usize << m).map(|_| F64(next())).collect();
            let mut want = column.clone();
            crate::domain::values(&mut want, offset);
            let mut got = column.clone();
            values(&mut got, offset);
            assert_eq!(got, want, "values, 2^{m}");
            coefficients(&mut got, offset);
            assert_eq!(got, column, "coefficients, 2^{m}");
            let mut want_inv = column.clone();
            crate::domain::coefficients(&mut want_inv, offset);
            let mut got_inv = column.clone();
            coefficients(&mut got_inv, offset);
            assert_eq!(got_inv, want_inv, "coefficients of values, 2^{m}");

            let columns: Vec<Vec<F64>> = (0..5)
                .map(|_| (0..1usize << m).map(|_| F64(next())).collect())
                .collect();
            let refs: Vec<&[F64]> = columns.iter().map(|c| &c[..]).collect();
            let batch = pack(&refs);
            let mut out = vec![K8::ZERO; batch.len()];
            if batch.len() >= 8 {
                values_batch_from(&batch, &mut out, offset, true);
                transpose_runs(&mut out);
                let mut again = batch.clone();
                values_batch(&mut again, offset, false);
                assert_eq!(again, out, "batch values in place, 2^{m}");
            }
            values_batch_from(&batch, &mut out, offset, false);
            for (l, c) in columns.iter().enumerate() {
                let mut w = c.clone();
                crate::domain::values(&mut w, offset);
                assert!(out.iter().zip(&w).all(|(row, &x)| row.0[l] == x), "batch values, 2^{m}");
            }
            assert!(out.iter().all(|row| row.0[5..].iter().all(|x| x.is_zero())));
            coefficients_batch(&mut out, offset);
            assert_eq!(out, batch, "batch coefficients, 2^{m}");
        }
    }

    /// The fold onto a smaller coset, the shifted cube and the subset sums against their direct definitions.
    #[test]
    fn folds_and_cubes() {
        let mut next = rng(5);
        let r = 12;
        let novel: Vec<F64> = (0..1usize << r).map(|_| F64(next())).collect();
        let first = (1 << 20) + (3 << 9);
        for e in [0usize, 2, 3, 9, 12] {
            let first = first & !((1usize << e) - 1);
            let got = on_coset_prefix(&novel, first, e);
            // Against the whole transform on the aligned coset of V_r holding it.
            let big = first & !((1usize << r) - 1);
            let mut all = novel.clone();
            crate::domain::values(&mut all, point(big));
            assert_eq!(
                got,
                all[first - big..first - big + (1 << e)].to_vec(),
                "fold onto 2^{e}"
            );
        }
        let table: Vec<F64> = (0..1usize << r).map(|_| F64(next())).collect();
        let delta: Vec<F64> = (0..r).map(|_| F64(next())).collect();
        let mut full = table.clone();
        for (l, &d) in delta.iter().enumerate() {
            let half = 1usize << l;
            for pair in full.chunks_exact_mut(2 * half) {
                let (lo, hi) = pair.split_at_mut(half);
                for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                    let t = d * (*a + *b);
                    *a += t;
                    *b += t;
                }
            }
        }
        for e in [0usize, 2, 3, 7, 12] {
            assert_eq!(shifted_cube(&table, &delta, e), full[..1 << e].to_vec(), "cube, 2^{e}");
        }
        for m in [0usize, 3, 15, 16, 23] {
            let data: Vec<F64> = (0..1usize << m).map(|_| F64(next())).collect();
            let mut want = data.clone();
            let mut half = 1;
            while half < want.len() {
                for pair in want.chunks_exact_mut(2 * half) {
                    let (lo, hi) = pair.split_at_mut(half);
                    for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                        *h += l;
                    }
                }
                half *= 2;
            }
            let mut got = data;
            subset_sums(&mut got);
            assert_eq!(got, want, "subset sums, 2^{m}");
        }
    }

    /// The lane types are the field's, lane by lane; the runs' transpose is a transpose.
    #[test]
    fn lanes_are_the_fields() {
        let mut next = rng(11);
        let mut e = || F192::new(next(), next(), next());
        let a: [F192; 8] = std::array::from_fn(|_| e());
        let b: [F192; 8] = std::array::from_fn(|_| e());
        let c = e();
        let limbs = |x: &[F192; 8]| -> [Kx8; 3] {
            [0, 1, 2].map(|k| Kx8::new(std::array::from_fn(|p| F64([x[p].c0, x[p].c1, x[p].c2][k]))))
        };
        let back = |x: Ex8| -> [F192; 8] {
            let l = x.limbs().map(|k| k.to_row());
            std::array::from_fn(|p| F192::new(l[0].0[p].0, l[1].0[p].0, l[2].0[p].0))
        };
        let (va, vb) = (Ex8::from_limbs(limbs(&a)), Ex8::from_limbs(limbs(&b)));
        assert_eq!(back(va * vb), std::array::from_fn(|p| a[p] * b[p]));
        assert_eq!(back(va + vb), std::array::from_fn(|p| a[p] + b[p]));
        let k = limbs(&b)[1];
        let kr = k.to_row();
        assert_eq!(back(va.mul_k(k)), std::array::from_fn(|p| a[p].mul_base(kr.0[p])));
        let mut sum = MixedSum::default();
        sum.add(&ESplat::new(c), k);
        sum.add(&ESplat::new(a[3]), k * k);
        let want: [F192; 8] = std::array::from_fn(|p| c.mul_base(kr.0[p]) + a[3].mul_base(kr.0[p] * kr.0[p]));
        assert_eq!(back(sum.reduce() + Ex8::splat(F192::ZERO)), want);
        assert_eq!(back(Ex8::from_k(k)), std::array::from_fn(|p| F192::from(kr.0[p])));
        let mut rows: Vec<K8> = (0..16).map(|_| K8(std::array::from_fn(|_| F64(next())))).collect();
        let before = rows.clone();
        transpose_runs(&mut rows);
        for g in 0..2 {
            for (l, row) in rows[8 * g..8 * g + 8].iter().enumerate() {
                assert!((0..8).all(|p| row.0[p] == before[8 * g + p].0[l]));
            }
        }
        let mut out: [Vec<F64>; 3] = std::array::from_fn(|_| vec![F64::ZERO; 13]);
        let [o0, o1, o2] = &mut out;
        fill_limbs8([o0, o1, o2], |j| Ex8::splat(F192::new(j as u64, 7, 9)));
        assert!(out[0].iter().enumerate().all(|(i, x)| x.0 == (i / 8) as u64) && out[2].iter().all(|x| x.0 == 9));
    }

    /// The interpolation from the first points of `D_M` is the whole coset's, for a polynomial of the degree.
    #[test]
    fn prefix_interpolation() {
        let mut next = rng(7);
        for (count, grain) in [
            (1usize, 0usize),
            (5, 0),
            (1000, 3),
            (1 << 10, 4),
            (5000, 6),
            (37_000, 10),
        ] {
            let sizes = prefix_sizes(count as u64, grain);
            let total: usize = sizes.iter().map(|&e| 1usize << e).sum();
            assert!(total >= count);
            let m = sizes[0] + 1;
            let novel: Vec<F64> = (0..total)
                .map(|i| if i < count { F64(next()) } else { F64::ZERO })
                .collect();
            let mut all = novel.clone();
            all.resize(1 << m, F64::ZERO);
            crate::domain::values(&mut all, point(1 << m));
            let mut got = all[..total].to_vec();
            interpolate_prefix(&mut got, &sizes, 1 << m);
            assert_eq!(got, novel, "count {count}, blocks {sizes:?}");
        }
    }
}
