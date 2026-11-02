// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! GF(2)-linear maps of `E = GF(2^192)` of the form `x ↦ Σ_k c_k x^(2^k)`, `N` of them at once: the weight of
//! Frobenius-twisted terms of one point, `Σ_k c_k eq(p, u)^(2^k) = L(eq(p, u))` on the cube (`leanvm_univariate`'s
//! batching sumcheck). A crate of its own for the GFNI kernel's intrinsics, which are `unsafe`.
//!
//! A map is its 192 × 192 bit matrix, as 24 × 24 blocks of 8 × 8 bits (input byte `i` to output byte `o`). One
//! element at a time it is 24 byte tables, `L(x) = Σ_i T_i[byte_i(x)]`; eight at a time, with GFNI, each block is one
//! `vgf2p8affineqb` lane, on the eight elements' byte `i`.

use primitives::field::F192;

/// `N` maps `x ↦ Σ_k c_k x^(2^k)`.
pub struct Linear<const N: usize> {
    tables: Vec<[[F192; N]; 256]>,
    /// Map `n`'s blocks from input byte `i` to output bytes `8h..8h + 8`, as `vgf2p8affineqb` matrices (one qword per
    /// output byte): `affine[n][i][h]`.
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
    affine: Vec<[[[u64; 8]; 3]; 24]>,
}

impl<const N: usize> Linear<N> {
    /// `coefficients[n][k]` is map `n`'s coefficient of `x^(2^k)`.
    pub fn new(coefficients: [&[F192]; N]) -> Self {
        let top = coefficients.iter().map(|c| c.len()).max().unwrap_or(0);
        // The images of the 192 bits (bit `b` is bit `b mod 64` of limb `b / 64`).
        let images: Vec<[F192; N]> = (0..192)
            .map(|b| {
                let mut limbs = [0u64; 3];
                limbs[b / 64] = 1u64 << (b % 64);
                let mut power = F192::new(limbs[0], limbs[1], limbs[2]);
                let mut sum = [F192::ZERO; N];
                for k in 0..top {
                    for (s, c) in sum.iter_mut().zip(&coefficients) {
                        if let Some(&c) = c.get(k) {
                            *s += c * power;
                        }
                    }
                    power = power.square();
                }
                sum
            })
            .collect();
        let mut tables = vec![[[F192::ZERO; N]; 256]; 24];
        for (i, table) in tables.iter_mut().enumerate() {
            for v in 1..256usize {
                let low = v.trailing_zeros() as usize;
                table[v] = std::array::from_fn(|n| table[v & (v - 1)][n] + images[8 * i + low][n]);
            }
        }
        Self {
            tables,
            #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
            affine: (0..N).map(|n| affine_blocks(&images, n)).collect(),
        }
    }

    /// The maps at `x`.
    #[inline]
    pub fn at(&self, x: F192) -> [F192; N] {
        let mut acc = [F192::ZERO; N];
        for (limb, word) in [x.c0, x.c1, x.c2].into_iter().enumerate() {
            for byte in 0..8 {
                let entry = &self.tables[8 * limb + byte][(word >> (8 * byte)) as usize & 0xff];
                for (a, &e) in acc.iter_mut().zip(entry) {
                    *a += e;
                }
            }
        }
        acc
    }

    /// The maps at eight elements.
    #[inline]
    pub fn at8(&self, x: &[F192; 8]) -> [[F192; 8]; N] {
        #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
        {
            // SAFETY: the kernel's target features are enabled at compile time.
            unsafe { self.at8_gfni(x) }
        }
        #[cfg(not(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi")))]
        {
            let each: [[F192; N]; 8] = std::array::from_fn(|e| self.at(x[e]));
            std::array::from_fn(|n| std::array::from_fn(|e| each[e][n]))
        }
    }

    /// [`Self::at8`] by `vgf2p8affineqb`: the eight elements' limbs transposed so that qword lane `l` of limb `h`'s
    /// register holds byte `l` of the eight elements, then per input byte `i` (broadcast) and output limb `h`, one
    /// affine product by the blocks from byte `i` to the limb's eight bytes; the sums transposed back.
    #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
    #[inline]
    unsafe fn at8_gfni(&self, x: &[F192; 8]) -> [[F192; 8]; N] {
        use std::arch::x86_64::*;
        // SAFETY: the caller has the target features; every load and store is of an 8-qword array.
        unsafe {
            // Byte 8l + e <- byte 8e + l: the 8 × 8 byte transpose of a register's qwords.
            let transpose = _mm512_set_epi64(
                0x3f37_2f27_1f17_0f07,
                0x3e36_2e26_1e16_0e06,
                0x3d35_2d25_1d15_0d05,
                0x3c34_2c24_1c14_0c04,
                0x3b33_2b23_1b13_0b03,
                0x3a32_2a22_1a12_0a02,
                0x3931_2921_1911_0901,
                0x3830_2820_1810_0800,
            );
            let mut bytes = [[0u64; 8]; 3];
            for (h, limb) in bytes.iter_mut().enumerate() {
                let words: [u64; 8] = std::array::from_fn(|e| [x[e].c0, x[e].c1, x[e].c2][h]);
                let v = _mm512_permutexvar_epi8(transpose, _mm512_loadu_si512(words.as_ptr().cast()));
                _mm512_storeu_si512(limb.as_mut_ptr().cast(), v);
            }
            let mut out = [[F192::ZERO; 8]; N];
            for (n, out) in out.iter_mut().enumerate() {
                let blocks = &self.affine[n];
                let mut acc = [_mm512_setzero_si512(); 3];
                for i in 0..24 {
                    let src = _mm512_set1_epi64(bytes[i / 8][i % 8] as i64);
                    for (h, acc) in acc.iter_mut().enumerate() {
                        let m = _mm512_loadu_si512(blocks[i][h].as_ptr().cast());
                        *acc = _mm512_xor_si512(*acc, _mm512_gf2p8affine_epi64_epi8::<0>(src, m));
                    }
                }
                let mut limbs = [[0u64; 8]; 3];
                for (h, acc) in acc.into_iter().enumerate() {
                    _mm512_storeu_si512(limbs[h].as_mut_ptr().cast(), _mm512_permutexvar_epi8(transpose, acc));
                }
                for (e, o) in out.iter_mut().enumerate() {
                    *o = F192::new(limbs[0][e], limbs[1][e], limbs[2][e]);
                }
            }
            out
        }
    }
}

/// Map `n`'s blocks as `vgf2p8affineqb` matrices: from input byte `i`, the qword for output byte `8h + l` has, in its
/// byte `7 - k`, the input bits `m` that output bit `k` reads.
#[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "avx512vbmi"))]
fn affine_blocks<const N: usize>(images: &[[F192; N]], n: usize) -> [[[u64; 8]; 3]; 24] {
    let bit = |x: F192, b: usize| ([x.c0, x.c1, x.c2][b / 64] >> (b % 64)) & 1;
    std::array::from_fn(|i| {
        std::array::from_fn(|h| {
            std::array::from_fn(|l| {
                let o = 8 * h + l;
                (0..8).fold(0u64, |q, k| {
                    let row = (0..8).fold(0u64, |r, m| r | bit(images[8 * i + m][n], 8 * o + k) << m);
                    q | row << (8 * (7 - k))
                })
            })
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eight_at_once_are_the_tables() {
        let mut state = 0x1234_5678u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut e = || F192::new(next(), next(), next());
        let (a, b): (Vec<F192>, Vec<F192>) = (0..64).map(|_| (e(), e())).unzip();
        let map = Linear::new([&a[..], &b[..17]]);
        for _ in 0..16 {
            let x: [F192; 8] = std::array::from_fn(|_| e());
            let eight = map.at8(&x);
            for (k, &xk) in x.iter().enumerate() {
                let direct = |c: &[F192]| {
                    let (mut power, mut sum) = (xk, F192::ZERO);
                    for &ck in c {
                        sum += ck * power;
                        power = power.square();
                    }
                    sum
                };
                assert_eq!(map.at(xk), [direct(&a), direct(&b[..17])]);
                assert_eq!([eight[0][k], eight[1][k]], map.at(xk));
            }
        }
    }
}
