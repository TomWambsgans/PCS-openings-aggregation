# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
"""Review (crates/leanvm_rec/REVIEW-REC.md, attack 6): pi1-rec's derived challenges, re-derived.

1. eq at the power point. For r_i = c^(2^i) (i < n), eq(r, x) = prod_{x_i = 1} c^(2^i) prod_{x_i = 0} (1 + c^(2^i)) is
   a polynomial in c with coefficients in GF(2). Checked for n <= 12: it is sum_{y superset of x} c^y (bitmasks), so the
   2^n polynomials are unitriangular in the subset order, a basis of the polynomials of degree < 2^n over GF(2), hence
   over E. So sum_x S(x) eq(r(c), x) is the zeta transform of S in the monomials c^y: zero iff S = 0 (Moebius), and of
   degree <= 2^n - 1. This is SPEC-REC 1.4's zerocheck (n = 22) and bus (n = 4) argument.
2. The bus: f_tau(c) = sum_s eq(alpha(c), s) tau_s is injective on tuples (1.), and prod (beta + f_tau(c)) over a
   multiset determines it (each factor is monic of degree 1 in beta over the UFD E[c]). A Monte Carlo over GF(2^8)
   (a toy field, so the bound is visible) of random distinct multisets: the collision rate of the products at random
   (beta, c) is below the Schwartz-Zippel bound 15 |M| / |F|.
3. The numbers: SPEC-REC 5's 164.6 / 152.5 (bus) and 170.0 / 157.9 (zerocheck), from SPEC 9's rows and C1's list.

python3 -I review/review_fs_powers.py
"""

import math
import random


def poly_mul_gf2(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return out


def eq_at_powers(x, n):
    """eq((c, c^2, ..., c^(2^(n-1))), x) as a GF(2)[c] bitmask."""
    p = 1
    for i in range(n):
        factor = (1 << (1 << i)) if x >> i & 1 else (1 | (1 << (1 << i)))
        p = poly_mul_gf2(p, factor)
    return p


def check_unitriangular(n):
    for x in range(1 << n):
        p = eq_at_powers(x, n)
        expected = 0
        for y in range(1 << n):
            if y & x == x:
                expected |= 1 << y
        assert p == expected, (n, x)
        assert p.bit_length() - 1 == (1 << n) - 1  # every eq has full degree 2^n - 1
        assert p & ((1 << x) - 1) == 0 and p >> x & 1  # lowest monomial c^x: unitriangular
    return True


# GF(2^8) = GF(2)[z]/(z^8 + z^4 + z^3 + z + 1), for the toy Monte Carlo.
MOD = 0x11B


def gf_mul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 0x100:
            a ^= MOD
    return out


def gf_pow(a, e):
    out = 1
    while e:
        if e & 1:
            out = gf_mul(out, a)
        a = gf_mul(a, a)
        e >>= 1
    return out


def fingerprint(tau, c):
    alpha = [gf_pow(c, 1 << i) for i in range(4)]
    total = 0
    for s, t in enumerate(tau):
        w = 1
        for i in range(4):
            w = gf_mul(w, alpha[i] if s >> i & 1 else 1 ^ alpha[i])
        total ^= gf_mul(w, t)
    return total


def product(multiset, beta, c):
    out = 1
    for tau in multiset:
        out = gf_mul(out, beta ^ fingerprint(tau, c))
    return out


def monte_carlo(trials=4000, size=6, seed=7):
    rng = random.Random(seed)
    hits = 0
    for _ in range(trials):
        m = [tuple(rng.randrange(256) for _ in range(16)) for _ in range(size)]
        m2 = list(m)
        # Change one entry of one tuple: the closest distinct multiset.
        k, s = rng.randrange(size), rng.randrange(16)
        t = list(m2[k])
        t[s] ^= 1 + rng.randrange(255)
        m2[k] = tuple(t)
        beta, c = rng.randrange(256), rng.randrange(256)
        hits += product(m, beta, c) == product(m2, beta, c)
    return hits / trials, 15 * size / 256


def main():
    for n in range(1, 13):
        check_unitriangular(n)
    print("1. eq((c, c^2, ..., c^(2^(n-1))), x) = sum_{y >= x} c^y for n <= 12: unitriangular, a basis; degree 2^n - 1")
    rate, bound = monte_carlo()
    print(f"2. toy GF(2^8), |M| = 6, one entry changed: collision rate {rate:.4f} <= Schwartz-Zippel {bound:.4f}")
    assert rate <= bound
    logq = 192
    l1 = 4473  # C1's certified level-0 list at a 2^27 stack (SPEC 9)
    tuples = 2 ** 23.38  # SPEC 9: every table full
    bus = -math.log2(16 * tuples / 2 ** logq)
    flock = -math.log2((2 ** 7 + 2 ** 22) / 2 ** logq)  # SPEC 9's Flock row (about 2^7 / |E|) plus 2^22 / |E|
    print(f"3. bus with alpha = (c, c^2, c^4, c^8): {bus:.1f} bits alone, {bus - math.log2(l1):.1f} after C1's list")
    print(f"   Flock with the eq point as squares: {flock:.1f} bits alone, {flock - math.log2(l1):.1f} after C1's list")


if __name__ == "__main__":
    main()
