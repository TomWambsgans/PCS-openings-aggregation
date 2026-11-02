# Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (E2ESoundness.lean).
"""Recompute Soundness.ksBound exactly, and the extractor's Guruswami-Sudan parameters at the
deployed witness table (mu = 25, R = 1), from the Lean definitions (transcribed: RpmV.lean's
ksBound, WhirBridge/Verifier.lean's openingBound, Cost.lean's verifierPermCalls; mumbai's
Statement/Extractor.lean's johnsonThreshold, gsNumVars, gsNumConstraints, gsPass,
gsMultiplicityBoundAt, gsMultiplicityAt).

    python3 -I formal/EndToEnd/Review/E2ESoundnessNumbers.py
"""
from fractions import Fraction as Fr
from math import isqrt, log2


def opening_bound(x):
    a = x + 10122
    return Fr(a) * (Fr(1, 2**128) + Fr(5 * a, 2**256))


setup_perm_calls = 2**20 * 2**32
verifier_perm_calls = (6 + 3 * 10122) * 2**32


def ks_bound(Q):
    b = 2**20 + (2**20 + Q) + 6
    N = b + 3 * 10122
    return (opening_bound(b) + opening_bound(b + 10122) + opening_bound(b + 2 * 10122)
            + Fr(N) * (Fr(1, 2**128) + Fr(5 * N, 2**256))
            + Fr((setup_perm_calls + Q + verifier_perm_calls) ** 2, 2**508))


def lg(f):
    return log2(f.numerator) - log2(f.denominator)


for e in [0, 20, 30, 40, 48, 64, 70, 80, 100, 126, 127]:
    Q = 2**e
    print(f"Q = 2^{e:3d}: ksBound = 2^{lg(ks_bound(Q)):.6f}")
print("ksBound(2^64) <= 2^-62 ?", ks_bound(2**64) <= Fr(1, 2**62))
print(f"ksBound(2^64) / 2^-62 - 1 = 2^{lg(ks_bound(2**64) * 2**62 - 1):.2f}")
lo, hi = 0, 2**200
while lo < hi:
    mid = (lo + hi) // 2
    if ks_bound(mid) >= 1:
        hi = mid
    else:
        lo = mid + 1
print(f"bound reaches 1 at Q = 2^{log2(lo):.3f}")

# --- the extractor's list decoder ---


def ceil_sqrt(x):
    s = isqrt(x)
    return s if s * s == x else s + 1


johnson_slack = [
    [34, 45, 55, 68, 85, 107, 134, 189, 237, 298, 375, 471, 663, 832],
    [34, 52, 65, 81, 102, 128, 161, 203, 255, 321, 404, 508, 639, 802],
    [51, 63, 79, 99, 124, 156, 196, 247, 311, 391, 492, 618, 776, 975],
    [49, 61, 77, 96, 121, 152, 191, 240, 303, 381, 478, 602, 756, 949]]


def johnson_threshold(mu, R):
    kappa = mu - 6
    n = 2 ** (kappa + R)
    D = 2**kappa - 1
    e = johnson_slack[R - 1][mu - 15]
    return (ceil_sqrt(2**44 * D * n) + e * n + 2**22 - 1) // 2**22


def gs_num_vars(k, W):
    return (W // (k - 1) + 1) * (2 * W + 2 - (k - 1) * (W // (k - 1))) // 2


def gs_num_constraints(n, m):
    return n * (m * (m + 1) // 2)


def gs_pass(k, n, A, m):
    W = m * A - 1
    return m > 0 and gs_num_constraints(n, m) < gs_num_vars(k, W) and W < m * A


def gs_bound(k, n, A):
    return ((k - 1) * n + 1) // (A * A - (k - 1) * n) + 1


def gs_multiplicity(k, n, A):
    b = gs_bound(k, n, A)
    for m in range(1, b):
        if gs_pass(k, n, A, m):
            return m
    return b


for mu in [15, 17, 20, 22, 25]:
    R = 1
    kappa = mu - 6
    n = 2 ** (kappa + R)
    k = 2**kappa
    A = johnson_threshold(mu, R)
    m = gs_multiplicity(k, n, A)
    W = m * A - 1
    ell = W // (k - 1)
    cons = gs_num_constraints(n, m)
    print(f"mu = {mu}: n = 2^{kappa + R} columns, A = {A} = {A / n:.4f} n "
          f"(unique decoding: > {(n + k) / 2 / n:.2f} n), multiplicity m = {m}, Y-degree l = {ell}, "
          f"conditions n m (m+1)/2 = 2^{log2(cons):.1f}, "
          f"(l+1) m n = 2^{log2((ell + 1) * m * n):.1f} elements of K")

# --- the extractor's stages at the deployed witness table (PcsQuotient/Extractor.lean's cost table) ---
# Counted in products of K, read off the loops of mumbai's novelInv/novelFwd and of Decoder.lean
# (toMono, gao, fromMono), constants dropped as in the table; not measured.
mu, R = 25, 1
kappa = mu - 6
m_ = kappa + R
n = 2**m_
k = 2**kappa
A = johnson_threshold(mu, R)
mult = gs_multiplicity(k, n, A)
ell = (mult * A - 1) // (k - 1)
fast_lane = (kappa * k + kappa * k / 2) + (kappa * n + kappa * n / 2)
ud_lane = (m_ * n + m_ * n / 2) + n * m_ * (m_ + 1) / 2 + 2**(kappa - 1) * kappa * (kappa + 1) / 2 \
    + (kappa * n + kappa * n / 2)
ud_per_error = 2 * (n + 1) + (n + k) / 2
e_max = (n - k) // 2
print(f"witness table: n = 2^{m_}, k = 2^{kappa}, Johnson threshold {A} ({A / n:.4f} n), "
      f"unique decoding from {(n + k) // 2} agreements (radius {e_max} = 2^{log2(e_max):.0f})")
print(f"fast path: 2^{log2(64 * fast_lane):.1f}")
print(f"unique decoder: 2^{log2(ud_lane):.1f} per lane + 2^{log2(ud_per_error):.1f} per wrong column; "
      f"64 lanes 2^{log2(64 * ud_lane):.1f}, at the radius "
      f"2^{log2(64 * (ud_lane + ud_per_error * e_max + 2 * e_max**2)):.1f}")
ms = (ell + 1)**3 * (mult * n)**2
print(f"list decoder: m = {mult}, l = {ell}, conditions 2^{log2(gs_num_constraints(n, mult)):.1f}, "
      f"Mulders-Storjohann (l+1)^3 (m n)^2 = 2^{log2(ms):.1f} per lane, 2^{log2(64 * ms):.1f} for 64")
