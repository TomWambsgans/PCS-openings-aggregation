# Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (UniSound's Closed128.lean).
"""Recompute UniSound.uniBound128 exactly, at the rounds' error e = 2^32 / |E| = 2^-160 that
uniKnowledgeSoundness_closed128 states, from the Lean definition (transcribed: formal/UniSound's
Fs.lean uniN, Fs128.lean uniBound128), and compare with uniBound (UniSoundnessNumbers.py).

    python3 -I formal/EndToEnd/Review/UniSoundnessNumbers128.py
"""
from fractions import Fraction as Fr
from math import log2

E_CARD = 2**192
E32 = Fr(2**32, E_CARD)  # the rounds' error bound e = 2^32 / |E|
EPS = Fr(269, 2**137)    # WhirBridge.εExact: the exact certified per-group bound


def uni_n(q):
    return 2**33 + q


def uni_bound128(e, q):
    """uniBound128 e Q = N (ε + 5 N / 2^256) + N (9952^2 e + 8 N / 2^256) + 2 N^2 / 2^256
    + (2^81 + Q)^2 / 2^508, N = 2^33 + Q, ε = 269 / 2^137."""
    n = uni_n(q)
    return (Fr(n) * (EPS + Fr(5 * n, 2**256))
            + Fr(n) * (9952**2 * e + Fr(8 * n, 2**256))
            + Fr(2 * n * n, 2**256)
            + Fr((2**81 + q) ** 2, 2**508))


def lg(f):
    return log2(f.numerator) - log2(f.denominator)


print(f"eps = 269 / 2^137 = 2^{lg(EPS):.4f} = {float(EPS * 2**128):.5f} * 2^-128")
for k in [0, 20, 32, 40, 48, 56, 60, 63, 64]:
    q = 2**k
    b = uni_bound128(E32, q)
    print(f"Q = 2^{k:2d}: uniBound128(2^-160, Q) = 2^{lg(b):.6f}, Q / bound = 2^{k - lg(b):.4f}")

b = uni_bound128(E32, 2**64)
n = uni_n(2**64)
parts = {
    "openings, once (N eps)": Fr(n) * EPS,
    "openings' failure term 5 N^2 / 2^256": Fr(n) * Fr(5 * n, 2**256),
    "list term N 9952^2 e": Fr(n) * 9952**2 * E32,
    "chain term 8 N^2 / 2^256": Fr(n) * Fr(8 * n, 2**256),
    "seed pair 2 N^2 / 2^256": Fr(2 * n * n, 2**256),
    "permutation term (2^81 + Q)^2 / 2^508": Fr((2**81 + 2**64) ** 2, 2**508),
}
for name, v in parts.items():
    print(f"  {name:40s} 2^{lg(v):.4f}")
print(f"uniBound128(2^-160, 2^64) = 2^{lg(b):.6f}")
print("uniBound128(2^-160, 2^64) <= 2^-64 ?", b <= Fr(1, 2**64))
# uniBound128 is increasing in Q, so the bound at 2^64 bounds every Q <= 2^64.
assert all(uni_bound128(E32, 2**k) <= uni_bound128(E32, 2**(k + 1)) for k in range(64))
assert b <= Fr(1, 2**64)
# The certified groups: the weakest at 2^24 ..= 2^28 is 128.95 bits (review/whir_params.py --large),
# below the threshold: 2^-128.95 <= eps.
assert Fr(1, 2**128) * Fr(5176, 10000) <= EPS
