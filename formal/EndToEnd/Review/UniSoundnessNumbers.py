# Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (UniSound's Closed.lean).
"""Recompute UniSound.uniBound exactly, at the rounds' error e = 2^32 / |E| = 2^-160 that
uniKnowledgeSoundness_closed states, from the Lean definitions (transcribed: formal/UniSound's
Fs.lean uniN, uniBound; formal/WhirBridge's LargeSound.lean openingBoundAt).

    python3 -I formal/EndToEnd/Review/UniSoundnessNumbers.py
"""
from fractions import Fraction as Fr
from math import log2

E_CARD = 2**192
E32 = Fr(2**32, E_CARD)  # the rounds' error bound e = 2^32 / |E|


def opening_bound_at(qv, qa):
    """openingBoundAt QV QA = (QA + QV) (2^-128 + 5 (QA + QV) / 2^256)."""
    a = qa + qv
    return Fr(a) * (Fr(1, 2**128) + Fr(5 * a, 2**256))


def uni_n(q):
    return 2**33 + q


def uni_bound(e, q):
    """uniBound e Q = 5 openingBoundAt 10122 N + N (9952^2 e + (2^128 + 8 N) / 2^256)
    + (2^81 + Q)^2 / 2^508, N = 2^33 + Q."""
    n = uni_n(q)
    return (5 * opening_bound_at(10122, n)
            + Fr(n) * (9952**2 * e + Fr(2**128 + 8 * n, 2**256))
            + Fr((2**81 + q) ** 2, 2**508))


def lg(f):
    return log2(f.numerator) - log2(f.denominator)


for k in [0, 20, 32, 40, 48, 56, 60, 63, 64]:
    q = 2**k
    print(f"Q = 2^{k:2d}: uniBound(2^-160, Q) = 2^{lg(uni_bound(E32, q)):.6f}")

b = uni_bound(E32, 2**64)
n = uni_n(2**64)
parts = {
    "openings (5 doom terms)": 5 * opening_bound_at(10122, n),
    "list term N 9952^2 e": Fr(n) * 9952**2 * E32,
    "tag term N 2^128 / 2^256": Fr(n) * Fr(2**128, 2**256),
    "chain term 8 N^2 / 2^256": Fr(n) * Fr(8 * n, 2**256),
    "permutation term (2^81 + Q)^2 / 2^508": Fr((2**81 + 2**64) ** 2, 2**508),
}
for name, v in parts.items():
    print(f"  {name:40s} 2^{lg(v):.4f}")
print(f"uniBound(2^-160, 2^64) = 2^{lg(b):.6f}")
print("uniBound(2^-160, 2^64) <= 2^-61 ?", b <= Fr(1, 2**61))
print("uniBound(2^-160, 2^64) <= 2^-62 ?", b <= Fr(1, 2**62))
# uniBound is increasing in Q, so the bound at 2^64 bounds every Q <= 2^64.
assert all(uni_bound(E32, 2**k) <= uni_bound(E32, 2**(k + 1)) for k in range(64))
assert b <= Fr(1, 2**61)
