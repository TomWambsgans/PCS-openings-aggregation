# Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (UniSound's Rec3/Final3.lean).
"""Recompute UniSound.uniBound3 exactly (pi1-rec3: three openings) at the rounds' error e = 2^35 / |E| = 2^-157 that
uniKnowledgeSoundness3_bits states (the narrow pairs' 8 * 2^32 / |E|), from the Lean definitions (formal/UniSound's
Rec3/Fs3.lean uniBound3, Fs.lean uniN; formal/WhirBridge's LargeSound.lean openingBoundAt), beside the main line's
uniBound at 2^32 / |E| and pi1-rec3's per-round errors.

    python3 -I formal/EndToEnd/Review/UniRec3Numbers.py
"""
from fractions import Fraction as Fr
from math import log2

E_CARD = 2**192


def opening_bound_at(qv, qa):
    a = qa + qv
    return Fr(a) * (Fr(1, 2**128) + Fr(5 * a, 2**256))


def bound(openings, e, q):
    n = 2**33 + q
    return (openings * opening_bound_at(10122, n) + Fr(n) * (9952**2 * e + Fr(2**128 + 8 * n, 2**256))
            + Fr((2**81 + q) ** 2, 2**508))


def lg(f):
    return log2(f.numerator) - log2(f.denominator)


q = 2**64
e35 = Fr(2**35, E_CARD)
print(f"main line  uniBound (5 openings, 2^32/|E|) at Q = 2^64: 2^{lg(bound(5, Fr(2**32, E_CARD), q)):.4f}")
print(f"pi1-rec3   uniBound3 (3 openings, 2^35/|E|) at Q = 2^64: 2^{lg(bound(3, e35, q)):.4f}")
assert bound(3, e35, q) <= Fr(1, 2**61)
assert all(bound(3, e35, 2**k) <= bound(3, e35, 2**(k + 1)) for k in range(64))
L = 9952
# busBound reference (formal/UniSound/UniSound/Ids/LvLink.lean): pushes 5, 5, 3, 5, 5, 11 at heights 18 18 18 18 17 18,
# memory 2^21, bytecode 2^19.
N_BUS = sum(p * 2**h for p, h in zip([5, 5, 3, 5, 5, 11], [18, 18, 18, 18, 17, 18])) + 2**21 + 2**19 + 1
print("pi1-rec3's rounds, per round and per list pair (L = 9952, the Lean bound's list):")
for name, err in [("a narrow pair, degree 8, 160-bit challenge", Fr(8, 2**160)),
                  ("the last plain narrow round", Fr(2, 2**160)),
                  ("Flock's zerocheck squares (2^22 - 1 at kappa = 18)", Fr(2**22 - 1, E_CARD)),
                  ("the bus at alpha = (c, c^2, c^4, c^8): 16 N + 99, N = busBound reference", Fr(16 * N_BUS + 99, E_CARD))]:
    print(f"  {name:80s} alone {-lg(err):6.1f} bits, times L^2 {-lg(err * L * L):6.1f} bits")
print("  the design's 129.0 bits (review/leanvm_rec_params.py) sums the batch's 14 rounds over 4473^2:",
      f"{-lg((13 * Fr(8, 2**160) + Fr(2, 2**160) + Fr(3, E_CARD)) * 4473**2):.1f}")
