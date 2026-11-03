# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
"""pi2's completeness error delta2 (RecCompose.Pi2E.delta2, Pi2P.deltaStaged), in exact rationals.

  delta2 N et epow = (1/2^256 + M/2^192) + (et + ct/2^192) + epow + N^2/2^508
  M  = 2^25 + 36   (the copy argument's bad triples, 2N + n_P per |E|^2, N = 2^24, n_P = 36)
  ct = 2^27        (t's bad points per good triple, 8N)

At N = 2^50 block calls, et = 2^-200, epow = 2^-300 (the bounds `delta2_le` takes), it checks
delta2 <= 2^-164, the Lean bound, and prints every term in bits.

Run: python3 -I formal/RecCompose/Review/Pi2Delta2.py
"""
from fractions import Fraction as Q
import math


def bits(x):
    return math.log2(x.numerator) - math.log2(x.denominator)


M = 2**25 + 36
ct = 2**27
N = 2**50
et = Q(1, 2**200)
epow = Q(1, 2**300)

terms = {
    "alpha's repetition 1/2^256": Q(1, 2**256),
    "bad triples (2^25+36)/2^192": Q(M, 2**192),
    "t's cache hit et": et,
    "bad t 2^27/2^192": Q(ct, 2**192),
    "proofs of work epow": epow,
    "rpmError N^2/2^508": Q(N * N, 2**508),
}
delta2 = sum(terms.values(), Q(0))
for k, v in terms.items():
    print(f"{k:32s} 2^{bits(v):.3f}")
print(f"{'delta2':32s} 2^{bits(delta2):.3f}")
assert delta2 <= Q(1, 2**164), "delta2_le fails"
# delta2_le's proof: each term against x = 2^-170, the copy argument's 2^4 x, t's 2^5 x, the rest x each: 52 x <= 2^6 x
x = Q(1, 2**170)
assert Q(1, 2**256) <= x and Q(M, 2**192) <= 16 * x and Q(ct, 2**192) == 32 * x
assert et <= x and epow <= x and Q(N * N, 2**508) <= x
print("delta2 <= 2^-164: ok")
