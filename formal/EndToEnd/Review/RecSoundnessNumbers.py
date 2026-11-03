# Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (RecCompose's Numbers.lean).
"""Recompute RecCompose.pi2Bound exactly (pi2's part of the recursive verifier, epsilon_2), from the Lean definition
(transcribed: formal/RecCompose/RecCompose/Numbers.lean's pi2N, pi2RoundErr, pi2Bound), with pi2's rounds' errors from
RecPiop.err (formal/RecPiop/RecPiop/Rounds.lean) at N = 2^24, rows of 16, the ports' d_j summing to 3, times the
candidate lists of W (L_W = 9952, 2^24 words) and Q (L_Q = 3564, 2^28 words), as RecPiop/Numbers.lean states them.

    python3 -I formal/EndToEnd/Review/RecSoundnessNumbers.py
"""
from fractions import Fraction as Fr
from math import log2

E_CARD = 2**192
EPS = Fr(269, 2**137)  # WhirBridge.epsExact: the exact certified per-group bound
N_POS = 2**24          # pi2's positions
LOG_W = 4              # rows of 16
D_SUM = 3              # the three four-limb ports (the statement, pi1's two roots): d_j = 1
L_W, L_Q = 9952, 3564  # the candidate lists of W (2^24 words) and Q (2^28 words)

# RecPiop.err: round 0 (alpha, beta, gamma), round 1 (t), round 2 (rho)
ERR = [Fr(3 * N_POS - 1 + D_SUM, E_CARD), Fr(5 * N_POS - 1, E_CARD), Fr(2**LOG_W - 1, E_CARD)]
# ListChainU's factors: the lists of the roots of rounds 0..j (W; W, Q; W, Q)
FAC = [L_W, L_W * L_Q, L_W * L_Q]
ROUNDS = [f * e for f, e in zip(FAC, ERR)]
PI2_ROUND_ERR = Fr(9952 * 3564 * (5 * 2**24 - 1), E_CARD)


def pi2_n(q):
    return 2**33 + q


def pi2_bound(q):
    """pi2Bound Q = N (eps + 5 N / 2^256) + N (e2 + 8 N / 2^256) + 2 N^2 / 2^256 + (2^81 + Q)^2 / 2^508,
    N = 2^33 + Q, eps = 269 / 2^137, e2 = 9952 * 3564 * (5 * 2^24 - 1) / 2^192."""
    n = pi2_n(q)
    return (Fr(n) * (EPS + Fr(5 * n, 2**256))
            + Fr(n) * (PI2_ROUND_ERR + Fr(8 * n, 2**256))
            + Fr(2 * n * n, 2**256)
            + Fr((2**81 + q) ** 2, 2**508))


def lg(f):
    return log2(f.numerator) - log2(f.denominator)


for name, r in zip(["copy (alpha, beta, gamma), over L_W", "identity at t, over L_W L_Q", "W's fold at rho, over L_W L_Q"],
                   ROUNDS):
    print(f"  round {name:38s} 2^{lg(r):.4f}  ({-lg(r):.2f} bits)")
assert max(ROUNDS) == PI2_ROUND_ERR  # pi2_rounds_le: the identity at t is the largest
print(f"e2 = pi2RoundErr = 2^{lg(PI2_ROUND_ERR):.4f}")
print(f"eps = 269 / 2^137 = 2^{lg(EPS):.4f}")
for k in [0, 20, 32, 40, 48, 56, 60, 63, 64]:
    q = 2**k
    b = pi2_bound(q)
    print(f"Q = 2^{k:2d}: pi2Bound(Q) = 2^{lg(b):.6f}, Q / bound = 2^{k - lg(b):.4f}")

b = pi2_bound(2**64)
n = pi2_n(2**64)
parts = {
    "openings, once (N eps)": Fr(n) * EPS,
    "openings' failure term 5 N^2 / 2^256": Fr(n) * Fr(5 * n, 2**256),
    "rounds N e2": Fr(n) * PI2_ROUND_ERR,
    "chain term 8 N^2 / 2^256": Fr(n) * Fr(8 * n, 2**256),
    "seed pair 2 N^2 / 2^256": Fr(2 * n * n, 2**256),
    "permutation term (2^81 + Q)^2 / 2^508": Fr((2**81 + 2**64) ** 2, 2**508),
}
for name, v in parts.items():
    print(f"  {name:40s} 2^{lg(v):.4f}")
print(f"epsilon_2 = pi2Bound(2^64) = 2^{lg(b):.6f}  ({64 - lg(b):.3f} bits as Q / epsilon_2)")
print("pi2Bound(2^64) <= 2^-64 ?", b <= Fr(1, 2**64))
# pi2Bound is increasing in Q, so the bound at 2^64 bounds every Q <= 2^64 (pi2Bound_le_bits).
assert all(pi2_bound(2**k) <= pi2_bound(2**(k + 1)) for k in range(64))
assert b <= Fr(1, 2**64)
