# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
"""Soundness of the univariate PIOP of crates/leanvm_univariate/SPEC.md, round by round, after the union bounds over
the level-0 Johnson lists of its two proof commitments (WHIR takes no OOD sample at level 0: a root binds a list
until the claims are opened), and the sizes of its commitments.

    python3 -I review/leanvm_univariate_params.py

Each challenge's error is the Schwartz-Zippel bound of the polynomial it must avoid, times the number of committed
tables it is drawn against: L1 (C1's list) for those drawn after C1 and before C2, L1 L2 after C2. The setup
commitments (bytecode, addresses, A0, B0) are computed by anyone from the program: an honest codeword's list within
the Johnson radius is itself (L = 1).
"""
import importlib.util
import math
import os

LOGQ = 192
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("whir_params", os.path.join(HERE, "whir_params.py"))
whir = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(whir)

# leanVM 42422001's tables (crates/verifier/src/layout.rs there): flush pairs, counters, and the degree of each pull
# and push fingerprint in the columns (2 for an address fp*o or a product value, 1 otherwise), in flush order:
# state, bytecode, then the memory flushes.
TABLES = {
    "XOR": dict(flushes=5, counters=4, pull=[1, 1, 2, 2, 2], push=[1, 1, 2, 2, 2]),
    "MUL": dict(flushes=5, counters=4, pull=[1, 1, 2, 2, 2], push=[1, 1, 2, 2, 2]),
    "SET": dict(flushes=3, counters=2, pull=[1, 1, 2], push=[1, 1, 2]),
    "DEREF": dict(flushes=5, counters=4, pull=[1, 1, 2, 2, 2], push=[1, 1, 2, 2, 2]),
    "JUMP": dict(flushes=5, counters=4, pull=[1, 1, 2, 2, 2], push=[2, 1, 2, 2, 2]),
    "BLAKE2S": dict(flushes=11, counters=10, pull=[1, 1] + [2] * 9, push=[1, 1] + [2] * 9),
}

# The shapes leanVM's gas-dump gave (crates/leanvm_flock_gas/src/shapes.rs): log memory, rows per table.
SHAPES = {
    32: (16, [6060, 6490, 11768, 4703, 2699, 6489]),
    128: (18, [23629, 25224, 32804, 17879, 10468, 25881]),
    400: (20, [73426, 78352, 92398, 55231, 32463, 80825]),
    1000: (21, [183266, 195439, 223851, 137591, 80937, 202025]),
    1290: (22, [236343, 252019, 287373, 177391, 104394, 260605]),
    2000: (22, [366327, 390501, 442955, 274831, 161790, 404025]),
}
LOG_BYTECODE = 19  # 2^23 stacked words, 16 a tuple
FLOCK_R1CS_LOG = 14
COPIES = 18  # BLAKE2S's limbs, committed again as univariate columns


def log2_ceil(x):
    return max(0, (x - 1).bit_length())


def layout(xmss):
    lm, rows = SHAPES[xmss]
    heights = [log2_ceil(r) for r in rows]
    r_w = max(heights + [lm])
    # C1: q_flock, the tables' columns (+ copies and one inverse a table), memory (4), bytecode final count.
    widths = [15, 15, 8, 15, 14, 19 + COPIES]
    c1 = (1 << (heights[5] + 8)) + sum((w + 1) << h for w, h in zip(widths, heights)) + (4 << lm) + (1 << LOG_BYTECODE)
    # The heap: memory, bytecode and the tables' blocks of leaves.
    leaves = (1 << lm) + (1 << LOG_BYTECODE) + sum(1 << h for h in heights)
    d = log2_ceil(leaves)
    h = d + 1
    # Leaf quotients' degrees (SPEC.md §5): (n-1)(1 + Σ deg) + (n - rows) - n for a table, n - 2 for memory, bytecode.
    leaf_degrees = {}
    for (name, t), r, rr in zip(TABLES.items(), heights, rows):
        n = 1 << r
        leaf_degrees[name] = (n - 1) * (1 + max(sum(t["pull"]), sum(t["push"]) - 1)) + (n - rr) - n
    leaf_degrees["memory"] = (1 << lm) - 2
    leaf_degrees["bytecode"] = (1 << LOG_BYTECODE) - 2
    # The constraint quotient: counters (z Π c + 1) Z_pad, JUMP, copies (composition degree r 2^(r-1)), public input.
    wq = 0
    for (name, t), r, rr in zip(TABLES.items(), heights, rows):
        n = 1 << r
        wq = max(wq, (n - 1) * (1 + t["counters"]) - rr)
    wq = max(wq, (1 << heights[3]) - 2, heights[5] * (1 << (heights[5] - 1)) - (1 << heights[5]), (1 << lm) - 3)
    c2 = 3 * ((1 << h) + (1 << h) + 1 + sum(dg + 1 for dg in leaf_degrees.values()) + wq + 1)
    n_tuples = sum(t["flushes"] * r for t, r in zip(TABLES.values(), rows)) + (1 << lm) + (1 << LOG_BYTECODE) + 1
    identities = {
        "tree": (1 << (h + 1)),
        **{f"leaf {k}": dg + (1 << (heights[list(TABLES).index(k)] if k in TABLES else (lm if k == "memory" else LOG_BYTECODE)))
           for k, dg in leaf_degrees.items()},
        "constraints Q_W": (1 << r_w) + wq,
    }
    constraints = 2 + 6 + COPIES + 3
    return dict(heights=heights, lm=lm, r_w=r_w, c1=c1, c2=c2, h=h, leaves=leaves, n_tuples=n_tuples,
                identities=identities, constraints=constraints, leaf_degrees=leaf_degrees, wq=wq)


# Certified level-0 Johnson lists for public layouts at rate 1/2, 17 grinding bits (branch lean-whir-large, 0aceeb1,
# `review/whir_params.py --large`). The code's eta search (whir_config.rs) gives smaller lists: it omits a
# 2^(l-1) row-union factor.
CERTIFIED_L0 = {24: 9952, 25: 7908, 26: 6296, 27: 4473, 28: 3564}


def level0_list(log_n):
    """The level-0 Johnson list bound L the code's eta search assumes at a stack of 2^log_n words, rate 1/2."""
    rates, cols, ks, _ = whir.ladder(log_n)
    best = whir.optimize(0, rates[0], cols[0], ks[0])
    return math.floor(2 ** best["logL"] + 1e-9)


def bits(error):
    return -math.log2(error)


def rounds(xmss, l1, l2, flock_rounds=32 + 14 + 10):
    q = 2.0 ** LOGQ
    lay = layout(xmss)
    n = lay["n_tuples"]
    out = []
    # Bus: (α, β) after C1. If push and pull multisets differ, Π(β + fp_α(push)) - Π(β + fp_α(pull)) is a nonzero
    # polynomial over E^5 of degree 4 in each factor (the Lean heap proof, branch lean-heap): one Schwartz-Zippel,
    # 4N/|E|. The heap identities only multiply (R P = P', T(1) fp(init) = fp(fin)), so a zero fingerprint needs no
    # exclusion.
    out.append(("bus fingerprint (α, β), multiset equality", 4 * n / q, l1))
    out.append(("γ: C1-only constraints batched", lay["constraints"] / q, l1))
    # Flock: leanVM's sumchecks (degree <= 3 a round), the skip, the lincheck's batching, the matrices' rounds, the
    # ring map: a few hundred over |E| (SPEC-FLOCK.md), drawn after C1.
    out.append(("Flock (zerocheck, lincheck, matrices, ring switch)", 3 * flock_rounds / q + 2 ** 7 / q, l1))
    # t after C2: every identity that fails as a polynomial identity is nonzero at t but for deg/|E|.
    out.append(("t: all identities (tree, leaves, Q_W)", sum(lay["identities"].values()) / q, l1 * l2))
    # The values at t enter only linear relations; ρ combines them, one claim per commitment.
    out.append(("ρ: relations combined into one claim per commitment", 120 / q, l1 * l2))
    return lay, out


def main():
    print("== commitments (words) and the level-0 lists WHIR's eta search assumes at their stacks (rate 1/2)")
    lists = {}
    for xmss in SHAPES:
        lay = layout(xmss)
        s1, s2 = log2_ceil(lay["c1"]), log2_ceil(lay["c2"])
        print(f" {xmss:>5} signatures: C1 2^{math.log2(lay['c1']):.2f} (stack 2^{s1}), C2 2^{math.log2(lay['c2']):.2f}"
              f" (stack 2^{s2}); heap 2^{lay['h']} positions; leaf quotients "
              + ", ".join(f"{k} {v / (1 << 18):.1f}·2^18" for k, v in lay["leaf_degrees"].items() if k in ("BLAKE2S", "XOR"))
              + f"; Q_W {lay['wq'] / (1 << 18):.2f}·2^18; bus tuples 2^{math.log2(lay['n_tuples']):.2f}"
              + ("  ** over 2^28 **" if max(s1, s2) > 28 else ""))
        lists[xmss] = (s1, s2)
    for xmss in [1000, 1290]:
        s1, s2 = lists[xmss]
        candidates = [
            ("the certified level-0 lists (WhirBridge-large)", CERTIFIED_L0[s1], CERTIFIED_L0[s2]),
            ("the code's eta search (omits a row-union factor)", level0_list(s1), level0_list(s2)),
            ("leanerVM's generic cap", 2 ** 18, 2 ** 18),
        ]
        for name, l1, l2 in candidates:
            lay, rs = rounds(xmss, l1, l2)
            print(f"\n== {xmss} signatures, lists from {name}: L1 = {l1} (2^{math.log2(l1):.2f}), L2 = {l2}"
                  f" (2^{math.log2(l2):.2f})")
            worst = 1e9
            for label, err, union in rs:
                b = bits(err * union)
                worst = min(worst, b)
                print(f"   {label:58s} {bits(err):6.1f} bits alone, {b:6.1f} after the union")
            total = sum(err * union for _, err, union in rs)
            print(f"   {'all rounds (sum of the unioned errors)':58s} {'':6s}       {bits(total):6.1f}")
    # A third proof commitment (C3 = one batched quotient) would be union-bounded over L1 L2 L3.
    lay = layout(1000)
    l = CERTIFIED_L0[27]
    third = sum(lay["identities"].values()) / 2.0**LOGQ * l**3
    print(f"\n   a third commitment at 1,000 signatures (certified lists): t after L1 L2 L3 = 2^{3 * math.log2(l):.1f}:"
          f" {bits(third):.1f} bits")
    print("\n   Not counted here: WHIR's own soundness at each opening (leanVM's parameters, 128 bits by its search),"
          "\n   Fiat-Shamir in the random-oracle model (Keccak-256), and Flock's fixed zerocheck coordinates (leanVM's).")


if __name__ == "__main__":
    main()
