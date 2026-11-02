# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
"""Review M1 (crates/leanvm_univariate/REVIEW-M1.md): the univariate PIOP's soundness recomputed from the code's
layouts rather than from SPEC.md's formulas.

    python3 -I review/review_m1_soundness.py

Differences from review/leanvm_univariate_params.py, on purpose:
- every Schwartz-Zippel degree at t is taken with the committed capacity of each quotient (the chunks of
  `verifier::chunks`, the third rounded up to a power of two), not the honest quotient's degree: a cheating prover
  fills the whole capacity;
- the heap's blocks are `heap.rs`'s (largest first, then aligned unused blocks), each unused block an identity of
  degree < 2^r;
- the bus's polynomial has degree 4 per tuple (eq(alpha, s) is multilinear in 4 variables; beta is linear);
- the relations rho combines are counted per commitment as `verifier.rs` states them; lambda and the batching
  sumcheck are separate rows;
- the PCS's own error is shown next to the PIOP's: leanVM's WHIR parameters target 128 bits an opening
  (review/whir_params.py, `optimize(target=128)`), and the main line makes 5 openings.
"""
import math

LOGQ = 192
# leanVM 42422001's tables (layout.rs): per flush, (pull degree, push degree) in the columns; counters; width.
TABLES = {
    "XOR": dict(pull=[1, 1, 2, 2, 2], push=[1, 1, 2, 2, 2], counters=4, sent_factors=2),
    "MUL": dict(pull=[1, 1, 2, 2, 2], push=[1, 1, 2, 2, 2], counters=4, sent_factors=5),
    "SET": dict(pull=[1, 1, 2], push=[1, 1, 2], counters=2, sent_factors=2),
    "DEREF": dict(pull=[1, 1, 2, 2, 2], push=[1, 1, 2, 2, 2], counters=4, sent_factors=5),
    "JUMP": dict(pull=[1, 1, 2, 2, 2], push=[2, 1, 2, 2, 2], counters=4, sent_factors=3),
    "BLAKE2S": dict(pull=[1, 1] + [2] * 9, push=[1, 1] + [2] * 9, counters=10, sent_factors=2),
}
# Fingerprints sent (pull, and JUMP's state push): verifier.rs's linearise over each flush's unsent columns.
SENT_FINGERPRINTS = {"XOR": 4, "MUL": 4, "SET": 2, "DEREF": 4, "JUMP": 6, "BLAKE2S": 10}
SHAPES = {
    32: (16, [6060, 6490, 11768, 4703, 2699, 6489]),
    128: (18, [23629, 25224, 32804, 17879, 10468, 25881]),
    400: (20, [73426, 78352, 92398, 55231, 32463, 80825]),
    1000: (21, [183266, 195439, 223851, 137591, 80937, 202025]),
    1290: (22, [236343, 252019, 287373, 177391, 104394, 260605]),
    2000: (22, [366327, 390501, 442955, 274831, 161790, 404025]),
}
LOG_BYTECODE = 19
CERTIFIED_L0 = {24: 9952, 25: 7908, 26: 6296, 27: 4473, 28: 3564}


def log2_ceil(x):
    return max(0, (x - 1).bit_length())


def chunks(count):
    """verifier::chunks: at most three powers of two covering `count` coefficients."""
    sizes, left = [], count
    while left > 0:
        top = left.bit_length() - 1
        if len(sizes) == 2 and left != 1 << top:
            sizes.append(top + 1)
            break
        sizes.append(top)
        left -= 1 << top
    return sizes


def capacity(count):
    return sum(1 << e for e in chunks(count))


def heap_blocks(lm, lb, heights):
    used = [("memory", lm, 0), ("bytecode", lb, 1)] + [(name, h, 2 + i) for i, (name, h) in enumerate(zip(TABLES, heights))]
    used.sort(key=lambda b: (-b[1], b[2]))
    total = sum(1 << r for _, r, _ in used)
    d = (total - 1).bit_length()
    base = 1 << d
    blocks, offset = [], 0
    for name, r, _ in used:
        blocks.append((name, r))
        offset += 1 << r
    while offset < base:
        r = (offset & -offset).bit_length() - 1
        while offset + (1 << r) > base:
            r -= 1
        blocks.append(("unused", r))
        offset += 1 << r
    return d + 1, blocks


def stack_vars(words):
    return max(15, log2_ceil(words))


def analyse(xmss):
    lm, rows = SHAPES[xmss]
    heights = [log2_ceil(r) for r in rows]
    r_w = max(heights + [lm])
    h, blocks = heap_blocks(lm, LOG_BYTECODE, heights)
    identities = {"tree": 1 << (h + 1)}
    c2_words = 3 * ((1 << h) + (1 << h) + 1)
    for name, r in blocks:
        n = 1 << r
        if name == "unused":
            identities[f"unused 2^{r}"] = n - 1
            continue
        if name in ("memory", "bytecode"):
            dq = 2 * (n - 1) - n
            lhs = 2 * (n - 1)
        else:
            t = TABLES[name]
            rr = rows[list(TABLES).index(name)]
            dq = max(1 + sum(t["pull"]), sum(t["push"])) * (n - 1) + (n - rr) - n
            lhs = max(1 + sum(t["pull"]), sum(t["push"])) * (n - 1) + (n - rr)
        cap = capacity(dq + 1)
        c2_words += 3 * cap
        identities[f"leaf {name}"] = max(lhs, n + cap - 1)
    # Q_W: verifier.rs's quotient degree, its capacity, and the lifted constraints' degrees.
    qd, lifted = 0, 0
    for (name, t), r, rr in zip(TABLES.items(), heights, rows):
        n = 1 << r
        if name == "JUMP":
            qd = max(qd, n - 2)
            lifted = max(lifted, 2 * (n - 1) + (1 << r_w) - n)
        qd = max(qd, (n - 1) * (1 + t["counters"]) + (n - rr) - n)
        lifted = max(lifted, (n - 1) * (1 + t["counters"]) + (n - rr) + (1 << r_w) - n)
        if name == "BLAKE2S":
            qd = max(qd, r * (n // 2) - n)
            lifted = max(lifted, r * (n // 2) + (1 << r_w) - n)
    qd = max(qd, (1 << lm) - 3)
    lifted = max(lifted, (1 << lm) - 1 + (1 << r_w) - 2)
    cap_w = capacity(qd + 1)
    c2_words += 3 * cap_w
    identities["Q_W"] = max(lifted, (1 << r_w) + cap_w - 1)
    # C1: q_flock, every column (copies included) and an inverse a table, memory (4), bytecode's final count.
    widths = [15, 15, 8, 15, 14, 37]
    c1_words = (1 << (heights[5] + 8)) + sum((w + 1) << hh for w, hh in zip(widths, heights)) + (4 << lm) + (1 << LOG_BYTECODE)
    # The bus: tuples a side (each table's flushes over its active rows, the memory, the bytecode, the boundary).
    side = sum(len(t["pull"]) * r for t, r in zip(TABLES.values(), rows)) + (1 << lm) + (1 << LOG_BYTECODE) + 1
    # Relations: C1 (sent columns, sent fingerprints, memory 2, bytecode 1, Q_W 1, Flock's ring 1), C2, setup.
    c1_rel = sum(t["counters"] + t["sent_factors"] for t in TABLES.values()) + sum(SENT_FINGERPRINTS.values()) + 2 + 1 + 1 + 1
    c2_rel = 1 + 1 + 1 + sum(1 for b in blocks) + 1
    return dict(lm=lm, heights=heights, h=h, blocks=blocks, identities=identities, c1=c1_words, c2=c2_words,
                side=side, c1_rel=c1_rel, c2_rel=c2_rel, r_w=r_w, cap_w=cap_w)


def flock_error(log_n, k=3):
    # skip (degree < 2^(k+1)), zerocheck rounds (eq factor: degree 3), lincheck's alpha (degree 3) and 8 rounds,
    # the matrices' k + 6 rounds, the ring switch's map (64 Frobenius terms, 6 stages): taken as 2^7 as the script does.
    return (2 ** (k + 1) + 3 * (log_n - k) + 3 + 2 * 8 + 2 * (k + 6) + 2 ** 7) / 2.0 ** LOGQ


def main():
    q = 2.0 ** LOGQ
    for xmss in SHAPES:
        a = analyse(xmss)
        s1, s2 = stack_vars(a["c1"]), stack_vars(a["c2"])
        if s1 > 28 or s2 > 28:
            print(f"{xmss}: over 2^28")
            continue
        l1, l2 = CERTIFIED_L0[max(s1, 24)], CERTIFIED_L0[max(s2, 24)]
        total_deg = sum(a["identities"].values())
        rounds = [
            ("bus (alpha, beta): multisets, degree 4 a tuple", 4 * a["side"] / q, l1),
            ("bus: a pull fingerprint vanishes", a["side"] / q, l1),
            ("gamma: 29 constraints", 28 / q, l1),
            ("Flock (k = 3)", flock_error(14 + a["heights"][5]), l1),
            ("t: every identity, committed capacities", total_deg / q, l1 * l2),
            ("rho: C1's relations", (a["c1_rel"] - 1) / q, l1 * l2),
            ("lambda (3 claims) and the 27-round batching sumcheck", (2 + 2 * max(s1, s2)) / q, l1 * l2),
        ]
        print(f"\n== {xmss} signatures: C1 2^{math.log2(a['c1']):.2f} (stack 2^{s1}), C2 2^{math.log2(a['c2']):.2f} "
              f"(stack 2^{s2}), H = {a['h']}, L1 = {l1}, L2 = {l2}; sum of degrees at t 2^{math.log2(total_deg):.2f}; "
              f"bus side 2^{math.log2(a['side']):.2f}; relations C1 {a['c1_rel']}, C2 {a['c2_rel']}")
        for name, deg in sorted(a["identities"].items(), key=lambda kv: -kv[1])[:4]:
            print(f"   largest identities: {name:22s} 2^{math.log2(deg):.2f}")
        total = 0
        for name, err, union in rounds:
            total += err * union
            print(f"   {name:56s} {-math.log2(err):6.1f} alone, {-math.log2(err * union):6.1f} after the union")
        print(f"   {'PIOP, all rounds':56s} {'':6s}        {-math.log2(total):6.1f}")
        whir = 5 * 2.0 ** -128
        print(f"   {'with 5 openings at 2^-128 each (the PCS target)':56s} {'':6s}        {-math.log2(total + whir):6.1f}")


if __name__ == "__main__":
    main()
