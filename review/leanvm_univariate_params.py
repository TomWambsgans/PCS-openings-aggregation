# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
"""Soundness of the univariate PIOP of crates/leanvm_univariate/SPEC.md (iteration 2), round by round, after the
union bounds over the level-0 Johnson lists of its two proof commitments (WHIR takes no OOD sample at level 0: a root
binds a list until the claims are opened), and the sizes of its commitments.

    python3 -I review/leanvm_univariate_params.py

Each challenge's error is the Schwartz-Zippel bound of the polynomial it must avoid, times the number of committed
tables it is drawn against: L1 (C1's list) for those drawn after C1 and before C2, L1 L2 after C2. The setup
commitments (bytecode, addresses, A0, B0) are computed by anyone from the program: an honest codeword's list within
the Johnson radius is itself (L = 1).

As review M1 (review/review_m1_soundness.py, REVIEW-M1.md F8) asks, and as the code states them:
- every degree at t is taken with each quotient's committed capacity (`verifier::chunks`, the third chunk rounded up
  to a power of two), sized for the height's fewest rows 2^(r-1) + 1 (SPEC.md §13, F1), since a cheating prover fills
  the whole capacity;
- a table's leaf identity is checked times Z_act(t) (degree <= 2^r), and its padding rows are any number up to n (the
  row counts are the prover's, announced in the stream);
- the heap's blocks are `heap.rs`'s, the unused blocks included, each an identity of degree < 2^r;
- the bus's polynomial has degree 4 a tuple (one Schwartz-Zippel over E^5), with every table full (the counts are
  the prover's: at most 2^r rows each); a zero fingerprint needs no exclusion (the identities only multiply);
- Flock's matrices' reduction runs its rounds in the batching sumcheck, so they are drawn after C2 (SPEC.md §13); the
  ring map in tower order errs with probability at most 6/|E| (one a stage, crates/leanvm_flock_gas/src/ring_tower.rs);
- rho, lambda and the batching sumcheck are separate rows.

Shapes whose proof stacks are below 2^24 words have no certified level-0 list (review M1, F3): they are flagged and
left out of the claims.
"""
import importlib.util
import math
import os

LOGQ = 192
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("whir_params", os.path.join(HERE, "whir_params.py"))
whir = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(whir)

# leanVM 42422001's tables (crates/verifier/src/layout.rs there): per flush, the degree of the pull and the push
# fingerprint in the columns (2 for an address fp*o or a product value, 1 otherwise); counters; the factor columns sent.
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
FLOCK_SKIP = 3  # FLOCK_MAIN's univariate skip
COPIES = 18  # BLAKE2S's limbs, committed again as univariate columns

# Certified level-0 lists for public layouts at rate 1/2, 17 grinding bits (branch lean-whir-large, 0aceeb1,
# `review/whir_params.py --large`). The code's eta search (whir_config.rs) gives smaller lists: it omits a
# 2^(l-1) row-union factor.
CERTIFIED_L0 = {24: 9952, 25: 7908, 26: 6296, 27: 4473, 28: 3564}
# leanVM's WHIR, unchanged, per opening (the coordinator's figure for these parameters; review M1, F3).
WHIR_BITS = 128.97
OPENINGS = 5  # C1, C2, the setup, A0, B0


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


def degree(plus, minus):
    """verifier::degree: saturating."""
    return max(0, plus - minus)


def least_rows(r):
    return 0 if r == 0 else (1 << (r - 1)) + 1


def heap_blocks(lm, lb, heights):
    """heap.rs: the used blocks largest first (memory, bytecode, then the tables in order), then aligned unused ones."""
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
    leaf_quotients = {}
    for name, r in blocks:
        n = 1 << r
        if name == "unused":
            identities[f"unused 2^{r}"] = max(n - 1, 0)
            continue
        if name in ("memory", "bytecode"):
            dq = degree(2 * (n - 1), n)
            lhs = 2 * (n - 1)
            times = 0
        else:
            t = TABLES[name]
            top = max(1 + sum(t["pull"]), sum(t["push"]))
            dq = degree(top * (n - 1) + (n - least_rows(r)), n)
            lhs = top * (n - 1) + n  # any number of padding rows, up to n
            times = n  # the identity is checked times Z_act, of degree <= 2^r
        cap = capacity(dq + 1)
        leaf_quotients[name] = cap / max(n, 1)
        c2_words += 3 * cap
        identities[f"leaf {name}"] = max(lhs, n + cap - 1) + times
    # Q_W: the quotient's degree (verifier.rs), its capacity, and the lifted constraints' degrees; the counters'
    # constraint holds on every row (no Z_pad).
    qd, lifted = 0, 0
    for (name, t), r in zip(TABLES.items(), heights):
        n = 1 << r
        if name == "JUMP":
            qd = max(qd, degree(n, 2))
            lifted = max(lifted, 2 * (n - 1) + (1 << r_w) - n)
        qd = max(qd, degree((n - 1) * (1 + t["counters"]), n))
        lifted = max(lifted, (n - 1) * (1 + t["counters"]) + (1 << r_w) - n)
        if name == "BLAKE2S":
            qd = max(qd, degree(r * (n // 2), n))
            lifted = max(lifted, r * (n // 2) + (1 << r_w) - n)
    qd = max(qd, degree(1 << lm, 3))
    lifted = max(lifted, (1 << lm) - 1 + (1 << r_w) - 2)
    cap_w = capacity(qd + 1)
    c2_words += 3 * cap_w
    identities["Q_W"] = max(lifted, (1 << r_w) + cap_w - 1)
    # C1: q_flock, every column (copies included) and an inverse a table, memory (4), bytecode's final count.
    widths = [15, 15, 8, 15, 14, 19 + COPIES]
    c1_words = (1 << (heights[5] + 8)) + sum((w + 1) << hh for w, hh in zip(widths, heights)) + (4 << lm) + (1 << LOG_BYTECODE)
    # The bus: tuples a side, every table full (the prover announces the counts, at most 2^r rows each), the memory,
    # the bytecode, the boundary.
    side = sum(len(t["pull"]) << r for t, r in zip(TABLES.values(), heights)) + (1 << lm) + (1 << LOG_BYTECODE) + 1
    side_honest = sum(len(t["pull"]) * rr for t, rr in zip(TABLES.values(), rows)) + (1 << lm) + (1 << LOG_BYTECODE) + 1
    # Relations: C1 (sent columns, sent fingerprints, memory 2, bytecode 1, Q_W 1, Flock's ring 1), C2, setup.
    c1_rel = sum(t["counters"] + t["sent_factors"] for t in TABLES.values()) + sum(SENT_FINGERPRINTS.values()) + 2 + 1 + 1 + 1
    c2_rel = 1 + 1 + 1 + len(blocks) + 1
    return dict(lm=lm, heights=heights, h=h, blocks=blocks, identities=identities, c1=c1_words, c2=c2_words,
                side=side, side_honest=side_honest, c1_rel=c1_rel, c2_rel=c2_rel, r_w=r_w, cap_w=cap_w,
                leaf_quotients=leaf_quotients, qd=qd)


def flock_before_c2(log_n, k=FLOCK_SKIP):
    """Flock's challenges drawn before C2: the skip (degree < 2^(k+1)), the zerocheck's rounds (eq factor split off:
    degree 3), the lincheck's alpha (degree 3) and 8 rounds (degree 2), the ring map in tower order (6)."""
    return (2 ** (k + 1) + 3 * (log_n - k) + 3 + 2 * 8 + 6) / 2.0 ** LOGQ


def level0_list(log_n):
    """The level-0 Johnson list bound L the code's eta search assumes at a stack of 2^log_n words, rate 1/2."""
    rates, cols, ks, _ = whir.ladder(log_n)
    best = whir.optimize(0, rates[0], cols[0], ks[0])
    return math.floor(2 ** best["logL"] + 1e-9)


def bits(error):
    return -math.log2(error)


def rounds(a, l1, l2):
    q = 2.0 ** LOGQ
    vars_ = max(stack_vars(a["c1"]), stack_vars(a["c2"]))
    return [
        ("bus (α, β): multisets, degree 4 a tuple, every table full", 4 * a["side"] / q, l1),
        ("γ: 29 C1-only constraints batched", 28 / q, l1),
        (f"Flock before C2 (skip {FLOCK_SKIP}, zerocheck, lincheck, ring map)", flock_before_c2(14 + a["heights"][5]), l1),
        ("t: every identity, committed capacities", sum(a["identities"].values()) / q, l1 * l2),
        ("ρ: C1's relations combined", (a["c1_rel"] - 1) / q, l1 * l2),
        (f"λ (4 claims) and the {vars_}-round batching sumcheck (Flock's matrices' rounds among them)",
         (3 + 2 * vars_) / q, l1 * l2),
    ]


def main():
    print("== commitments (words) and the quotients' capacities (iteration 2: sized for 2^(r-1) + 1 rows)")
    for xmss in SHAPES:
        a = analyse(xmss)
        s1, s2 = stack_vars(a["c1"]), stack_vars(a["c2"])
        flag = "  ** over 2^28 **" if max(s1, s2) > 28 else ("  ** below 2^24: no certified list **" if min(s1, s2) < 24 else "")
        print(f" {xmss:>5} signatures: C1 2^{math.log2(a['c1']):.2f} (stack 2^{s1}), C2 2^{math.log2(a['c2']):.2f}"
              f" (stack 2^{s2}); heap 2^{a['h']} positions; leaf capacities "
              + ", ".join(f"{k} {v:.2f}n" for k, v in a["leaf_quotients"].items() if k in ("XOR", "SET", "BLAKE2S"))
              + f"; Q_W {a['cap_w'] / (1 << 18):.2f}·2^18; bus side 2^{math.log2(a['side']):.2f} full"
              f" (2^{math.log2(a['side_honest']):.2f} at the measured counts){flag}")
    for xmss in [1000, 1290]:
        a = analyse(xmss)
        s1, s2 = stack_vars(a["c1"]), stack_vars(a["c2"])
        candidates = [
            ("the certified level-0 lists (WhirBridge-large)", CERTIFIED_L0[s1], CERTIFIED_L0[s2]),
            ("the code's eta search (omits a row-union factor)", level0_list(s1), level0_list(s2)),
            ("leanerVM's generic cap", 2 ** 18, 2 ** 18),
        ]
        for name, l1, l2 in candidates:
            rs = rounds(a, l1, l2)
            print(f"\n== {xmss} signatures, lists from {name}: L1 = {l1} (2^{math.log2(l1):.2f}), L2 = {l2}"
                  f" (2^{math.log2(l2):.2f}); Σ deg at t 2^{math.log2(sum(a['identities'].values())):.2f}")
            for label, err, union in rs:
                print(f"   {label:76s} {bits(err):6.1f} bits alone, {bits(err * union):6.1f} after the union")
            total = sum(err * union for _, err, union in rs)
            print(f"   {'PIOP, all rounds (sum of the unioned errors)':76s} {'':6s}       {bits(total):6.1f}")
    # The PCS (review M1, F3): leanVM's WHIR at ≈ 128.97 certified bits an opening, 5 openings.
    plain = WHIR_BITS - math.log2(OPENINGS)
    print(f"\n   WHIR, {OPENINGS} openings: {WHIR_BITS} bits each; a plain union {plain:.1f} bits. In the query-bounded"
          "\n   random-permutation model of the end theorems the openings' transcripts are domain-separated and share"
          "\n   the adversary's Q queries, so their total is about (Q + 5)·ε rather than 5·Q·ε: about"
          f" {WHIR_BITS:.2f} - log2(1 + 5/Q) ≈ {WHIR_BITS:.1f} bits for Q ≫ 5.")
    print("\n   Not counted: Fiat-Shamir in the random-oracle model (Keccak-256), and Flock's fixed zerocheck"
          "\n   coordinates (leanVM's).")


if __name__ == "__main__":
    main()
