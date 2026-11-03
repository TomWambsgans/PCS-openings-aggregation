# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
"""Recursion for the univariate leanVM 42422001 verifier (crates/leanvm_rec/SPEC-REC.md): the sizes of the outer
proof pi2 in each arithmetization, its soundness round by round after the union bounds over WHIR's level-0 Johnson
lists, and the contract's gas.

    python3 -I review/leanvm_rec_params.py

MEASURED (crates/leanvm_rec/tests/counts.rs and quotient_reference.rs, on h1): pi1's verifier graph at 1,000
signatures (Keccak-256 calls and permutations, E operations, packings, claims), and the Merkle-path circuit's rows per
Keccak-f and words per row. MODELLED (here): every pi2 size, every soundness figure, every gas figure. The models are
formulas over the measured counts; SPEC-REC.md §2-§4 derives each one.
"""
import importlib.util
import math
import os
import sys

sys.dont_write_bytecode = True  # review/__pycache__ is tracked: loading the other scripts must not rewrite it

LOGQ = 192
HERE = os.path.dirname(os.path.abspath(__file__))


def _load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


uni = _load("leanvm_univariate_params")
CERTIFIED_L0 = uni.CERTIFIED_L0
WHIR_BITS = uni.WHIR_BITS

# ---------------------------------------------------------------------------------------------------------------------
# MEASURED: pi1's verifier graph, Claims::Point, 1,000 signatures (crates/leanvm_rec/tests/counts.rs, count_report).
# perms: Keccak-f[1600] permutations of every Keccak-256 call, the seed's included; ops: live E operations with the
# ring switch's kernel expanded; packs: live stream reads + challenges (each a bytes/bits <-> E packing in pi2).
PI1 = {
    "main line (skip 3)": dict(perms=131, calls=104, challenges=103, products=6413, linear=5218, reads=297,
                               coords=46, values=5, stream=7072, bits=125, zero=13),
    "pi1-rec (skip 3; alpha, zerocheck point derived)": dict(perms=107, calls=80, challenges=79, products=6437,
                                                             linear=5218, reads=297, coords=46, values=5, stream=7072,
                                                             bits=125, zero=13),
    "leanVM skip (skip 6, weighted)": dict(perms=135, calls=98, challenges=97, products=10802, linear=5021, reads=347,
                                           coords=43, values=5, stream=8272, bits=125, zero=13),
    "pi1-rec at skip 6": dict(perms=114, calls=77, challenges=76, products=6800, linear=5591, reads=347, coords=43,
                              values=5, stream=8272, bits=125, zero=13),
    "BLAKE2s omitted (scale only)": dict(perms=52, calls=37, challenges=36, products=2009, linear=1982, reads=147,
                                         coords=27, values=3, stream=3472, bits=125, zero=13),
}
# MEASURED: crates/quotient's circuit (tests/quotient_reference.rs): rows per Keccak-f, the membership circuit, and the
# words per row of its three tables at 2^22 rows (4 cells a row; witness and quotient hidden).
QUOTIENT_ROWS_PER_PERM = 113_114
QUOTIENT_MERKLE = dict(perms=34, used=3_878_612, log_rows=22, witness=20_971_520, wiring=16_777_216,
                       quotient=264_241_152)
# MEASURED: pi1's main line on revm (crates/leanvm_univariate SPEC.md §13): execution 182,104 gas straight for 11,631
# E operations, of which transcript 11,175, calldata reads 6,442, PCS_OPEN 3,444: the per-operation cost below.
GAS_PER_OP = (182_104 - 11_175 - 6_442 - 3_444) / (6413 + 5218)

# ---------------------------------------------------------------------------------------------------------------------
# pi2's arithmetizations (SPEC-REC.md §2). Each gives the positions (wired cells) of one Keccak-f, the row width W
# (the values the verifier is sent at t), and the quotient table's words per position.
ROUNDS = 24


def keccak_positions(design):
    """Positions of one Keccak-f[1600] permutation."""
    if design == "B4":  # crates/quotient's bit gate, 4 cells a row (measured rows)
        return 4 * QUOTIENT_ROWS_PER_PERM
    if design == "C16":  # cell outputs, 16-cell rows: chi5+theta rows (15 cells), 2 C (6) + 1 D (3) rows
        return ROUNDS * (320 + 192) * 16
    if design == "C64":  # cell outputs, slice rows: 25 b, 5 C, 5 C_prev, 25 a' (60 of 64)
        return ROUNDS * 64 * 64
    if design == "D16v":  # virtual pushes, 16-position rows: plane-0 rows (10) + 3 D units, planes 1-4 (15), D rows;
        # and the theta prep of round 0 (C_0: 320 rows of 5 pulls, 3 to a 16-row)
        return ROUNDS * (64 + 256 + 16) * 16 + 107 * 16
    if design == "D32v":  # virtual pushes, slice rows: 25 b + 5 C_prev pulls, 30 expression pushes; + a theta prep
        return (ROUNDS + 1) * 64 * 32
    raise ValueError(design)


DESIGNS = {
    # name: (row width W = values at t, quotient words per position, extra values, proof commitments, note)
    "B4": dict(W=4, qwords=13.75, extra=1, note="crates/quotient's chi gate on bits, cell outputs"),
    "C16": dict(W=16, qwords=9 + 3 / 16, extra=2, note="cell outputs, chi5+theta rows"),
    "C64": dict(W=64, qwords=9 + 3 / 64, extra=2, note="cell outputs, slice rows"),
    # extra: sigma(t) and kappa(t), the setup's wiring and constants columns
    # q < 4N: a (block, role) indicator has degree N - 2^s, about N for a small block (the review's finding 4)
    "D16v": dict(W=16, qwords=3 + 3 * 4, extra=2, note="virtual pushes, chi5+theta + partial sums"),
    "D32v": dict(W=32, qwords=3 + 3 * 4, extra=2, note="virtual pushes, slice rows"),
}


def other_positions(pi1, design):
    """Positions besides Keccak's rounds: E products and linear operations (K-limbs: a product 6 pulls, a sum 6),
    the packings (64 bits a limb, 3 limbs an element, W - 1 bits a row), the public region and constants, the
    absorption XORs of the multi-block hashes' later blocks, and the stream's free bits."""
    w = DESIGNS[design]["W"]
    per_row = max(1, w // 6)
    e_rows = (pi1["products"] + pi1["linear"]) / per_row
    packs = (pi1["reads"] + pi1["challenges"]) * 3 * math.ceil(65 / (w - 1)) * w
    public = 3 * (pi1["coords"] + pi1["values"] + 14) + 3 * 461
    absorb = (pi1["perms"] - pi1["calls"]) * 1088 * 2  # the XOR of a later block into the state, 2 pulls a bit
    # the stream's bits are free cells: a free cell (a self-loop pushing b^2: b is a bit) and the slot that produces it
    # into its segment, 2 positions a bit (the public input's 256 bits likewise)
    inputs = 2 * 8 * (pi1["stream"] + 32)
    return e_rows * w + packs + public + absorb + inputs


def size(pi1_name, design):
    pi1, d = PI1[pi1_name], DESIGNS[design]
    keccak = pi1["perms"] * keccak_positions(design)
    total = keccak + other_positions(pi1, design)
    log_n = math.ceil(math.log2(total))
    n = 1 << log_n
    q = d["qwords"] * n
    return dict(keccak=keccak, total=total, log_n=log_n, n=n, fill=total / n, witness=n, quotient=q,
                values=d["W"] + d["extra"])


def stack(words):
    return max(24, math.ceil(math.log2(words) - 1e-9))


def bits(err):
    return -math.log2(err)


# ---------------------------------------------------------------------------------------------------------------------
# Soundness (SPEC-REC.md §5).

def pi1_rec2_rounds(xmss=1000):
    """pi1-rec2's rounds (SPEC-REC.md §12): pi1-rec's, Flock's lincheck terminal checked by the circuit's walk (no
    matrices' rounds in the batch, 3 claims), and the batching sumcheck's challenges narrow: 160 bits, so each round of
    degree 2 errs with probability 2/2^160 (over C1's and C2's lists, as every challenge after C2)."""
    out = []
    for label, err, union in pi1_rec_rounds(xmss):
        if label.startswith("λ"):
            vars_ = int(label.split("the ")[1].split("-round")[0])
            out.append(("λ (3 claims)", 2 / 2.0 ** LOGQ, union))
            label, err = f"the {vars_}-round batching sumcheck, narrow challenges (160 bits)", 2 * vars_ / 2.0 ** 160
        out.append((label, err, union))
    return out


def pi1_rec_rounds(xmss=1000, derived=True):
    """pi1's rounds as review/leanvm_univariate_params.py states them, with pi1-rec's two derivations: the bus's alpha
    as (c, c^2, c^4, c^8) (each fingerprint multilinear in alpha, so degree 16 in c a tuple, with beta independent),
    and Flock's zerocheck eq point after its first coordinate as squares (degree 2^22 - 1 in c)."""
    a = uni.analyse(xmss)
    s1, s2 = uni.stack_vars(a["c1"]), uni.stack_vars(a["c2"])
    l1, l2 = CERTIFIED_L0[s1], CERTIFIED_L0[s2]
    rs = uni.rounds(a, l1, l2)
    if not derived:
        return rs
    out = []
    for label, err, union in rs:
        if label.startswith("bus"):
            label, err = "bus (α = (c, c², c⁴, c⁸), β): degree 16 a tuple in c, every table full", err * 4
        if label.startswith("Flock"):
            label, err = label + " + the eq point as powers (2^22)", err + 2 ** 22 / 2.0 ** LOGQ
        out.append((label, err, union))
    return out


def pi2_rounds(s, split=False, design="D16v"):
    """pi2's rounds: the copy argument's (alpha, beta) after W; t after Q; the fold and claim combination. With
    `split`, Q is two commitments (h, then q and the gate quotient), and the caller multiplies in h's list."""
    q = 2.0 ** LOGQ
    q_words = s["quotient"] - 3 * s["n"] if split else s["quotient"]
    lw, lq = CERTIFIED_L0[stack(s["witness"])], CERTIFIED_L0[stack(q_words)]
    n = s["n"]
    if design.startswith("D"):
        t = ("t: the copy identity h · d_pull · d_push, degree ≤ 5N (d_push's selectors and quadratic pushes)", 5 * n)
    else:
        w = DESIGNS[design]["W"]
        t = (f"t: the copy identity h · d · d' (3N) and the gate's (2N/{w})", 3 * n + 2 * n // w)
    return lw, lq, [
        ("copy argument (α, β): 2N fractions, unique tags both sides, and no vanishing denominator", 4 * n / q, lw),
        # As built (pi2/adapt.rs; REVIEW-REC.md N4): a three-limb port's fingerprint is the element itself (no γ);
        # the four-limb ones (the statement, pi1's two roots) are (L0 + Y L1) + γ (L2 + Y L3), degree 1 in γ.
        ("γ: the four-limb ports' fingerprints (L0 + Y L1) + γ (L2 + Y L3), degree 1 (3 ports)", 3 / q, lw),
        (t[0], t[1] / q, lw * lq),
        # Since PI2.md §9 (lever 2), ρ is W's fold only (degree 15 over W's list): Q's claim is the identity's own
        # combination of h(t) and q(t) (t's row), the setup's is at β and binds ξ = κ(t) + β σ(t) exactly (L = 1).
        # Before: ρ's claims on three commitments, the errors adding, (15 L_W + L_Q + 1)/2^192 (REVIEW-REC.md N4).
        ("ρ: W's fold (degree 15)", 15 / q, lw),
    ]


# ---------------------------------------------------------------------------------------------------------------------
# Gas (SPEC-REC.md §4): EIP-7623 max(16 B + exec, 40 B) (zero bytes 4 and 10), EIP-7976's floor at 64 a byte.

def calldata(pi1, values, pi2_roots=2, extra=0):
    """selector 4, public input 32, row counts 24, pi1's roots 64, pi1's claims (distinct coordinates and values,
    24 bytes each), pi2's roots and values; zero bytes: one a row count, and the random bytes' 1/256."""
    b = 4 + 32 + 24 + 64 + 24 * (pi1["coords"] + pi1["values"]) + 32 * pi2_roots + 24 * values + extra
    zero = 6 + round((b - 10) / 256)
    return b, zero


# The (region block, role) pairs whose push is an expression, each one indicator at t: a coset of a Cantor subspace
# (roles in the position's high 4 bits, regions aligned blocks of rows), w_m(t) / ((w_s(t) + u) κ), one division.
# D16v: K0a, K0b (13 expression roles, 2 blocks each), K1 (10, 3), KD (8, 2), Kprep (3, 2), XOR (8, 2), 5 packing
# types (1, 2), E products (6, 2), E sums (6, 2), squares (5, 2), free bits (16, 2), public fingerprints (4, 1).
# D32v: the slice rows (30 roles: 2 RC types x 2 blocks, the prep 1) and the same others with 32-wide rows.
EXPRESSION_PAIRS = {"D16v": 26 + 26 + 30 + 16 + 6 + 16 + 10 + 12 + 12 + 10 + 32 + 4, "D32v": 120 + 30 + 100}


def verifier_ops(design, values):
    """The pi2 verifier's E operations at t (SPEC-REC.md §4, §6): digits, the row's values from its fold, the push
    formulas, their selection (one indicator a region block and expression role, batch-inverted), the copy
    identity, the public side."""
    w = DESIGNS[design]["W"]
    lw = int(math.log2(w))
    digits = 2 * 25
    fold = 2 * sum((1 << j) * (1 << (lw - j)) for j in range(lw)) + 2 * w + 20
    formulas = {"B4": 8, "C16": 120, "C64": 400, "D16v": 345, "D32v": 450}[design]
    if design.startswith("D"):
        # each pair: its denominator (1 add, 1 mul by κ), 3 muls of the batch inversion, the product with its
        # formula's value minus the forward's, and the sum; one inversion for all
        selection = 6 * EXPRESSION_PAIRS[design] + 70
    else:
        selection = 61 + 10 + 7 * w + 70 + 4 * 40 + 4 * w
    identity = 100
    # the public side of the copy argument: one fraction 1/(α + c0 + γ c1 + γ² c2 + β τ_J) an element (57: pi1's
    # 51 claims' elements, 2 roots, the public input, the counts) and a check (13), batch-inverted
    publics = 57 + 13
    public = publics * (4 + 3) + 70
    return digits + fold + formulas + selection + identity + public


def execution(pi1, design, values, claims_pi2=4, calls_pi2=3, pi2_words=123):
    ops = verifier_ops(design, values)
    words_pi1 = 5 * 3 + 134 + 5
    marshal = 15 * (words_pi1 + pi2_words) + 100 * (5 + calls_pi2)
    reads = 6 * (pi1["coords"] + pi1["values"] + values + 8)
    transcript = 420 + 4 * 100
    entry = 500
    return round(GAS_PER_OP * ops + marshal + reads + transcript + entry), ops


def tx(b, zero, exec_gas, claims, c, floor=40):
    nonzero = b - zero
    standard = 16 * nonzero + 4 * zero + exec_gas + c * claims
    floor_gas = floor * nonzero + (10 if floor == 40 else 64) * zero
    return max(standard, floor_gas)


def grouped(x):
    return f"{round(x):,}"


def main():
    print("== pi1's verifier (MEASURED, 1,000 signatures, Claims::Point)")
    for name, p in PI1.items():
        print(f"  {name:52s} Keccak-256 {p['calls']:>3}, Keccak-f {p['perms']:>3}, challenges {p['challenges']:>3},"
              f" E products {p['products']:>5}, linear {p['linear']:>5}, packings {p['reads'] + p['challenges']:>3},"
              f" claims' coordinates {p['coords']} + {p['values']} values")
    m = QUOTIENT_MERKLE
    print(f"\n== crates/quotient (MEASURED): {QUOTIENT_ROWS_PER_PERM:,} rows a Keccak-f; the Merkle path's {m['perms']}"
          f" permutations use {m['used']:,} of 2^{m['log_rows']} rows; words a row: witness"
          f" {m['witness'] / 2**22:.2f}, wiring {m['wiring'] / 2**22:.2f}, quotient {m['quotient'] / 2**22:.2f}"
          f" (2^{math.log2(m['quotient']):.2f}, hidden)")
    for p in ["main line (skip 3)", "pi1-rec (skip 3; alpha, zerocheck point derived)"]:
        rows = PI1[p]["perms"] * QUOTIENT_ROWS_PER_PERM
        print(f"   {p}: {rows:,} rows of that gate = 2^{math.log2(rows):.2f} rows: quotient 2^"
              f"{math.log2(rows * 63):.2f} words, over 2^28 by {rows * 63 / 2**28:.1f}x")

    print("\n== pi2's arithmetizations (MODELLED from the measured counts; N = positions, a power of two)")
    rows = []
    for design in DESIGNS:
        for p in ["main line (skip 3)", "pi1-rec (skip 3; alpha, zerocheck point derived)"]:
            s = size(p, design)
            fits = s["quotient"] <= 2 ** 28
            rows.append((design, p, s, fits))
            print(f"  {design:5s} [{DESIGNS[design]['note']}] x {p[:8]}: Keccak-f {keccak_positions(design):,}"
                  f" positions, total {s['total'] / 1e6:.2f}M -> N = 2^{s['log_n']} ({100 * s['fill']:.0f}% used);"
                  f" W 2^{math.log2(s['witness']):.2f}, Q 2^{math.log2(s['quotient']):.2f}"
                  f" {'fits 2^28' if fits else '** over 2^28 **'}; {s['values']} values at t")

    print("\n== soundness (MODELLED; per round, bits after the union over the lists it is drawn against)")
    for derived in (False, True):
        rs = pi1_rec_rounds(derived=derived)
        print(f"  pi1 {'pi1-rec' if derived else 'main line'} (C1 4,473, C2 4,473):")
        for label, err, union in rs:
            print(f"     {label:90s} {bits(err):6.1f} alone, {bits(err * union):6.1f} after")
        print(f"     {'PIOP':90s}        {bits(sum(e * u for _, e, u in rs)):6.1f}")
    rs = pi1_rec2_rounds()
    print("  pi1 pi1-rec2 (C1 4,473, C2 4,473; SPEC-REC.md §12):")
    for label, err, union in rs:
        print(f"     {label:90s} {bits(err):6.1f} alone, {bits(err * union):6.1f} after")
    print(f"     {'PIOP':90s}        {bits(sum(e * u for _, e, u in rs)):6.1f}")
    for design in ["D16v", "D32v", "C16"]:
        p = "pi1-rec (skip 3; alpha, zerocheck point derived)" if design == "D16v" else "main line (skip 3)"
        s = size(p, design)
        lw, lq, rs = pi2_rounds(s, split=design == "C16", design=design)
        extra = ""
        if design == "C16":
            # two quotient commitments (h, then q and the gate quotient) in one round: t pays three lists
            lh = CERTIFIED_L0[stack(3 * s["n"])]
            rs = [(l, e, u * (lh if l.startswith(("t", "ρ")) else 1)) for l, e, u in rs]
            extra = f", H {lh}"
        print(f"  pi2 {design} (N = 2^{s['log_n']}; lists W {lw}, Q {lq}{extra}):")
        for label, err, union in rs:
            print(f"     {label:90s} {bits(err):6.1f} alone, {bits(err * union):6.1f} after")
        print(f"     {'PIOP':90s}        {bits(sum(e * u for _, e, u in rs)):6.1f}")
    openings = 5 + 3
    print(f"  WHIR openings: pi1's 5 + pi2's 3 = {openings}, {WHIR_BITS} bits each: a plain union"
          f" {WHIR_BITS - math.log2(openings):.1f}; in the query-bounded model about {WHIR_BITS:.1f}")
    # pi1-rec2 (SPEC-REC.md §12 item 4): no claims on A0, B0 (the lincheck's terminal by the circuit's walk).
    openings = 3 + 3
    print(f"  pi1-rec2: pi1's 3 + pi2's 3 = {openings} openings: a plain union {WHIR_BITS - math.log2(openings):.1f}")

    print("\n== gas (MODELLED): transaction gas without the 21,000 base; claims c = 0 / 2K / 5K / 20K")
    configs = [
        ("D16v x pi1-rec (recommended)", "D16v", "pi1-rec (skip 3; alpha, zerocheck point derived)", 4, 3, 123, 0),
        ("D32v x pi1 main line (fallback)", "D32v", "main line (skip 3)", 4, 3, 123, 0),
        ("C64 x pi1 main line", "C64", "main line (skip 3)", 4, 3, 123, 0),
        ("C16 x pi1-rec (3 proof commitments)", "C16", "pi1-rec (skip 3; alpha, zerocheck point derived)", 5, 4, 150, 32),
    ]
    print(f"  {'configuration':40s} {'calldata':>9s} {'exec':>7s} {'E ops':>6s} {'claims':>6s}   EIP-7623 c = 0 / 2K / 5K / 20K"
          "        (+21K base, c = 0)   EIP-7976 c = 0 / 20K")
    for name, design, p, claims2, calls2, words2, extra in configs:
        pi1 = PI1[p]
        s = size(p, design)
        b, zero = calldata(pi1, s["values"], pi2_roots=2 + (design == "C16"), extra=0)
        ex, ops = execution(pi1, design, s["values"], claims2, calls2, words2)
        claims = 5 + claims2
        g = [tx(b, zero, ex, claims, c) for c in (0, 2000, 5000, 20000)]
        g76 = [tx(b, zero, ex, claims, c, floor=64) for c in (0, 20000)]
        print(f"  {name:40s} {b:>7,} B {ex:>7,} {ops:>6,} {claims:>6}   " + " / ".join(grouped(x) for x in g)
              + f"   ({grouped(g[0] + 21000)})   " + " / ".join(grouped(x) for x in g76))
    # the chain pi1 -> pi2 (D32v) -> pi3 (D16v of pi2's verifier): pi2's claims on-chain as t2, rho2 and 4 values
    pi1 = PI1["main line (skip 3)"]
    b, zero = calldata(pi1, 18, pi2_roots=4, extra=24 * 6)
    ex, ops = execution(pi1, "D16v", 18, 8, 6, 250)
    claims = 5 + 4 + 4
    g = [tx(b, zero, ex, claims, c) for c in (0, 2000, 5000, 20000)]
    g76 = [tx(b, zero, ex, claims, c, floor=64) for c in (0, 20000)]
    print(f"  {'chain pi1 -> pi2 (D32v) -> pi3 (D16v)':40s} {b:>7,} B {ex:>7,} {ops:>6,} {claims:>6}   "
          + " / ".join(grouped(x) for x in g) + f"   ({grouped(g[0] + 21000)})   " + " / ".join(grouped(x) for x in g76))
    print("  measured today (pi1 on chain, main line, deployed): 7,108 B, 192,392 exec, 5 claims: 305,808 / 315,808 /"
          " 330,808 / 405,808; EIP-7976 454,912")
    print(f"\n  (per-operation gas {GAS_PER_OP:.2f}: pi1's measured execution less its transcript, reads and calls, over"
          " its E operations)")
    points_report()


# ---------------------------------------------------------------------------------------------------------------------
# The claims' points (crates/leanvm_rec/SPEC-POINTS.md): the batching sumcheck's rounds k variables at a time on V_k's
# coordinate functionals, one challenge a round, so that the batch's point r is a function of ceil(27 / k) elements.
#
# MEASURED, the two baselines: R3 (leanvm-rec @ 4a57c61, PI2.md §0: pi1-rec, 46 coordinates and 5 values) and
# leanvm-rec-opt @ 5e0ea89 (PI2.md §9 there: pi1-rec2, no claims on A0, B0, so 27 coordinates and 3 values; pi2's 17
# values; the calls' inputs written once). Calldata bytes and zero bytes, execution at c = 0, transaction, pi2's ports
# and positions used.
BASELINES = {
    "R3, pi1-rec (leanvm-rec @ 4a57c61)": dict(b=1844, zero=7, exec=39674, tx=73550, ports=67,
                                               positions=14_370_656, coords=46, values=5),
    "pi1-rec2 (leanvm-rec-opt @ 5e0ea89)": dict(b=1292, zero=4, exec=31103, tx=51727, ports=47,
                                                positions=15_880_064, coords=27, values=3),
}
# MEASURED: a public element's port in pi2's verifier (PI2.md §9, lever 1a': the public side 6,794 -> 4,723 gas for
# 67 -> 47 ports); pi2's positions a stream bit (a free bit: a self-loop and its copy), a packing (SPEC-REC §10.3:
# 77,200 positions for 376), a Keccak-256 call's later block (54,928 for 27), an E operation (114,704 for 11,655).
PORT_GAS = (6794 - 4723) / (67 - 47)
POS_BIT, POS_PACKING, POS_LATER_BLOCK, POS_OP = 2, 77_200 / 376, 54_928 / 27, 114_704 / (6437 + 5218)
# MEASURED (leanvm_flock_gas transcript::tests::pairs_cost_what_the_plain_rounds_do_in_permutations): the batch's 27
# variables in plain rounds 135 E operations, in pairs 278.
OPS_PLAIN, OPS_PAIRS = 135, 278
# MODELLED: the contract's work a public element besides its port (its calldata read, its 24 bytes in pi2's
# first hash and CALLDATACOPY), and the derivation of a pair's two coordinates from its challenge (two FIELD_MULs, two
# XORs and their stack work), or of the 27 digits from one element (26 squarings and XORs).
READ_GAS, HASH_GAS_A_BYTE = 18, 9 / 32
DERIVE_PAIR_GAS, DERIVE_DIGIT_GAS = 50, 23
BATCH_VARS = 27


def permutations_of(data_bytes):
    """Keccak-f permutations of one Keccak-256 of the 32-byte state and `data_bytes` (rate 136, pad10*1)."""
    return (32 + data_bytes) // 136 + 1


def grouped_rounds(k, vars_=BATCH_VARS, degree=2):
    """The batch in rounds of k variables (the last round the rest): its challenges, its scalars, its permutations.
    A round of j variables: the summand's restriction to V_j's coordinate-functional curve, of degree degree * j *
    2^(j-1), its coefficients but one sent."""
    rounds = [k] * (vars_ // k) + ([vars_ % k] if vars_ % k else [])
    scalars = [degree * j * 2 ** (j - 1) for j in rounds]
    return dict(seeds=len(rounds), scalars=sum(scalars), perms=sum(permutations_of(24 * s) for s in scalars))


def with_points(base, seeds_saved, extra_exec, floor=40):
    """A baseline with `seeds_saved` fewer public elements (24 bytes, a port, a read and its hashing each) and
    `extra_exec` gas of derivation."""
    b = base["b"] - 24 * seeds_saved
    exec_gas = base["exec"] - seeds_saved * (PORT_GAS + READ_GAS + 24 * HASH_GAS_A_BYTE) + extra_exec
    return b, exec_gas, tx(b, base["zero"], exec_gas, 0, 0, floor)


def points_report():
    print("\n== the claims' points (SPEC-POINTS.md; MODELLED from the measured counts above)")
    print(f"  the batch over {BATCH_VARS} variables, degree 2 a variable, in rounds of k variables on V_k's coordinate"
          " functionals:")
    plain = grouped_rounds(1)
    for k in (1, 2, 3, 4):
        g = grouped_rounds(k)
        extra = g["perms"] - plain["perms"]
        print(f"    k = {k}: {g['seeds']:>2} challenges, {g['scalars']:>3} scalars, {g['perms']:>2} Keccak-f"
              f" ({extra:+d}: {extra * keccak_positions('D16v') / 1e6:+.2f}M of pi2's positions)")
    mixed = dict(seeds=3 + 9, perms=3 * permutations_of(24 * 24) + 9 * permutations_of(24 * 8))
    print(f"    3 triples and 9 pairs: {mixed['seeds']} challenges, {mixed['perms']} Keccak-f"
          f" ({mixed['perms'] - plain['perms']:+d})")

    pairs = grouped_rounds(2)
    # pi2: the pairs' extra scalars are stream bits and packings, 13 fewer challenges 13 fewer packings, each pair's
    # hash one later block, and the pairs' extra operations.
    more_scalars = pairs["scalars"] - plain["scalars"]
    fewer = plain["seeds"] - pairs["seeds"]
    later = (BATCH_VARS // 2) * (permutations_of(24 * 8) - 1)
    delta = (more_scalars * (24 * 8 * POS_BIT + POS_PACKING) - fewer * POS_PACKING + later * POS_LATER_BLOCK
             + (OPS_PAIRS - OPS_PLAIN) * POS_OP)
    print(f"  pi2 with pairs: Keccak-f {plain['perms']} -> {pairs['perms']}; {more_scalars:+d} stream scalars"
          f" ({24 * more_scalars:+,} B of pi1's stream), {-fewer:+d} challenges, {later:+d} later blocks,"
          f" {OPS_PAIRS - OPS_PLAIN:+d} E operations: {delta / 1e3:+.1f}K positions")
    for name, base in BASELINES.items():
        used = base["positions"] + delta
        print(f"    on {name}: {base['positions']:,} -> {used:,.0f} of 2^24 ({100 * used / 2**24:.1f}%)")

    q = 2.0 ** LOGQ
    l12 = CERTIFIED_L0[27] ** 2
    plain_err = (3 + 2 * BATCH_VARS) / q
    pairs_err = (3 + 8 * (BATCH_VARS // 2) + 2 * (BATCH_VARS % 2)) / q
    print(f"  soundness: λ and the batch, over C1's and C2's lists ({CERTIFIED_L0[27]}^2): plain {bits(plain_err):.1f}"
          f" alone, {bits(plain_err * l12):.1f} after; pairs (degree 8 a pair) {bits(pairs_err):.1f} alone,"
          f" {bits(pairs_err * l12):.1f} after; the PIOP stays at t's 142.3")
    # pi1-rec3 (SPEC-REC.md §12, as built on leanvm-rec-opt): the pairs' challenges and the last plain round's narrow,
    # 160 bits (lever 1c): a pair of degree 8 errs with probability 8/2^160, the plain round 2/2^160; λ stays 192-bit.
    narrow_err = (8 * (BATCH_VARS // 2) + 2 * (BATCH_VARS % 2)) / 2.0 ** 160 + 3 / q
    print(f"  pi1-rec3, the pairs' challenges narrow (160 bits): λ and the batch {bits(narrow_err):.1f} alone,"
          f" {bits(narrow_err * l12):.1f} after the union (pi1-rec3's weakest round; t 142.3)")

    print("  gas, EIP-7623 c = 0 without the base (B calldata bytes, X execution):")
    derive_pairs = (BATCH_VARS // 2) * DERIVE_PAIR_GAS
    for name, base in BASELINES.items():
        print(f"    {name}: B {base['b']:,}, X {base['exec']:,}, tx {base['tx']:,} (measured)")
        for label, saved, derive in [
            (f"pairs: r from {pairs['seeds']} elements", fewer, derive_pairs),
            ("bound: r from 1 element (not reachable, §2)", BATCH_VARS - 1, (BATCH_VARS - 1) * DERIVE_DIGIT_GAS),
        ]:
            b, ex, t = with_points(base, saved, derive)
            t76 = with_points(base, saved, derive, floor=64)[2]
            base76 = tx(base["b"], base["zero"], base["exec"], 0, 0, 64)
            print(f"      + {label:46s} B {b:,}, X {ex:,.0f}, tx {t:,.0f} ({t - base['tx']:+,.0f});"
                  f" EIP-7976 {base76:,} -> {t76:,.0f} ({t76 - base76:+,.0f})")
    print(f"    pairs at any execution: at most {40 * 24 * fewer:,} (the floor's 40 a byte of {24 * fewer} bytes), at"
          f" least {16 * 24 * fewer + fewer * (PORT_GAS + READ_GAS + 24 * HASH_GAS_A_BYTE) - derive_pairs:,.0f}"
          " (16 a byte, the ports, the reads, the derivation)")


if __name__ == "__main__":
    main()
