# Part of this repository (written by an adversarial review). MIT OR Apache-2.0; see NOTICE.md.
"""Replicates leanVM's WHIR eta search (crates/pcs/src/whir_config.rs) at this repository's three stack sizes,
and prints, per level, the Johnson list bound L the search assumes and every soundness term.

    python3 review/whir_params.py
"""
import math
import struct

LOGQ = 192.0
RS_DEG = (1 << 31) + (1 << 15) + (1 << 7) + (1 << 3) + (1 << 1) + 1


def reduced_rate(r, c):
    return (2.0**c - 1) / 2.0 ** (c + r)


def mparam(r, c, eta):
    return max(math.ceil(math.sqrt(reduced_rate(r, c)) / eta), 3)


def log_a(r, eta, c):
    rho = reduced_rate(r, c)
    s = math.sqrt(rho)
    g = 1 - s - eta
    h = mparam(r, c, eta) + 0.5
    num = 2 * h**5 + 3 * h * g * rho
    den = 3 * rho**1.5
    n = 2.0 ** (c + r)
    return math.log2(num / den * n + h / s)


def per_q(r, c, eta):
    rho = reduced_rate(r, c)
    g = 1 - math.sqrt(rho) - eta
    return math.log2(1 / (1 - g))


def log_l(r, c, eta):
    rho = reduced_rate(r, c)
    return math.log2(1 / (2 * eta * math.sqrt(rho)))


def ood_bits(r, c, eta, mu, s):
    l, lm = log_l(r, c, eta), math.log2(mu)
    return LOGQ - l - lm if s == 0 else s * (LOGQ - lm) - (2 * l - 1)


def alg_bits(r, c, eta, prev, s):
    d = max(RS_DEG, prev + s, 2)
    return LOGQ - math.log2(d) - log_l(r, c, eta)


def next_up(x):
    return struct.unpack("d", struct.pack("q", struct.unpack("q", struct.pack("d", x))[0] + 1))[0]


def eta_for_m(r, c, m):
    eta = math.sqrt(reduced_rate(r, c)) / m
    while mparam(r, c, eta) > m:
        eta = next_up(eta)
    return eta


def optimize(level, r, c, ilv, target=128, grind=17, prev=0):
    qt, mu, bl, best = target - grind, c + ilv, 2 ** (c + r), None
    for m in range(3, 4097):
        eta = eta_for_m(r, c, m)
        if eta >= 1 - math.sqrt(reduced_rate(r, c)):
            continue
        pg = LOGQ - log_a(r, eta, c)
        if pg + 1e-12 < target:
            break
        pq = per_q(r, c, eta)
        q = math.ceil(qt / pq)
        if q > bl:
            continue
        if level == 0:
            s = 0
        else:
            s = next((s for s in range(1, 9) if ood_bits(r, c, eta, mu, s) + 1e-12 >= target), None)
            if s is None:
                continue
        if ood_bits(r, c, eta, mu, s) + 1e-12 < target or alg_bits(r, c, eta, prev, s) + 1e-12 < target:
            continue
        cand = dict(m=m, eta=eta, queries=q, ood=s, logL=log_l(r, c, eta), pg=pg, perq=pq,
                    ood_bits=ood_bits(r, c, eta, mu, s), alg=alg_bits(r, c, eta, prev, s), mu=mu)
        if best is None or q < best["queries"]:
            best = cand
    return best


def ladder(log_n, r0=1):
    rates, cols, ks = [r0], [log_n - 6], [6]
    n, red, fold, rate = log_n - 6, 3, 6, r0
    while n > 5:
        k = min(4, n)
        rate = rate + fold - red
        red = 1
        rates.append(rate)
        cols.append(n - k)
        ks.append(k)
        n -= k
        fold = k
    return rates, cols, ks, n


def configs():
    out = {}
    for name, log_n in [("wiring", 24), ("witness", 25), ("quotient", 28)]:
        rates, cols, ks, yr = ladder(log_n)
        levels, prev = [], 0
        for i, (r, c, k) in enumerate(zip(rates, cols, ks)):
            o = optimize(i, r, c, k, prev=prev)
            o.update(rate=r, cols=c, k=k)
            levels.append(o)
            prev = o["queries"]
        out[name] = (log_n, yr, levels)
    return out


# ---------------------------------------------------------------------------------------------------------
# The reduction's rounds after the union over the level-0 Johnson lists (WHIR takes no OOD sample at level
# 0, so a root binds only to a list until the claims are opened).
# ---------------------------------------------------------------------------------------------------------

# leanerVM `mumbai`, LeanVM/Protocol/Whir/Params/Deployed.lean, certTable: level 0 of (mu, R = 1), eta = e / 2^22.
FORMAL_ETA_E = {24: 298, 25: 375, 28: 832}


def list_max(log_n, eta, r=1):
    c = log_n - 6
    return math.floor(1 / (2 * eta * math.sqrt(reduced_rate(r, c))))


def reduction_rounds(l_witness, l_quotient, n_cells=2**24, identity_degree=2**28 + 2**22 + 9230):
    """Bits of each round of the reduction, the round's error unioned over the lists it precedes."""
    q = 2.0**192
    copy_paper = (2 * n_cells**2 + 4 * n_cells + 8) / q  # main.tex / formal: 2N^2 + 4N + 8
    copy_tight = (6 * n_cells + 8) / q  # one uncancelled pole: 2N bad beta, 2N bad alpha, 2N for DD' on H
    ident = identity_degree / q
    lb = lambda e: -math.log2(e)
    return {
        "copy (alpha,beta,gamma), paper bound": (lb(copy_paper), lb(copy_paper * l_witness)),
        "copy (alpha,beta,gamma), tight bound": (lb(copy_tight), lb(copy_tight * l_witness)),
        "identities (t)": (lb(ident), lb(ident * l_witness * l_quotient)),
        "rho": (lb(3 / q), lb((3 * l_witness + l_quotient) / q)),
        "WHIR batching lambda on R2 (J = 2)": (None, lb(l_quotient / q)),
    }


def report_unions():
    code = configs()
    lists = {
        "whir_config.rs eta search (the code's accounting)": {
            name: math.floor(2 ** code[name][2][0]["logL"] + 1e-9) for name in code
        },
        "leanerVM certified eta (what F2 would import)": {
            name: list_max(log_n, FORMAL_ETA_E[log_n] / 2**22)
            for name, log_n in [("wiring", 24), ("witness", 25), ("quotient", 28)]
        },
    }
    for title, ls in lists.items():
        print(f"\n== level-0 lists, {title}: " + ", ".join(f"{k} L={v} (2^{math.log2(v):.2f})" for k, v in ls.items()))
        for name, (ideal, union) in reduction_rounds(ls["witness"], ls["quotient"]).items():
            ideal_s = "     -" if ideal is None else f"{ideal:6.1f}"
            print(f"   {name:40s} ideal commitments {ideal_s} bits, after the union {union:6.1f} bits")
    cap = (2 * 2**48 + 4 * 2**24 + 8) * 2**18 / 2**192
    print(f"\n   with leanerVM's generic cap L <= 2^18 instead, the copy round (paper bound): {-math.log2(cap):.1f} bits")


def split_opening_attack(queries=225, grinding=17, d=0.25):
    """Two separate openings of one root, each against a different list member half a code distance apart."""
    per_attempt = queries * -math.log2(1 - d)
    return per_attempt, per_attempt + grinding + 1


if __name__ == "__main__":
    for name, (log_n, yr, levels) in configs().items():
        print(f"== {name}: stack 2^{log_n}, residual 2^{yr}")
        for i, o in enumerate(levels):
            print(
                f" L{i}: rate 1/2^{o['rate']} msg 2^{o['cols']} fold {o['k']} m={o['m']} eta={o['eta']:.6f}"
                f" queries={o['queries']} ood={o['ood']} log2L={o['logL']:.3f} (L={2**o['logL']:.1f})"
                f" pg={o['pg']:.2f} q-bits={o['queries'] * o['perq']:.2f}+17 ood-bits={o['ood_bits']:.2f}"
                f" alg={o['alg']:.2f}"
            )
    report_unions()
    bits, work = split_opening_attack()
    print("\n== split opening of the quotient table's two claims (f halfway between two list members):")
    print(f"   one opening passes its 225 level-0 queries with (3/4)^225 = 2^-{bits:.1f};"
          f" both, with 17-bit grinding: about 2^{work:.1f} Keccak-f calls")
    print(f"   the count was sized for words farther than the Johnson radius: (1 - 0.2896)^225 = "
          f"2^-{225 * -math.log2(1 - 0.2896):.1f}")
