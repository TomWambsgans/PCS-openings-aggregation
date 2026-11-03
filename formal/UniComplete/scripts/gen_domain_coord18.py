# Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
"""Regenerate the literal certificate of `UniComplete/DomainCoord18.lean`.

Reimplements `UniStatement.coordinateFunctionals 18` (Gauss-Jordan over GF(2^64) = GF(2)[x]/(x^64+x^4+x^3+x+1),
the Lean's pivot rule and row order) and rewrites the region of DomainCoord18.lean between the markers
`-- BEGIN GENERATED` and `-- END GENERATED`: the matrix `[M | I]` before and after each group of column steps as
literal words (`gjW0 ... gjW18`), the kernel checks of each group, and the chain into `coordinateFunctionals_18`.
Nothing here is trusted: every literal is checked by the Lean kernel (`decide +kernel`).

usage: python3 -I gen_domain_coord18.py path/to/DomainCoord18.lean
"""
import sys

MOD = (1 << 64) | 0b11011
R = 18
GROUPS = [3, 3, 3, 3, 3, 3]

# `UniStatement.beta`'s first 18 words (`UniComplete.Domain.betaWords`, kernel-checked in DomainBasis).
BETA = [0x0000000000000001, 0x19c9369f278adc02, 0xa181e7d66f5ff794, 0x5db84357ce785d08,
        0xb973d466f5c9d0ca, 0x521ac889831a075e, 0x033ce8beddc8a656, 0xb5846c4e07b91010,
        0x4087b8cbb37a32ec, 0x00d0d3888c0ae17c, 0xafd5ac70237f2222, 0xe3f5af99cc3aaaf8,
        0x5a1db3b16a0b58b8, 0x09947c54fe7ee248, 0x0e8eaf0e0068f544, 0xa2a113500b4b4f5a,
        0xe96f9805d6ce0bb0, 0x53496f8b5c9edd4c]


def mul(a, b):
    r = 0
    for i in range(64):
        if b >> i & 1:
            r ^= a << i
    for i in range(127, 63, -1):
        if r >> i & 1:
            r ^= MOD << (i - 64)
    return r


def inv(a):
    e = (1 << 64) - 2
    r = 1
    while e:
        if e & 1:
            r = mul(r, a)
        a = mul(a, a)
        e >>= 1
    return r


def frob(x, m):
    for _ in range(m):
        x = mul(x, x)
    return x


def init(r):
    """`gjInit r`: rows `[β_j^(2^m) for m < r] ++ [c = j]`."""
    return [[frob(BETA[j], m) for m in range(r)] + [1 if c == j else 0 for c in range(r)] for j in range(r)]


def step(r, col, rows):
    """`gjStep r col`: pivot = first row at or below `col` with a nonzero entry in `col` (else `col`), swap,
    normalise, eliminate the other rows in order."""
    rows = [list(x) for x in rows]
    pivot = col
    for i in range(col, r):
        if rows[i][col] != 0:
            pivot = i
            break
    row_col, row_pivot = rows[col], rows[pivot]
    rows[col] = row_pivot
    rows[pivot] = row_col
    iv = inv(rows[col][col])
    rows[col] = [mul(x, iv) for x in rows[col]]
    for i in range(r):
        f = rows[i][col]
        if i != col and f != 0:
            p = rows[col]
            rows[i] = [x ^ mul(f, q) for x, q in zip(rows[i], p)]
    return rows


def out(r, rows):
    """`gjOut r`: `a[l][m] = rows[m][r + l]`."""
    return [[rows[m][r + l] for m in range(r)] for l in range(r)]


def lit(rows):
    return "[" + ",\n    ".join("[" + ", ".join("0x%016x" % w for w in row) + "]" for row in rows) + "]"


def generate():
    states, cols, c = [init(R)], [0], 0
    for k in GROUPS:
        rows = states[-1]
        for col in range(c, c + k):
            rows = step(R, col, rows)
        c += k
        states.append(rows)
        cols.append(c)
    a = out(R, states[-1])
    for l in range(R):
        for j in range(R):
            s = 0
            for m in range(R):
                s ^= mul(a[l][m], frob(BETA[j], m))
            assert s == (1 if l == j else 0), (l, j)
    parts = []
    for idx, rows in enumerate(states):
        parts.append("/-- The matrix after the first `%d` column steps, as words. -/\n"
                     "def gjW%d : List (List UInt64) :=\n  %s\n" % (cols[idx], cols[idx], lit(rows)))
    parts.append("/-- The starting matrix `[M | I]`, `M[j][m] = β_j^(2^m)`. -/\n"
                 "theorem gjInit_words : toWords (gjInitF 18) = gjW0 := by\n  decide +kernel\n")
    for idx, k in enumerate(GROUPS):
        c0 = cols[idx]
        parts.append("/-- Columns `%d … %d`. -/\n"
                     "theorem gjSteps_%d : toWords (gjStepsF 18 %d %d (ofWords gjW%d)) = gjW%d := by\n"
                     "  decide +kernel\n" % (c0, c0 + k - 1, c0, c0, k, c0, cols[idx + 1]))
    nest = "rows"
    for idx, k in enumerate(GROUPS):
        nest = "gjSteps 18 %d %d (%s)" % (cols[idx], k, nest)
    splits = ",\n    ".join("gjSteps_split 18 0 %d %d %d %d (by norm_num) (by norm_num)"
                            % (cols[idx + 1], cols[idx], GROUPS[idx], cols[idx])
                            for idx in range(len(GROUPS) - 1, 0, -1))
    parts.append("/-- The elimination, cut into its groups of columns. -/\n"
                 "theorem gjSteps_18_split (rows : Array (Array K)) :\n    gjSteps 18 0 18 rows =\n      %s := by\n"
                 "  rw [%s]\n" % (nest, splits))
    rws = ",\n    ".join(["eq_ofWords gjInit_words"] +
                         ["eq_ofWords gjSteps_%d" % cols[idx] for idx in range(len(GROUPS))])
    parts.append("/-- **`coordinateFunctionals 18`, as the literal matrix after the elimination.** -/\n"
                 "theorem coordinateFunctionals_18 : coordinateFunctionals 18 = gjOut 18 (ofWords gjW18) := by\n"
                 "  rw [coordinateFunctionals_eq_gjSteps, gjSteps_18_split]\n"
                 "  simp only [gjSteps_eq_F, gjInit_eq_F]\n"
                 "  rw [%s]\n" % rws)
    return "\n".join(parts)


def main():
    path = sys.argv[1]
    src = open(path).read()
    begin, end = "-- BEGIN GENERATED", "-- END GENERATED"
    i = src.index(begin)
    i = src.index("\n", i) + 1
    j = src.index(end)
    open(path, "w").write(src[:i] + "\n" + generate() + "\n" + src[j:])


if __name__ == "__main__":
    main()
