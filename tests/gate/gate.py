# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Checks Demos.Gate.gate against mpmath at 50 digits.

For each call, the reference decides from the binary64 inputs, read from their bit patterns,
whether the covariance S is symmetric and positive definite, by a Cholesky factorization in exact
rational arithmetic, and computes the squared Mahalanobis distance nu' S^-1 nu by solving
S x = nu with mpmath at 50 digits.

Each line of the input, which `verified-cases-gate --gate-bits` prints, holds
`gate d nu s g status lo hi verdict`, with the arrays as comma-separated bit patterns.  An
input outside the documented ranges, or with an asymmetric S, must give status 1.  A covariance
that is not positive definite must not give status 0.  An accepted result must contain the
reference distance, and its verdict must agree with the reference: verdict
must be 1 when hi <= g, 2 when g < lo, and 0 otherwise, and verdict 1 requires a distance at most
g and verdict 2 a distance above g.  A positive definite covariance must give status 0 when its
condition number is at most 1e12 for d <= 9, 1e8 for d <= 16, 1e6 for d <= 32, and 1e4 for
d <= 64, unless the distance exceeds 2^1023, which overflows the arithmetic, and for d <= 9 the
relative width of the distance must be at most WIDTH times the condition number.  The script prints the statuses and the largest relative widths.
Usage: uv run tests/gate/gate.py CASES"""
import struct
import sys
from collections import Counter
from fractions import Fraction

from mpmath import mp, mpf, matrix, lu_solve

mp.dps = 50

WIDTH = mpf("1e-12")


def required(d, cond):
    """Whether a positive definite covariance must be accepted: the region where the review's
    sweep and these cases accepted every matrix."""
    limit = 1e12 if d <= 9 else 1e8 if d <= 16 else 1e6 if d <= 32 else 1e4
    return cond <= limit


def flt(bits):
    return struct.unpack("<d", struct.pack("<Q", int(bits)))[0]


def floats(field):
    return [] if field == "" else [flt(b) for b in field.split(",")]


def finite(x):
    return x == x and abs(x) != float("inf")


def positive_definite(s, d):
    """Cholesky in exact rationals: every pivot of the symmetric elimination is positive."""
    a = [[Fraction(s[i * d + j]) for j in range(d)] for i in range(d)]
    for k in range(d):
        if a[k][k] <= 0:
            return False
        for i in range(k + 1, d):
            f = a[i][k] / a[k][k]
            for j in range(k + 1, d):
                a[i][j] -= f * a[k][j]
    return True


def condition(s, d):
    m = matrix([[mpf(s[i * d + j]) for j in range(d)] for i in range(d)])
    ev = [abs(x) for x in mp.eigsy(m, eigvals_only=True)]
    return max(ev) / min(ev)


def main(path):
    failures = 0
    checks = 0
    statuses = Counter()
    widest = (mpf(0), None)
    for line in open(path):
        parts = line.split(" ")
        d = int(parts[1])
        nu, s = floats(parts[2]), floats(parts[3])
        g = flt(parts[4])
        status, verdict = int(parts[5]), int(parts[8])
        lo, hi = flt(parts[6]), flt(parts[7])
        checks += 1
        statuses[status] += 1
        label = f"d={d} g={g!r}"
        valid = (1 <= d <= 64 and len(s) == d * d and all(map(finite, nu)) and
                 all(map(finite, s)) and finite(g) and g >= 0 and
                 all(s[i * d + j] == s[j * d + i] for i in range(d) for j in range(d)))
        if not valid:
            if status != 1:
                print(f"fail {label}: status {status} for an input outside the ranges")
                failures += 1
            continue
        pd = positive_definite(s, d)
        if not pd:
            if status == 0:
                print(f"fail {label}: status 0 for a covariance that is not positive definite")
                failures += 1
            continue
        cond = condition(s, d)
        m = matrix([[mpf(s[i * d + j]) for j in range(d)] for i in range(d)])
        v = matrix([mpf(x) for x in nu])
        x = lu_solve(m, v)
        dist = sum(v[i] * x[i] for i in range(d))
        if status != 0:
            if required(d, cond) and dist < mpf(2) ** 1023:
                print(f"fail {label}: status {status} for a condition number {mp.nstr(cond, 3)}")
                failures += 1
            continue
        if not (mpf(lo) <= dist <= mpf(hi)):
            print(f"fail {label}: distance {mp.nstr(dist, 20)} outside [{lo!r}, {hi!r}]")
            failures += 1
        rule = 1 if hi <= g else 2 if g < lo else 0
        ok = {1: dist <= g, 2: dist > g, 0: True}[verdict]
        if verdict != rule or not ok:
            print(f"fail {label}: verdict {verdict}, rule {rule}, distance {mp.nstr(dist, 20)}")
            failures += 1
        if dist > 0:
            width = (mpf(hi) - mpf(lo)) / dist / cond
            if d <= 9 and width > WIDTH:
                print(f"fail {label}: relative width {mp.nstr(width * cond, 3)} at condition "
                      f"{mp.nstr(cond, 3)}")
                failures += 1
            if width > widest[0]:
                widest = (width, f"{label} condition {mp.nstr(cond, 3)}")
    print("statuses: " + ", ".join(f"{k}: {n}" for k, n in sorted(statuses.items())))
    print(f"largest relative width over the condition number: {mp.nstr(widest[0], 3)} at {widest[1]}")
    print(f"{checks} checks, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
