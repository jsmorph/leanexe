# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Checks the intervals of Demos.Gate.tail, cdf, and quantile against mpmath at 50 digits.

The reference tail and distribution function are mpmath's regularized incomplete gamma functions
of shape k/2 at x/2, which mpmath computes independently of the program's closed form.  The
reference quantile at p is the root of the regularized lower incomplete gamma function less p,
found by bisection to a relative width of 1e-40.  Each input is read from its bit pattern, so the
references belong to the binary64 inputs.

Each line of the input, which `verified-cases-chisquare --bits` prints, holds `tail k x status lo hi`,
`cdf k x status lo hi`, or `quantile k p h status lo hi`, with the bit patterns of the floats.  An
input inside the documented ranges must give status 0 and an interval that contains the
reference, and an input outside them status 1 with zero endpoints.  With u = 2^-53, a tail at a
point x from 0 to 1,450 must have a relative width of at most 8 (k + x + 10) u, a distribution
function an absolute width of at most 4 (k + 10) u, and a quantile interval at p from 1e-6 to
1 - 2^-53 a relative width of at most 2 (k + 10) u / min(p, 1 - p).  These bounds are those of the
README, about 1.5 times the largest values that the cases give.  The script prints, for each kind,
the largest ratio of a width to its bound.
Usage: uv run tests/gate/distribution.py CASES"""
import struct
import sys

from mpmath import mp, mpf, gammainc

mp.dps = 50

U = mpf(2) ** -53


def tail_bound(k, x):
    return 8 * (k + mpf(x) + 10) * U


def cdf_bound(k):
    return 4 * (k + 10) * U


def quantile_bound(k, p):
    return 2 * (k + 10) * U / min(mpf(p), 1 - mpf(p))


def flt(bits):
    return struct.unpack("<d", struct.pack("<Q", int(bits)))[0]


def finite(x):
    return x == x and abs(x) != float("inf")


def lower(k, x):
    if x <= 0:
        return mpf(0)
    return gammainc(mpf(k) / 2, 0, mpf(x) / 2, regularized=True)


def upper(k, x):
    if x <= 0:
        return mpf(1)
    return gammainc(mpf(k) / 2, mpf(x) / 2, mp.inf, regularized=True)


def root(k, p):
    lo, hi = mpf("1e-2000"), mpf(k) + 2 * mp.sqrt(40 * k) + 80
    while lower(k, hi) < p:
        hi *= 2
    assert lower(k, lo) < p
    while hi - lo > hi * mpf("1e-40"):
        mid = mp.sqrt(lo * hi)
        if lower(k, mid) < p:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def main(path):
    failures = 0
    checks = 0
    widest = {"tail": (mpf(0), None), "cdf": (mpf(0), None), "quantile": (mpf(0), None)}
    for line in open(path):
        parts = line.split()
        kind = parts[0]
        k = int(parts[1])
        status = int(parts[-3])
        lo, hi = flt(parts[-2]), flt(parts[-1])
        checks += 1
        if kind in ("tail", "cdf"):
            x = flt(parts[2])
            valid = finite(x) and 1 <= k <= 1000
            label = f"{kind} k={k} x={x!r}"
            if not valid:
                if status != 1 or lo != 0 or hi != 0:
                    print(f"fail {label}: status {status}, expected 1")
                    failures += 1
                continue
            ref = upper(k, x) if kind == "tail" else lower(k, x)
            if status != 0 or not (mpf(lo) <= ref <= mpf(hi)):
                print(f"fail {label}: status {status} [{lo!r}, {hi!r}] reference {mp.nstr(ref, 20)}")
                failures += 1
                continue
            if kind == "tail":
                if not (0 <= x <= 1450):
                    continue
                ratio = (mpf(hi) - mpf(lo)) / ref / tail_bound(k, x)
            else:
                ratio = (mpf(hi) - mpf(lo)) / cdf_bound(k)
            if ratio > 1:
                print(f"fail {label}: width {mp.nstr(ratio, 3)} times its bound")
                failures += 1
            if ratio > widest[kind][0]:
                widest[kind] = (ratio, label)
        else:
            p = flt(parts[2])
            h = int(parts[3])
            valid = finite(p) and 0 < p < 1 and 1 <= k <= 1000 and h <= 64
            label = f"quantile k={k} p={p!r} h={h}"
            if not valid:
                if status != 1 or lo != 0 or hi != 0:
                    print(f"fail {label}: status {status}, expected 1")
                    failures += 1
                continue
            ref = root(k, mpf(p))
            if status != 0 or not (mpf(lo) <= ref <= mpf(hi)):
                print(f"fail {label}: status {status} [{lo!r}, {hi!r}] reference {mp.nstr(ref, 20)}")
                failures += 1
                continue
            if p >= 1e-6 and h == 64:
                ratio = (mpf(hi) - mpf(lo)) / ref / quantile_bound(k, p)
                if ratio > 1:
                    print(f"fail {label}: width {mp.nstr(ratio, 3)} times its bound")
                    failures += 1
                if ratio > widest[kind][0]:
                    widest[kind] = (ratio, label)
    for kind, (width, label) in widest.items():
        print(f"largest {kind} width: {mp.nstr(width, 3)} times its bound, at {label}")
    print(f"{checks} checks, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
