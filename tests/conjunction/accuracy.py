# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Checks the intervals of Demos.Conjunction.Accuracy.circularError and linearError against
reference radii computed with mpmath, independently of the program's method.

The reference probability of the disk of radius r is (2 pi sqrt(det C))^-1 times the integral over
the angle t of the radial integral of rho exp(-q(rho u(t))/2) from 0 to r, where q is the quadratic
form of the density and u(t) the unit vector at angle t.  The radial integral has a closed form in
exp and erf.  The angular integral uses the trapezoid rule on the periodic integrand, with the
number of points doubled until two successive values agree to 1e-24.  The reference radius is the
root of the probability less p, bracketed by halving and doubling and found by Anderson's method,
and accepted when the probability there differs from p by less than 1e-22.  For a centered isotropic covariance, the script also checks the
reference radius against sigma sqrt(-2 ln(1 - p)).  The reference half-width of the linear error is
the root of (erf((L - b)/sqrt(2v)) + erf((L + b)/sqrt(2v)))/2 - p at 40 digits, and for b = 0 the
script also checks it against sqrt(2v) erfinv(p).

Each line of the input, which `verified-cases-accuracy --bits` prints, holds
`circular m1 m2 c11 c12 c22 p n k status lo hi` or `linear b v p k status lo hi`, with the bit
patterns of the floats.  A result must have status 0 with the reference in [lo, hi], except for the
inputs listed in UNFINISHED, which must have status 2.  An accepted circular interval at p = 0.9
must be at most 12/n of the reference wide, the bound that the measurement of the requirements
gives, and an accepted linear interval at most 1e-8 of it.  The script prints each result, its
reference, and its width relative to the reference.
Usage: uv run tests/conjunction/accuracy.py CASES"""
import struct
import sys

from mpmath import mp, mpf

mp.dps = 40

# Inputs (m1, m2, c11, c12, c22, p, n) whose searches must end with status 2.
UNFINISHED = {(0.0, 0.0, 1.0, 0.0, 1.0, 0.9999999, 16), (0.0, 0.0, 1.0, 0.0, 1.0, 0.999999, 256),
              (0.0, 0.0, 1.0, 0.0, 1.0, 0.99, 256), (0.0, 0.0, 1.0, 0.0, 1.0, 0.5, 1),
              (0.0, 0.0, 1.0, 0.0, 1.0, 0.5, 2)}


def double(bits: str) -> float:
    return struct.unpack("<d", struct.pack("<Q", int(bits)))[0]


def disk_probability(m1, m2, c11, c12, c22, r):
    det = c11 * c22 - c12 * c12
    i11, i12, i22 = c22 / det, -c12 / det, c11 / det
    c = i11 * m1 * m1 + 2 * i12 * m1 * m2 + i22 * m2 * m2

    def radial(t):
        u1, u2 = mp.cos(t), mp.sin(t)
        a = i11 * u1 * u1 + 2 * i12 * u1 * u2 + i22 * u2 * u2
        b = i11 * u1 * m1 + i12 * (u1 * m2 + u2 * m1) + i22 * u2 * m2
        k = b / a
        d = c - b * b / a
        s = mp.sqrt(a / 2)
        t1 = (mp.exp(-c / 2) - mp.exp(-(a * (r - k) ** 2 + d) / 2)) / a
        t2 = k * mp.sqrt(mp.pi / (2 * a)) * mp.exp(-d / 2) * (mp.erf((r - k) * s) + mp.erf(k * s))
        return t1 + t2

    points = 64
    total = mp.fsum(radial(2 * mp.pi * j / points) for j in range(points))
    value = 2 * mp.pi * total / points
    while True:
        total += mp.fsum(radial(2 * mp.pi * (2 * j + 1) / (2 * points)) for j in range(points))
        points *= 2
        refined = 2 * mp.pi * total / points
        if abs(refined - value) < mpf("1e-24"):
            return refined / (2 * mp.pi * mp.sqrt(det))
        value = refined


def line_probability(b, v, x):
    k = mp.sqrt(2 * v)
    return (mp.erf((x - b) / k) + mp.erf((x + b) / k)) / 2


def root(f, guess, tol):
    """The root of the increasing function f on (0, inf), bracketed from guess > 0."""
    a = b = guess
    while f(a) > 0:
        a /= 2
    while f(b) < 0:
        b *= 2
    x = mp.findroot(f, (a, b), solver="anderson")
    if abs(f(x)) >= tol:
        raise ValueError(f"no root near {guess}: residual {f(x)}")
    return x


def main() -> int:
    failures = 0
    disk_roots = {}
    for line in open(sys.argv[1]):
        fields = line.split()
        if not fields:
            continue
        if fields[0] == "circular":
            values = [double(f) for f in fields[1:7]]
            n, k, status = int(fields[7]), int(fields[8]), int(fields[9])
            lo, hi = mpf(double(fields[10])), mpf(double(fields[11]))
            m1, m2, c11, c12, c22, p = [mpf(x) for x in values]
            label = (f"circular m=({values[0]:g},{values[1]:g}) "
                     f"C=({values[2]:g},{values[3]:g},{values[4]:g}) p={values[5]:g} n={n} k={k}")
            if (*values, n) in UNFINISHED:
                ok = status == 2
                print(f"{'ok  ' if ok else 'FAIL'} {label} status={status}, expected 2")
                failures += 0 if ok else 1
                continue
            key = tuple(fields[1:7])
            if key not in disk_roots:
                guess = (lo + hi) / 2 if status == 0 else mp.sqrt(c11 + c22)
                ref = root(lambda r: disk_probability(m1, m2, c11, c12, c22, r) - p, guess,
                           mpf("1e-22"))
                if m1 == 0 and m2 == 0 and c12 == 0 and c11 == c22:
                    closed = mp.sqrt(c11) * mp.sqrt(-2 * mp.log(1 - p))
                    if abs(closed - ref) > mpf("1e-18") * closed:
                        print(f"FAIL {label} reference {ref} differs from the closed form {closed}")
                        failures += 1
                disk_roots[key] = ref
            ref = disk_roots[key]
        elif fields[0] == "linear":
            values = [double(f) for f in fields[1:4]]
            k, status = int(fields[4]), int(fields[5])
            lo, hi = mpf(double(fields[6])), mpf(double(fields[7]))
            b, v, p = [mpf(x) for x in values]
            label = f"linear b={values[0]:g} v={values[1]:g} p={values[2]:g} k={k}"
            guess = abs(b) + 2 * mp.sqrt(v)
            ref = root(lambda x: line_probability(b, v, x) - p, guess, mpf("1e-35"))
            if b == 0:
                closed = mp.sqrt(2 * v) * mp.erfinv(p)
                if abs(closed - ref) > mpf("1e-30") * closed:
                    print(f"FAIL {label} reference {ref} differs from the closed form {closed}")
                    failures += 1
        else:
            print(f"FAIL unknown line: {line.strip()}")
            failures += 1
            continue
        ok = status == 0 and lo <= ref <= hi
        if ok and fields[0] == "circular" and values[5] == 0.9:
            ok = (hi - lo) / ref <= mpf(12) / n
        if ok and fields[0] == "linear":
            ok = (hi - lo) / ref <= mpf("1e-8")
        failures += 0 if ok else 1
        print(f"{'ok  ' if ok else 'FAIL'} {label} status={status} ref={mp.nstr(ref, 17)} "
              f"lo={mp.nstr(lo, 17)} hi={mp.nstr(hi, 17)} width={mp.nstr((hi - lo) / ref, 3)}")
    print(f"{failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
