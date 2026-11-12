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
root of the probability less p, bracketed by halving and doubling, narrowed by bisection to a
relative width of 1e-6, and found by Anderson's method, and accepted when the probability there
differs from p by less than 1e-22.  For a centered isotropic covariance, the script also checks the
reference radius against sigma sqrt(-2 ln(1 - p)).  The reference half-width of the linear error is
the root of (erf((L - b)/sqrt(2v)) + erf((L + b)/sqrt(2v)))/2 - p at 40 digits, and for b = 0 the
script also checks it against sqrt(2v) erfinv(p).

Each line of the input, which `verified-cases-accuracy --bits` and `verified-cases-adaptive --bits`
print, holds `circular m1 m2 c11 c12 c22 p n k status lo hi` for circularError,
`adaptive m1 m2 c11 c12 c22 p n k status lo hi` for circularErrorAdaptive,
`linear b v p k status lo hi` for linearError, or `probability m1 m2 c11 c12 c22 r n status lo hi`
for pcAdaptive, with the bit patterns of the floats.  A result must have status 0 with the
reference in [lo, hi], except for the inputs listed in UNFINISHED and UNFINISHED_ADAPTIVE, which
must have status 2.  An accepted circular interval at p = 0.9 must be at most 12/n of the reference
wide, an adaptive one at most ADAPTIVE_BOUND/n, the bounds that the measurements of the
requirements give, and an accepted linear interval at most 1e-8 of it.  The reference probability
of a probability line is the polar integral of tests/conjunction/reference.py at 50 digits.

The lines of `verified-cases-adaptive --sweep` hold `sweep method nmin`, the least panel count at
which the method's search returned status 0, and then the result at that count, as a line
`circular-at` or `adaptive-at` with the fields of `circular`.  Such a result must have status 0 and
contain the reference.  The script prints each result, its reference, and its width relative to
the reference.
Usage: uv run tests/conjunction/accuracy.py CASES"""
import struct
import sys

from mpmath import mp, mpf

import reference

mp.dps = 40

# Inputs (m1, m2, c11, c12, c22, p, n) whose searches must end with status 2.
UNFINISHED = {(0.0, 0.0, 1.0, 0.0, 1.0, 0.9999999, 16), (0.0, 0.0, 1.0, 0.0, 1.0, 0.999999, 256),
              (0.0, 0.0, 1.0, 0.0, 1.0, 0.99, 256), (0.0, 0.0, 1.0, 0.0, 1.0, 0.5, 1),
              (0.0, 0.0, 1.0, 0.0, 1.0, 0.5, 2)}


# Inputs (m1, m2, c11, c12, c22, p, n) whose adaptive searches must end with status 2.
UNFINISHED_ADAPTIVE = {(0.0, 0.0, 1.0, 0.0, 1.0, 0.9999999, 256),
                       (0.0, 0.0, 1.0, 0.0, 1.0, 0.999999, 1024),
                       (0.0, 0.0, 1.0, 0.0, 1.0, 0.99, 16)}

# The bound on n times the relative width of an accepted adaptive interval at p = 0.9.
ADAPTIVE_BOUND = 14


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
    while b - a > mpf("1e-6") * b:
        c = (a + b) / 2
        if f(c) < 0:
            a = c
        else:
            b = c
    x = mp.findroot(f, (a, b), solver="anderson")
    if abs(f(x)) >= tol:
        raise ValueError(f"no root near {guess}: residual {f(x)}")
    return x


def main() -> int:
    failures = 0
    disk_roots = {}
    probability_refs = {}
    for line in open(sys.argv[1]):
        fields = line.split()
        if not fields:
            continue
        kind = fields[0]
        if kind == "sweep":
            print(f"     sweep {fields[1]} {' '.join(fields[3:])}: least n with status 0 is "
                  f"{fields[2]}")
            continue
        if kind == "probability":
            values = [double(f) for f in fields[1:7]]
            n, status = int(fields[7]), int(fields[8])
            lo, hi = mpf(double(fields[9])), mpf(double(fields[10]))
            key = tuple(fields[1:7])
            if key not in probability_refs:
                with mp.workdps(50):
                    probability_refs[key] = reference.reference(*[mpf(v) for v in values])
            ref = probability_refs[key]
            ok = status == 0 and lo <= ref <= hi
            failures += 0 if ok else 1
            print(f"{'ok  ' if ok else 'FAIL'} probability m=({values[0]:g},{values[1]:g}) "
                  f"C=({values[2]:g},{values[3]:g},{values[4]:g}) r={values[5]:g} n={n} "
                  f"status={status} ref={mp.nstr(ref, 17)} lo={mp.nstr(lo, 17)} "
                  f"hi={mp.nstr(hi, 17)} width={mp.nstr(hi - lo, 3)}")
            continue
        if kind in ("circular", "adaptive", "circular-at", "adaptive-at"):
            values = [double(f) for f in fields[1:7]]
            n, k, status = int(fields[7]), int(fields[8]), int(fields[9])
            lo, hi = mpf(double(fields[10])), mpf(double(fields[11]))
            m1, m2, c11, c12, c22, p = [mpf(x) for x in values]
            label = (f"{kind} m=({values[0]:g},{values[1]:g}) "
                     f"C=({values[2]:g},{values[3]:g},{values[4]:g}) p={values[5]:g} n={n} k={k}")
            unfinished = {"circular": UNFINISHED, "adaptive": UNFINISHED_ADAPTIVE}.get(kind, set())
            if (*values, n) in unfinished:
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
        elif kind == "linear":
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
        if ok and kind == "circular" and values[5] == 0.9:
            ok = (hi - lo) / ref <= mpf(12) / n
        if ok and kind == "adaptive" and values[5] == 0.9:
            ok = (hi - lo) / ref <= mpf(ADAPTIVE_BOUND) / n
        if ok and kind == "linear":
            ok = (hi - lo) / ref <= mpf("1e-8")
        failures += 0 if ok else 1
        print(f"{'ok  ' if ok else 'FAIL'} {label} status={status} ref={mp.nstr(ref, 17)} "
              f"lo={mp.nstr(lo, 17)} hi={mp.nstr(hi, 17)} width={mp.nstr((hi - lo) / ref, 3)}")
    print(f"{failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
