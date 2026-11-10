# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Checks the intervals of Demos.Conjunction.pc against a reference value of the
probability of collision.  The reference integrates the Gaussian density over the disk in polar
coordinates with mpmath at 50 digits, independently of the program's reduction to one dimension.
Each line of the input, which `verified-cases-conjunction --bits` prints, holds the bit patterns
`m1 m2 c11 c12 c22 r n status lo hi`.  The check fails when a result is rejected or when the reference lies outside `[lo, hi]`.  It prints the
reference, the interval, and the width of each case.
Usage: uv run tests/conjunction/reference.py CASES"""
import struct
import sys

from mpmath import mp, mpf

mp.dps = 50


def double(bits: str) -> float:
    return struct.unpack("<d", struct.pack("<Q", int(bits)))[0]


def reference(m1, m2, c11, c12, c22, r):
    det = c11 * c22 - c12 * c12
    norm = 1 / (2 * mp.pi * mp.sqrt(det))

    def density(rho, theta):
        dx = rho * mp.cos(theta) - m1
        dy = rho * mp.sin(theta) - m2
        q = (c22 * dx * dx - 2 * c12 * dx * dy + c11 * dy * dy) / det
        return norm * mp.exp(-q / 2) * rho

    quarter = mp.pi / 2
    angles = [quarter * k for k in range(5)]
    return mp.quad(density, [0, r / 2, r], angles)


def main() -> int:
    failures = 0
    cache = {}
    for line in open(sys.argv[1]):
        fields = line.split()
        if not fields:
            continue
        values = [double(f) for f in fields[:6]]
        n = int(fields[6])
        status = int(fields[7])
        lo = mpf(double(fields[8]))
        hi = mpf(double(fields[9]))
        key = tuple(fields[:6])
        if key not in cache:
            cache[key] = reference(*[mpf(v) for v in values])
        ref = cache[key]
        ok = status == 0 and lo <= ref <= hi
        if not ok:
            failures += 1
        print(
            f"{'ok  ' if ok else 'FAIL'} m=({values[0]:g},{values[1]:g}) "
            f"C=({values[2]:g},{values[3]:g},{values[4]:g}) r={values[5]:g} n={n} "
            f"status={status} ref={mp.nstr(ref, 17)} lo={mp.nstr(lo, 17)} "
            f"hi={mp.nstr(hi, 17)} width={mp.nstr(hi - lo, 3)}"
        )
    print(f"{failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
