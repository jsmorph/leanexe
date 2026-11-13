# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Checks the message form of the conjunction program against a projection and a probability
computed in high precision.  Each line of the input, which `verified-cases-conjunction --message`
prints, holds the kind `valid` or `rejected`, the bit patterns of the 24 values of the two states
and covariances and of the radius, the panel count, the status and endpoints of `pcMessage`, and
the status and endpoints of the five intervals of `encounterAt`.  For a valid input the check
projects the states and covariances onto the encounter plane with mpmath at 50 digits, with
matrices and the axes of `planeAxes`, requires each projected quantity to lie in its interval,
integrates the density over the disk with the polar quadrature of `reference.py`, and requires the
probability to lie in `[lo, hi]`.  For a rejected input it requires status 1.
Usage: uv run tests/conjunction/message.py CASES"""
import os
import sys

from mpmath import matrix, mp, mpf, sqrt

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from reference import double, reference  # noqa: E402

mp.dps = 50


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def unit(a):
    n = sqrt(dot(a, a))
    return [x / n for x in a]


def inertial(position, velocity, entries):
    """The covariance in the inertial frame of one given in the RTN frame of the state."""
    r = unit(position)
    n = unit(cross(position, velocity))
    t = cross(n, r)
    rr, tr, tt, nr, nt, nn = entries
    c = matrix([[rr, tr, nr], [tr, tt, nt], [nr, nt, nn]])
    q = matrix([[r[i], t[i], n[i]] for i in range(3)])
    return q * c * q.T


def encounter(values):
    """The miss vector and the covariance in the encounter plane, in m and m²."""
    p1, v1, c1 = values[0:3], values[3:6], values[6:12]
    p2, v2, c2 = values[12:15], values[15:18], values[18:24]
    c = inertial(p1, v1, c1) + inertial(p2, v2, c2)
    d = [1000 * (a - b) for a, b in zip(p2, p1)]
    z = unit([a - b for a, b in zip(v2, v1)])
    dz = dot(d, z)
    x = unit([a - dz * b for a, b in zip(d, z)])
    y = cross(z, x)
    xm, ym = matrix(x), matrix(y)
    return [dot(d, x), dot(d, y), (xm.T * c * xm)[0], (xm.T * c * ym)[0], (ym.T * c * ym)[0]]


def main() -> int:
    failures = 0
    cache = {}
    names = ["m1", "m2", "c11", "c12", "c22"]
    for line in open(sys.argv[1]):
        fields = line.split()
        if not fields:
            continue
        kind = fields[0]
        values = [mpf(double(f)) for f in fields[1:25]]
        r = mpf(double(fields[25]))
        n = int(fields[26])
        status = int(fields[27])
        lo = mpf(double(fields[28]))
        hi = mpf(double(fields[29]))
        plane = fields[30:45]
        if kind == "rejected":
            ok = status == 1
            if not ok:
                failures += 1
            print(f"{'ok  ' if ok else 'FAIL'} rejected n={n} status={status}")
            continue
        key = tuple(fields[1:26])
        if key not in cache:
            e = encounter(values)
            cache[key] = (e, reference(*e, r))
        e, ref = cache[key]
        notes = []
        for i, name in enumerate(names):
            s = int(plane[3 * i])
            a = mpf(double(plane[3 * i + 1]))
            b = mpf(double(plane[3 * i + 2]))
            if s != 0 or not a <= e[i] <= b:
                notes.append(f"{name} outside [{mp.nstr(a, 17)}, {mp.nstr(b, 17)}]")
        if status != 0 or not lo <= ref <= hi:
            notes.append("probability outside the interval")
        ok = not notes
        if not ok:
            failures += 1
        print(
            f"{'ok  ' if ok else 'FAIL'} m=({mp.nstr(e[0], 8)},{mp.nstr(e[1], 3)}) "
            f"C=({mp.nstr(e[2], 8)},{mp.nstr(e[3], 8)},{mp.nstr(e[4], 8)}) r={mp.nstr(r, 6)} "
            f"n={n} status={status} ref={mp.nstr(ref, 17)} lo={mp.nstr(lo, 17)} "
            f"hi={mp.nstr(hi, 17)} width={mp.nstr(hi - lo, 3)}"
            + "".join(f"; {note}" for note in notes)
        )
    print(f"{failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
