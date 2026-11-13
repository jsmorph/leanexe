# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""The differential test of the conjunction program against the published cases of
tests/conjunction/published.py.

For a case given in the encounter plane, the inputs are the published numbers.  For a case given
as two states and two covariances in an inertial frame, the script projects them onto the encounter
plane at 50 digits: the relative position r and velocity v are the first object's less the
second's, z = v/|v| is the plane's normal, x is the unit vector along the part of r perpendicular
to z, y = z cross x, the mean is (r.x, r.y) = (|r - (r.z) z|, 0), and the plane covariance is the
sum of the two covariances projected on (x, y).  Each input is then rounded to the nearest double.

`inputs` prints, for each case, the lines that `verified-cases-adaptive --evaluate` reads: the
method, `pc` or `adaptive`, the case's name, the bit patterns of the doubles, and the panel count,
for each count of PANELS.  `check RESULTS` reads the lines that it prints and checks each case.
The reference value of a case is that of tests/conjunction/reference.py for its doubles, which
integrates the density over the disk in polar coordinates at 50 digits.  The script also integrates
the one-dimensional form of the README at 50 digits and requires the two to agree to a relative
1e-20, so that a failure of either quadrature shows.  Every result must have status 0 and contain
the reference.  Each published value is compared with the reference at its tolerance, half a unit
in its last figure for Chan's values and a relative 1e-3 for Alfano's, and a value farther away is
a disagreement, which must have a recorded cause in published.py.  For each result, the report
also states whether the interval contains the published value, meets the band of the tolerance
around it, or excludes the band, in which case the interval alone shows the disagreement.  The
script prints the report and exits with status 1 on a failure.
Usage: uv run tests/conjunction/benchmark.py inputs | check RESULTS"""
import struct
import sys
from decimal import Decimal

from mpmath import erf, exp, mp, mpf, pi, quad, sqrt

import published
import reference

mp.dps = 50

PANELS = [('pc', 4096), ('pc', 65536), ('pc', 1048576), ('adaptive', 4096), ('adaptive', 65536)]
ALFANO_TOLERANCE = Decimal('1e-3')
AGREEMENT = mpf('1e-20')


def bits(x: float) -> int:
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def double(b: str) -> float:
    return struct.unpack('<d', struct.pack('<Q', int(b)))[0]


def dot(a, b):
    return sum(p * q for p, q in zip(a, b))


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def unit(a):
    n = sqrt(dot(a, a))
    return [p / n for p in a]


def matrix(c):
    xx, xy, xz, yy, yz, zz = [mpf(e) for e in c]
    return [[xx, xy, xz], [xy, yy, yz], [xz, yz, zz]]


def form(u, c, w):
    return sum(u[i] * c[i][j] * w[j] for i in range(3) for j in range(3))


def encounter(r, v, c, full=False):
    """The mean and covariance in the encounter plane of the relative position r, the relative
    velocity v, and the combined covariance c, at 50 digits.  The mean is (|r - (r.z) z|, 0), or
    (|r|, 0) with `full`, as CARA's functions place it."""
    z = unit(v)
    perpendicular = [a - dot(r, z) * b for a, b in zip(r, z)]
    x = unit(perpendicular)
    y = cross(z, x)
    m1 = sqrt(dot(r, r) if full else dot(perpendicular, perpendicular))
    return m1, mpf(0), form(x, c, x), form(x, c, y), form(y, c, y)


def project(case: published.Alfano):
    """The mean and covariance in the encounter plane of the two states of a case."""
    p, s = case.primary, case.secondary
    r = [mpf(a) - mpf(b) for a, b in zip(p.position, s.position)]
    v = [mpf(a) - mpf(b) for a, b in zip(p.velocity, s.velocity)]
    c1, c2 = matrix(p.covariance), matrix(s.covariance)
    return encounter(r, v, [[c1[i][j] + c2[i][j] for j in range(3)] for i in range(3)])


def cases():
    """Each case's name, its doubles (m1, m2, c11, c12, c22, r), and its published values."""
    for case in published.CHAN:
        s1, s2 = mpf(case.sigma1), mpf(case.sigma2)
        plane = (mpf(case.m1), mpf(case.m2), s1 * s1, mpf(0), s2 * s2, mpf(case.radius))
        yield case.name.replace(' ', '-'), tuple(float(v) for v in plane), [case.value], 'digits'
    for case in published.ALFANO:
        plane = (*project(case), mpf(case.radius))
        yield f'Alfano-{case.case}', tuple(float(v) for v in plane), case.values, 'relative'


def one_dimensional(m1, m2, c11, c12, c22, r):
    """The probability as (2 sqrt(2 pi c11))^-1 times the integral over [-r, r] of
    exp(-(x - m1)^2/(2 c11)) (erf((h - mu)/k) + erf((h + mu)/k)), with breakpoints at the mean and
    at four standard deviations around it."""
    s = sqrt(c11)
    k = sqrt(2 * (c22 - c12 * c12 / c11))

    def f(x):
        h = sqrt(max(r * r - x * x, mpf(0)))
        mu = m2 + c12 / c11 * (x - m1)
        return exp(-(x - m1) ** 2 / (2 * c11)) * (erf((h - mu) / k) + erf((h + mu) / k))

    points = sorted({-r, r, *[p for p in (m1 - 4 * s, m1, m1 + 4 * s) if -r < p < r]})
    return quad(f, points) / (2 * sqrt(2 * pi * c11))


def tolerance(value: str, kind: str) -> mpf:
    if kind == 'digits':
        return mpf(str(Decimal(1).scaleb(Decimal(value).as_tuple().exponent) / 2))
    return mpf(str(Decimal(value) * ALFANO_TOLERANCE))


def relation(lo, hi, value, tol) -> str:
    if lo <= value <= hi:
        return 'contains'
    if lo <= value + tol and value - tol <= hi:
        return 'meets'
    return 'excludes'


def inputs():
    for name, plane, _, _ in cases():
        for method, n in PANELS:
            print(method, name, *(bits(v) for v in plane), n)


def check(path: str) -> int:
    results = {}
    for line in open(path):
        fields = line.split()
        if fields:
            results.setdefault(fields[1], []).append(fields)
    failures = 0
    computed = {}
    for name, plane, values, kind in cases():
        if plane not in computed:
            args = [mpf(v) for v in plane]
            computed[plane] = reference.reference(*args), one_dimensional(*args)
        ref, other = computed[plane]
        print(f'{name} m=({plane[0]!r}, {plane[1]!r}) C=({plane[2]!r}, {plane[3]!r}, '
              f'{plane[4]!r}) r={plane[5]!r}')
        print(f'  reference {mp.nstr(ref, 20)}, one-dimensional form differs by '
              f'{mp.nstr(abs(other - ref) / ref, 3)}')
        if abs(other - ref) > AGREEMENT * ref:
            print('  FAIL the two reference quadratures disagree')
            failures += 1
        for v in values:
            p, tol = mpf(v.value), tolerance(v.value, kind)
            agrees = abs(p - ref) <= tol
            print(f'  {v.label} {v.value}: relative difference {mp.nstr((p - ref) / ref, 3)}, '
                  f'{"agrees" if agrees else "disagrees"} at {mp.nstr(tol, 3)}')
            if not agrees and v.cause is None:
                print('  FAIL disagreement without a recorded cause')
                failures += 1
            elif agrees and v.cause is not None:
                print('  FAIL a cause is recorded but the value agrees')
                failures += 1
            elif v.cause is not None:
                print(f'    cause: {v.cause}')
        got = results.get(name, [])
        if len(got) != len(PANELS):
            print(f'  FAIL {len(got)} results, {len(PANELS)} expected')
            failures += 1
        for fields in got:
            method, n, status = fields[0], int(fields[8]), int(fields[9])
            lo, hi = mpf(double(fields[10])), mpf(double(fields[11]))
            ok = status == 0 and lo <= ref <= hi
            failures += not ok
            width = mp.nstr((hi - lo) / ref, 3) if ref > 0 else 'inf'
            marks = ', '.join(
                f'{v.label} {relation(lo, hi, mpf(v.value), tolerance(v.value, kind))}'
                for v in values)
            print(f'  {"ok  " if ok else "FAIL"} {method} n={n} status={status} '
                  f'lo={mp.nstr(lo, 17)} hi={mp.nstr(hi, 17)} relative width {width}; {marks}')
    print(f'{failures} failures')
    return 1 if failures else 0


def main() -> int:
    if sys.argv[1:] == ['inputs']:
        inputs()
        return 0
    if len(sys.argv) == 3 and sys.argv[1] == 'check':
        return check(sys.argv[2])
    print(__doc__.rsplit('\n', 1)[-1], file=sys.stderr)
    return 2


if __name__ == '__main__':
    sys.exit(main())
