# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Checks the results of Demos.Attitude.triad against TRIAD and its error bound computed in
mpmath at 50 digits from the real values of the inputs, written apart from the program.

Each input line, which `verified-cases-attitude --bits` prints, holds a class, the bits of the
fourteen arguments and of a true attitude's quaternion, the status, the status and the endpoints
of each of the nine intervals, and the bits of `err`.  The check requires status 0 for the
classes `good` and `worst`, 1 for `bad1`, and 2 for `bad2`.  For status 0 or 2 it requires every
interval accepted and the reference matrix inside it.  For status 0 it requires `err` at or above
`F + arcsin(η/(1 - η))`, with `η` from the returned intervals, and less than `1e-12` above it.
For the classes `good` and `worst`, it checks that the true attitude meets the error bounds and
that the midpoint matrix of the intervals moves no tested unit vector farther than `err` from its
true image, testing the vectors perpendicular to the axis of the error rotation, where the angle
is largest, and 64 random vectors.
Usage: uv run tests/attitude/reference.py CASES"""
import random
import struct
import sys

from mpmath import mp, mpf, sqrt, sin, cos, asin, acos

mp.dps = 50


def double(bits: str):
    return mpf(struct.unpack("<d", struct.pack("<Q", int(bits)))[0])


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def norm(a):
    return sqrt(dot(a, a))


def unit(a):
    n = norm(a)
    return [x / n for x in a]


def frame(a, b):
    t1 = unit(a)
    t2 = unit(cross(a, b))
    return [t1, t2, cross(t1, t2)]


def triad(b1, b2, r1, r2):
    t = frame(b1, b2)
    s = frame(r1, r2)
    return [[sum(s[i][j] * t[i][k] for i in range(3)) for k in range(3)] for j in range(3)]


def rotate(q, v):
    n = sqrt(sum(x * x for x in q))
    w, x, y, z = (c / n for c in q)
    p = [x, y, z]
    t = [2 * c for c in cross(p, v)]
    u = cross(p, t)
    return [v[i] + w * t[i] + u[i] for i in range(3)]


def angle(a, b):
    c = dot(a, b) / (norm(a) * norm(b))
    return acos(max(mpf(-1), min(mpf(1), c)))


def bound(e1, e2, r1, r2):
    st = norm(cross(unit(r1), unit(r2)))
    x = sin(e1 + e2) / st
    h = sin(e1 / 2) ** 2 + cos(e1 / 2) ** 2 * x * x / (2 * (1 + sqrt(1 - x * x)))
    return 2 * asin(sqrt(h)), x


def apply(m, v):
    return [sum(m[j][k] * v[k] for k in range(3)) for j in range(3)]


def worst_angle(m, q, rng):
    """The largest angle between m v and the true image of v over the tested unit vectors."""
    qc = [q[0], -q[1], -q[2], -q[3]]
    cols = [rotate(q, e) for e in ([1, 0, 0], [0, 1, 0], [0, 0, 1])]
    # E = m Q^T maps the true image of v to m v
    e = [[sum(m[j][k] * cols[i][k] for k in range(3)) for i in range(3)] for j in range(3)]
    axis = [e[2][1] - e[1][2], e[0][2] - e[2][0], e[1][0] - e[0][1]]
    vs = []
    if norm(axis) > 0:
        a = unit(axis)
        p = unit(cross(a, [1, 0, 0] if abs(a[0]) < mpf("0.9") else [0, 1, 0]))
        p2 = cross(a, p)
        for k in range(16):
            c, s = cos(2 * mp.pi * k / 16), sin(2 * mp.pi * k / 16)
            y = [c * p[i] + s * p2[i] for i in range(3)]
            vs.append(rotate(qc, y))
    for _ in range(64):
        v = [mpf(rng.gauss(0, 1)) for _ in range(3)]
        vs.append(unit(v))
    return max(angle(apply(m, v), rotate(q, v)) for v in vs)


def main() -> int:
    rng = random.Random(20261111)
    failures = 0
    counts = {}
    ratio = {"good": mpf(0), "worst": mpf(0)}
    excess = mpf(0)
    for line in open(sys.argv[1]):
        f = line.split()
        if not f:
            continue
        cls = f[0]
        raw = f[1:19]
        vals = [double(b) for b in raw[:18]]
        b1, b2, r1, r2 = vals[0:3], vals[3:6], vals[6:9], vals[9:12]
        e1, e2 = vals[12], vals[13]
        q = vals[14:18]
        status = int(f[19])
        ivs = [(int(f[20 + 3 * i]), double(f[21 + 3 * i]), double(f[22 + 3 * i])) for i in range(9)]
        err = double(f[47])
        counts[(cls, status)] = counts.get((cls, status), 0) + 1
        want = {"good": 0, "worst": 0, "bad1": 1, "bad2": 2}.get(cls)
        problems = []
        if want is not None and status != want:
            problems.append(f"status {status}, expected {want}")
        if status in (0, 2):
            t = triad(b1, b2, r1, r2)
            for i, (s, lo, hi) in enumerate(ivs):
                if s != 0 or not (lo <= t[i // 3][i % 3] <= hi):
                    problems.append(f"entry {i} not enclosed")
        if status == 0:
            f_val, x = bound(e1, e2, r1, r2)
            eta = sqrt(sum((hi - lo) ** 2 for _, lo, hi in ivs))
            ref = f_val + asin(eta / (1 - eta))
            if not (ref <= err):
                problems.append(f"err {err} below its formula {ref}")
            elif err - ref > mpf("1e-12"):
                problems.append(f"err {err} exceeds its formula {ref} by more than 1e-12")
            excess = max(excess, err - ref)
            if cls in ("good", "worst"):
                h1 = angle(rotate(q, unit(b1)), unit(r1))
                h2 = angle(rotate(q, unit(b2)), unit(r2))
                if h1 > e1 or h2 > e2:
                    problems.append("the true attitude does not meet the error bounds")
                else:
                    mid = [[(ivs[3 * j + k][1] + ivs[3 * j + k][2]) / 2 for k in range(3)]
                           for j in range(3)]
                    w = worst_angle(mid, q, rng)
                    if w > err:
                        problems.append(f"error {w} above err {err}")
                    if err > 0:
                        ratio[cls] = max(ratio[cls], w / err)
        if problems:
            failures += 1
            print("FAIL", cls, " ".join(raw[:14]), "; ".join(problems))
    for key in sorted(counts):
        print(f"class {key[0]} status {key[1]}: {counts[key]}")
    print(f"largest error over err: good {mp.nstr(ratio['good'], 6)}, worst {mp.nstr(ratio['worst'], 6)}")
    print(f"largest excess of err over its formula: {mp.nstr(excess, 3)}")
    print("failures:", failures)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
