# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Checks the results of Demos.Attitude.QMethod.qmethod against Davenport's matrix, its
eigenvectors, and the bounds of the q-method computed in mpmath at 50 digits from the real values
of the inputs, written apart from the program.

Each input line, which `verified-cases-qmethod --bits` prints, holds a class, the number of input
values, the bits of the input and of a true attitude's quaternion, and the bits of the eight
result values: status, `w`, `x`, `y`, `z`, `errOpt`, `err`, and the cut `c`.  The check requires
status 0 for the classes `good`, `bias`, `edge`, and `turned`, 1 for `bad1`, and 2 for `bad2`,
and zeros after the status of a result of status 1 or 2.  For status 0 it requires `q̂` of unit
length within `1e-15` and with `w ≥ 0`, computes `K` and its eigenvalues `λ1 ≥ λ2 ≥ λ3 ≥ λ4` and a
unit eigenvector `e` of `λ1`, and requires `λ2 < c < λ1`, the angle `2 arccos |q̄ · e|` between the
attitudes of `q̂` and `e` at most `errOpt`, `μ > c` and `μt > c`, the sines `s = ρ / (μ - c)` and
`t = ρt / (μt - c)` at most 1, where `μ` is the Rayleigh quotient of `q̄`, `ρ` its residual,
`ρt = Σ a sin ε`, and `μt = Σ a cos ε`, `errOpt` at or above `2 arcsin s` and less than `1e-12`
above it, and `err` at or above `2 (arcsin s + arcsin t)` and less than `1e-12` above it.  It
checks that the true attitude meets the error bounds and that the angle between its attitude and
that of `q̂` is at most `err`.
Usage: uv run tests/attitude/qreference.py CASES"""
import struct
import sys

from mpmath import mp, mpf, matrix, eigsy, sqrt, sin, cos, asin, acos

mp.dps = 50


def double(bits: str):
    return mpf(struct.unpack("<d", struct.pack("<Q", int(bits)))[0])


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def unit(a):
    n = sqrt(dot(a, a))
    return [x / n for x in a]


def qmul(p, q):
    w1, x1, y1, z1 = p
    w2, x2, y2, z2 = q
    return [w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2, w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2,
            w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2, w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2]


def rotate(q, v):
    """The image of `v` under the attitude of the unit quaternion `q`: `q v q*`."""
    c = [q[0], -q[1], -q[2], -q[3]]
    return qmul(qmul(q, [0, v[0], v[1], v[2]]), c)[1:]


def angle(a, b):
    c = dot(a, b) / sqrt(dot(a, a) * dot(b, b))
    return acos(max(-1, min(1, c)))


def davenport(obs):
    """`Σ a K(b̄, r̄)`, with `qᵀ K q = Σ a r̄ · (q b̄ q*)` for `q = (w, x, y, z)`."""
    B = [[sum(a * r[j] * b[k] for b, r, a, _ in obs) for k in range(3)] for j in range(3)]
    s = B[0][0] + B[1][1] + B[2][2]
    z = [B[2][1] - B[1][2], B[0][2] - B[2][0], B[1][0] - B[0][1]]
    K = matrix(4, 4)
    K[0, 0] = s
    for j in range(3):
        K[0, j + 1] = K[j + 1, 0] = z[j]
        for k in range(3):
            K[j + 1, k + 1] = B[j][k] + B[k][j] - (s if j == k else 0)
    return K


def main():
    expect = {"good": 0, "bias": 0, "edge": 0, "turned": 0, "bad1": 1, "bad2": 2}
    counts = {}
    failures = []
    worst = {}
    above = mpf(0)
    turned = []
    for line in open(sys.argv[1]):
        f = line.split()
        cls, m = f[0], int(f[1])
        xs = [double(b) for b in f[2:2 + m]]
        qt = [double(b) for b in f[2 + m:6 + m]]
        out = [double(b) for b in f[6 + m:14 + m]]
        status = int(out[0])
        counts[(cls, status)] = counts.get((cls, status), 0) + 1
        tag = f"{cls} line {sum(counts.values())}"
        if status != expect[cls]:
            failures.append(f"{tag}: status {status}, expected {expect[cls]}")
            continue
        if status != 0:
            if any(x != 0 for x in out[1:]):
                failures.append(f"{tag}: nonzero values after status {status}")
            continue
        n = int(xs[0])
        obs = []
        for i in range(n):
            r = xs[1 + 8 * i:9 + 8 * i]
            obs.append((unit(r[0:3]), unit(r[3:6]), r[6], r[7]))
        K = davenport(obs)
        E, Q = eigsy(K)
        order = sorted(range(4), key=lambda i: E[i], reverse=True)
        l1, l2 = E[order[0]], E[order[1]]
        e = [Q[r, order[0]] for r in range(4)]
        if abs(sqrt(dot(out[1:5], out[1:5])) - 1) > mpf("1e-15") or out[1] < 0:
            failures.append(f"{tag}: q̂ not of unit length with w ≥ 0")
        q = unit(out[1:5])
        errOpt, err, c = out[5], out[6], out[7]
        if not (l2 < c < l1):
            failures.append(f"{tag}: cut {c} outside ({l2}, {l1})")
            continue
        opt = 2 * acos(min(1, abs(dot(q, e))))
        if opt > errOpt:
            failures.append(f"{tag}: angle to the optimum {opt} above errOpt {errOpt}")
        Kq = [sum(K[i, j] * q[j] for j in range(4)) for i in range(4)]
        mu = dot(q, Kq)
        rho = sqrt(sum((Kq[i] - mu * q[i]) ** 2 for i in range(4)))
        rt = sum(a * sin(eps) for _, _, a, eps in obs)
        mt = sum(a * cos(eps) for _, _, a, eps in obs)
        if not (mu > c and mt > c):
            failures.append(f"{tag}: a gap to the cut is not positive")
            continue
        s = rho / (mu - c)
        t = rt / (mt - c)
        if not (s <= 1 and t <= 1):
            failures.append(f"{tag}: a sine above 1, s = {s}, t = {t}")
            continue
        fopt = 2 * asin(s)
        ferr = 2 * (asin(s) + asin(t))
        if not (fopt <= errOpt < fopt + mpf("1e-12")):
            failures.append(f"{tag}: errOpt {errOpt} against its formula {fopt}")
        if not (ferr <= err < ferr + mpf("1e-12")):
            failures.append(f"{tag}: err {err} against its formula {ferr}")
        above = max(above, errOpt - fopt, err - ferr)
        if cls == "turned":
            turned.append(errOpt / opt)
        qn = unit(qt)
        for b, r, a, eps in obs:
            if angle(rotate(qn, b), r) > eps:
                failures.append(f"{tag}: the true attitude violates an error bound")
        true = 2 * acos(min(1, abs(dot(q, qn))))
        if true > err:
            failures.append(f"{tag}: true error {true} above err {err}")
        if err > 0:
            worst[cls] = max(worst.get(cls, mpf(0)), true / err)
    print("class   status  count")
    for (cls, status), k in sorted(counts.items()):
        print(f"{cls:7s} {status:6d}  {k:5d}")
    print(f"largest excess of errOpt or err over its formula: {mp.nstr(above, 3)}")
    if turned:
        print("errOpt over the angle to the optimum, class turned: "
              f"{mp.nstr(min(turned), 4)} to {mp.nstr(max(turned), 4)}")
    for cls, r in sorted(worst.items()):
        print(f"largest true error over err, class {cls}: {mp.nstr(r, 3)}")
    for msg in failures:
        print("fail:", msg)
    if failures:
        sys.exit(1)
    print("every check passed")


if __name__ == "__main__":
    main()
