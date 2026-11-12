# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Tests the avoidance module against an oracle of the two-body model and the probability of
collision, written apart from the program.

The script builds the cases of `cases()`, runs the exports `authorize` and `pcBox` of the
WebAssembly module with `tests/avoidance/authorize.mjs` under Node, and checks each output.

The oracle propagates a state with its own two-body solution: the classical elements of the
state, Kepler's equation `E - e sin E = M` solved by Newton's method in mpmath at 40 digits, and
the state at the new anomaly.  It forms the relative state of the requirements, takes the axes of
the encounter plane from the coordinate axis least aligned with the relative velocity, which
differ from the program's, and computes the probability as an integral over the angle of the
radial integral along each ray from the disk's center, which has a closed form in `exp` and
`erf`, by the trapezoid rule on the periodic integrand with the number of points doubled until
two values agree to 1e-25.  Before the cases it compares the propagation with a fourth-order
Runge-Kutta integration of Newton's equation from five states, and the probability with mpmath's
two-dimensional quadrature on three inputs.

For each conjunction it samples velocity changes and displacements: the eight corners of the box,
each with a corner of the padding, the center, and six random points, and it climbs from the
largest sample by a compass search inside the box and the padding.  It checks:
  - status 1 exactly for the invalid inputs, with the output 1, 0;
  - an output of 2 + 3K values, with K in its second entry;
  - status 0 exactly when every verdict is 0, status 3 exactly when some verdict is 2;
  - verdict 0 exactly when hi < T among the accepted enclosures;
  - for every conjunction with verdict 0 or 1, every sampled probability in [lo, hi];
  - for status 0, every sampled probability below the threshold;
  - a verdict other than 0 for a conjunction with a sampled probability above 10 T;
  - the status and the verdicts that each case fixes in advance.
It records the ratio of hi to the largest sampled probability.  After the first run it builds
cases whose threshold equals an upper end hi, the next double above it, and a value between lo
and hi, and requires verdicts 1, 0, and 1.  For `pcBox` it samples the 32 corners and the center
of the five intervals and requires each probability in [lo, hi].  With --mutate it also alters
correct outputs and requires the checks to fail on each.  It prints one line per case and exits
with status 1 on any failure.

Usage: uv run tests/avoidance/oracle.py MODULE [--mutate]"""
import json
import math
import random
import struct
import subprocess
import sys
from dataclasses import dataclass, field, replace
from pathlib import Path

from mpmath import mp, mpf

mp.dps = 40
MU = 398600.4418
PANELS = 4096


def bits(x: float) -> str:
    return struct.pack(">d", x).hex()


def unbits(h: str) -> float:
    return struct.unpack(">d", bytes.fromhex(h))[0]


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def scale(c, a):
    return [c * x for x in a]


def norm(a):
    return mp.sqrt(dot(a, a))


def unit(a):
    return scale(1 / norm(a), a)


# ### The oracle's two-body propagation


def kepler_state(mu, r, v, t):
    """The state t seconds after (r, v) on the Kepler orbit of its classical elements."""
    mu = mpf(mu)
    r = [mpf(x) for x in r]
    v = [mpf(x) for x in v]
    t = mpf(t)
    R = norm(r)
    v2 = dot(v, v)
    rv = dot(r, v)
    inv_a = 2 / R - v2 / mu
    if inv_a <= 0:
        raise ValueError("unbound")
    a = 1 / inv_a
    h = cross(r, v)
    evec = [((v2 - mu / R) * ri - rv * vi) / mu for ri, vi in zip(r, v)]
    e = norm(evec)
    if e >= 1:
        raise ValueError("not elliptic")
    P = scale(1 / e, evec) if e > 0 else scale(1 / R, r)
    Q = scale(1 / norm(h), cross(h, P))
    E0 = mp.atan2(rv / (e * mp.sqrt(mu * a)), (1 - R / a) / e) if e > 0 else mpf(0)
    n = mp.sqrt(mu / a**3)
    M = E0 - e * mp.sin(E0) + n * t
    E = M
    for _ in range(200):
        dE = (E - e * mp.sin(E) - M) / (1 - e * mp.cos(E))
        E -= dE
        if abs(dE) < mpf(10) ** (-35):
            break
    b = a * mp.sqrt(1 - e * e)
    pos = add(scale(a * (mp.cos(E) - e), P), scale(b * mp.sin(E), Q))
    rnow = a * (1 - e * mp.cos(E))
    vel = scale(mp.sqrt(mu * a) / rnow, add(scale(-mp.sin(E), P),
                                             scale(mp.sqrt(1 - e * e) * mp.cos(E), Q)))
    return pos, vel


def rk4(mu, r, v, t, steps=40000):
    """Newton's equation integrated in binary64 with the classical fourth-order method."""
    h = t / steps

    def acc(p):
        d = math.sqrt(p[0] ** 2 + p[1] ** 2 + p[2] ** 2) ** 3
        return [-mu * x / d for x in p]

    r = list(r)
    v = list(v)
    for _ in range(steps):
        k1r, k1v = v, acc(r)
        r2 = [a + h / 2 * b for a, b in zip(r, k1r)]
        v2 = [a + h / 2 * b for a, b in zip(v, k1v)]
        k2r, k2v = v2, acc(r2)
        r3 = [a + h / 2 * b for a, b in zip(r, k2r)]
        v3 = [a + h / 2 * b for a, b in zip(v, k2v)]
        k3r, k3v = v3, acc(r3)
        r4 = [a + h * b for a, b in zip(r, k3r)]
        v4 = [a + h * b for a, b in zip(v, k3v)]
        k4r, k4v = v4, acc(r4)
        r = [a + h / 6 * (p + 2 * q + 2 * s + w) for a, p, q, s, w in zip(r, k1r, k2r, k3r, k4r)]
        v = [a + h / 6 * (p + 2 * q + 2 * s + w) for a, p, q, s, w in zip(v, k1v, k2v, k3v, k4v)]
    return r, v


# ### The oracle's probability


def erf_diff(a, b):
    """erf(a) - erf(b), through erfc when both arguments have one sign."""
    if a > 0 and b > 0:
        return mp.erfc(b) - mp.erfc(a)
    if a < 0 and b < 0:
        return mp.erfc(-a) - mp.erfc(-b)
    return mp.erf(a) - mp.erf(b)


def pc2d(m1, m2, c11, c12, c22, R):
    """The integral of the Gaussian density over the disk of radius R about the origin: over the
    angle, of the radial integral along each ray, by the trapezoid rule."""
    det = c11 * c22 - c12 * c12
    if c11 <= 0 or det <= 0:
        raise ValueError("covariance not positive definite")
    p11, p12, p22 = c22 / det, -c12 / det, c11 / det
    c0 = p11 * m1 * m1 + 2 * p12 * m1 * m2 + p22 * m2 * m2

    def ray(theta):
        u1, u2 = mp.cos(theta), mp.sin(theta)
        A = p11 * u1 * u1 + 2 * p12 * u1 * u2 + p22 * u2 * u2
        B = p11 * u1 * m1 + p12 * (u1 * m2 + u2 * m1) + p22 * u2 * m2
        mu = B / A
        k = mp.exp(-(c0 - B * B / A) / 2)
        s = mp.sqrt(A / 2)
        i1 = (mp.exp(-A * mu * mu / 2) - mp.exp(-A * (R - mu) ** 2 / 2)) / A
        i0 = mp.sqrt(mp.pi / (2 * A)) * erf_diff(s * (R - mu), -s * mu)
        return k * (i1 + mu * i0)

    def trapezoid(n):
        return 2 * mp.pi / n * mp.fsum(ray(2 * mp.pi * i / n) for i in range(n))

    n = 32
    prev = trapezoid(n)
    while True:
        n *= 2
        cur = trapezoid(n)
        if abs(cur - prev) <= mpf(10) ** -25 * abs(cur) or n >= 2 ** 16:
            break
        prev = cur
    return cur / (2 * mp.pi * mp.sqrt(det))


def pc2d_quad(m1, m2, c11, c12, c22, R):
    """The same integral by mpmath's two-dimensional quadrature in polar coordinates."""
    det = c11 * c22 - c12 * c12

    def density(rho, theta):
        dx = rho * mp.cos(theta) - m1
        dy = rho * mp.sin(theta) - m2
        q = (c22 * dx * dx - 2 * c12 * dx * dy + c11 * dy * dy) / det
        return mp.exp(-q / 2) * rho

    quarter = mp.pi / 2
    with mp.workdps(20):
        v = mp.quad(density, [0, R / 2, R], [quarter * k for k in range(5)])
    return v / (2 * mp.pi * mp.sqrt(det))


def cov_apply(C, e):
    cxx, cxy, cxz, cyy, cyz, czz = C
    return [cxx * e[0] + cxy * e[1] + cxz * e[2], cxy * e[0] + cyy * e[1] + cyz * e[2],
            cxz * e[0] + cyz * e[1] + czz * e[2]]


def pc_encounter(rho, nu, C, R):
    """The probability of collision of the straight-line encounter: the Gaussian with mean rho and
    covariance C, projected on the plane perpendicular to nu, over the disk of radius R."""
    z = unit(nu)
    k = min(range(3), key=lambda i: abs(z[i]))
    ek = [mpf(1) if i == k else mpf(0) for i in range(3)]
    g1 = unit(sub(ek, scale(dot(ek, z), z)))
    g2 = cross(z, g1)
    m1, m2 = dot(rho, g1), dot(rho, g2)
    c11 = dot(g1, cov_apply(C, g1))
    c12 = dot(g1, cov_apply(C, g2))
    c22 = dot(g2, cov_apply(C, g2))
    return pc2d(m1, m2, c11, c12, c22, mpf(R))


@dataclass
class Block:
    dt: float
    r1: list
    v1: list
    r2: list
    v2: list
    C: list
    R: float

    def values(self):
        return [self.dt] + self.r1 + self.v1 + self.r2 + self.v2 + self.C + [self.R]


@dataclass
class Case:
    name: str
    xs: list
    n: int
    expect: float | None = None
    verdicts: list | None = None
    invalid: bool = False
    derived: bool = False


def block_of(xs, j):
    b = 15 + 20 * j
    v = xs[b:b + 20]
    return Block(v[0], v[1:4], v[4:7], v[7:10], v[10:13], v[13:19], v[19])


def sample_pc(xs, j, dv, d):
    """The oracle's probability of conjunction j after the velocity change dv with the
    displacement d."""
    mu = xs[0]
    rb, vb = xs[1:4], xs[4:7]
    blk = block_of(xs, j)
    p1, u1 = kepler_state(mu, rb, [vb[i] + mpf(dv[i]) for i in range(3)], blk.dt)
    p0, u0 = kepler_state(mu, rb, vb, blk.dt)
    rho = [mpf(blk.r1[i]) - mpf(blk.r2[i]) + (p1[i] - p0[i]) + mpf(d[i]) for i in range(3)]
    nu = [mpf(blk.v1[i]) - mpf(blk.v2[i]) + (u1[i] - u0[i]) for i in range(3)]
    return pc_encounter(rho, nu, [mpf(c) for c in blk.C], blk.R)


def samples(xs, seed):
    """Velocity changes and displacements: box corners with padding corners, the center, and six
    random points."""
    box = [(xs[7], xs[8]), (xs[9], xs[10]), (xs[11], xs[12])]
    P = xs[13]
    out = []
    for k in range(8):
        dv = [box[i][(k >> i) & 1] for i in range(3)]
        d = [P if (k >> i) & 1 else -P for i in range(3)]
        out.append((dv, d))
    out.append(([(lo + hi) / 2 for lo, hi in box], [0.0, 0.0, 0.0]))
    rng = random.Random(seed)
    for _ in range(6):
        dv = [lo + (hi - lo) * rng.random() for lo, hi in box]
        d = [P * (2 * rng.random() - 1) for _ in range(3)]
        out.append((dv, d))
    return out


def climb(xs, j, start, value):
    """A compass search for a larger probability inside the box and the padding, from `start`."""
    box = [(xs[7], xs[8]), (xs[9], xs[10]), (xs[11], xs[12])]
    P = xs[13]
    lows = [lo for lo, _ in box] + [-P] * 3
    highs = [hi for _, hi in box] + [P] * 3
    point = list(start[0]) + list(start[1])
    steps = [(hi - lo) / 4 for lo, hi in zip(lows, highs)]
    for _ in range(5):
        moved = True
        while moved:
            moved = False
            for i in range(6):
                if steps[i] == 0:
                    continue
                for sign in (1, -1):
                    q = list(point)
                    q[i] = min(highs[i], max(lows[i], q[i] + sign * steps[i]))
                    if q == point:
                        continue
                    try:
                        v = sample_pc(xs, j, q[:3], q[3:])
                    except ValueError:
                        continue
                    if v > value:
                        point, value, moved = q, v, True
        steps = [s / 2 for s in steps]
    return value


def probabilities(xs, j):
    """The sampled probabilities of conjunction j, None where the oracle cannot evaluate one, and
    the largest probability that the compass search reaches."""
    pcs = []
    for dv, d in samples(xs, 1000 * j + 7):
        try:
            pcs.append(sample_pc(xs, j, dv, d))
        except ValueError:
            pcs.append(None)
    good = [(p, s) for p, s in zip(pcs, samples(xs, 1000 * j + 7)) if p is not None]
    top = None
    if good:
        best, start = max(good, key=lambda t: t[0])
        top = climb(xs, j, start, best)
    return pcs, top


# ### Cases


def rtn_cov(r, v, sr, st, sn, rho_rt=0.0):
    """A covariance in km² from standard deviations in the radial, transverse, and normal axes
    of the state (r, v), with the correlation rho_rt of the first two."""
    rh = unit([mpf(x) for x in r])
    nh = unit(cross([mpf(x) for x in r], [mpf(x) for x in v]))
    th = cross(nh, rh)
    axes = [rh, th, nh]
    S = [[sr * sr, rho_rt * sr * st, 0.0], [rho_rt * sr * st, st * st, 0.0], [0.0, 0.0, sn * sn]]
    C = [[mpf(0)] * 3 for _ in range(3)]
    for i in range(3):
        for k in range(3):
            C[i][k] = sum(mpf(S[a][b]) * axes[a][i] * axes[b][k] for a in range(3) for b in range(3))
    return [float(C[0][0]), float(C[0][1]), float(C[0][2]), float(C[1][1]), float(C[1][2]),
            float(C[2][2])]


def conjunction(rb, vb, dt, miss, angle_deg, speed=1.0, sig=(0.1, 1.0, 0.1), R=0.02,
                along=0.0, rho_rt=0.0, burn=None, along_nu=0.0):
    """A conjunction dt seconds after the burn.  The primary's nominal state is the two-body
    propagation of (rb, vb), moved by `along` km along its velocity.  The secondary's velocity is
    the primary's rotated by angle_deg about the radial axis and scaled by `speed`.  The relative
    position is the miss vector (radial, cross) in km in the plane perpendicular to the relative
    velocity, plus `along_nu` km along that velocity: relative to the nominal state, or, with
    `burn`, relative to the two-body state after that velocity change."""
    p, u = kepler_state(MU, rb, vb, dt)
    q, w = p, u
    if burn is not None:
        q, w = kepler_state(MU, rb, [vb[i] + mpf(burn[i]) for i in range(3)], dt)
    rh = unit(q)
    nh = unit(cross(q, w))
    th = cross(nh, rh)
    sp = norm(w) * speed
    a = mp.radians(angle_deg)
    v2 = add(scale(sp * mp.cos(a), th), scale(sp * mp.sin(a), nh))
    nu = sub(w, v2)
    z = unit(nu)
    xr = unit(sub(rh, scale(dot(rh, z), z)))
    yc = cross(z, xr)
    m = add(add(scale(miss[0], xr), scale(miss[1], yc)), scale(along_nu, z))
    r1 = add(p, scale(along, unit(u)))
    r2 = sub(add(r1, sub(q, p)), m)
    C = rtn_cov(p, u, *sig, rho_rt=rho_rt)
    return Block(float(dt), [float(x) for x in r1], [float(x) for x in u],
                 [float(x) for x in r2], [float(x) for x in v2], C, R)


def leo(alt=500.0, inc=51.6, ecc=0.0):
    """The state at perigee of an orbit of the given perigee altitude, inclination, and
    eccentricity."""
    R0 = 6378.137 + alt
    v = math.sqrt(MU * (1 + ecc) / R0)
    i = math.radians(inc)
    return [R0, 0.0, 0.0], [0.0, v * math.cos(i), v * math.sin(i)]


def header(rb, vb, box, P, T):
    return [MU] + list(rb) + list(vb) + list(box) + [P, T]


def along(vb, dv):
    t = [x / math.sqrt(sum(y * y for y in vb)) for x in vb]
    return [dv * x for x in t]


def along_box(vb, dv, half):
    """A box of half-width `half` in each axis about the velocity change of size dv along vb."""
    c = along(vb, dv)
    out = []
    for i in range(3):
        out += [c[i] - half, c[i] + half]
    return out


def cases():
    out = []
    rb, vb = leo()
    T = 1e-4
    near = conjunction(rb, vb, 2700.0, (0.03, 0.0), 90.0)
    far = conjunction(rb, vb, 5000.0, (1.0, 0.5), 60.0)

    def case(name, rb, vb, box, blocks, expect=None, verdicts=None, P=0.0, T=T, n=PANELS):
        xs = header(rb, vb, box, P, T)
        for b in blocks:
            xs += b.values()
        out.append(Case(name, xs, n, expect, verdicts))

    case("avoid 10 cm/s, box 1 mm/s", rb, vb, along_box(vb, 1e-4, 1e-6), [near], 0.0, [0])
    case("zero burn, high probability", rb, vb, [0.0] * 6, [near], 2.0, [1])
    case("two conjunctions accepted", rb, vb, along_box(vb, 1e-4, 1e-6), [near, far], 0.0, [0, 0])
    case("three conjunctions, one fails", rb, vb, along_box(vb, 1e-4, 1e-6),
         [near, far, conjunction(rb, vb, 2700.0, (-0.6, 0.0), 90.0)], 2.0, [0, 0, 1])
    rbq, vbq = leo(inc=0.0)
    case("equatorial primary", rbq, vbq, along_box(vbq, 1e-4, 1e-6),
         [conjunction(rbq, vbq, 2000.0, (0.02, 0.01), 75.0)], 0.0, [0])
    rbp, vbp = leo(inc=90.0)
    case("polar primary", rbp, vbp, along_box(vbp, 1e-4, 1e-6),
         [conjunction(rbp, vbp, 2000.0, (0.02, 0.01), 75.0)], 0.0, [0])
    rbc = [7000.0, 0.0, 0.0]
    vbc = [0.0, math.sqrt(MU / 7000.0), 0.0]
    case("circular equatorial primary", rbc, vbc, along_box(vbc, 1e-4, 1e-6),
         [conjunction(rbc, vbc, 3000.0, (0.0, 0.0), 90.0)], 0.0, [0])
    rbe, vbe = leo(alt=700.0, inc=30.0, ecc=0.3)
    case("eccentric primary e = 0.3", rbe, vbe, along_box(vbe, 1e-4, 1e-6),
         [conjunction(rbe, vbe, 4000.0, (0.03, 0.0), 80.0)], 0.0, [0])
    case("crossing at 1 km/s", rb, vb, along_box(vb, 1e-4, 1e-6),
         [conjunction(rb, vb, 2700.0, (0.03, 0.0), 7.6)], 0.0, [0])
    case("a day after the burn", rb, vb, along_box(vb, 2e-5, 1e-6),
         [conjunction(rb, vb, 86400.0, (0.03, 0.0), 90.0)], 0.0, [0])
    case("8,000 s after the burn, 10 km cross-track deviation", rb, vb, along_box(vb, 1e-4, 1e-6),
         [conjunction(rb, vb, 8000.0, (0.03, 0.0), 90.0, sig=(0.05, 0.2, 10.0))], 0.0, [0])
    case("a day after the burn, 10 km cross-track deviation", rb, vb, along_box(vb, 1e-4, 1e-6),
         [conjunction(rb, vb, 86400.0, (0.03, 0.0), 90.0, sig=(0.05, 0.2, 10.0))])
    case("box 1e-3 km/s", rb, vb, along_box(vb, 1e-4, 1e-3), [near])
    case("box 1e-5 km/s", rb, vb, along_box(vb, 1e-4, 1e-5), [near])
    case("padding 50 m", rb, vb, along_box(vb, 1e-4, 1e-6), [near], 0.0, [0], P=0.05)
    case("elongated covariance 100:1", rb, vb, along_box(vb, 1e-4, 1e-6),
         [conjunction(rb, vb, 2700.0, (0.03, 0.0), 90.0, sig=(0.02, 2.0, 0.02), rho_rt=0.5)])
    case("nominal moved 1 km along track", rb, vb, along_box(vb, 1e-4, 1e-6),
         [conjunction(rb, vb, 2700.0, (0.03, 0.0), 90.0, along=1.0)], 0.0, [0])
    case("16 panels", rb, vb, along_box(vb, 1e-4, 1e-6), [near], n=16)
    # Point boxes with the secondary placed near the trajectory after the burn, so that the
    # probability after the burn is high and an error in the propagation moves it far.
    def moved(r, v, t):
        p, u = kepler_state(MU, r, v, t)
        return [float(x) for x in p], [float(x) for x in u]

    rbm, vbm = moved(*leo(ecc=0.01), 1000.0)
    rbqm, vbqm = moved(*leo(inc=0.0, ecc=0.005), 1000.0)
    rbem, vbem = moved(rbe, vbe, 1500.0)
    for name, rbx, vbx, dt in [("LEO", rbm, vbm, 600.0), ("LEO", rbm, vbm, 8000.0),
                               ("LEO", rbm, vbm, 86400.0), ("equatorial", rbqm, vbqm, 8000.0),
                               ("circular", rbc, vbc, 8000.0), ("e = 0.3", rbem, vbem, 8000.0)]:
        burn = along(vbx, 1e-4)
        box = [burn[0], burn[0], burn[1], burn[1], burn[2], burn[2]]
        case(f"point burn, {name}, {dt:g} s", rbx, vbx, box,
             [conjunction(rbx, vbx, dt, (0.03, 0.0), 90.0, burn=burn)], 2.0, [1])
    burn = along(vbm, 1e-4)
    pbox = [burn[0], burn[0], burn[1], burn[1], burn[2], burn[2]]
    for speed_angle, label in [(90.0, "10 km/s"), (7.6, "1 km/s")]:
        case(f"point burn, 5 km along the relative velocity, {label}", rbm, vbm, pbox,
             [conjunction(rbm, vbm, 2700.0, (0.03, 0.0), speed_angle, burn=burn, along_nu=5.0)],
             2.0, [1])
    case("point burn, padding 100 m", rbm, vbm, pbox,
         [conjunction(rbm, vbm, 2700.0, (0.3, 0.0), 90.0, burn=burn, sig=(0.05, 0.5, 0.05))],
         P=0.1)
    ibox = [burn[0] - 2e-5, burn[0] + 2e-5, burn[1] - 2e-5, burn[1] + 2e-5, burn[2] - 2e-5,
            burn[2] + 2e-5]
    case("box about a burn that cancels the miss", rbm, vbm, ibox,
         [conjunction(rbm, vbm, 2700.0, (0.0, 0.0), 90.0, burn=burn, sig=(0.03, 0.3, 0.03))],
         2.0, [1])
    ind = near.values()
    z = unit(sub([mpf(x) for x in ind[4:7]], [mpf(x) for x in ind[10:13]]))
    lam = 2.0
    C = [mpf(c) for c in ind[13:19]]
    zz = [z[0] * z[0], z[0] * z[1], z[0] * z[2], z[1] * z[1], z[1] * z[2], z[2] * z[2]]
    ind[13:19] = [float(C[i] - lam * zz[i]) for i in range(6)]
    case("covariance indefinite along the relative velocity", rb, vb, along_box(vb, 1e-4, 1e-6),
         [Block(ind[0], ind[1:4], ind[4:7], ind[7:10], ind[10:13], ind[13:19], ind[19])])
    neg = near.values()
    neg[13:19] = [-0.01, 0.0, 0.0, -0.01, 0.0, -0.01]
    negb = Block(*([neg[0], neg[1:4], neg[4:7], neg[7:10], neg[10:13], neg[13:19], neg[19]]))
    case("covariance negative definite", rb, vb, along_box(vb, 1e-4, 1e-6), [negb], 3.0, [2])
    case("one rejected, one high", rb, vb, [0.0] * 6, [negb, near], 3.0, [2, 1])
    par = near.values()
    par[10:13] = [par[4] - par[1] / 700.0, par[5] - par[2] / 700.0, par[6] - par[3] / 700.0]
    parb = Block(par[0], par[1:4], par[4:7], par[7:10], par[10:13], par[13:19], par[19])
    case("relative velocity along r1", rb, vb, along_box(vb, 1e-4, 1e-6), [parb], 3.0, [2])
    case("unbound after the burn", rb, vb, along_box(vb, 4.0, 1e-6), [near], 3.0, [2])
    good = header(rb, vb, along_box(vb, 1e-4, 1e-6), 0.0, T) + near.values()

    def invalid(name, xs, n=PANELS):
        out.append(Case(name, xs, n, 1.0, invalid=True))

    invalid("short array", good[:34])
    invalid("one value too many", good + [0.0])
    invalid("NaN", good[:20] + [math.nan] + good[21:])
    invalid("infinite threshold", good[:14] + [math.inf] + good[15:])
    invalid("mu zero", [0.0] + good[1:])
    invalid("box unordered", good[:7] + [good[8], good[7]] + good[9:])
    invalid("negative padding", good[:13] + [-1e-3] + good[14:])
    invalid("dt zero", good[:15] + [0.0] + good[16:])
    invalid("radius zero", good[:34] + [0.0])
    invalid("panels zero", good, 0)
    invalid("panels above 2^20", good, 2 ** 20 + 1)
    invalid("65 conjunctions", header(rb, vb, along_box(vb, 1e-4, 1e-6), 0.0, T)
            + near.values() * 65)
    return out


def box_cases():
    """Intervals of the mean and the covariance for `pcBox`, and the radius."""
    return [
        ([-0.12, -0.09, 0.10, 0.14, 0.50, 0.51, -1e-5, 1e-5, 0.0099, 0.0101], 0.02),
        ([0.2, 0.25, -0.1, -0.05, 0.25, 0.26, 0.11, 0.13, 0.09, 0.095], 0.015),
        ([0.0, 0.001, 0.0, 0.001, 0.01, 0.0101, 0.0, 0.0, 0.01, 0.0101], 0.01),
        ([1.0, 1.0, 0.0, 0.0, 0.04, 0.041, 0.0, 0.0, 4.0, 4.1], 0.02),
    ]


# ### Running and checking


def run(module, queries):
    proc = subprocess.run(["node", str(Path(__file__).with_name("authorize.mjs")), module],
                          input="\n".join(json.dumps(q) for q in queries) + "\n",
                          capture_output=True, text=True, check=True)
    return [json.loads(line) for line in proc.stdout.splitlines() if line]


@dataclass
class Evidence:
    """The oracle's probabilities of each conjunction of a case."""
    pcs: list = field(default_factory=list)
    tops: list = field(default_factory=list)


def evidence(c):
    ev = Evidence()
    if c.invalid:
        return ev
    for j in range((len(c.xs) - 15) // 20):
        pcs, top = probabilities(c.xs, j)
        ev.pcs.append(pcs)
        ev.tops.append(top)
    return ev


def check_case(c, out, ev, tol=mpf(10) ** -20):
    """The failures of an output, and the ratios of hi to the largest sampled probability."""
    ys = [unbits(h) for h in out]
    fails = []
    if c.invalid:
        if ys != [1.0, 0.0]:
            fails.append(f"invalid input gave {ys[:2]}")
        return fails, []
    if ys[:1] == [1.0]:
        return ["status 1 for a valid input"], []
    K = (len(c.xs) - 15) // 20
    if len(ys) != 2 + 3 * K or ys[1] != K:
        return [f"output of size {len(ys)} for {K} conjunctions"], []
    status = ys[0]
    T = mpf(c.xs[14])
    verdicts = [ys[2 + 3 * j] for j in range(K)]
    want = 0.0 if all(v == 0.0 for v in verdicts) else 3.0 if 2.0 in verdicts else 2.0
    if status != want:
        fails.append(f"status {status} with verdicts {verdicts}")
    ratios = []
    for j in range(K):
        verdict, lo, hi = verdicts[j], mpf(ys[3 + 3 * j]), mpf(ys[4 + 3 * j])
        pcs = [p for p in ev.pcs[j] + [ev.tops[j]] if p is not None]
        if verdict not in (0.0, 1.0, 2.0):
            fails.append(f"conjunction {j}: verdict {verdict}")
        if verdict == 2.0 and (lo != 0 or hi != 0):
            fails.append(f"conjunction {j}: verdict 2 with ends {lo}, {hi}")
        if verdict in (0.0, 1.0):
            if (verdict == 0.0) != (hi < T):
                fails.append(f"conjunction {j}: verdict {verdict} with hi {mp.nstr(hi, 8)}")
            if len(pcs) < len(ev.pcs[j]) + 1:
                fails.append(f"conjunction {j}: accepted, but the oracle cannot evaluate a sample")
            for p in pcs:
                if not (lo - tol * abs(lo) <= p <= hi + tol * abs(hi)):
                    fails.append(f"conjunction {j}: sample {mp.nstr(p, 8)} outside "
                                 f"[{mp.nstr(lo, 8)}, {mp.nstr(hi, 8)}]")
            if pcs and max(pcs) > 0:
                ratios.append(hi / max(pcs))
        if status == 0.0 and any(p >= T for p in pcs):
            fails.append(f"conjunction {j}: status 0 with a sample at or above T")
        if any(p > 10 * T for p in pcs) and verdict == 0.0:
            fails.append(f"conjunction {j}: verdict 0 with a sample above 10 T")
    if c.expect is not None and status != c.expect:
        fails.append(f"status {status}, expected {c.expect}")
    if c.verdicts is not None and verdicts != [float(v) for v in c.verdicts]:
        fails.append(f"verdicts {verdicts}, expected {c.verdicts}")
    return fails, ratios


def mutations(c, out, ev):
    """Altered outputs that the checks must reject."""
    ys = [unbits(h) for h in out]
    alts = []
    if c.invalid:
        alts.append(("status 0 for an invalid input", [bits(0.0), bits(0.0)]))
        return alts
    alts.append(("status 1", [bits(1.0)] + out[1:]))
    K = (len(ys) - 2) // 3
    for j in range(K):
        pcs = [p for p in ev.pcs[j] + [ev.tops[j]] if p is not None]
        top = max(pcs) if pcs else None
        if ys[2 + 3 * j] != 2.0:
            if top is not None and top > 0:
                alt = list(out)
                alt[4 + 3 * j] = bits(float(top) * 0.5)
                alts.append((f"hi of {j} below the largest sample", alt))
            if top is not None and top > 10 * c.xs[14]:
                alt = list(out)
                alt[0] = bits(0.0)
                for k in range(K):
                    alt[2 + 3 * k] = bits(0.0)
                alts.append(("status 0 with a sample above 10 T", alt))
        elif top is not None and top > 0:
            alt = list(out)
            alt[2 + 3 * j] = bits(0.0)
            alts.append((f"verdict 0 for the rejected enclosure {j}", alt))
    if ys[0] == 3.0:
        alts.append(("status 2 for a rejection", [bits(2.0)] + out[1:]))
    return alts


def threshold_cases(c, out):
    """Cases whose threshold is an upper end hi, the next double above it, and a value between
    lo and hi, with the verdicts they fix."""
    ys = [unbits(h) for h in out]
    derived = []
    for j in range((len(ys) - 2) // 3):
        lo, hi = ys[3 + 3 * j], ys[4 + 3 * j]
        if ys[2 + 3 * j] == 2.0 or hi <= 0:
            continue
        others = [None] * ((len(ys) - 2) // 3)
        for t, v, label in [(hi, 1, "T = hi"), (math.nextafter(hi, math.inf), 0, "T above hi"),
                            ((lo + hi) / 2, 1, "T between lo and hi")]:
            if label == "T between lo and hi" and not lo < (lo + hi) / 2 < hi:
                continue
            xs = list(c.xs)
            xs[14] = t
            want = list(others)
            want[j] = v
            derived.append((Case(f"{c.name}, {label} of {j}", xs, c.n, derived=True), j, v))
        break
    return derived


def check_propagation():
    """The oracle's propagation against a Runge-Kutta integration of Newton's equation."""
    states = [leo(), leo(inc=0.0), leo(alt=700.0, inc=30.0, ecc=0.3),
              ([7000.0, 0.0, 0.0], [0.0, math.sqrt(MU / 7000.0), 0.0]),
              ([-4000.0, 5000.0, 2000.0], [-5.0, -3.0, 4.0])]
    worst = 0.0
    for r, v in states:
        p, u = kepler_state(MU, r, v, 5400.0)
        q, w = rk4(MU, r, v, 5400.0)
        worst = max(worst, max(abs(float(p[i]) - q[i]) for i in range(3)),
                    1000 * max(abs(float(u[i]) - w[i]) for i in range(3)))
    return worst


def check_quadrature():
    """The trapezoid rule over the rays against mpmath's two-dimensional quadrature."""
    worst = mpf(0)
    for args in [(0.3, -0.1, 0.01, 0.002, 0.04, 0.02), (0.0, 0.0, 1e-4, 0.0, 1e-2, 0.01),
                 (0.05, 0.08, 0.25, 0.1, 0.09, 0.015)]:
        a = [mpf(x) for x in args]
        p, q = pc2d(*a), pc2d_quad(*a)
        worst = max(worst, abs(p - q) / q)
    return worst


def main() -> int:
    module = sys.argv[1]
    mutate = "--mutate" in sys.argv[2:]
    worst = check_propagation()
    print(f"propagation against Runge-Kutta: largest difference {worst:.3e} km "
          "(velocity in m/s)", flush=True)
    failures = 0 if worst < 1e-6 else 1
    wq = check_quadrature()
    print(f"probability against mpmath's quadrature: largest relative difference "
          f"{mp.nstr(wq, 3)}", flush=True)
    failures += 0 if wq < 1e-15 else 1
    cs = cases()
    outs = run(module, [{"xs": [bits(x) for x in c.xs], "n": c.n} for c in cs])
    rejected = total = 0
    all_ratios = []
    derived = []
    for c, o in zip(cs, outs):
        ev = evidence(c)
        fails, ratios = check_case(c, o["out"], ev)
        all_ratios += ratios
        ys = [unbits(h) for h in o["out"]]
        failures += 1 if fails else 0
        K = (len(ys) - 2) // 3 if not c.invalid else 0
        detail = " ".join(f"[{ys[3 + 3 * j]:.4g}, {ys[4 + 3 * j]:.4g}] v{int(ys[2 + 3 * j])}"
                          f" max {float(ev.tops[j]) if ev.tops[j] is not None else 0:.4g}"
                          for j in range(K))
        ratio = f" ratio {float(max(ratios)):.3g}" if ratios else ""
        print(f"{'ok  ' if not fails else 'FAIL'} {c.name}: status {int(ys[0])} {detail}"
              f"{ratio} {o['ms']:.1f} ms", flush=True)
        for f in fails:
            print(f"      {f}")
        if mutate:
            for label, alt in mutations(c, o["out"], ev):
                total += 1
                if check_case(c, alt, ev)[0]:
                    rejected += 1
                else:
                    failures += 1
                    print(f"      mutation not detected: {label}")
        if not c.invalid and ys[0] != 1.0:
            for dc, j, v in threshold_cases(c, o["out"]):
                derived.append((dc, j, v, ev))
    douts = run(module, [{"xs": [bits(x) for x in dc.xs], "n": dc.n} for dc, _, _, _ in derived])
    for (dc, j, v, ev), o in zip(derived, douts):
        fails, _ = check_case(dc, o["out"], ev)
        ys = [unbits(h) for h in o["out"]]
        if ys[2 + 3 * j] != v:
            fails.append(f"verdict {ys[2 + 3 * j]}, expected {v}")
        failures += 1 if fails else 0
        print(f"{'ok  ' if not fails else 'FAIL'} {dc.name}: verdict {int(ys[2 + 3 * j])}")
        for f in fails:
            print(f"      {f}")
    queries = [{"box": [bits(x) for x in ends + [r]], "n": PANELS} for ends, r in box_cases()]
    for (ends, r), o in zip(box_cases(), run(module, queries)):
        lo, hi = mpf(unbits(o["lo"])), mpf(unbits(o["hi"]))
        fails = []
        if o["status"] != 0:
            fails.append(f"status {o['status']}")
        pts = [[ends[2 * i + ((k >> i) & 1)] for i in range(5)] for k in range(32)]
        pts.append([(ends[2 * i] + ends[2 * i + 1]) / 2 for i in range(5)])
        top = mpf(0)
        for m1, m2, c11, c12, c22 in pts:
            p = pc2d(mpf(m1), mpf(m2), mpf(c11), mpf(c12), mpf(c22), mpf(r))
            top = max(top, p)
            if o["status"] == 0 and not lo <= p <= hi:
                fails.append(f"sample {mp.nstr(p, 8)} outside [{mp.nstr(lo, 8)}, "
                             f"{mp.nstr(hi, 8)}]")
        failures += 1 if fails else 0
        print(f"{'ok  ' if not fails else 'FAIL'} pcBox {ends} r={r}: [{float(lo):.5g}, "
              f"{float(hi):.5g}], largest corner {float(top):.5g}")
        for f in fails:
            print(f"      {f}")
    if all_ratios:
        print(f"hi over the largest sample: {float(min(all_ratios)):.3g} to "
              f"{float(max(all_ratios)):.3g}")
    if mutate:
        print(f"mutations: {rejected} of {total} rejected")
    print(f"{failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
