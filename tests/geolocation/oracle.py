# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0", "numpy==2.5.3"]
# ///
"""Tests the geolocation module against dense sampling of its model.

The script builds the cases of `cases()`, runs the export `locate` of the WebAssembly module on
each with `tests/geolocation/locate.mjs` under Node, and checks every output against an oracle
written apart from the program.  The oracle evaluates the model of
`Demos/Geolocation/requirements.md`: the WGS 84 position, the distances, the range rates, the
time and frequency differences, and for the TEME frame the sidereal angle, its rate, and the
rotation into the Earth-fixed frame with its own matrices.  It evaluates in binary64 for dense
sampling and in mpmath at 30 digits for every sample within 1e-9 of a bound.

For each case it chooses parameters: the center of every interval, the parameter that produced
the measurements, random admissible parameters, and random corners of the intervals.  It finds
the solutions of the measurement equations in the region for each parameter by Gauss-Newton
iterations from a grid of starting points, and samples a grid around each solution out to where
the residuals exceed their bounds.  A sample is consistent for a parameter when every residual
lies within its bound.

For each output it checks the claims of the requirements:
  - status 3 and the output 3, 0, 0, 0 exactly for the invalid inputs;
  - for valid inputs, the status that the case states, an output of 4 + 7K values, labels 0 and
    1, at most C boxes, at most (N + 1) C box tests, N levels completed at status 2, fewer than N
    at status 1, at most N at status 0, and boxes with ordered ends inside the region;
  - every consistent sample, for every parameter, lies in a returned box;
  - every sample of a box labeled 1 (its corners, its center, and random points) fits the
    measurements for every parameter;
  - at status 0, every box labeled 0 has a binary64 size at most r or no binary64 middle strictly
    inside its longest side, and no two boxes overlap in more than their boundaries.
It also checks that the output follows the method: at status 0, the center of every box fits each
measurement for the central parameter within its bound plus eight times a bound of the
measurement's change over the box and the variation over the parameters.  With --mutate, the
script also alters correct outputs so that each alteration is wrong (it removes the box that
holds the most consistent samples, moves an end of a box past a consistent sample that no other
box holds, labels 1 a box that holds a sample that fails for the central parameter, reports
status 3, and returns the region as one box labeled 1) and requires the check to fail on each.
It prints one line per case, then a summary, and exits with status 1 on any failure.  With
--cost, it skips the checks and takes the time of each call as the median of 9 calls.

With --samples in place of MODULE, it prints the solutions and samples of each valid case.

Usage: uv run tests/geolocation/oracle.py MODULE [--mutate | --cost]
       uv run tests/geolocation/oracle.py --samples"""
import json
import math
import struct
import subprocess
import sys
from dataclasses import dataclass, field, replace
from pathlib import Path

import numpy as np
from mpmath import mp, mpf

mp.dps = 30

A = 6378.137
F = 1 / 298.257223563
E2 = F * (2 - F)
C = 299792.458
MU = 398600.4418
ROOT = Path(__file__).resolve().parents[2]


def bits(x: float) -> str:
    return struct.pack(">d", x).hex()


def unbits(h: str) -> float:
    return struct.unpack(">d", bytes.fromhex(h))[0]


# The model in binary64, vectorized over points.


def position(phi, lam, h):
    s = np.sin(phi)
    c = np.cos(phi)
    n = A / np.sqrt(1 - E2 * s * s)
    return np.stack([(n + h) * c * np.cos(lam), (n + h) * c * np.sin(lam),
                     (n * (1 - E2) + h) * s], axis=-1)


def residuals(x, case, par):
    """The residuals model - y of the measurements at the points x (N x 3) for the parameter."""
    s, u, f = par
    out = np.empty((x.shape[0], len(case.meas)))
    for k, (kind, i, j, y, _) in enumerate(case.meas):
        di = s[i] - x
        dj = s[j] - x
        ri = np.sqrt(np.sum(di * di, axis=1))
        rj = np.sqrt(np.sum(dj * dj, axis=1))
        if kind == 1:
            out[:, k] = (ri - rj) / C - y
        else:
            out[:, k] = -f * (np.sum(di * u[i], axis=1) / ri - np.sum(dj * u[j], axis=1) / rj) / C - y
    return out


# The model in mpmath at one point.


def position_mp(phi, lam, h):
    a = mpf("6378.137")
    f = 1 / mpf("298.257223563")
    e2 = f * (2 - f)
    s = mp.sin(phi)
    c = mp.cos(phi)
    n = a / mp.sqrt(1 - e2 * s * s)
    return [(n + h) * c * mp.cos(lam), (n + h) * c * mp.sin(lam), (n * (1 - e2) + h) * s]


def residuals_mp(pt, case, par):
    s, u, f = par
    x = position_mp(mpf(pt[0]), mpf(pt[1]), mpf(pt[2]))
    c = mpf("299792.458")
    out = []
    for kind, i, j, y, _ in case.meas:
        di = [mpf(s[i][q]) - x[q] for q in range(3)]
        dj = [mpf(s[j][q]) - x[q] for q in range(3)]
        ri = mp.sqrt(sum(d * d for d in di))
        rj = mp.sqrt(sum(d * d for d in dj))
        if kind == 1:
            out.append((ri - rj) / c - mpf(y))
        else:
            rri = sum(di[q] * mpf(u[i][q]) for q in range(3)) / ri
            rrj = sum(dj[q] * mpf(u[j][q]) for q in range(3)) / rj
            out.append(-mpf(f) * (rri - rrj) / c - mpf(y))
    return out


def fits(pts, case, par):
    """For each point, whether it fits the measurements for the parameter, with mpmath for the
    points within 1e-9 of a bound; and the number of samples that mpmath cannot decide."""
    if len(pts) == 0:
        return np.zeros(0, dtype=bool), 0
    x = position(pts[:, 0], pts[:, 1], pts[:, 2])
    r = residuals(x, case, par)
    eps = np.array([m[4] for m in case.meas])
    scale = np.array([abs(m[3]) + m[4] + 1e-12 for m in case.meas])
    margin = eps - np.abs(r)
    ok = np.all(margin >= 0, axis=1)
    near = np.any(np.abs(margin) < 1e-9 * scale, axis=1)
    undecided = 0
    for q in np.nonzero(near)[0]:
        rm = residuals_mp(pts[q], case, par)
        ms = [mpf(m[4]) - abs(v) for m, v in zip(case.meas, rm)]
        if any(abs(v) < mpf(10) ** -25 for v in ms):
            undecided += 1
        ok[q] = all(v >= 0 for v in ms)
    return ok, undecided


# Cases.


@dataclass
class Case:
    name: str
    status: int
    frame: int = 0
    n: int = 0
    rx: list = field(default_factory=list)  # (t lo, t hi, position lo/hi x3, velocity lo/hi x3)
    meas: list = field(default_factory=list)  # (kind, i, j, value, bound)
    freq: tuple = (406.0e6, 406.1e6)
    region: tuple = (0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
    res: float = 0.2
    levels: int = 60
    cap: int = 65536
    day: float = 0.0
    xp: tuple = (0.0, 0.0)
    yp: tuple = (0.0, 0.0)
    raw: list | None = None
    truth: tuple | None = None
    true_par: tuple | None = None

    def values(self):
        if self.raw is not None:
            return self.raw
        v = [1.0, float(self.frame), float(len(self.rx)), float(len(self.meas)), self.day,
             self.xp[0], self.xp[1], self.yp[0], self.yp[1], self.freq[0], self.freq[1],
             *self.region, self.res, float(self.levels), float(self.cap)]
        for r in self.rx:
            v.extend(r)
        for kind, i, j, y, e in self.meas:
            v.extend([float(kind), float(i), float(j), y, e])
        return v

    def valid(self):
        return self.raw is None


def unit(v):
    return v / np.linalg.norm(v)


def receiver_state(phi, lam, alt, heading, ascending=True):
    """A receiver above the geodetic point (phi, lam) at altitude alt over a sphere of radius A,
    moving on a circular orbit at the given heading in degrees, as an Earth-fixed position and a
    velocity relative to the rotating Earth."""
    rad = A + alt
    p = rad * np.array([math.cos(phi) * math.cos(lam), math.cos(phi) * math.sin(lam),
                        math.sin(phi)])
    east = np.array([-math.sin(lam), math.cos(lam), 0.0])
    north = np.array([-math.sin(phi) * math.cos(lam), -math.sin(phi) * math.sin(lam),
                      math.cos(phi)])
    hd = math.radians(heading)
    v = math.sqrt(MU / rad) * (math.cos(hd) * north + math.sin(hd) * east)
    w = np.array([0.0, 0.0, 7.2921158553e-5])
    return p, v - np.cross(w, p)


def rx_entry(p, v, dp=0.0, dv=0.0, t=(0.0, 0.0)):
    out = [t[0], t[1]]
    for q in range(3):
        out.extend([float(p[q] - dp), float(p[q] + dp)])
    for q in range(3):
        out.extend([float(v[q] - dv), float(v[q] + dv)])
    return out


def entry_par(case, rng=None, corner=False):
    """The parameter at the centers of the intervals, a random admissible one, or a random
    corner."""
    s = np.zeros((len(case.rx), 3))
    u = np.zeros((len(case.rx), 3))

    def pick(lo, hi):
        if rng is None:
            return (lo + hi) / 2
        if corner:
            return lo if rng.random() < 0.5 else hi
        return lo + (hi - lo) * rng.random()

    for i, r in enumerate(case.rx):
        for q in range(3):
            s[i, q] = pick(r[2 + 2 * q], r[3 + 2 * q])
            u[i, q] = pick(r[8 + 2 * q], r[9 + 2 * q])
    f = pick(case.freq[0], case.freq[1])
    return s, u, f


def model_values(case, x, par):
    saved = case.meas
    case.meas = [(k, i, j, 0.0, e) for k, i, j, _, e in saved]
    r = residuals(position(*[np.array([v]) for v in x]), case, par)[0]
    case.meas = saved
    return r


def scenario(name, status, emitter, sats, kinds, *, eps_t=1e-6, eps_f=0.5, dp=0.0, dv=0.0,
             region=None, res=0.2, levels=60, cap=65536, seed=1, offset=None, freq=None):
    """A case with the emitter at (phi, lam, h) in degrees and km, receivers above the given
    points (lat, lon, alt, heading in degrees), and measurements of the given kinds between
    receiver 0 and each other receiver."""
    rng = np.random.default_rng(seed)
    phi, lam, h = math.radians(emitter[0]), math.radians(emitter[1]), emitter[2]
    rx = []
    for la, lo, alt, hd in sats:
        p, v = receiver_state(math.radians(la), math.radians(lo), alt, hd)
        rx.append(rx_entry(p, v, dp, dv))
    case = Case(name, status, rx=rx, res=res, levels=levels, cap=cap)
    if freq is not None:
        case.freq = freq
    if region is None:
        d = math.radians(2.0)
        region = (phi - d, phi + d, lam - d, lam + d, h, h)
    case.region = region
    meas = []
    for kind in kinds:
        for j in range(1, len(sats)):
            meas.append((kind, 0, j, 0.0, eps_t if kind == 1 else eps_f))
    case.meas = meas
    true_par = entry_par(case, rng)
    vals = model_values(case, (phi, lam, h), true_par)
    shift = offset if offset is not None else [0.0] * len(meas)
    case.meas = [(k, i, j, float(v) + float(rng.uniform(-0.8, 0.8)) * e + o, e)
                 for (k, i, j, _, e), v, o in zip(meas, vals, shift)]
    case.truth = (phi, lam, h)
    case.true_par = true_par
    return case


MEO = [(10.0, 30.0, 23222.0, 20.0), (55.0, 10.0, 23222.0, 160.0), (40.0, 70.0, 23222.0, 300.0),
       (-15.0, 50.0, 23222.0, 80.0)]


def cases():
    out = []
    em = (35.0, 40.0, 0.0)
    out.append(scenario("meo4-tdoa", 0, em, MEO, [1]))
    out.append(scenario("meo4-fdoa", 0, em, MEO, [2], seed=2))
    out.append(scenario("meo4-both", 0, em, MEO, [1, 2], seed=3))
    leo = [(36.0, 41.0, 800.0, 10.0), (34.0, 39.5, 800.0, 10.0)]
    out.append(scenario("leo2-two-solutions", 0, em, leo, [1, 2], eps_t=2e-7, eps_f=1.0, seed=4,
                        region=(math.radians(25.0), math.radians(45.0), math.radians(30.0),
                                math.radians(50.0), 0.0, 0.0), res=0.2))
    d = math.radians(1.0)
    out.append(scenario("aircraft", 0, (35.0, 40.0, 9.0), MEO, [1, 2], seed=5,
                        region=(math.radians(35.0) - d, math.radians(35.0) + d,
                                math.radians(40.0) - d, math.radians(40.0) + d, 0.0, 12.0),
                        res=0.25))
    out.append(scenario("receiver-intervals", 0, em, MEO, [1, 2], dp=0.01, dv=1e-5, seed=6))
    out.append(scenario("whole-earth", 0, em, MEO, [1, 2], seed=7,
                        region=(-1.5707963267948968, 1.5707963267948968, -3.1415926535897936,
                                3.1415926535897936, 0.0, 0.0), res=1.0))
    out.append(scenario("region-without-emitter", 0, em, MEO, [1, 2], seed=8,
                        region=(math.radians(10.0), math.radians(12.0), math.radians(10.0),
                                math.radians(12.0), 0.0, 0.0)))
    out.append(scenario("inconsistent", 0, em, MEO, [1, 2], seed=9,
                        offset=[5e-5, 0, 0, 0, 0, 0]))
    out.append(scenario("near-pole", 0, (89.9, 120.0, 0.0),
                        [(70.0, 100.0, 23222.0, 0.0), (75.0, -60.0, 23222.0, 90.0),
                         (60.0, 170.0, 23222.0, 200.0), (65.0, 30.0, 23222.0, 300.0)],
                        [1, 2], seed=10,
                        region=(math.radians(88.0), 1.5707963267948968, math.radians(0.0),
                                math.radians(360.0), 0.0, 0.0), res=0.2))
    out.append(scenario("antimeridian", 0, (-20.0, 179.99, 0.0),
                        [(-10.0, 160.0, 23222.0, 30.0), (-45.0, 175.0, 23222.0, 150.0),
                         (5.0, -170.0, 23222.0, 270.0), (-30.0, -150.0, 23222.0, 10.0)],
                        [1, 2], seed=11,
                        region=(math.radians(-21.0), math.radians(-19.0), 3.0, 3.3, 0.0, 0.0)))
    out.append(scenario("levels-zero", 2, em, MEO, [1, 2], seed=12, levels=0))
    out.append(scenario("levels-ten", 2, em, MEO, [1, 2], seed=13, levels=10))
    out.append(scenario("cap-four", 1, em, MEO, [1, 2], seed=14, cap=4))
    out.append(scenario("wide-bounds", 0, em, MEO, [1, 2], eps_t=2e-5, eps_f=5.0, seed=15,
                        res=0.5))
    good = cases_valid_template(out[2])
    out.extend(invalid_cases(good))
    return out


def cases_valid_template(case):
    return case.values()


def invalid_cases(v):
    """Inputs that break each requirement of the interface."""
    bad = []

    def alter(name, idx, value):
        w = list(v)
        w[idx] = value
        bad.append(Case(name, 3, raw=w))

    n = int(v[2])
    m = int(v[3])
    base = 20 + 14 * n
    alter("version", 0, 2.0)
    alter("frame-two", 1, 2.0)
    alter("receivers-one", 2, 1.0)
    alter("receivers-fraction", 2, 4.5)
    alter("measurements-zero", 3, 0.0)
    alter("day-fraction", 4, 0.5)
    alter("polar-unordered", 5, 1.0)
    alter("frequency-zero", 9, 0.0)
    alter("frequency-unordered", 10, 1.0)
    alter("latitude-unordered", 12, -2.0)
    alter("longitude-unordered", 14, -4.0)
    alter("height-unordered", 16, -1.0)
    alter("resolution-zero", 17, 0.0)
    alter("levels-high", 18, 129.0)
    alter("cap-zero", 19, 0.0)
    alter("cap-high", 19, 65537.0)
    alter("receiver-unordered", 23, v[22] - 1.0)
    alter("kind-three", base, 3.0)
    alter("index-high", base + 1, float(n))
    alter("index-equal", base + 2, 0.0)
    alter("bound-negative", base + 4, -1.0)
    alter("nan", 25, float("nan"))
    alter("infinite", base + 3, float("inf"))
    bad.append(Case("short", 3, raw=list(v)[:-1]))
    bad.append(Case("long", 3, raw=list(v) + [0.0]))
    bad.append(Case("empty", 3, raw=[]))
    _ = m
    return bad


# Running the module.


def run(module, inputs, repeat=1):
    text = "".join(json.dumps([bits(x) for x in v]) + "\n" for v in inputs)
    proc = subprocess.run(["node", str(ROOT / "tests/geolocation/locate.mjs"), module, str(repeat)],
                          input=text, capture_output=True, text=True, check=True)
    outs = []
    for line in proc.stdout.splitlines():
        o = json.loads(line)
        outs.append(([unbits(h) for h in o["out"]], o["ms"]))
    return outs


# Solutions and samples.


def unknowns(case):
    return 3 if case.region[4] < case.region[5] else 2


def point_of(case, v):
    if len(v) == 3:
        return np.array(v)
    return np.array([v[0], v[1], case.region[4]])


def normalized(case, par, v):
    eps = np.array([m[4] for m in case.meas])
    p = point_of(case, v)
    return residuals(position(p[0:1], p[1:2], p[2:3]), case, par)[0] / eps


def gauss_newton(case, par, v0, iters=60):
    v = np.array(v0, dtype=float)
    steps = np.array([1e-7, 1e-7, 1e-4])[: len(v)]
    lam = 1e-3
    g = normalized(case, par, v)
    for _ in range(iters):
        jac = np.empty((len(g), len(v)))
        for d in range(len(v)):
            w = v.copy()
            w[d] += steps[d]
            jac[:, d] = (normalized(case, par, w) - g) / steps[d]
        lhs = jac.T @ jac
        rhs = jac.T @ g
        try:
            dv = np.linalg.solve(lhs + lam * np.diag(np.diag(lhs) + 1e-30), -rhs)
        except np.linalg.LinAlgError:
            break
        w = v + dv
        g2 = normalized(case, par, w)
        if np.sum(g2 * g2) < np.sum(g * g):
            v, g = w, g2
            lam = max(lam / 10, 1e-12)
            if np.max(np.abs(dv[:2])) < 1e-13:
                break
        else:
            lam *= 10
            if lam > 1e12:
                break
    return v, float(np.max(np.abs(g)))


def seeds(case, par):
    """Starting points: the local minima of the sum of squared normalized residuals on a grid
    over the region."""
    r = case.region
    nphi = 181 if r[1] - r[0] > 0.5 else 61
    nlam = 361 if r[3] - r[2] > 0.5 else 61
    phis = np.linspace(r[0], r[1], nphi)
    lams = np.linspace(r[2], r[3], nlam)
    hs = [0.5 * (r[4] + r[5])]
    pp, ll = np.meshgrid(phis, lams, indexing="ij")
    eps = np.array([m[4] for m in case.meas])
    out = []
    for h in hs:
        x = position(pp.ravel(), ll.ravel(), np.full(pp.size, h))
        g = residuals(x, case, par) / eps
        s = np.sum(np.log1p(g * g), axis=1).reshape(pp.shape)
        for a in range(nphi):
            for b in range(nlam):
                nb = s[max(a - 1, 0):a + 2, max(b - 1, 0):b + 2]
                if s[a, b] <= nb.min():
                    v = [phis[a], lams[b]] + ([h] if unknowns(case) == 3 else [])
                    out.append(v)
    return out


def solutions(case, par, starts):
    found = []
    for v0 in starts:
        v, worst = gauss_newton(case, par, v0)
        r = case.region
        inside = r[0] - 1e-9 <= v[0] <= r[1] + 1e-9 and r[2] - 1e-9 <= v[1] <= r[3] + 1e-9
        if len(v) == 3:
            inside = inside and r[4] - 1e-6 <= v[2] <= r[5] + 1e-6
        if worst <= 1.5 and inside:
            p = position(*[np.array([q]) for q in point_of(case, v)])[0]
            if all(np.linalg.norm(p - position(*[np.array([q]) for q in point_of(case, w)])[0])
                   > 0.05 for w in found):
                found.append(v)
    return found


def grid_around(case, par, v):
    """Samples on a grid around the solution v, widened until no consistent sample lies on the
    grid's border."""
    eps = np.array([m[4] for m in case.meas])
    g = normalized(case, par, v)
    steps = np.array([1e-7, 1e-7, 1e-4])[: len(v)]
    jac = np.empty((len(g), len(v)))
    for d in range(len(v)):
        w = v.copy()
        w[d] += steps[d]
        jac[:, d] = (normalized(case, par, w) - g) / steps[d]
    width = 1.5 * np.sum(np.abs(np.linalg.pinv(jac)), axis=1)
    width = np.maximum(width, [1e-6, 1e-6, 1e-3][: len(v)])
    r = case.region
    count = 81 if len(v) == 2 else 21
    for _ in range(8):
        axes = []
        for d in range(len(v)):
            lo = max(v[d] - width[d], r[2 * d])
            hi = min(v[d] + width[d], r[2 * d + 1])
            axes.append(np.linspace(lo, hi, count))
        mesh = np.meshgrid(*axes, indexing="ij")
        pts = np.stack([m.ravel() for m in mesh], axis=1)
        if len(v) == 2:
            pts = np.column_stack([pts, np.full(len(pts), r[4])])
        ok, und = fits(pts, case, par)
        okm = ok.reshape(mesh[0].shape)
        border = False
        for d in range(len(v)):
            lo_edge = np.take(okm, 0, axis=d).any() and axes[d][0] > r[2 * d]
            hi_edge = np.take(okm, -1, axis=d).any() and axes[d][-1] < r[2 * d + 1]
            if lo_edge or hi_edge:
                border = True
        if not border:
            return pts, ok, und
        width = width * 2
    return pts, ok, und


def parameters(case, rng):
    pars = [("center", entry_par(case))]
    if case.true_par is not None:
        pars.append(("true", case.true_par))
    for q in range(3):
        pars.append((f"random{q}", entry_par(case, rng)))
    for q in range(2):
        pars.append((f"corner{q}", entry_par(case, rng, corner=True)))
    return pars


@dataclass
class Prepared:
    pars: list
    samples: list  # (parameter index, points, consistent mask)
    undecided: int
    solutions: int


def prepare(case):
    rng = np.random.default_rng(99)
    pars = parameters(case, rng)
    starts = seeds(case, pars[0][1])
    if case.truth is not None:
        starts.append(list(case.truth[:unknowns(case)]))
    base = solutions(case, pars[0][1], starts)
    samples = []
    und = 0
    nsol = len(base)
    for q, (_, par) in enumerate(pars):
        sols = base if q == 0 else solutions(case, par, [list(v) for v in base])
        for v in sols:
            pts, ok, u = grid_around(case, par, np.array(v))
            samples.append((q, pts, ok))
            und += u
    return Prepared(pars, samples, und, nsol)


# Checks.


def boxes_of(out):
    k = int(out[1])
    b = np.array(out[4:4 + 7 * k], dtype=float).reshape(k, 7) if k else np.zeros((0, 7))
    return b


def covered(boxes, pts):
    if len(pts) == 0:
        return np.zeros(0, dtype=bool)
    if len(boxes) == 0:
        return np.zeros(len(pts), dtype=bool)
    res = np.zeros(len(pts), dtype=bool)
    for start in range(0, len(boxes), 2000):
        b = boxes[start:start + 2000]
        inside = ((b[None, :, 0] <= pts[:, None, 0]) & (pts[:, None, 0] <= b[None, :, 1]) &
                  (b[None, :, 2] <= pts[:, None, 1]) & (pts[:, None, 1] <= b[None, :, 3]) &
                  (b[None, :, 4] <= pts[:, None, 2]) & (pts[:, None, 2] <= b[None, :, 5]))
        res |= inside.any(axis=1)
    return res


def size_and_side(b):
    sa = 6378.137 * (b[1] - b[0])
    sb = 6378.137 * (b[3] - b[2])
    sc = b[5] - b[4]
    if sb <= sa and sc <= sa:
        return 0, sa
    if sc <= sb:
        return 1, sb
    return 2, sc


def unsplittable(b, r):
    side, size = size_and_side(b)
    lo, hi = b[2 * side], b[2 * side + 1]
    md = lo + (hi - lo) * 0.5
    return not (r < size and math.isfinite(md) and lo < md < hi)


def overlaps(boxes):
    order = np.argsort(boxes[:, 0], kind="stable")
    b = boxes[order]
    for a in range(len(b)):
        for c in range(a + 1, len(b)):
            if b[c, 0] >= b[a, 1]:
                break
            if (min(b[a, 1], b[c, 1]) > max(b[a, 0], b[c, 0]) and
                    min(b[a, 3], b[c, 3]) > max(b[a, 2], b[c, 2]) and
                    (min(b[a, 5], b[c, 5]) > max(b[a, 4], b[c, 4]) or
                     (b[a, 4] == b[a, 5] and b[c, 4] == b[c, 5] and b[a, 4] == b[c, 4]))):
                return True
    return False


def box_radius(b):
    corners = np.array([[p, l, h] for p in b[0:2] for l in b[2:4] for h in b[4:6]])
    c = np.array([[0.5 * (b[0] + b[1]), 0.5 * (b[2] + b[3]), 0.5 * (b[4] + b[5])]])
    pc = position(c[:, 0], c[:, 1], c[:, 2])[0]
    pk = position(corners[:, 0], corners[:, 1], corners[:, 2])
    return float(np.max(np.linalg.norm(pk - pc, axis=1))), c


def gradient_bounds(case, par, x):
    """Bounds of the change of each measurement per km of emitter displacement near x."""
    s, u, f = par
    out = []
    for kind, i, j, _, _ in case.meas:
        ri = np.linalg.norm(s[i] - x)
        rj = np.linalg.norm(s[j] - x)
        if kind == 1:
            out.append(2.0 / C)
        else:
            out.append(abs(f) / C * (2 * np.linalg.norm(u[i]) / ri + 2 * np.linalg.norm(u[j]) / rj))
    return np.array(out)


def check(case, out, prep):
    """The failures of an output, as a list of strings."""
    errs = []
    v = case.values()
    if not case.valid():
        if [x for x in out] != [3.0, 0.0, 0.0, 0.0]:
            errs.append(f"invalid input gave {out[:4]}")
        return errs
    if len(out) < 4:
        return ["output shorter than 4"]
    status, k, tests, lev = out[0], out[1], out[2], out[3]
    if status != case.status:
        errs.append(f"status {status}, expected {case.status}")
    if k != int(k) or len(out) != 4 + 7 * int(k):
        errs.append(f"length {len(out)} for K = {k}")
        return errs
    if k > case.cap:
        errs.append(f"{k} boxes above the cap {case.cap}")
    if tests > (case.levels + 1) * case.cap:
        errs.append(f"{tests} tests above (N + 1) C")
    if status == 2 and lev != case.levels:
        errs.append(f"status 2 with {lev} levels")
    if status == 1 and lev >= case.levels:
        errs.append(f"status 1 with {lev} levels")
    if status == 0 and lev > case.levels:
        errs.append(f"status 0 with {lev} levels")
    boxes = boxes_of(out)
    reg = case.region
    for q, b in enumerate(boxes):
        if b[6] not in (0.0, 1.0):
            errs.append(f"box {q} label {b[6]}")
        if not (reg[0] <= b[0] <= b[1] <= reg[1] and reg[2] <= b[2] <= b[3] <= reg[3] and
                reg[4] <= b[4] <= b[5] <= reg[5]):
            errs.append(f"box {q} outside the region or unordered")
    if errs:
        return errs
    for q, pts, ok in prep.samples:
        cons = pts[ok]
        miss = ~covered(boxes, cons)
        if miss.any():
            errs.append(f"{int(miss.sum())} consistent samples of parameter {prep.pars[q][0]} "
                        f"outside every box, e.g. {cons[miss][0].tolist()}")
    rng = np.random.default_rng(7)
    inner = boxes[boxes[:, 6] == 1.0]
    for b in inner[:400]:
        corners = np.array([[p, l, h] for p in b[0:2] for l in b[2:4] for h in b[4:6]])
        rnd = np.column_stack([b[0] + (b[1] - b[0]) * rng.random(6), b[2] + (b[3] - b[2]) *
                               rng.random(6), b[4] + (b[5] - b[4]) * rng.random(6)])
        center = np.array([[0.5 * (b[0] + b[1]), 0.5 * (b[2] + b[3]), 0.5 * (b[4] + b[5])]])
        pts = np.vstack([corners, rnd, center])
        for name, par in prep.pars:
            ok, _ = fits(pts, case, par)
            if not ok.all():
                errs.append(f"box labeled 1 {b[:6].tolist()} holds a point that does not fit "
                            f"for parameter {name}")
                break
        if len(errs) > 5:
            break
    if status == 0 and len(boxes):
        for b in boxes:
            if b[6] == 0.0 and not unsplittable(b, case.res):
                errs.append(f"status 0 with a splittable box labeled 0: {b[:6].tolist()}")
                break
        if len(boxes) <= 20000 and overlaps(boxes):
            errs.append("two boxes overlap")
        center_par = prep.pars[0][1]
        variation = parameter_variation(case, prep, boxes)
        eps = np.array([m[4] for m in case.meas])
        for b in boxes:
            rad, c = box_radius(b)
            x = position(c[:, 0], c[:, 1], c[:, 2])
            r = residuals(x, case, center_par)[0]
            g = gradient_bounds(case, center_par, x[0])
            if np.any(np.abs(r) > eps + 8 * (g * rad + variation)):
                errs.append(f"status 0 with a box far from the consistent set: {b[:6].tolist()}")
                break
    return errs


def parameter_variation(case, prep, boxes):
    centers = np.array([[0.5 * (b[0] + b[1]), 0.5 * (b[2] + b[3]), 0.5 * (b[4] + b[5])]
                        for b in boxes[:50]])
    if len(centers) == 0:
        return np.zeros(len(case.meas))
    x = position(centers[:, 0], centers[:, 1], centers[:, 2])
    base = residuals(x, case, prep.pars[0][1])
    worst = np.zeros(len(case.meas))
    for _, par in prep.pars[1:]:
        worst = np.maximum(worst, np.max(np.abs(residuals(x, case, par) - base), axis=0))
    return worst


# Mutations.


def mutations(case, out, prep):
    """Wrong outputs made from a correct one."""
    muts = []
    boxes = boxes_of(out)
    head = list(out[:4])

    def pack(bs, status=None):
        h = list(head)
        if status is not None:
            h[0] = status
        h[1] = float(len(bs))
        return h + [float(x) for x in np.array(bs).ravel()]

    allcons = [pts[ok] for _, pts, ok in prep.samples]
    cons = np.vstack(allcons) if allcons else np.zeros((0, 3))
    if len(boxes) and len(cons):
        counts = [int(covered(boxes[q:q + 1], cons).sum()) for q in range(len(boxes))]
        q = int(np.argmax(counts))
        if counts[q] > 0:
            muts.append(("remove the fullest box", pack(np.delete(boxes, q, axis=0))))
        for q in range(len(boxes)):
            inq = covered(boxes[q:q + 1], cons)
            if not inq.any():
                continue
            others = covered(np.delete(boxes, q, axis=0), cons)
            only = cons[inq & ~others]
            if len(only):
                b = boxes.copy()
                b[q, 0] = np.nextafter(only[0][0], math.inf)
                if b[q, 0] > b[q, 1]:
                    b[q, 1] = b[q, 0]
                muts.append(("move an end past a consistent sample", pack(b)))
                break
    if len(boxes):
        par = prep.pars[0][1]
        for q, b in enumerate(boxes):
            if b[6] != 0.0:
                continue
            corners = np.array([[p, l, h] for p in b[0:2] for l in b[2:4] for h in b[4:6]])
            ok, _ = fits(corners, case, par)
            if not ok.all():
                bb = boxes.copy()
                bb[q, 6] = 1.0
                muts.append(("label 1 a box with a failing point", pack(bb)))
                break
    muts.append(("status 3", pack(boxes, 3.0)))
    reg = case.region
    muts.append(("the region labeled 1", pack(np.array([[*reg, 1.0]]))))
    return muts


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return 2
    module = args[0]
    mutate = "--mutate" in args
    cost = "--cost" in args
    cs = cases()
    if module == "--samples":
        for c in cs:
            if c.valid():
                prep = prepare(c)
                ns = sum(len(p) for _, p, _ in prep.samples)
                nc = sum(int(ok.sum()) for _, _, ok in prep.samples)
                print(f"{c.name}: {prep.solutions} solutions, {nc} of {ns} samples consistent, "
                      f"{prep.undecided} undecided")
        return 0
    if cost:
        outs = run(module, [c.values() for c in cs if c.valid()], repeat=9)
        for c, (out, ms) in zip([c for c in cs if c.valid()], outs):
            print(f"{c.name}: status {out[0]:.0f}, {out[1]:.0f} boxes, {out[2]:.0f} tests, "
                  f"{out[3]:.0f} levels, {ms:.2f} ms")
        return 0
    outs = run(module, [c.values() for c in cs])
    failed = 0
    mutation_total = 0
    mutation_caught = 0
    total_samples = 0
    total_consistent = 0
    total_undecided = 0
    for c, (out, ms) in zip(cs, outs):
        prep = prepare(c) if c.valid() else Prepared([], [], 0, 0)
        ns = sum(len(p) for _, p, _ in prep.samples)
        nc = sum(int(ok.sum()) for _, _, ok in prep.samples)
        total_samples += ns
        total_consistent += nc
        total_undecided += prep.undecided
        errs = check(c, out, prep)
        line = (f"{c.name}: status {out[0]:.0f}, {out[1]:.0f} boxes, {out[2]:.0f} tests, "
                f"{out[3]:.0f} levels" if len(out) >= 4 else f"{c.name}: short output")
        if c.valid():
            line += (f", {prep.solutions} solutions, {nc} of {ns} samples consistent, "
                     f"{ms:.1f} ms")
        if errs:
            failed += 1
            print(line + ": FAIL")
            for e in errs[:5]:
                print("    " + e)
        else:
            print(line + ": ok")
        if mutate and c.valid() and not errs:
            for name, m in mutations(c, out, prep):
                mutation_total += 1
                if check(c, m, prep):
                    mutation_caught += 1
                else:
                    print(f"    mutation not caught: {name}")
    print(f"{len(cs) - failed} of {len(cs)} cases pass; {total_consistent} consistent samples of "
          f"{total_samples}; {total_undecided} undecided")
    if mutate:
        print(f"{mutation_caught} of {mutation_total} mutations caught")
    return 1 if failed or (mutate and mutation_caught != mutation_total) else 0


if __name__ == "__main__":
    sys.exit(main())
