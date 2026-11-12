# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0", "numpy==2.5.3"]
# ///
"""Tests the geolocation module against dense sampling of its model.

The script builds the cases of `cases()`, runs the export `locate` of the WebAssembly module on
each with `tests/geolocation/locate.mjs` under Node, and checks every output against an oracle
written apart from the program.  The oracle evaluates the model of
`Demos/Geolocation/requirements.md` with its own formulas: the WGS 84 position, the distances,
the range rates, and the time and frequency differences, in binary64 for dense sampling and in
mpmath at 30 digits for every sample within 1e-9 of a bound.  For the TEME frame it computes the
sidereal angle from the GMST 1982 polynomial in the Julian date, rotates with its own matrices,
and takes the Earth-fixed velocity as the numerical derivative, in mpmath, of the rotated
position along the receiver's straight-line motion.

A parameter is a choice of each receiver's state, time, and polar motion in their intervals and
of the carrier frequency.  For each case the oracle takes the center of every interval, the
parameter that produced the measurements, three random parameters, and two random corners of the
intervals.  For each parameter it covers the region with cells by a Lipschitz subdivision: a cell
is dropped when some measurement's residual at its center exceeds the bound by more than a bound
of the residual's change over the cell, and the cells are split until their size is at most the
case's resolution or the smaller cell size that the case states.  It samples a grid of 4 points
along each side of every remaining cell, at fractions that no bisection reaches, and a sample is
consistent for the parameter when every residual lies within its bound.

For each output it checks the claims of the requirements:
  - status 3 and the output 3, 0, 0, 0 exactly for the invalid inputs;
  - for valid inputs, the status that the case states, an output of 4 + 7K values, labels 0 and
    1, at most C boxes, at most (N + 1) C box tests, N levels completed at status 2, fewer than N
    at status 1, at most N at status 0, and boxes with ordered ends inside the region;
  - the number of boxes, the boxes labeled 1, and boxes at both ends of the longitude where the
    case states them;
  - every consistent sample, for every parameter, lies in a returned box;
  - every sample of a box labeled 1 (its corners, its center, and random points) fits the
    measurements for every parameter;
  - at status 0, every box labeled 0 has a binary64 size at most r or no computed middle strictly
    inside its longest side, and no two boxes overlap in more than their boundaries.
It also checks that the output follows the method: at every status, the center of every box fits
each measurement for the central parameter within its bound plus eight times the sum of bounds of
the measurement's change over the box and over every admissible parameter.  With
--mutate, it alters correct outputs so that each alteration is wrong (it removes the box that
holds the most consistent samples, moves an end of a box past a consistent sample that no other
box holds, labels 1 a box with a corner that fails for the central parameter, adds a small box at a
corner of the region far from the consistent set, reports status 3,
and returns the region as one box labeled 1) and requires the check to fail on each.  It prints
one line per case, then a summary, and exits with status 1 on any failure.  With --cost, it skips
the checks and takes the time of each call as the median of 9 calls.  With --samples in place of
MODULE, it prints the cells and samples of each valid case.

Usage: uv run tests/geolocation/oracle.py MODULE [--mutate | --cost]
       uv run tests/geolocation/oracle.py --samples"""
import json
import math
import struct
import subprocess
import sys
from dataclasses import dataclass, field
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


@dataclass
class Par:
    """A parameter's Earth-fixed states in binary64 and in mpmath, and its carrier frequency."""
    s: np.ndarray
    u: np.ndarray
    f: float
    smp: list
    ump: list


def residuals(x, case, par):
    """The residuals model - y of the measurements at the points x (N x 3)."""
    out = np.empty((x.shape[0], len(case.meas)))
    for k, (kind, i, j, y, _) in enumerate(case.meas):
        di = par.s[i] - x
        dj = par.s[j] - x
        ri = np.sqrt(np.sum(di * di, axis=1))
        rj = np.sqrt(np.sum(dj * dj, axis=1))
        if kind == 1:
            out[:, k] = (ri - rj) / C - y
        else:
            out[:, k] = (-par.f * (np.sum(di * par.u[i], axis=1) / ri -
                                   np.sum(dj * par.u[j], axis=1) / rj) / C - y)
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
    x = position_mp(mpf(pt[0]), mpf(pt[1]), mpf(pt[2]))
    c = mpf("299792.458")
    out = []
    for kind, i, j, y, _ in case.meas:
        di = [par.smp[i][q] - x[q] for q in range(3)]
        dj = [par.smp[j][q] - x[q] for q in range(3)]
        ri = mp.sqrt(sum(d * d for d in di))
        rj = mp.sqrt(sum(d * d for d in dj))
        if kind == 1:
            out.append((ri - rj) / c - mpf(y))
        else:
            rri = sum(di[q] * par.ump[i][q] for q in range(3)) / ri
            rrj = sum(dj[q] * par.ump[j][q] for q in range(3)) / rj
            out.append(-mpf(par.f) * (rri - rrj) / c - mpf(y))
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


# The TEME frame.


def gmst_mp(d, t):
    """GMST 1982 in radians at the day d and the seconds t of UT1, from the polynomial in the
    Julian date."""
    jd = mpf("2400000.5") + mpf(d) + mpf(t) / 86400
    tt = (jd - 2451545) / 36525
    return (2 * mp.pi / 86400) * (mpf("67310.54841") + (876600 * 3600 + mpf("8640184.812866")) *
                                  tt + mpf("0.093104") * tt ** 2 - mpf("6.2e-6") * tt ** 3)


def rot(axis, a, v):
    """SOFA's rotation of the frame by a about the axis."""
    c, s = mp.cos(a), mp.sin(a)
    x, y, z = v
    if axis == 1:
        return [x, c * y + s * z, -s * y + c * z]
    if axis == 2:
        return [c * x - s * z, y, s * x + c * z]
    return [c * x + s * y, -s * x + c * y, z]


def teme_to_earth(d, t, xp, yp, r, v):
    """The Earth-fixed position and velocity of a TEME state at the seconds t of UT1, the
    velocity as the derivative along r + v (t' - t)."""
    arc = mp.pi / 648000

    def at(tp):
        pos = [r[q] + v[q] * (tp - t) for q in range(3)]
        return rot(1, -yp * arc, rot(2, -xp * arc, rot(3, gmst_mp(d, tp), pos)))

    s = at(t)
    u = [mp.diff(lambda tp: at(tp)[q], t) for q in range(3)]
    return s, u


# Cases.


@dataclass
class Case:
    name: str
    status: int
    frame: int = 0
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
    pick_true: dict | None = None
    count: int | None = None
    label1: int | None = None
    ends: bool = False
    cell: float | None = None

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


def pick(lo, hi, rng, corner):
    if rng is None:
        return lo + (hi - lo) / 2 if lo != hi else lo
    if corner:
        return lo if rng.random() < 0.5 else hi
    return lo + (hi - lo) * rng.random()


def choose(case, rng=None, corner=False):
    """A parameter's choice: each receiver's time, position, and velocity, the polar motion, and
    the frequency, at the centers, at random, or at random corners."""
    rx = []
    for r in case.rx:
        rx.append([pick(r[2 * q], r[2 * q + 1], rng, corner) for q in range(7)])
    return {"rx": rx, "xp": pick(*case.xp, rng, corner), "yp": pick(*case.yp, rng, corner),
            "f": pick(*case.freq, rng, corner)}


def par_of(case, ch):
    """The Earth-fixed parameter of a choice."""
    smp, ump = [], []
    for r in ch["rx"]:
        if case.frame == 0:
            smp.append([mpf(r[1]), mpf(r[2]), mpf(r[3])])
            ump.append([mpf(r[4]), mpf(r[5]), mpf(r[6])])
        else:
            s, u = teme_to_earth(case.day, mpf(r[0]), mpf(ch["xp"]), mpf(ch["yp"]),
                                 [mpf(r[1]), mpf(r[2]), mpf(r[3])],
                                 [mpf(r[4]), mpf(r[5]), mpf(r[6])])
            smp.append(s)
            ump.append(u)
    s = np.array([[float(v) for v in p] for p in smp])
    u = np.array([[float(v) for v in p] for p in ump])
    return Par(s, u, ch["f"], smp, ump)


def receiver_state(phi, lam, alt, heading):
    """A receiver above the geodetic point (phi, lam) at altitude alt over a sphere of radius A,
    on a circular orbit at the given heading in degrees: its Earth-fixed position, its velocity
    relative to the rotating Earth, and its inertial velocity in the same axes.  For alt = 0 the
    receiver stands on the ellipsoid at rest on the Earth."""
    w = np.array([0.0, 0.0, 7.2921158553e-5])
    if alt == 0.0:
        p = position(np.array([phi]), np.array([lam]), np.array([0.0]))[0]
        return p, np.zeros(3), np.cross(w, p)
    rad = A + alt
    p = rad * np.array([math.cos(phi) * math.cos(lam), math.cos(phi) * math.sin(lam),
                        math.sin(phi)])
    east = np.array([-math.sin(lam), math.cos(lam), 0.0])
    north = np.array([-math.sin(phi) * math.cos(lam), -math.sin(phi) * math.sin(lam),
                      math.cos(phi)])
    hd = math.radians(heading)
    v = math.sqrt(MU / rad) * (math.cos(hd) * north + math.sin(hd) * east)
    return p, v - np.cross(w, p), v


def rx_entry(p, v, dp=0.0, dv=0.0, t=(0.0, 0.0)):
    out = [t[0], t[1]]
    for q in range(3):
        out.extend([float(p[q] - dp), float(p[q] + dp)])
    for q in range(3):
        out.extend([float(v[q] - dv), float(v[q] + dv)])
    return out


def scenario(name, status, emitter, sats, kinds, *, eps_t=1e-6, eps_f=0.5, dp=0.0, dv=0.0,
             region=None, res=0.2, levels=60, cap=65536, seed=1, offset=None, frame=0,
             dt=0.0, polar=(0.0, 0.0), dpolar=0.0, pairs=None, freq=None, **expect):
    """A case with the emitter at (phi, lam, h) in degrees and km, receivers above the given
    points (lat, lon, alt, heading in degrees), and measurements of the given kinds between
    receiver 0 and each other receiver, or between the given pairs.  For the TEME frame the
    receivers' states are TEME states at the time 43200 s of MJD 61000 within dt, with the polar
    motion within dpolar of polar."""
    rng = np.random.default_rng(seed)
    phi, lam, h = math.radians(emitter[0]), math.radians(emitter[1]), emitter[2]
    case = Case(name, status, frame=frame, res=res, levels=levels, cap=cap, **expect)
    if freq is not None:
        case.freq = freq
    rx = []
    if frame == 1:
        case.day = 61000.0
        case.xp = (polar[0] - dpolar, polar[0] + dpolar)
        case.yp = (polar[1] - dpolar, polar[1] + dpolar)
        theta = float(gmst_mp(61000, 43200))
    for la, lo, alt, hd in sats:
        p, v, vin = receiver_state(math.radians(la), math.radians(lo), alt, hd)
        if frame == 0:
            rx.append(rx_entry(p, v, dp, dv))
        else:
            c, s = math.cos(theta), math.sin(theta)
            r = np.array([c * p[0] - s * p[1], s * p[0] + c * p[1], p[2]])
            vt = np.array([c * vin[0] - s * vin[1], s * vin[0] + c * vin[1], vin[2]])
            rx.append(rx_entry(r, vt, dp, dv, (43200.0 - dt, 43200.0 + dt)))
    case.rx = rx
    if region is None:
        d = math.radians(2.0)
        region = (phi - d, phi + d, lam - d, lam + d, h, h)
    case.region = region
    meas = []
    for kind in kinds:
        for i, j in pairs or [(0, j) for j in range(1, len(sats))]:
            meas.append((kind, i, j, 0.0, eps_t if kind == 1 else eps_f))
    case.meas = meas
    ch = choose(case, rng)
    par = par_of(case, ch)
    x = position(np.array([phi]), np.array([lam]), np.array([h]))
    vals = residuals(x, case, par)[0]
    shift = offset if offset is not None else [0.0] * len(meas)
    case.meas = [(k, i, j, float(v) + float(rng.uniform(-0.8, 0.8)) * e + o, e)
                 for (k, i, j, _, e), v, o in zip(meas, vals, shift)]
    case.pick_true = ch
    return case


MEO = [(10.0, 30.0, 23222.0, 20.0), (55.0, 10.0, 23222.0, 160.0), (40.0, 70.0, 23222.0, 300.0),
       (-15.0, 50.0, 23222.0, 80.0)]
LEO3 = [(36.0, 41.0, 800.0, 10.0), (34.0, 39.5, 800.0, 10.0), (35.5, 38.0, 800.0, 190.0)]
DEG = math.radians(1.0)
PI_UP = 3.1415926535897936
HALF_PI_UP = 1.5707963267948968


def near(phi, lam, d, h0=0.0, h1=0.0):
    return (math.radians(phi - d), math.radians(phi + d), math.radians(lam - d),
            math.radians(lam + d), h0, h1)


def cases():
    out = []
    em = (35.0, 40.0, 0.0)
    out.append(scenario("meo4-tdoa", 0, em, MEO, [1]))
    out.append(scenario("meo4-fdoa", 0, em, MEO, [2], seed=2))
    out.append(scenario("meo4-both", 0, em, MEO, [1, 2], seed=3))
    leo = [(36.0, 41.0, 800.0, 10.0), (34.0, 39.5, 800.0, 10.0)]
    out.append(scenario("leo2-two-solutions", 0, em, leo, [1, 2], eps_t=2e-7, eps_f=1.0, seed=4,
                        region=near(35, 40, 10)))
    out.append(scenario("aircraft", 0, (35.0, 40.0, 9.0), MEO, [1, 2], seed=5,
                        region=near(35, 40, 1, 0.0, 12.0), res=0.25))
    out.append(scenario("vertical-line", 0, (35.0, 40.0, 9.0), MEO, [1, 2], seed=17,
                        region=(math.radians(35.0), math.radians(35.0), math.radians(40.0),
                                math.radians(40.0), 0.0, 12.0), res=0.01))
    out.append(scenario("receiver-intervals", 0, em, MEO, [1, 2], dp=0.01, dv=1e-5, seed=6))
    out.append(scenario("wide-receiver-intervals", 0, em, MEO, [1], dp=0.5, dv=1e-4,
                        eps_t=1e-7, seed=18, res=0.1, cell=0.02))
    out.append(scenario("f-wide-fine", 0, em, LEO3, [2], eps_f=0.1, seed=19, res=0.02,
                        region=near(35, 40, 0.5)))
    out.append(scenario("whole-earth", 0, em, MEO, [1, 2], seed=7,
                        region=(-HALF_PI_UP, HALF_PI_UP, -PI_UP, PI_UP, 0.0, 0.0), res=1.0))
    out.append(scenario("region-without-emitter", 0, em, MEO, [1, 2], seed=8,
                        region=near(11, 11, 1), count=0))
    out.append(scenario("inconsistent", 0, em, MEO, [1, 2], seed=9,
                        offset=[5e-5, 0, 0, 0, 0, 0], count=0))
    out.append(scenario("near-pole", 0, (89.9, 120.0, 0.0),
                        [(70.0, 100.0, 23222.0, 0.0), (75.0, -60.0, 23222.0, 90.0),
                         (60.0, 170.0, 23222.0, 200.0), (65.0, 30.0, 23222.0, 300.0)],
                        [1, 2], seed=10,
                        region=(math.radians(88.0), HALF_PI_UP, 0.0, math.radians(360.0), 0.0,
                                0.0)))
    out.append(scenario("at-pole", 0, (89.998, 30.0, 0.0),
                        [(70.0, 100.0, 23222.0, 0.0), (75.0, -60.0, 23222.0, 90.0),
                         (60.0, 170.0, 23222.0, 200.0), (65.0, 30.0, 23222.0, 300.0)],
                        [1, 2], seed=20,
                        region=(math.radians(89.0), HALF_PI_UP, -PI_UP, PI_UP, 0.0, 0.0)))
    out.append(scenario("antimeridian", 0, (-20.0, 179.9999, 0.0),
                        [(-10.0, 160.0, 23222.0, 30.0), (-45.0, 175.0, 23222.0, 150.0),
                         (5.0, -170.0, 23222.0, 270.0), (-30.0, -150.0, 23222.0, 10.0)],
                        [1, 2], seed=11,
                        region=(math.radians(-21.0), math.radians(-19.0), 3.0, 3.3, 0.0, 0.0)))
    out.append(scenario("antimeridian-ends", 0, (-20.0, 179.9999, 0.0),
                        [(-10.0, 160.0, 23222.0, 30.0), (-45.0, 175.0, 23222.0, 150.0),
                         (5.0, -170.0, 23222.0, 270.0), (-30.0, -150.0, 23222.0, 10.0)],
                        [1, 2], seed=21,
                        region=(math.radians(-21.0), math.radians(-19.0), -PI_UP, PI_UP, 0.0,
                                0.0), ends=True))
    out.append(scenario("ground-receiver", 0, em,
                        [(35.0002, 40.0002, 0.0, 0.0)] + MEO[:3], [1, 2], seed=22,
                        pairs=[(0, 1), (0, 2), (1, 2), (1, 3)], region=near(35, 40, 0.05),
                        res=0.01))
    out.append(scenario("levels-zero", 2, em, MEO, [1, 2], seed=12, levels=0, count=1))
    out.append(scenario("levels-zero-far", 2, em, MEO, [1, 2], seed=23, levels=0,
                        region=near(20, 60, 1), count=0))
    out.append(scenario("label-one-final", 2, em, MEO, [1], eps_t=1e-3, seed=24, levels=0,
                        region=near(35, 40, 0.1), res=5.0, count=1, label1=1))
    out.append(scenario("label-one-levels", 0, em, MEO, [1], eps_t=2e-5, seed=25, res=0.5,
                        label1=1))
    out.append(scenario("levels-ten", 2, em, MEO, [1, 2], seed=13, levels=10))
    out.append(scenario("levels-exact", 0, em, MEO, [1, 2], seed=3, levels=24))
    out.append(scenario("cap-four", 1, em, MEO, [1, 2], seed=14, cap=4))
    out.append(scenario("cap-one", 1, em, MEO, [1, 2], seed=26, cap=1))
    out.append(scenario("wide-bounds", 0, em, MEO, [1, 2], eps_t=2e-5, eps_f=5.0, seed=15,
                        res=0.5))
    out.append(scenario("teme-both", 0, em, MEO, [1, 2], seed=30, frame=1, polar=(0.1, 0.3),
                        dpolar=0.01, dt=1e-6))
    out.append(scenario("teme-tdoa", 0, em, MEO, [1], seed=31, frame=1, polar=(0.1, 0.3)))
    out.append(scenario("teme-fdoa", 0, em, MEO, [2], seed=32, frame=1, polar=(0.1, 0.3),
                        eps_f=0.2))
    out.append(scenario("teme-fdoa-leo", 0, em, LEO3, [2], seed=33, frame=1, eps_f=0.1,
                        res=0.02, region=near(35, 40, 0.5)))
    out.append(scenario("teme-wide-time", 0, em, MEO, [1, 2], seed=34, frame=1, dt=5.0,
                        eps_t=1e-6, eps_f=0.5, res=2.0, cell=0.2))
    out.append(scenario("teme-big-polar", 0, em, MEO, [1, 2], seed=35, frame=1,
                        polar=(20000.0, 30000.0), region=near(35, 40, 6), res=0.5))
    four = scenario("teme-status-four", 4, em, MEO, [1, 2], seed=36, frame=1)
    four.rx[0][0] = 1e300
    four.rx[0][1] = 1e300
    four.pick_true = None
    out.append(four)
    out.extend(invalid_cases(out[2].values()))
    return out


def invalid_cases(v):
    """Inputs that break each requirement of the interface."""
    bad = []

    def alter(name, idx, value):
        w = list(v)
        w[idx] = value
        bad.append(Case(name, 3, raw=w))

    n = int(v[2])
    base = 20 + 14 * n
    alter("version", 0, 2.0)
    alter("frame-two", 1, 2.0)
    alter("receivers-one", 2, 1.0)
    alter("receivers-fraction", 2, 4.5)
    alter("measurements-zero", 3, 0.0)
    alter("day-fraction", 4, 0.5)
    alter("day-negative", 4, -1.0)
    alter("day-high", 4, 4294967296.0)
    alter("polar-unordered", 5, 1.0)
    alter("polar-y-unordered", 7, 1.0)
    alter("frequency-zero", 9, 0.0)
    alter("frequency-unordered", 10, 1.0)
    alter("latitude-unordered", 12, -2.0)
    alter("longitude-unordered", 14, -4.0)
    alter("height-unordered", 16, -1.0)
    alter("resolution-zero", 17, 0.0)
    alter("levels-high", 18, 129.0)
    alter("cap-zero", 19, 0.0)
    alter("cap-high", 19, 65537.0)
    alter("time-unordered", 21, -1.0)
    alter("receiver-unordered", 23, v[22] - 1.0)
    alter("kind-three", base, 3.0)
    alter("index-high", base + 1, float(n))
    alter("index-negative", base + 1, -1.0)
    alter("index-equal", base + 2, 0.0)
    alter("bound-negative", base + 4, -1.0)
    alter("nan", 25, float("nan"))
    alter("infinite", base + 3, float("inf"))
    bad.append(Case("short", 3, raw=list(v)[:-1]))
    bad.append(Case("long", 3, raw=list(v) + [0.0]))
    bad.append(Case("empty", 3, raw=[]))
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


# Cells and samples.


def cos_max(lo, hi):
    """The largest |cos| over [lo, hi]: 1 when the interval holds 0 or reaches beyond ±pi, and
    otherwise the larger value at its ends."""
    lo, hi = np.asarray(lo), np.asarray(hi)
    one = ((lo <= 0) & (hi >= 0)) | (lo < -math.pi) | (hi > math.pi)
    m = np.maximum(np.abs(np.cos(lo)), np.abs(np.cos(hi)))
    return np.where(one, 1.0, m)


def change_bounds(case, par, x, rad):
    """Bounds of the change of each measurement's model over a ball of radius rad (km) about
    each point of x."""
    out = np.empty((x.shape[0], len(case.meas)))
    for k, (kind, i, j, _, _) in enumerate(case.meas):
        if kind == 1:
            out[:, k] = 2.0 / C
        else:
            ri = np.linalg.norm(par.s[i] - x, axis=1) - rad
            rj = np.linalg.norm(par.s[j] - x, axis=1) - rad
            g = abs(par.f) / C * (2 * np.linalg.norm(par.u[i]) / np.where(ri > 0, ri, np.nan) +
                                  2 * np.linalg.norm(par.u[j]) / np.where(rj > 0, rj, np.nan))
            out[:, k] = np.where(np.isnan(g), np.inf, g)
    return out


def cells_for(case, par, limit=400000):
    """The cells of the Lipschitz subdivision of the region that may hold consistent points."""
    r = case.region
    eps = np.array([m[4] for m in case.meas])
    ys = np.array([abs(m[3]) for m in case.meas])
    r0 = 6400.0 + max(r[5], 0.0)
    cells = np.array([list(r)])
    done = []
    for _ in range(200):
        if len(cells) == 0:
            break
        c = (cells[:, 0::2] + cells[:, 1::2]) / 2
        cm = cos_max(cells[:, 0], cells[:, 1])
        sp = r0 * (cells[:, 1] - cells[:, 0])
        sl = r0 * cm * (cells[:, 3] - cells[:, 2])
        sh = cells[:, 5] - cells[:, 4]
        rad = (sp + sl + sh) / 2
        x = position(c[:, 0], c[:, 1], c[:, 2])
        res = residuals(x, case, par)
        g = change_bounds(case, par, x, rad)
        drop = np.any(np.abs(res) > eps + g * rad[:, None] + 1e-9 * (ys + eps), axis=1)
        cells, sp, sl, sh = cells[~drop], sp[~drop], sl[~drop], sh[~drop]
        small = np.maximum(np.maximum(sp, sl), sh) <= (case.cell or case.res)
        done.append(cells[small])
        cells, sp, sl, sh = cells[~small], sp[~small], sl[~small], sh[~small]
        if len(cells) > limit:
            raise RuntimeError(f"{case.name}: more than {limit} cells")
        side = np.where((sp >= sl) & (sp >= sh), 0, np.where(sl >= sh, 1, 2))
        lo = cells.copy()
        hi = cells.copy()
        idx = np.arange(len(cells))
        mid = (cells[idx, 2 * side] + cells[idx, 2 * side + 1]) / 2
        lo[idx, 2 * side + 1] = mid
        hi[idx, 2 * side] = mid
        cells = np.vstack([lo, hi])
    done.append(cells)
    return np.vstack(done) if done else np.zeros((0, 6))


def samples_in(cells):
    """A grid of 4 points along each side of every cell, at fractions that are not dyadic, so
    that no sample lies on a side that bisection makes, without repeated points."""
    f = (np.arange(4) + 0.4) / 4
    pts = []
    for a in f:
        for b in f:
            for c in f:
                pts.append(cells[:, 0::2] + np.array([a, b, c]) * (cells[:, 1::2] -
                                                                   cells[:, 0::2]))
    return np.unique(np.vstack(pts), axis=0)


def parameters(case, rng):
    pars = [("center", par_of(case, choose(case)))]
    if case.pick_true is not None:
        pars.append(("true", par_of(case, case.pick_true)))
    for q in range(3):
        pars.append((f"random{q}", par_of(case, choose(case, rng))))
    for q in range(2):
        pars.append((f"corner{q}", par_of(case, choose(case, rng, corner=True))))
    return pars


@dataclass
class Prepared:
    pars: list
    samples: list  # (parameter index, points, consistent mask)
    undecided: int
    cells: int


def prepare(case):
    rng = np.random.default_rng(99)
    pars = parameters(case, rng)
    samples = []
    und = 0
    ncells = 0
    for q, (_, par) in enumerate(pars):
        cells = cells_for(case, par)
        ncells += len(cells)
        pts = samples_in(cells)
        ok, u = fits(pts, case, par)
        samples.append((q, pts, ok))
        und += u
    return Prepared(pars, samples, und, ncells)


# Checks.


def boxes_of(out):
    k = int(out[1])
    return np.array(out[4:4 + 7 * k], dtype=float).reshape(k, 7) if k else np.zeros((0, 7))


def covered(boxes, pts):
    """For each point, whether some box holds it."""
    return cover_count(boxes, pts) > 0


def cover_count(boxes, pts):
    """For each point, the number of boxes that hold it, by the points of each box's latitude
    slab."""
    hit = np.zeros(len(pts), dtype=int)
    if len(pts) == 0 or len(boxes) == 0:
        return hit
    order = np.argsort(pts[:, 0], kind="stable")
    ph = pts[order, 0]
    for b in boxes:
        a = np.searchsorted(ph, b[0], side="left")
        z = np.searchsorted(ph, b[1], side="right")
        if a == z:
            continue
        idx = order[a:z]
        p = pts[idx]
        sel = (b[2] <= p[:, 1]) & (p[:, 1] <= b[3]) & (b[4] <= p[:, 2]) & (p[:, 2] <= b[5])
        hit[idx[sel]] += 1
    return hit


def size_and_side(b):
    """The program's size of a box, with the library's cos replaced by math.cos."""
    sa = 6378.137 * (b[1] - b[0])
    c = 1.0 if b[0] <= 0.0 <= b[1] else max(abs(math.cos(b[0])), abs(math.cos(b[1])))
    sb = 6378.137 * c * (b[3] - b[2])
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
    return not (r * (1 + 1e-12) < size and math.isfinite(md) and lo < md < hi)


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


def method_ok(case, prep, boxes):
    """Whether the center of every box fits each measurement for the central parameter within
    its bound plus eight times bounds of the change over the box and over the parameters."""
    if len(boxes) == 0:
        return True
    c = np.column_stack([(boxes[:, 0] + boxes[:, 1]) / 2, (boxes[:, 2] + boxes[:, 3]) / 2,
                         (boxes[:, 4] + boxes[:, 5]) / 2])
    x = position(c[:, 0], c[:, 1], c[:, 2])
    corners = []
    for p in (0, 1):
        for q in (2, 3):
            for s in (4, 5):
                corners.append(position(boxes[:, p], boxes[:, q], boxes[:, s]))
    rad = np.max(np.stack([np.linalg.norm(k - x, axis=1) for k in corners]), axis=0)
    center = prep.pars[0][1]
    base = residuals(x, case, center)
    eps = np.array([m[4] for m in case.meas])
    g = change_bounds(case, center, x, rad)
    bad = np.abs(base) > eps + 8 * (g * rad[:, None] + parameter_bounds(case, center, x))
    return not bad.any()


def parameter_bounds(case, par, x):
    """Bounds of each measurement's change from the central parameter to any admissible one, at
    the points x: from the largest moves of each receiver's Earth-fixed position and velocity
    over its intervals, and the half-width of the frequency's interval."""
    ds, du = [], []
    for r in case.rx:
        hp = math.sqrt(sum(((r[3 + 2 * q] - r[2 + 2 * q]) / 2) ** 2 for q in range(3)))
        hv = math.sqrt(sum(((r[9 + 2 * q] - r[8 + 2 * q]) / 2) ** 2 for q in range(3)))
        if case.frame == 1:
            pos = math.sqrt(sum(((r[2 + 2 * q] + r[3 + 2 * q]) / 2) ** 2 for q in range(3)))
            vel = math.sqrt(sum(((r[8 + 2 * q] + r[9 + 2 * q]) / 2) ** 2 for q in range(3)))
            turn = (7.3e-5 * (r[1] - r[0]) / 2 +
                    math.pi / 648000 * ((case.xp[1] - case.xp[0]) + (case.yp[1] - case.yp[0])))
            ds.append(hp + (pos + hp) * turn)
            du.append(hv + (vel + hv) * turn + 7.3e-5 * (hp + (pos + hp) * turn) + 1e-12 * pos)
        else:
            ds.append(hp)
            du.append(hv)
    out = np.empty((x.shape[0], len(case.meas)))
    hf = (case.freq[1] - case.freq[0]) / 2
    for k, (kind, i, j, _, _) in enumerate(case.meas):
        if kind == 1:
            out[:, k] = (ds[i] + ds[j]) / C
        else:
            di = par.s[i] - x
            dj = par.s[j] - x
            ri = np.linalg.norm(di, axis=1)
            rj = np.linalg.norm(dj, axis=1)
            rri = np.sum(di * par.u[i], axis=1) / ri
            rrj = np.sum(dj * par.u[j], axis=1) / rj
            ni = np.linalg.norm(par.u[i]) + du[i]
            nj = np.linalg.norm(par.u[j]) + du[j]
            ci = du[i] + 2 * ni * ds[i] / np.maximum(ri - ds[i], 1e-9)
            cj = du[j] + 2 * nj * ds[j] / np.maximum(rj - ds[j], 1e-9)
            out[:, k] = ((abs(par.f) + hf) * (ci + cj) + hf * np.abs(rri - rrj)) / C
    return out


def check(case, out, prep):
    """The failures of an output, as a list of strings."""
    errs = []
    if not case.valid():
        if list(out) != [3.0, 0.0, 0.0, 0.0]:
            errs.append(f"invalid input gave {out[:4]}")
        return errs
    if len(out) < 4:
        return ["output shorter than 4"]
    status, k, tests, lev = out[0], out[1], out[2], out[3]
    if status != case.status:
        errs.append(f"status {status}, expected {case.status}")
    if status == 4:
        if list(out) != [4.0, 0.0, 0.0, 0.0]:
            errs.append(f"status 4 with {out[:4]}")
        return errs
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
    if case.count is not None and k != case.count:
        errs.append(f"{k} boxes, expected {case.count}")
    if case.label1 is not None and int(np.sum(boxes[:, 6] == 1.0)) < case.label1:
        errs.append(f"fewer than {case.label1} boxes labeled 1")
    if case.ends and not (len(boxes) and boxes[:, 2].min() <= reg[2] + 1e-3 and
                          boxes[:, 3].max() >= reg[3] - 1e-3):
        errs.append("no boxes at both ends of the longitude")
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
    for b in inner[:300]:
        corners = np.array([[p, l, h] for p in b[0:2] for l in b[2:4] for h in b[4:6]])
        rnd = np.column_stack([b[0] + (b[1] - b[0]) * rng.random(6),
                               b[2] + (b[3] - b[2]) * rng.random(6),
                               b[4] + (b[5] - b[4]) * rng.random(6)])
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
    if not method_ok(case, prep, boxes):
        errs.append("a box far from the consistent set")
    return errs


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
        alone = cons[cover_count(boxes, cons) == 1]
        counts = [int(covered(boxes[q:q + 1], alone).sum()) for q in range(len(boxes))]
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
                muts.append(("label 1 a box with a failing corner", pack(bb)))
                break
    muts.append(("status 3", pack(boxes, 3.0)))
    r = case.region
    corner = np.array([[r[0], r[0] + (r[1] - r[0]) * 1e-6, r[2], r[2] + (r[3] - r[2]) * 1e-6,
                        r[4], r[5], 0.0]])
    if len(boxes) and not covered(boxes, corner[:, [0, 2, 4]]).any():
        muts.append(("add a box far from the consistent set", pack(np.vstack([boxes, corner]))))
    region = np.array([[*case.region, 1.0]])
    if not (len(boxes) == 1 and np.array_equal(boxes, region)):
        muts.append(("the region labeled 1", pack(region)))
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
            if c.valid() and c.status != 4:
                prep = prepare(c)
                ns = sum(len(p) for _, p, _ in prep.samples)
                nc = sum(int(ok.sum()) for _, _, ok in prep.samples)
                print(f"{c.name}: {prep.cells} cells, {nc} of {ns} samples consistent, "
                      f"{prep.undecided} undecided")
        return 0
    if cost:
        valid = [c for c in cs if c.valid()]
        outs = run(module, [c.values() for c in valid], repeat=9)
        for c, (out, ms) in zip(valid, outs):
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
        prep = prepare(c) if c.valid() and c.status != 4 else Prepared([], [], 0, 0)
        ns = sum(len(p) for _, p, _ in prep.samples)
        nc = sum(int(ok.sum()) for _, _, ok in prep.samples)
        total_samples += ns
        total_consistent += nc
        total_undecided += prep.undecided
        errs = check(c, out, prep)
        line = (f"{c.name}: status {out[0]:.0f}, {out[1]:.0f} boxes, {out[2]:.0f} tests, "
                f"{out[3]:.0f} levels" if len(out) >= 4 else f"{c.name}: short output")
        if c.valid() and len(out) >= 4:
            lab = int(np.sum(boxes_of(out)[:, 6] == 1.0)) if out[0] != 4 else 0
            line += f", {lab} labeled 1, {nc} of {ns} samples consistent, {ms:.1f} ms"
        if errs:
            failed += 1
            print(line + ": FAIL")
            for e in errs[:5]:
                print("    " + e)
        else:
            print(line + ": ok")
        if mutate and c.valid() and c.status != 4 and not errs:
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
