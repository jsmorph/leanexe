# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0", "numpy==2.5.3"]
# ///
"""Tests the event-window module against dense sampling of its model.

The script builds the cases of `cases()`, runs the export `events` of the WebAssembly module on
each with `tests/events/events.mjs` under Node, and checks every output against an oracle written
apart from the program.  The oracle evaluates the model of `Demos/Events/requirements.md` with
its own solver of Kepler's equation, its own evaluation of the USNO formula for the Sun, and each
event's functions g1 and g2, in binary64 for dense sampling and in mpmath at 30 digits for samples
whose g1 or g2 lies within 1e-7 of zero and for the refinement of crossings.

For each output it checks the claims of the requirements:
  - status 2 and the output 2, 0, 0, 0 exactly for the invalid inputs;
  - for valid inputs, the status that the case states, an output of 4 + 3K values, at most
    (N + 1) C cell tests, N levels completed at status 0 and fewer at status 1, labels 0 and 1,
    at most C runs, runs in increasing order inside [t0, t1], and no two consecutive runs with
    equal labels that touch;
  - every sampled time at which the condition holds, both ends of the window among them, lies in
    a returned run, and the condition holds at every sampled time of a run labeled 1;
  - for each change of the condition between two samples, refined by bisection in mpmath to
    1e-10 minutes, the time on the side where the condition holds lies in a run, and the time on
    the other side lies in no run labeled 1;
  - for the shadow with P > 0, the same claims for the four trajectories displaced by P along
    the gradient of g2 and along the Sun's direction, toward and away from the shadow.
It also checks that the output follows the method where the margins far exceed rounding: for
status 0 after 18 levels or more, with D = max((t1 - t0) / 2^N, 1e-9) minutes, every sampled
time at which gk + Lk D + Wk < 0 for both k lies in a run labeled 1, and every sampled time in a
run has gk <= Lk D + Wk for both k.  A sample whose g lies within 1e-12 of zero in mpmath counts
as inconclusive and is reported.  With --mutate, the script also alters correct outputs so that
each alteration is wrong (it removes the run that holds the most samples of the condition, moves
the start of a run past a refined time of the condition, labels 1 a run that holds a refined
time at which the condition fails, reports status 2, and returns the whole window as one run
labeled 1 or labeled 0) and requires the check to fail on each.  It prints one line per case,
then a summary, and exits with status 1 on any failure.  With --cost, it skips the checks and
takes the time of each call as the median of 9 calls.

Usage: uv run tests/events/oracle.py MODULE [--mutate | --cost]"""
import datetime
import json
import math
import struct
import subprocess
import sys
from dataclasses import dataclass, replace
from pathlib import Path

import numpy as np
from mpmath import mp, mpf

mp.dps = 30
MU = 398600.4418
RE = 6378.137
STEP = 0.001
TOL = mpf(10) ** -12


def bits(x: float) -> str:
    return struct.pack(">d", x).hex()


def unbits(h: str) -> float:
    return struct.unpack(">d", bytes.fromhex(h))[0]


def day(y: int, mo: int, d: int, h: float = 0.0) -> float:
    """Days from J2000.0, the Julian date 2451545.0, at the given UTC time."""
    t = datetime.datetime(y, mo, d, tzinfo=datetime.timezone.utc)
    j2000 = datetime.datetime(2000, 1, 1, 12, tzinfo=datetime.timezone.utc)
    return (t - j2000).total_seconds() / 86400.0 + h / 24.0


@dataclass(frozen=True)
class Orbit:
    a: float
    e: float
    incl: float
    node: float
    argp: float
    m0: float
    epoch: float


@dataclass(frozen=True)
class Case:
    name: str
    kind: str
    orbit: Orbit
    d0: float
    t0: float
    t1: float
    code: float
    angle: float
    radius: float = RE
    pad: float = 0.0
    b: tuple = (0.0, 0.0, 0.0)
    levels: float = 20.0
    cap: float = 65536.0
    mu: float = MU
    version: float = 1.0
    step: float = STEP
    status: int = 0
    invalid: bool = False
    raw: tuple | None = None

    def values(self) -> list[float]:
        if self.raw is not None:
            return list(self.raw)
        o = self.orbit
        return [self.version, o.a, o.e, o.incl, o.node, o.argp, o.m0, o.epoch, self.mu, self.d0,
                self.t0, self.t1, self.code, self.angle, self.radius, self.pad, *self.b,
                self.levels, self.cap]


# The model in binary64, vectorized.

def frame(o: Orbit) -> tuple[np.ndarray, np.ndarray]:
    i, w, n = (math.radians(x) for x in (o.incl, o.argp, o.node))
    p = np.array([math.cos(w) * math.cos(n) - math.sin(w) * math.sin(n) * math.cos(i),
                  math.cos(w) * math.sin(n) + math.sin(w) * math.cos(n) * math.cos(i),
                  math.sin(w) * math.sin(i)])
    q = np.array([-math.sin(w) * math.cos(n) - math.cos(w) * math.sin(n) * math.cos(i),
                  -math.sin(w) * math.sin(n) + math.cos(w) * math.cos(n) * math.cos(i),
                  math.cos(w) * math.sin(i)])
    return p, q


def motion(o: Orbit, mu: float) -> float:
    return 60.0 * math.sqrt(mu / o.a) / o.a


def kepler_np(m: np.ndarray, e: float) -> np.ndarray:
    m = np.mod(m, 2 * np.pi)
    x = np.where(e < 0.8, m + e * np.sin(m), np.pi)
    for _ in range(60):
        x = x - (x - e * np.sin(x) - m) / (1 - e * np.cos(x))
    return x


def position_np(o: Orbit, t: np.ndarray, mu: float) -> np.ndarray:
    m = math.radians(o.m0) + motion(o, mu) * (t - o.epoch)
    ecc = kepler_np(m, o.e)
    p, q = frame(o)
    x = o.a * (np.cos(ecc) - o.e)
    y = o.a * math.sqrt(1 - o.e * o.e) * np.sin(ecc)
    return x[:, None] * p[None, :] + y[:, None] * q[None, :]


def sun_np(d0: float, t: np.ndarray) -> np.ndarray:
    d = d0 + t / 1440.0
    g = np.radians(357.529 + 0.98560028 * d)
    lam = np.radians(280.459 + 0.98564736 * d + 1.915 * np.sin(g) + 0.020 * np.sin(2 * g))
    eps = np.radians(23.439 - 0.00000036 * d)
    return np.stack([np.cos(lam), np.cos(eps) * np.sin(lam), np.sin(eps) * np.sin(lam)], axis=1)


def rsw_np(o: Orbit, r: np.ndarray, b) -> np.ndarray:
    p, q = frame(o)
    w = np.cross(p, q)
    rh = r / np.linalg.norm(r, axis=1)[:, None]
    s = np.cross(w[None, :], rh)
    return b[0] * rh + b[1] * s + b[2] * w[None, :]


def functions_np(c: Case, t: np.ndarray, shift=None) -> tuple[np.ndarray, np.ndarray]:
    """g1 and g2 of the case's event at the times t, for the position displaced by shift(r, s)."""
    s = sun_np(c.d0, t)
    if c.code == 2.0:
        b = np.array(c.b)
        g = np.linalg.norm(b) * math.cos(math.radians(c.angle)) - s @ b
        return g, g
    r = position_np(c.orbit, t, c.mu)
    if c.code == 3.0:
        v = rsw_np(c.orbit, r, c.b)
        g = np.linalg.norm(c.b) * math.cos(math.radians(c.angle)) - np.sum(v * s, axis=1)
        return g, g
    if shift is not None:
        r = r + shift(r, s)
    d = np.sum(r * s, axis=1)
    y = np.linalg.norm(np.cross(r, s), axis=1)
    al = math.radians(c.angle)
    return d, y * math.cos(al) + d * math.sin(al) - c.radius


# The model in mpmath.

def kepler_mp(m, e):
    m = m % (2 * mp.pi)
    x = m + e * mp.sin(m) if e < 0.8 else mp.pi
    for _ in range(100):
        dx = (x - e * mp.sin(x) - m) / (1 - e * mp.cos(x))
        x -= dx
        if abs(dx) < mpf(10) ** -28:
            break
    return x


def frame_mp(o: Orbit):
    i, w, n = (mpf(x) * mp.pi / 180 for x in (o.incl, o.argp, o.node))
    p = [mp.cos(w) * mp.cos(n) - mp.sin(w) * mp.sin(n) * mp.cos(i),
         mp.cos(w) * mp.sin(n) + mp.sin(w) * mp.cos(n) * mp.cos(i), mp.sin(w) * mp.sin(i)]
    q = [-mp.sin(w) * mp.cos(n) - mp.cos(w) * mp.sin(n) * mp.cos(i),
         -mp.sin(w) * mp.sin(n) + mp.cos(w) * mp.cos(n) * mp.cos(i), mp.cos(w) * mp.sin(i)]
    return p, q


def position_mp(o: Orbit, t, mu: float):
    n = 60 * mp.sqrt(mpf(mu) / mpf(o.a)) / mpf(o.a)
    m = mpf(o.m0) * mp.pi / 180 + n * (mpf(t) - mpf(o.epoch))
    a, e = mpf(o.a), mpf(o.e)
    ecc = kepler_mp(m, e)
    p, q = frame_mp(o)
    x = a * (mp.cos(ecc) - e)
    y = a * mp.sqrt(1 - e * e) * mp.sin(ecc)
    return [x * p[k] + y * q[k] for k in range(3)]


def sun_mp(d0: float, t):
    d = mpf(d0) + mpf(t) / 1440
    rad = mp.pi / 180
    g = (mpf("357.529") + mpf("0.98560028") * d) * rad
    lam = (mpf("280.459") + mpf("0.98564736") * d + mpf("1.915") * mp.sin(g)
           + mpf("0.020") * mp.sin(2 * g)) * rad
    eps = (mpf("23.439") - mpf("0.00000036") * d) * rad
    return [mp.cos(lam), mp.cos(eps) * mp.sin(lam), mp.sin(eps) * mp.sin(lam)]


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def cross(u, v):
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]


def norm(u):
    return mp.sqrt(dot(u, u))


def functions_mp(c: Case, t, shift=None):
    s = sun_mp(c.d0, t)
    cb = mp.cos(mpf(c.angle) * mp.pi / 180)
    b = [mpf(x) for x in c.b]
    if c.code == 2.0:
        g = norm(b) * cb - dot(b, s)
        return g, g
    r = position_mp(c.orbit, t, c.mu)
    if c.code == 3.0:
        p, q = frame_mp(c.orbit)
        w = cross(p, q)
        rn = norm(r)
        rh = [x / rn for x in r]
        sv = cross(w, rh)
        v = [b[0] * rh[k] + b[1] * sv[k] + b[2] * w[k] for k in range(3)]
        g = norm(b) * cb - dot(v, s)
        return g, g
    if shift is not None:
        r = [r[k] + x for k, x in enumerate(shift_mp(shift, r, s))]
    d = dot(r, s)
    y = norm(cross(r, s))
    al = mpf(c.angle) * mp.pi / 180
    return d, y * mp.cos(al) + d * mp.sin(al) - mpf(c.radius)


def shift_mp(shift, r, s):
    rf = np.array([[float(x) for x in r]])
    sf = np.array([[float(x) for x in s]])
    return [mpf(float(x)) for x in shift(rf, sf)[0]]


# Rate bounds and margins, from the requirements.

OMEGA = math.pi / 180 * (0.98564736 + 1.955 * 0.98560028 * math.pi / 180 + 0.00000036) / 1440


def rates(c: Case) -> tuple[float, float, float, float]:
    """L1, L2, w1, w2 of the case's event."""
    o = c.orbit
    speed = o.a * motion(o, c.mu) / (1 - o.e)
    nb = math.sqrt(sum(x * x for x in c.b))
    if c.code == 1.0:
        al = math.radians(c.angle)
        k = abs(math.cos(al)) + abs(math.sin(al))
        l1 = speed + o.a * (1 + o.e) * OMEGA
        return l1, k * l1, c.pad, k * c.pad
    if c.code == 2.0:
        return nb * OMEGA, nb * OMEGA, 0.0, 0.0
    l = (abs(c.b[0]) + abs(c.b[1])) * speed / (o.a * (1 - o.e)) + nb * OMEGA
    return l, l, 0.0, 0.0


# Classification of samples.

def classify(c: Case, t: np.ndarray, shift=None):
    """The condition at each sample, g1 and g2, and the indices of inconclusive samples."""
    g1, g2 = functions_np(c, t, shift)
    scale = 1e-7 if c.code == 1.0 else 1e-10 * max(1.0, math.sqrt(sum(x * x for x in c.b)))
    holds = (g1 <= 0) & (g2 <= 0)
    near = np.nonzero((np.abs(g1) < scale) | (np.abs(g2) < scale))[0]
    unsure = []
    for i in near:
        h1, h2 = functions_mp(c, float(t[i]), shift)
        if abs(h1) < TOL or abs(h2) < TOL:
            unsure.append(int(i))
        holds[i] = h1 <= 0 and h2 <= 0
    return holds, g1, g2, unsure


def holds_mp(c: Case, t, shift=None) -> bool:
    h1, h2 = functions_mp(c, t, shift)
    return h1 <= 0 and h2 <= 0


def refine(c: Case, ta: float, tb: float, a_holds: bool, shift=None) -> tuple[float, float]:
    """A pair of times within 1e-10 minutes, the condition holding at the first and failing at
    the second, between two samples whose conditions differ."""
    yes, no = (mpf(ta), mpf(tb)) if a_holds else (mpf(tb), mpf(ta))
    while abs(yes - no) > mpf(10) ** -10:
        mid = (yes + no) / 2
        if holds_mp(c, mid, shift):
            yes = mid
        else:
            no = mid
    return float(yes), float(no)


def member(runs: list, t: np.ndarray, label: int | None = None) -> np.ndarray:
    """Whether each time lies in a run, or in a run with the given label."""
    rs = sorted(r for r in runs if label is None or r[2] == label)
    if not rs:
        return np.zeros(len(t), dtype=bool)
    lo = np.array([r[0] for r in rs])
    hi = np.array([r[1] for r in rs])
    out = np.zeros(len(t), dtype=bool)
    k = np.searchsorted(lo, t, side="right") - 1
    for shift in (0, 1, 2):
        j = k - shift
        ok = j >= 0
        jj = np.where(ok, j, 0)
        out |= ok & (lo[jj] <= t) & (t <= hi[jj])
    return out


# The cases.

def median_angle(c: Case) -> float:
    """The median over the window of the angle between the case's vector and the Sun."""
    t = np.linspace(c.t0, c.t1, 4001)
    g, _ = functions_np(replace(c, angle=0.0), t)
    nb = math.sqrt(sum(x * x for x in c.b))
    return float(np.degrees(np.median(np.arccos(np.clip((nb - g) / nb, -1.0, 1.0))))) + 1e-4


def sun_ra_dec(d0: float) -> tuple[float, float]:
    s = sun_np(d0, np.array([0.0]))[0]
    return math.degrees(math.atan2(s[1], s[0])), math.degrees(math.asin(s[2]))


def cases() -> list[Case]:
    out: list[Case] = []
    equinox = day(2026, 3, 20)
    solstice = day(2026, 6, 21)
    autumn = day(2026, 11, 11)
    ra, _ = sun_ra_dec(equinox)
    leo = Orbit(6878.0, 0.001, 0.0, 0.0, 0.0, 0.0, 0.0)
    for name, al in [("penumbra", 0.269), ("umbra", -0.264), ("cylinder", 0.0)]:
        out.append(Case(f"LEO in the Sun's plane, {name}", "shadow", leo, equinox, 0.0, 1440.0,
                        1.0, al))
    out.append(Case("LEO, padding 5 km", "padding", leo, equinox, 0.0, 1440.0, 1.0, 0.269,
                    pad=5.0))
    out.append(Case("LEO, padding 50 km", "padding", leo, equinox, 0.0, 300.0, 1.0, -0.264,
                    pad=50.0))
    ra_a, dec_a = sun_ra_dec(autumn)
    dawn = Orbit(7078.0, 0.0012, 98.2, ra_a + 90.0, 90.0, 0.0, 0.0)
    out.append(Case("dawn-dusk orbit, Sun near the normal", "shadow", dawn, autumn, 0.0, 1440.0,
                    1.0, 0.269))
    geo = Orbit(42164.0, 0.0002, 0.05, 0.0, 0.0, 0.0, 0.0)
    out.append(Case("GEO at the equinox", "shadow", geo, equinox, 0.0, 1440.0, 1.0, 0.269))
    out.append(Case("GEO at the equinox, umbra", "shadow", geo, equinox, 0.0, 1440.0, 1.0,
                    -0.264))
    out.append(Case("GEO at the solstice", "shadow", geo, solstice, 0.0, 1440.0, 1.0, 0.269))
    molniya = Orbit(26554.0, 0.72, 63.4, 40.0, 270.0, 10.0, 0.0)
    out.append(Case("Molniya", "shadow", molniya, equinox, 0.0, 1440.0, 1.0, 0.269))
    out.append(Case("Molniya, umbra", "shadow", molniya, solstice, 0.0, 1440.0, 1.0, -0.264))
    for name, t0, t1 in [("begins in the shadow", 50.0, 400.0), ("ends in the shadow",
                                                                  0.0, 90.0)]:
        out.append(Case(f"LEO window {name}", "end", leo, equinox, t0, t1, 1.0, 0.269))
    for beta in (67.5, 67.9, 68.0, 68.1):
        o = Orbit(6878.0, 0.0, 90.0, ra + beta, 0.0, 0.0, 0.0)
        out.append(Case(f"grazing, beta {beta}", "grazing", o, equinox, 0.0, 1440.0, 1.0, 0.269))
    s = sun_np(autumn + 3.5, np.array([0.0]))[0]
    out.append(Case("inertial vector toward the Sun of day 3.5, 1 deg", "inertial", leo, autumn,
                    0.0, 10080.0, 2.0, 1.0, b=tuple(float(x) for x in s), levels=24.0,
                    step=0.01))
    out.append(Case("inertial vector, 120 deg", "inertial", leo, autumn, 0.0, 10080.0, 2.0, 120.0,
                    b=(0.0, 0.0, 1.0), levels=24.0, step=0.01))
    out.append(Case("inertial vector, 180 deg", "inertial", leo, autumn, 0.0, 1440.0, 2.0, 180.0,
                    b=(1.0, -2.0, 3.0), step=0.01))
    out.append(Case("along-track vector, 30 deg", "rsw", leo, equinox, 0.0, 1440.0, 3.0, 30.0,
                    b=(0.0, 1.0, 0.0)))
    c = Case("zenith vector, dawn-dusk", "rsw", dawn, autumn, 0.0, 1440.0, 3.0, 0.0,
             b=(1.0, 0.0, 0.0))
    out.append(replace(c, angle=median_angle(c)))
    out.append(Case("tilted vector, Molniya", "rsw", molniya, equinox, 0.0, 1440.0, 3.0, 45.0,
                    b=(0.3, -0.5, 0.8)))
    eqx = 9575.115
    mol = Orbit(26560.0, 0.72, 63.4, 40.0, 270.0, 340.0, 0.0)
    for name, b in [("along-track", (0.0, 1.0, 0.0)), ("mixed", (0.6, -0.8, 0.3))]:
        c = Case(f"{name} vector, Molniya perigee", "rsw", mol, eqx, 0.0, 80.0, 3.0, 0.0, b=b)
        out.append(replace(c, angle=median_angle(c)))
    c = Case("cross-track vector over two days", "rsw", leo, equinox, 0.0, 2880.0, 3.0, 0.0,
             b=(0.0, 0.0, 1.0))
    out.append(replace(c, angle=median_angle(c)))
    out.append(Case("Earth radius above the perigee", "shadow", leo, equinox, 0.0, 1440.0, 1.0,
                    0.0, radius=7000.0))
    gto = Orbit(24396.0, 0.73, 7.0, 0.0, 180.0, 180.0, 0.0)
    out.append(Case("transfer orbit, shadow at perigee", "shadow", gto, eqx, 0.0, 640.0, 1.0,
                    0.269))
    far = Orbit(200000.0, 0.0, 180.0, 0.0, 0.0, 172.72, 0.0)
    out.append(Case("circular orbit at 200,000 km", "high", far, eqx, 0.0, 600.0, 1.0, 0.269))
    for t0 in (206.0896, 206.1716, 374.40254311666644):
        out.append(Case(f"circular orbit at 200,000 km, 2 min from {t0:.4f}", "high", far, eqx,
                        t0, t0 + 2.0, 1.0, 0.269, levels=6.0))
    out.append(Case("no levels", "cap", leo, equinox, 0.0, 1440.0, 1.0, 0.269, levels=0.0))
    out.append(Case("cap 1", "cap", leo, equinox, 0.0, 1440.0, 1.0, 0.269, cap=1.0, status=1))
    out.append(Case("cap 64", "cap", leo, equinox, 0.0, 1440.0, 1.0, 0.269, cap=64.0, status=1))
    out.append(Case("40 levels", "cap", leo, equinox, 28.2, 30.2, 1.0, 0.269, levels=40.0))
    huge = Orbit(1e300, 0.1, 30.0, 0.0, 0.0, 0.0, 0.0)
    out.append(Case("rejected enclosures", "reject", huge, equinox, 0.0, 1440.0, 1.0, 0.269,
                    levels=10.0, step=0.5))
    rng = np.random.default_rng(20261111)
    for k in range(8):
        o = Orbit(float(rng.uniform(6700, 7600)), float(rng.uniform(0, 0.02)),
                  float(rng.uniform(0, 180)), float(rng.uniform(0, 360)),
                  float(rng.uniform(0, 360)), float(rng.uniform(0, 360)),
                  float(rng.uniform(-100, 100)))
        d0 = float(rng.uniform(day(2020, 1, 1), day(2030, 1, 1)))
        if k % 2 == 0:
            out.append(Case(f"random shadow {k}", "random", o, d0, 0.0, 1440.0, 1.0,
                            float(rng.uniform(-0.3, 0.3)), pad=float(rng.uniform(0, 3))))
        else:
            b = tuple(float(x) for x in rng.normal(size=3))
            out.append(Case(f"random vector {k}", "random", o, d0, 0.0, 1440.0, 3.0,
                            float(rng.uniform(10, 80)), b=b))
    base = Case("invalid", "invalid", leo, equinox, 0.0, 1440.0, 1.0, 0.269, invalid=True)
    nan = float("nan")
    for name, change in [("version 2", dict(version=2.0)),
                         ("e = 1", dict(orbit=replace(leo, e=1.0))),
                         ("a = 0", dict(orbit=replace(leo, a=0.0))),
                         ("mu = 0", dict(mu=0.0)),
                         ("d0 beyond 1e6 days", dict(d0=2e6)),
                         ("t0 after t1", dict(t0=10.0, t1=5.0)),
                         ("window beyond 1e9 minutes", dict(t1=2e9)),
                         ("event 4", dict(code=4.0)),
                         ("alpha 90", dict(angle=90.0)),
                         ("R 0", dict(radius=0.0)),
                         ("P negative", dict(pad=-1.0)),
                         ("beta 181", dict(code=2.0, angle=181.0, b=(1.0, 0.0, 0.0))),
                         ("b zero", dict(code=3.0, angle=30.0)),
                         ("61 levels", dict(levels=61.0)),
                         ("cap 0", dict(cap=0.0)),
                         ("levels 2.5", dict(levels=2.5)),
                         ("NaN inclination", dict(orbit=replace(leo, incl=nan)))]:
        out.append(replace(base, name=name, **change))
    out.append(replace(base, name="20 values", raw=tuple(base.values()[:20])))
    out.append(replace(base, name="22 values", raw=tuple(base.values() + [0.0])))
    return out


# Running the module.

def run(module: str, cs: list[Case], repeat: int = 1) -> list[dict]:
    lines = "\n".join(json.dumps([bits(x) for x in c.values()]) for c in cs) + "\n"
    script = Path(__file__).with_name("events.mjs")
    res = subprocess.run(["node", str(script), module, str(repeat)], input=lines, text=True,
                         capture_output=True, check=True)
    outs = []
    for line in res.stdout.splitlines():
        d = json.loads(line)
        outs.append({"out": [unbits(h) for h in d["out"]], "ms": d["ms"]})
    return outs


def runs_of(out: list[float]) -> list[tuple[float, float, int]]:
    k = int(out[1])
    return [(out[4 + 3 * j], out[5 + 3 * j], int(out[6 + 3 * j])) for j in range(k)]


def samples(c: Case) -> np.ndarray:
    n = int(math.ceil((c.t1 - c.t0) / c.step))
    t = np.linspace(c.t0, c.t1, max(n, 1) + 1)
    t[0], t[-1] = c.t0, c.t1
    return t


def shifts(c: Case) -> list:
    """Displacements by P along the gradient of g2 and along the Sun's direction."""
    if c.code != 1.0 or c.pad == 0.0:
        return []
    al = math.radians(c.angle)

    def grad(sign):
        def f(r, s):
            d = np.sum(r * s, axis=1)[:, None]
            perp = r - d * s
            y = perp / np.linalg.norm(perp, axis=1)[:, None]
            return sign * c.pad * (math.cos(al) * y + math.sin(al) * s)
        return f

    def along(sign):
        return lambda r, s: sign * c.pad * s

    return [grad(-1.0), grad(1.0), along(-1.0), along(1.0)]


def check(c: Case, out: list[float], t: np.ndarray | None = None, cls=None) -> tuple[list[str], dict]:
    """The failures of an output, and facts for the summary."""
    fails: list[str] = []
    info = {"unsure": 0, "crossings": 0}
    if c.invalid:
        if out != [2.0, 0.0, 0.0, 0.0]:
            fails.append(f"invalid input gave {out[:4]}")
        return fails, info
    if len(out) < 4 or out[0] != float(c.status):
        return [f"status {out[:1]}, expected {c.status}"], info
    k = int(out[1])
    if len(out) != 4 + 3 * k or out[1] != k:
        return [f"size {len(out)} for K = {out[1]}"], info
    if out[2] > (c.levels + 1) * c.cap:
        fails.append(f"{out[2]:g} cell tests above (N + 1) C")
    if (out[0] == 0.0 and out[3] != c.levels) or (out[0] == 1.0 and not out[3] < c.levels):
        fails.append(f"{out[3]:g} levels at status {out[0]:g}")
    rs = runs_of(out)
    if any(r[2] not in (0, 1) for r in rs):
        fails.append("a label other than 0 or 1")
    if any(not (c.t0 <= r[0] <= r[1] <= c.t1) for r in rs):
        fails.append("a run outside the window")
    for a, b in zip(rs, rs[1:]):
        if not (a[0] < b[0] and a[1] <= b[0]):
            fails.append(f"runs out of order at {a[0]:.6f}")
            break
        if a[2] == b[2] and a[1] >= b[0]:
            fails.append(f"two runs labeled {a[2]} touch at {a[1]:.6f}")
            break
    if k > c.cap:
        fails.append(f"{k} runs above the cap")
    if t is None:
        t = samples(c)
    targets = [None] + shifts(c)
    for shift in targets:
        if cls is not None and shift is None:
            holds, g1, g2, unsure = cls
        else:
            holds, g1, g2, unsure = classify(c, t, shift)
        ok = np.ones(len(t), dtype=bool)
        ok[unsure] = False
        info["unsure"] += len(unsure)
        tag = "" if shift is None else " (displaced)"
        inrun = member(rs, t)
        in1 = member(rs, t, 1)
        miss = np.nonzero(ok & holds & ~inrun)[0]
        if len(miss):
            fails.append(f"{len(miss)} samples of the condition in no run{tag}, first "
                         f"{t[miss[0]]:.6f}")
        wrong = np.nonzero(ok & ~holds & in1)[0]
        if len(wrong):
            fails.append(f"{len(wrong)} samples without the condition in a run labeled 1{tag}, "
                         f"first {t[wrong[0]]:.6f}")
        change = np.nonzero(holds[:-1] != holds[1:])[0]
        for i in change:
            if not (ok[i] and ok[i + 1]):
                continue
            yes, no = refine(c, float(t[i]), float(t[i + 1]), bool(holds[i]), shift)
            info["crossings"] += 1
            if shift is None:
                info.setdefault("refined", []).append((yes, no))
            if not member(rs, np.array([yes]))[0]:
                fails.append(f"crossing {yes:.10f} in no run{tag}")
            if member(rs, np.array([no]), 1)[0]:
                fails.append(f"crossing {no:.10f} inside a run labeled 1{tag}")
        if shift is None and out[0] == 0.0 and c.levels >= 18:
            l1, l2, w1, w2 = rates(c)
            w = max((c.t1 - c.t0) / 2.0 ** c.levels, 1e-9)
            m1 = l1 * w * 1e-6 + 1e-9
            m2 = l2 * w * 1e-6 + 1e-9
            deep = ok & (g1 + l1 * w + w1 < -m1) & (g2 + l2 * w + w2 < -m2)
            bad = np.nonzero(deep & ~in1)[0]
            if len(bad):
                fails.append(f"{len(bad)} samples deep in the condition outside runs labeled 1, "
                             f"first {t[bad[0]]:.6f}")
            far = np.nonzero(ok & inrun & ((g1 > l1 * w + w1 + m1) | (g2 > l2 * w + w2 + m2)))[0]
            if len(far):
                fails.append(f"{len(far)} samples in runs beyond L w + w, first {t[far[0]]:.6f}")
    return fails, info


def mutations(c: Case, out: list[float], t: np.ndarray, cls, info) -> list[tuple[str, list[float]]]:
    """Altered outputs, each of them wrong, that the check must reject."""
    holds = cls[0]
    rs = runs_of(out)
    head = out[:4]
    refined = info.get("refined", [])
    muts: list[tuple[str, list[float]]] = []

    def pack(runs):
        flat = [x for r in runs for x in (r[0], r[1], float(r[2]))]
        return [head[0], float(len(runs)), head[2], head[3]] + flat

    if holds.any() and rs:
        counts = [int(np.sum(holds & member([r], t))) for r in rs]
        j = int(np.argmax(counts))
        if counts[j] > 0:
            muts.append(("run removed", pack(rs[:j] + rs[j + 1:])))
    for yes, _ in refined:
        hit = [j for j, r in enumerate(rs) if r[0] <= yes <= r[1]]
        if hit and yes < rs[hit[0]][1]:
            j = hit[0]
            lo, hi, lab = rs[j]
            moved = float(np.nextafter(yes, math.inf))
            muts.append(("start moved past a time of the condition",
                         pack(rs[:j] + [(moved, hi, lab)] + rs[j + 1:])))
            break
    for _, no in refined:
        hit = [j for j, r in enumerate(rs) if r[0] <= no <= r[1] and r[2] == 0]
        if hit:
            j = hit[0]
            lo, hi, _ = rs[j]
            muts.append(("label 1 on a run that holds a time without the condition",
                         pack(rs[:j] + [(lo, hi, 1)] + rs[j + 1:])))
            break
    muts.append(("status 2", [2.0, 0.0, 0.0, 0.0]))
    if not holds.all():
        muts.append(("whole window labeled 1", pack([(c.t0, c.t1, 1)])))
    if out[0] == 0.0 and c.levels >= 18 and (~holds).any():
        muts.append(("whole window labeled 0", pack([(c.t0, c.t1, 0)])))
    return muts


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    module = sys.argv[1]
    mutate = "--mutate" in sys.argv
    cost = "--cost" in sys.argv
    cs = cases()
    if cost:
        res = run(module, cs, 9)
        print(f"{'case':54} {'K':>5} {'tests':>8} {'ms':>9}")
        for c, r in zip(cs, res):
            o = r["out"]
            if c.invalid:
                continue
            print(f"{c.name:54} {int(o[1]):5d} {int(o[2]):8d} {r['ms']:9.2f}")
        return 0
    res = run(module, cs)
    failed = 0
    caught = 0
    tried = 0
    unsure = 0
    for c, r in zip(cs, res):
        o = r["out"]
        t = samples(c) if not c.invalid else None
        cls = classify(c, t) if not c.invalid else None
        fails, info = check(c, o, t, cls)
        unsure += info["unsure"]
        status = "ok" if not fails else "FAIL"
        if fails:
            failed += 1
        summary = (f"status {int(o[0])} K {int(o[1])} tests {int(o[2])} levels {int(o[3])}"
                   if len(o) >= 4 else str(o))
        print(f"{status:4} {c.name:54} {summary} crossings {info['crossings']} "
              f"unsure {info['unsure']}")
        for f in fails:
            print(f"     {f}")
        if mutate and not c.invalid and not fails:
            for name, m in mutations(c, o, t, cls, info):
                tried += 1
                mf, _ = check(c, m, t, cls)
                if mf:
                    caught += 1
                else:
                    failed += 1
                    print(f"     mutation passed: {name}")
    valid = sum(1 for c in cs if not c.invalid)
    print(f"{len(cs)} cases, {valid} valid and {len(cs) - valid} invalid; {failed} failures; "
          f"{unsure} inconclusive samples")
    if mutate:
        print(f"mutations: {caught} of {tried} rejected")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
