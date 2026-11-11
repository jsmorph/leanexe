# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0", "numpy==2.5.3"]
# ///
"""Tests the screening module against dense sampling of the two-body model.

The script builds the cases of `cases()`, runs the export `screen` of the WebAssembly module on
each with `tests/screening/screen.mjs` under Node, and checks every output against an oracle
written apart from the program.  The oracle propagates both Kepler orbits with its own solver of
Kepler's equation, in binary64 for dense sampling and in mpmath at 30 digits for refinement.

For each output it checks the claims of the requirements, with T = D + P:
  - status 4 exactly for the invalid inputs;
  - status 1 and 2: the sampled separation over the window, the refined minima, and the window's
    ends stay above T, and the least distance between the two paths, from a grid of eccentric
    anomalies refined by golden-section search, exceeds T; for status 1 the perigee radius of one
    orbit also exceeds the apogee radius of the other by more than T;
  - status 0 and 3: every sampled time with a separation below T, both ends of the window, and
    every refined local minimum below T lie in a returned interval; every interval marked certain
    holds a time with a separation at most T; the intervals number at most C;
  - path verdict 2: the least distance between the paths is at most T.
It also checks that the output follows the method where the margins far exceed rounding:
  - a radial gap above T + 1 km with the apogee-perigee filter on gives status 1;
  - with the orbit-path filter at 20 levels or more and no stop at its cap, paths farther apart
    than T + 1 km give status 2, and paths within T - 1 km give verdict 2;
  - for status 0 after 18 levels or more, every refined minimum below T - 1 km lies in an
    interval marked certain;
  - for status 0, every sampled time in a returned interval has a separation at most T + V w,
    where V is the sum of the speed bounds a n / (1 - e) and w the width of the window over 2 to
    the number of levels.
A sample or a minimum within 1e-6 km of T counts as inconclusive and is reported.  With --mutate,
the script also alters correct outputs (it removes the interval that holds the deepest minimum,
reports status 1 for a close pair, marks certain an interval whose least separation exceeds
T + 1 km, and returns the whole window as one interval when some time of it lies farther than
T + V w + 1 km) and requires the check to fail on each.  It prints one line per
case with the cost of the call, then a summary by kind of case, and exits with status 1 on any
failure.  With --cost, it skips the checks and takes the time of each call as the median of 9
calls.

Usage: uv run tests/screening/oracle.py MODULE [--mutate | --cost]"""
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
STEP = 0.0005
TOL = 1e-6


def bits(x: float) -> str:
    return struct.pack(">d", x).hex()


def unbits(h: str) -> float:
    return struct.unpack(">d", bytes.fromhex(h))[0]


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
    o1: Orbit
    o2: Orbit
    t0: float
    t1: float
    d: float = 5.0
    pad: float = 0.0
    apsides: float = 1.0
    lp: float = 20.0
    cp: float = 65536.0
    levels: float = 20.0
    cap: float = 65536.0
    mu: float = MU
    version: float = 1.0
    invalid: bool = False

    def values(self) -> list[float]:
        o1, o2 = self.o1, self.o2
        return [self.version, o1.a, o1.e, o1.incl, o1.node, o1.argp, o1.m0, o1.epoch,
                o2.a, o2.e, o2.incl, o2.node, o2.argp, o2.m0, o2.epoch, self.mu,
                self.t0, self.t1, self.d, self.pad, self.apsides, self.lp, self.cp,
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


def path_np(o: Orbit, ecc: np.ndarray) -> np.ndarray:
    p, q = frame(o)
    x = o.a * (np.cos(ecc) - o.e)
    y = o.a * math.sqrt(1 - o.e * o.e) * np.sin(ecc)
    return x[:, None] * p[None, :] + y[:, None] * q[None, :]


def position_np(o: Orbit, t: np.ndarray, mu: float) -> np.ndarray:
    m = math.radians(o.m0) + motion(o, mu) * (t - o.epoch)
    return path_np(o, kepler_np(m, o.e))


def separation_np(c: Case, t: np.ndarray) -> np.ndarray:
    return np.linalg.norm(position_np(c.o1, t, c.mu) - position_np(c.o2, t, c.mu), axis=1)


# The model in mpmath, for refinement.

def path_mp(o: Orbit, ecc):
    i, w, n = (mpf(x) * mp.pi / 180 for x in (o.incl, o.argp, o.node))
    p = [mp.cos(w) * mp.cos(n) - mp.sin(w) * mp.sin(n) * mp.cos(i),
         mp.cos(w) * mp.sin(n) + mp.sin(w) * mp.cos(n) * mp.cos(i), mp.sin(w) * mp.sin(i)]
    q = [-mp.sin(w) * mp.cos(n) - mp.cos(w) * mp.sin(n) * mp.cos(i),
         -mp.sin(w) * mp.sin(n) + mp.cos(w) * mp.cos(n) * mp.cos(i), mp.cos(w) * mp.sin(i)]
    a, e = mpf(o.a), mpf(o.e)
    x = a * (mp.cos(ecc) - e)
    y = a * mp.sqrt(1 - e * e) * mp.sin(ecc)
    return [x * p[k] + y * q[k] for k in range(3)]


def kepler_mp(m, e):
    m = m % (2 * mp.pi)
    x = m + e * mp.sin(m) if e < 0.8 else mp.pi
    for _ in range(100):
        dx = (x - e * mp.sin(x) - m) / (1 - e * mp.cos(x))
        x -= dx
        if abs(dx) < mpf(10) ** -28:
            break
    return x


def position_mp(o: Orbit, t, mu: float):
    n = 60 * mp.sqrt(mpf(mu) / mpf(o.a)) / mpf(o.a)
    m = mpf(o.m0) * mp.pi / 180 + n * (mpf(t) - mpf(o.epoch))
    return path_mp(o, kepler_mp(m, mpf(o.e)))


def separation_mp(c: Case, t) -> mpf:
    p1, p2 = position_mp(c.o1, t, c.mu), position_mp(c.o2, t, c.mu)
    return mp.sqrt(sum((p1[k] - p2[k]) ** 2 for k in range(3)))


def golden(f, lo, hi, rounds: int = 80):
    """The minimum of a unimodal function on [lo, hi]: its place and value."""
    lo, hi = mpf(lo), mpf(hi)
    g = (mp.sqrt(5) - 1) / 2
    x1, x2 = hi - g * (hi - lo), lo + g * (hi - lo)
    f1, f2 = f(x1), f(x2)
    for _ in range(rounds):
        if f1 < f2:
            hi, x2, f2 = x2, x1, f1
            x1 = hi - g * (hi - lo)
            f1 = f(x1)
        else:
            lo, x1, f1 = x1, x2, f2
            x2 = lo + g * (hi - lo)
            f2 = f(x2)
    return (x1, f1) if f1 < f2 else (x2, f2)


# Construction of cases.

def state_np(o: Orbit, t: float, mu: float) -> tuple[np.ndarray, np.ndarray]:
    """The position in km and the velocity in km/min at t."""
    n = motion(o, mu)
    ecc = kepler_np(np.array([math.radians(o.m0) + n * (t - o.epoch)]), o.e)[0]
    p, q = frame(o)
    b = math.sqrt(1 - o.e * o.e)
    r = o.a * (math.cos(ecc) - o.e) * p + o.a * b * math.sin(ecc) * q
    rate = n / (1 - o.e * math.cos(ecc))
    v = o.a * rate * (-math.sin(ecc) * p + b * math.cos(ecc) * q)
    return r, v


def elements(r: np.ndarray, v: np.ndarray, t: float, mu: float) -> Orbit:
    """The orbit through position r (km) with velocity v (km/min) at t, for a generic geometry."""
    mum = mu * 3600.0
    h = np.cross(r, v)
    rn, vn = np.linalg.norm(r), np.linalg.norm(v)
    ev = ((vn * vn - mum / rn) * r - np.dot(r, v) * v) / mum
    e = float(np.linalg.norm(ev))
    a = 1.0 / (2.0 / rn - vn * vn / mum)
    incl = math.acos(h[2] / np.linalg.norm(h))
    nv = np.cross([0.0, 0.0, 1.0], h)
    node = math.atan2(nv[1], nv[0])
    nh = nv / np.linalg.norm(nv)
    hh = h / np.linalg.norm(h)
    argp = math.atan2(np.dot(np.cross(nh, ev), hh), np.dot(nh, ev))
    nu = math.atan2(np.dot(np.cross(ev, r), hh) / e, np.dot(ev, r) / e)
    ecc = 2 * math.atan2(math.sqrt(1 - e) * math.sin(nu / 2), math.sqrt(1 + e) * math.cos(nu / 2))
    m = ecc - e * math.sin(ecc)
    return Orbit(a, e, math.degrees(incl), math.degrees(node), math.degrees(argp),
                 math.degrees(m), t)


def rotate(v: np.ndarray, axis: np.ndarray, angle: float) -> np.ndarray:
    k = axis / np.linalg.norm(axis)
    return (v * math.cos(angle) + np.cross(k, v) * math.sin(angle)
            + k * np.dot(k, v) * (1 - math.cos(angle)))


def encounter(rng, o1: Orbit, tc: float, miss: float, angle: float, scale: float) -> Orbit:
    """An orbit whose straight-line approach to o1 at tc misses by `miss` km."""
    r1, v1 = state_np(o1, tc, MU)
    v2 = rotate(v1, r1, angle) * scale
    rel = v2 - v1
    side = np.cross(rel, r1)
    side /= np.linalg.norm(side)
    o2 = elements(r1 + miss * side, v2, tc, MU)
    r2, _ = state_np(o2, tc, MU)
    assert np.linalg.norm(r2 - (r1 + miss * side)) < 1e-6, "construction failed"
    return o2


def leo(rng, e_max: float = 0.02) -> Orbit:
    return Orbit(float(rng.uniform(6700, 7600)), float(rng.uniform(0, e_max)),
                 float(rng.uniform(5, 175)), float(rng.uniform(0, 360)),
                 float(rng.uniform(0, 360)), float(rng.uniform(0, 360)), 0.0)


def cases() -> list[Case]:
    rng = np.random.default_rng(20261111)
    out: list[Case] = []
    for k, factor in enumerate([0.0, 0.1, 0.5, 0.99, 1.01, 2.0, 10.0, 0.3, 0.8, 1.5]):
        o1 = leo(rng)
        if k == 0:
            o1 = replace(o1, e=0.0)
        tc = float(rng.uniform(100, 1340))
        o2 = encounter(rng, o1, tc, 5.0 * factor, math.radians(float(rng.uniform(15, 165))),
                       float(rng.uniform(0.98, 1.02)))
        out.append(Case(f"approach {factor:g} D", "approach", o1, o2, 0.0, 1440.0))
    for k in range(4):
        o1 = leo(rng)
        tc = float(rng.uniform(300, 1100))
        o2 = encounter(rng, o1, tc, 1.0, math.radians(float(rng.uniform(30, 150))), 1.0)
        dt = 2.5 / 600.0
        if k % 2 == 0:
            out.append(Case("ends before the minimum", "end", o1, o2, tc - 600.0, tc - dt))
        else:
            out.append(Case("starts after the minimum", "end", o1, o2, tc + dt, tc + 600.0))
    for k in range(10):
        out.append(Case(f"random LEO {k}", "random", leo(rng), leo(rng), 0.0, 1440.0))
    for k in range(3):
        o1 = leo(rng)
        o2 = replace(o1, incl=o1.incl + 0.01 * (k + 1), m0=o1.m0 + 1.0 + k, a=o1.a + 0.2 * k)
        out.append(Case(f"near-coplanar {k}", "coplanar", o1, o2, 0.0, 1440.0))
    molniya = Orbit(26554.0, 0.72, 63.4, 40.0, 270.0, 10.0, 0.0)
    gto = Orbit(24400.0, 0.73, 7.0, 100.0, 178.0, 200.0, 0.0)
    for k, o in enumerate([molniya, gto]):
        out.append(Case(f"eccentric {k}", "eccentric", o, leo(rng), 0.0, 1440.0))
    o1 = leo(rng)
    tc = 700.0
    o2 = encounter(rng, molniya, tc, 2.0, math.radians(60.0), 1.0)
    out.append(Case("eccentric approach", "eccentric", molniya, o2, 0.0, 1440.0, levels=22.0))
    geo = Orbit(42164.0, 0.0002, 0.05, 80.0, 10.0, 30.0, 0.0)
    out.append(Case("LEO and GEO", "apsides", leo(rng), geo, 0.0, 1440.0))
    out.append(Case("LEO and MEO", "apsides", leo(rng), Orbit(26560.0, 0.01, 55.0, 10.0, 20.0,
                                                               30.0, 0.0), 0.0, 1440.0))
    circ = Orbit(7000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
    polar = Orbit(7000.0, 0.1, 90.0, 0.0, 90.0, 50.0, 0.0)
    out.append(Case("crossing paths 70 km apart", "path", circ, polar, 0.0, 1440.0))
    out.append(Case("same, apsides filter off", "path", circ, polar, 0.0, 1440.0, apsides=0.0))
    out.append(Case("same, path filter off", "path-off", circ, polar, 0.0, 1440.0, lp=0.0))
    o1 = leo(rng)
    o2 = encounter(rng, o1, 700.0, 7.0, math.radians(90.0), 1.0)
    out.append(Case("padding 4 km, miss 7 km", "padding", o1, o2, 0.0, 1440.0, pad=4.0))
    out.append(Case("padding 0, miss 7 km", "padding", o1, o2, 0.0, 1440.0))
    for k in range(3):
        o1 = leo(rng)
        tc = float(rng.uniform(1000, 9000))
        o2 = encounter(rng, o1, tc, 2.0, math.radians(float(rng.uniform(30, 150))), 1.0)
        out.append(Case(f"week {k}", "week", o1, o2, 0.0, 10080.0, levels=23.0))
    o1 = leo(rng)
    o2 = encounter(rng, o1, 700.0, 1.0, math.radians(70.0), 1.0)
    out.append(Case("cap 64", "cap", o1, o2, 0.0, 1440.0, cap=64.0, lp=0.0, apsides=0.0))
    out.append(Case("cap 1", "cap", o1, o2, 0.0, 1440.0, cap=1.0, lp=0.0, apsides=0.0))
    out.append(Case("no levels", "cap", o1, o2, 0.0, 1440.0, levels=0.0, lp=0.0, apsides=0.0))
    out.append(Case("40 levels", "cap", o1, o2, 699.0, 701.0, levels=40.0, lp=0.0,
                    apsides=0.0))
    out.append(Case("path verdict 3", "path", circ, polar, 0.0, 1440.0, lp=4.0))
    out.append(Case("path verdict 4", "path", o1, o2, 0.0, 1440.0, cp=4.0, apsides=0.0))
    huge = Orbit(1e103, 0.1, 30.0, 0.0, 0.0, 0.0, 0.0)
    out.append(Case("rejected enclosures", "reject", huge, huge, 0.0, 1440.0, levels=12.0,
                    cap=4096.0))
    n9 = 60.0 * math.sqrt(MU / 9000.0) / 9000.0
    perigee = Orbit(9000.0, 0.3, 30.0, 40.0, 50.0, math.degrees(-n9 * 720.0), 0.0)
    out.append(Case("head-on at perigee", "eccentric", perigee,
                    encounter(rng, perigee, 720.0, 0.0, math.radians(160.0), 1.0), 0.0, 1440.0))
    circles = (Orbit(7000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0),
               Orbit(7002.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0))
    out.append(Case("circles 2 km apart, D 1, P 3", "padding", *circles, 0.0, 1440.0, d=1.0,
                    pad=3.0))
    out.append(Case("circles 2 km apart, D 1, P 0", "padding", *circles, 0.0, 1440.0, d=1.0))
    polar3 = Orbit(7003.0, 0.0, 90.0, 0.0, 0.0, 40.0, 0.0)
    out.append(Case("paths 3 km apart, D 1, P 3", "padding", circles[0], polar3, 0.0, 1440.0,
                    d=1.0, pad=3.0, apsides=0.0))
    o1 = leo(rng)
    o2 = encounter(rng, o1, 600.0, 3.0, math.radians(100.0), 1.0)
    out.append(Case("miss 3 km, D 1, P 3", "padding", o1, o2, 0.0, 1440.0, d=1.0, pad=3.0))
    o2 = encounter(rng, o1, 600.0, 1.5, math.radians(100.0), 1.0)
    out.append(Case("miss 1.5 km, D 1, 8 levels", "padding", o1, o2, 0.0, 1440.0, d=1.0,
                    levels=8.0))
    base = Case("invalid", "invalid", o1, o2, 0.0, 1440.0, invalid=True)
    out += [replace(base, name="eccentricity 1", o1=replace(o1, e=1.0)),
            replace(base, name="negative axis", o2=replace(o2, a=-7000.0)),
            replace(base, name="reversed window", t0=10.0, t1=5.0),
            replace(base, name="negative threshold", d=-1.0),
            replace(base, name="61 levels", levels=61.0),
            replace(base, name="fractional cap", cap=10.5),
            replace(base, name="version 2", version=2.0),
            replace(base, name="NaN element", o1=replace(o1, incl=math.nan)),
            replace(base, name="infinite epoch", o2=replace(o2, epoch=math.inf)),
            replace(base, name="window beyond 1e9 minutes", t0=-1e308, t1=1e308),
            replace(base, name="cap above 2^20", cap=2.0 ** 20 + 1)]
    return out


# The checks.

@dataclass
class Output:
    status: int
    count: int
    verdict: int
    tests: int
    levels: int
    intervals: list[tuple[float, float, int]]
    ms: float


def parse(line: str) -> Output:
    obj = json.loads(line)
    ys = [unbits(h) for h in obj["out"]]
    ivs = [(ys[5 + 3 * j], ys[6 + 3 * j], int(ys[7 + 3 * j])) for j in range((len(ys) - 5) // 3)]
    return Output(int(ys[0]), int(ys[1]), int(ys[2]), int(ys[3]), int(ys[4]), ivs, obj["ms"])


LAST: dict[str, tuple] = {}


def sampled(c: Case) -> tuple[np.ndarray, np.ndarray]:
    """The samples of the separation over the window, kept for the last case."""
    if "sampled" in LAST and LAST["sampled"][0] == c:
        return LAST["sampled"][1]
    n = int(math.ceil((c.t1 - c.t0) / STEP)) + 1
    ts = np.linspace(c.t0, c.t1, n)
    seps = np.concatenate([separation_np(c, ts[k:k + 1_000_000])
                           for k in range(0, n, 1_000_000)])
    LAST["sampled"] = (c, (ts, seps))
    return ts, seps


def minima(c: Case, ts: np.ndarray, seps: np.ndarray, below: float) -> list[tuple[mpf, mpf]]:
    """The refined local minima of the sampled separation under `below`, and the window ends,
    kept for the last case."""
    if "minima" in LAST and LAST["minima"][0] == (c, below):
        return LAST["minima"][1]
    idx = np.nonzero((seps[1:-1] < seps[:-2]) & (seps[1:-1] <= seps[2:])
                     & (seps[1:-1] < below))[0] + 1
    out = []
    for k in idx:
        out.append(golden(lambda t: separation_mp(c, t), ts[k - 1], ts[k + 1]))
    for t in (c.t0, c.t1):
        out.append((mpf(t), separation_mp(c, t)))
    LAST["minima"] = ((c, below), out)
    return out


def golden_np(f, lo: np.ndarray, hi: np.ndarray, rounds: int = 60) -> np.ndarray:
    """The places of the minima of a vectorized unimodal function on the intervals."""
    g = (math.sqrt(5) - 1) / 2
    for _ in range(rounds):
        x1, x2 = hi - g * (hi - lo), lo + g * (hi - lo)
        left = f(x1) < f(x2)
        hi = np.where(left, x2, hi)
        lo = np.where(left, lo, x1)
    return (lo + hi) / 2


PATHS: dict[tuple, float] = {}


def path_minimum(c: Case) -> float:
    """The least distance between the two paths: a grid of eccentric anomalies, refined by
    alternating golden-section searches from the 24 closest grid pairs."""
    key = (c.o1, c.o2)
    if key in PATHS:
        return PATHS[key]
    grid = np.linspace(0, 2 * np.pi, 1441)[:-1]
    p1, p2 = path_np(c.o1, grid), path_np(c.o2, grid)
    d = np.linalg.norm(p1[:, None, :] - p2[None, :, :], axis=2)
    best = np.argsort(d, axis=None)[:24]
    x, y = grid[best // 1440], grid[best % 1440]
    h = 2 * np.pi / 1440
    for _ in range(40):
        x = golden_np(lambda u: np.linalg.norm(path_np(c.o1, u) - path_np(c.o2, y), axis=1),
                      x - h, x + h)
        y = golden_np(lambda u: np.linalg.norm(path_np(c.o1, x) - path_np(c.o2, u), axis=1),
                      y - h, y + h)
        h *= 0.7
    result = float(np.linalg.norm(path_np(c.o1, x) - path_np(c.o2, y), axis=1).min())
    PATHS[key] = result
    return result


def speed_bound(c: Case) -> float:
    return sum(o.a * motion(o, c.mu) / (1 - o.e) for o in (c.o1, c.o2))


def covered(ivs, t: float) -> bool:
    return any(lo <= t <= hi for lo, hi, _ in ivs)


def check(c: Case, o: Output) -> tuple[list[str], int]:
    """The failures of an output, and the number of inconclusive samples and minima."""
    fails: list[str] = []
    inconclusive = 0
    if c.invalid:
        if o.status != 4:
            fails.append(f"status {o.status} for an invalid input")
        return fails, 0
    if o.status == 4:
        return ["status 4 for a valid input"], 0
    thr = c.d + c.pad
    ts, seps = sampled(c)
    mins = minima(c, ts, seps, thr + 1.0)
    path = path_minimum(c)
    r1 = (c.o1.a * (1 - c.o1.e), c.o1.a * (1 + c.o1.e))
    r2 = (c.o2.a * (1 - c.o2.e), c.o2.a * (1 + c.o2.e))
    gap = max(r2[0] - r1[1], r1[0] - r2[1])
    if c.apsides == 1.0 and gap > thr + 1.0 and o.status != 1:
        fails.append(f"status {o.status} for a radial gap of {gap:.3f} km")
    if o.status != 1 and c.lp >= 20 and o.verdict != 4:
        if path > thr + 1.0 and o.status != 2:
            fails.append(f"status {o.status} for paths {path:.3f} km apart")
        if path < thr - 1.0 and o.verdict != 2:
            fails.append(f"verdict {o.verdict} for paths {path:.3f} km apart")
    if o.status in (1, 2):
        if (seps < thr + TOL).any():
            fails.append(f"status {o.status} with a sampled separation {seps.min():.6f}")
        for t, v in mins:
            if v <= thr + TOL:
                fails.append(f"status {o.status} with a minimum {float(v):.6f} at {float(t):.6f}")
        if path <= thr + TOL:
            fails.append(f"status {o.status} with paths {path:.6f} km apart")
        if o.status == 1 and gap <= thr:
            fails.append("status 1 without a radial gap")
        return fails, 0
    if o.count != len(o.intervals) or o.count > c.cap:
        fails.append(f"{o.count} intervals in the count, {len(o.intervals)} written")
    for k in np.nonzero(seps < thr - TOL)[0]:
        if not covered(o.intervals, float(ts[k])):
            fails.append(f"sample at {ts[k]:.6f} with separation {seps[k]:.6f} not covered")
            break
    inconclusive += int(np.count_nonzero(np.abs(seps - thr) <= TOL))
    for t, v in mins:
        if v < thr - TOL and not covered(o.intervals, float(t)):
            fails.append(f"minimum {float(v):.6f} at {float(t):.6f} not covered")
        elif abs(v - thr) <= TOL:
            inconclusive += 1
        if (o.status == 0 and c.levels >= 18 and v < thr - 1.0 and
                not any(lo <= t <= hi and cert == 1 for lo, hi, cert in o.intervals)):
            fails.append(f"minimum {float(v):.6f} at {float(t):.6f} in no certain interval")
    for lo, hi, certain in o.intervals:
        if certain == 1 and least_in(c, ts, seps, lo, hi) > thr + TOL:
            fails.append(f"certain interval [{lo}, {hi}] without a close approach")
    if o.status == 0:
        slack = speed_bound(c) * (c.t1 - c.t0) / 2 ** o.levels
        inside = np.zeros(len(ts), dtype=bool)
        for lo, hi, _ in o.intervals:
            inside |= (ts >= lo) & (ts <= hi)
        if inside.any() and seps[inside].max() > thr + slack * (1 + 1e-9) + TOL:
            fails.append(f"a returned time has separation {seps[inside].max():.6f}, above "
                         f"T + V w = {thr + slack:.6f}")
    if o.verdict == 2 and path > thr + TOL:
        fails.append("path verdict 2 with paths farther apart than the threshold")
    return fails, inconclusive


def least_in(c: Case, ts: np.ndarray, seps: np.ndarray, lo: float, hi: float) -> float:
    """The least separation in [lo, hi]: the dense samples in it, or 201 points when it holds
    fewer than three samples, refined by golden-section search around the least."""
    inside = np.nonzero((ts >= lo) & (ts <= hi))[0]
    if inside.size >= 3:
        k = int(inside[np.argmin(seps[inside])])
        a, b, best = ts[max(k - 1, inside[0])], ts[min(k + 1, inside[-1])], float(seps[k])
    else:
        inner = np.linspace(lo, hi, 201)
        sep = separation_np(c, inner)
        k = int(np.argmin(sep))
        a, b, best = inner[max(k - 1, 0)], inner[min(k + 1, 200)], float(sep[k])
    _, v = golden(lambda t: separation_mp(c, t), a, b)
    return min(float(v), best)


def mutations(c: Case, o: Output) -> list[tuple[str, Output]]:
    """Altered outputs that a correct check must reject."""
    out = []
    if o.status in (0, 3) and o.intervals:
        ts, seps = sampled(c)
        k = int(np.argmin(seps))
        if seps[k] < c.d + c.pad - TOL:
            kept = [iv for iv in o.intervals if not iv[0] <= ts[k] <= iv[1]]
            out.append(("drop the deepest interval", replace(o, intervals=kept, count=len(kept))))
            out.append(("report status 1", replace(o, status=1, intervals=[], count=0)))
        far = [j for j, (lo, hi, cert) in enumerate(o.intervals)
               if cert == 0 and least_in(c, ts, seps, lo, hi) > c.d + c.pad + 1.0]
        if far:
            ivs = list(o.intervals)
            lo, hi, _ = ivs[far[0]]
            ivs[far[0]] = (lo, hi, 1)
            out.append(("mark a far interval certain", replace(o, intervals=ivs)))
    if o.status == 0 and c.levels >= 4:
        ts, seps = sampled(c)
        slack = speed_bound(c) * (c.t1 - c.t0) / 2 ** o.levels
        if seps.max() > c.d + c.pad + slack + 1.0:
            whole = [(c.t0, c.t1, 0)]
            out.append(("return the whole window", replace(o, intervals=whole, count=1)))
    return out


def main() -> int:
    module = sys.argv[1]
    mutate = "--mutate" in sys.argv[2:]
    cost = "--cost" in sys.argv[2:]
    cs = cases()
    root = Path(__file__).resolve().parents[2]
    lines = "\n".join(json.dumps([bits(x) for x in c.values()]) for c in cs) + "\n"
    run = subprocess.run(["node", str(root / "tests/screening/screen.mjs"), module,
                          "9" if cost else "1"], input=lines, capture_output=True, text=True,
                         check=True)
    outs = [parse(line) for line in run.stdout.splitlines() if line]
    assert len(outs) == len(cs)
    failures = 0
    summary: dict[str, list[Output]] = {}
    for c, o in zip(cs, outs):
        fails, inc = ([], 0) if cost else check(c, o)
        failures += len(fails)
        summary.setdefault(c.kind, []).append(o)
        print(f"{'ok  ' if not fails else 'FAIL'} {c.name}: status {o.status}, verdict "
              f"{o.verdict}, {o.count} intervals ({sum(iv[2] for iv in o.intervals)} certain), "
              f"{o.tests} tests, {o.levels} levels, {o.ms:.1f} ms, {inc} inconclusive")
        for f in fails:
            print(f"     {f}")
        if mutate:
            for what, bad in mutations(c, o):
                caught = bool(check(c, bad)[0])
                failures += 0 if caught else 1
                print(f"     mutation '{what}': {'detected' if caught else 'NOT DETECTED'}")
    print("kind        cases  tests (mean, max)        ms (mean, max)")
    for kind, os in summary.items():
        tests = [o.tests for o in os]
        ms = [o.ms for o in os]
        print(f"{kind:<11} {len(os):>5}  {sum(tests) / len(os):>9.0f} {max(tests):>9}"
              f"  {sum(ms) / len(os):>11.2f} {max(ms):>9.2f}")
    print(f"{failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
