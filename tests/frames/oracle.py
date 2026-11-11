# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""The independent oracle of the frames programs, in mpmath at 40 digits.

`inputs` prints the input lines of the containment test, which the case executable's `--serve`
mode reads; `check OUTPUTS` reads the lines that mode prints, each the input line followed by the
result, and checks every result.  Before it checks, the oracle reproduces the values of SOFA's test
suite, as ERFA's `t_erfa_c.c` repeats them, for `iauGmst82`, `iauPom00`, `iauGc2gd`, and
`iauGd2gc`.

The oracle evaluates the formulas of `Demos/Frames/requirements.md` from their sources, apart from
the programs: the sidereal time in the form of the function `gstime` of AIAA 2006-6753, with
`T = (JD - 2451545)/36525` from the Julian date `2400000.5 + d + s/86400` of UT1; the rotations of
SOFA's `iauRx`, `iauRy`, and `iauRz`; the position of geodetic coordinates on WGS 84; and the
geodetic coordinates of a point by the fixed-point iteration `phi = atan2(z + e^2 N sin phi, p)`,
the longitude by `atan2`, and the height by `p/cos phi - N` or `z/sin phi - N (1 - e^2)`.  A result
with status 0 must contain the oracle's value at every sampled point of its arguments' intervals,
an angle up to a whole number of turns, and its width must stay within the bound that each check
states.  A case with an expected status must return it.

Lines, each float as the decimal value of its bit pattern:
  gmst d lo hi                                          -> status lo hi
  teme d slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi -> status, then status lo hi for x, y, z
  cart latlo lathi lonlo lonhi hlo hhi                  -> status, then status lo hi for x, y, z
  geod xlo xhi ylo yhi zlo zhi                          -> status, then status lo hi for lat, lon, h
An input line may end with `expect N`, which the output repeats before the result.
Usage: uv run tests/frames/oracle.py inputs > INPUTS; uv run tests/frames/oracle.py check OUTPUTS
"""
import itertools
import math
import random
import struct
import sys

from mpmath import mp, mpf

mp.dps = 40

ARITY = {"gmst": 3, "teme": 13, "cart": 6, "geod": 6}


def bits(x: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def double(w: str) -> float:
    return struct.unpack("<d", struct.pack("<Q", int(w)))[0]


# ### Sidereal time


def theta(d, s):
    """GMST 1982 in radians, unreduced, at the day d and the seconds s of UT1."""
    jd = mpf("2400000.5") + d + mpf(s) / 86400
    t = (jd - 2451545) / 36525
    sec = (mpf("67310.54841") + (876600 * 3600 + mpf("8640184.812866")) * t
           + mpf("0.093104") * t ** 2 - mpf("6.2e-6") * t ** 3)
    return 2 * mp.pi / 86400 * sec


def reduce(angle):
    return angle - 2 * mp.pi * mp.floor(angle / (2 * mp.pi))


# ### Rotations, as SOFA defines them


def rx(a):
    c, s = mp.cos(a), mp.sin(a)
    return [[1, 0, 0], [0, c, s], [0, -s, c]]


def ry(a):
    c, s = mp.cos(a), mp.sin(a)
    return [[c, 0, -s], [0, 1, 0], [s, 0, c]]


def rz(a):
    c, s = mp.cos(a), mp.sin(a)
    return [[c, s, 0], [-s, c, 0], [0, 0, 1]]


def mul(a, b):
    return [[mp.fsum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def apply(m, v):
    return [mp.fsum(m[i][k] * v[k] for k in range(3)) for i in range(3)]


def earth_fixed(th, xp, yp, r):
    arcsec = mp.pi / 648000
    w = mul(rx(-mpf(yp) * arcsec), ry(-mpf(xp) * arcsec))
    return apply(mul(w, rz(th)), [mpf(c) for c in r])


# ### Geodetic coordinates on WGS 84, in km


A = mpf("6378.137")
F = 1 / mpf("298.257223563")
E2 = F * (2 - F)


def position(lat, lon, h):
    lat, lon, h = mpf(lat), mpf(lon), mpf(h)
    n = A / mp.sqrt(1 - E2 * mp.sin(lat) ** 2)
    return [(n + h) * mp.cos(lat) * mp.cos(lon), (n + h) * mp.cos(lat) * mp.sin(lon),
            (n * (1 - E2) + h) * mp.sin(lat)]


def geodetic(x, y, z):
    """Latitude, longitude, and height of a point off the polar axis and away from the center."""
    x, y, z = mpf(x), mpf(y), mpf(z)
    p = mp.sqrt(x * x + y * y)
    lat = mp.atan2(z, p * (1 - E2))
    for _ in range(400):
        n = A / mp.sqrt(1 - E2 * mp.sin(lat) ** 2)
        new = mp.atan2(z + E2 * n * mp.sin(lat), p)
        if abs(new - lat) < mpf("1e-36"):
            lat = new
            break
        lat = new
    else:
        raise ValueError(f"no convergence at {x}, {y}, {z}")
    n = A / mp.sqrt(1 - E2 * mp.sin(lat) ** 2)
    if abs(lat) < mp.pi / 4:
        h = p / mp.cos(lat) - n
    else:
        h = z / mp.sin(lat) - n * (1 - E2)
    lon = mp.atan2(y, x)
    r = position(lat, lon, h)
    if not (abs(lat) < mp.pi / 2 and n + h > 0 and
            max(abs(r[0] - x), abs(r[1] - y), abs(r[2] - z)) < mpf("1e-20")):
        raise ValueError(f"the iteration left the near side at {x}, {y}, {z}")
    return lat, lon, h


def in_domain(x, y, z) -> bool:
    p = mp.sqrt(mpf(x) ** 2 + mpf(y) ** 2)
    return p > 0 and (p > A * E2 or abs(mpf(z)) > A * E2 / (1 - F))


# ### SOFA's test values


def self_test() -> int:
    failures = 0

    def near(label, got, want, tol):
        nonlocal failures
        if abs(got - mpf(want)) > mpf(tol):
            print(f"FAIL sofa {label}: {mp.nstr(got, 25)}, expected {want}")
            failures += 1

    near("gmst82", reduce(theta(53736, 0)), "1.754174981860675096", "1e-12")
    xp, yp, sp = mpf("2.55060238e-7"), mpf("1.860359247e-6"), mpf("-0.1367174580728891460e-10")
    rpom = mul(mul(rx(-yp), ry(-xp)), rz(sp))
    expected = [["0.9999999999999674721", "-0.1367174580728846989e-10", "0.2550602379999972345e-6"],
                ["0.1414624947957029801e-10", "0.9999999999982695317", "-0.1860359246998866389e-5"],
                ["-0.2550602379741215021e-6", "0.1860359247002414021e-5", "0.9999999999982370039"]]
    for i in range(3):
        for j in range(3):
            near(f"pom00[{i}][{j}]", rpom[i][j], expected[i][j], "1e-16")
    lat, lon, h = geodetic(2000, 3000, 5244)
    near("gc2gd longitude", lon, "0.9827937232473290680", "1e-14")
    near("gc2gd latitude", lat, "0.97160184819075459", "1e-14")
    near("gc2gd height", h * 1000, "331.4172461426059892", "1e-8")
    r = position(-0.5, 3.1, 2.5)
    for i, want in enumerate(["-5599000.5577049947", "233011.67223479203", "-3040909.4706983363"]):
        near(f"gd2gc [{i}]", r[i] * 1000, want, "1e-7")
    print(f"sofa test values: {failures} failures")
    return failures


# ### Inputs


def fl(x: float) -> str:
    return str(bits(x))


def unit(rng):
    u = [rng.gauss(0, 1) for _ in range(3)]
    n = sum(c * c for c in u) ** 0.5
    return [c / n for c in u]


def geod_point(lat, lon, h):
    n = 6378.137 / math.sqrt(1 - 0.0066943799901413165 * math.sin(lat) ** 2)
    return [(n + h) * math.cos(lat) * math.cos(lon), (n + h) * math.cos(lat) * math.sin(lon),
            (n * 0.9933056200098587 + h) * math.sin(lat)]


def inputs() -> None:
    rng = random.Random(20261111)
    out = []
    nan, inf = float("nan"), float("inf")
    # Days from 1900 to 2100, times of day, widths of the interval of UT1, and seconds outside
    # [0, 86400).
    for _ in range(200):
        d = rng.randint(15020, 88069)
        s = rng.uniform(0, 86400)
        w = rng.choice([0.0, 0.0, 1e-6, 1e-3, 0.5])
        out.append(f"gmst {d} {fl(s)} {fl(s + w)}")
    for d, s in [(51544, 43200.0), (51544, 0.0), (53736, 0.0), (0, 0.0), (41317, -3600.0),
                 (60000, 90000.0), (60000, 86399.999999), (4294967295, 0.0), (88069, 1e6)]:
        out.append(f"gmst {d} {fl(s)} {fl(s)}")
    for d, lo, hi, status in [(4294967296, 0.0, 1.0, 1), (60000, 1.0, 0.0, 1), (60000, nan, 1.0, 1),
                              (60000, 0.0, inf, 1), (60000, -1e300, 1e300, 2),
                              (2 ** 63, 0.0, 0.0, 1)]:
        out.append(f"gmst {d} {fl(lo)} {fl(hi)} expect {status}")
    # TEME positions of low, navigation, and geostationary orbits, polar motion under 1
    # arcsecond, and boxes.
    for _ in range(150):
        d = rng.randint(41317, 66000)
        s = rng.uniform(0, 86400)
        sw = rng.choice([0.0, 1e-3])
        xp, yp = rng.uniform(-0.5, 0.5), rng.uniform(-0.5, 0.5)
        pw = rng.choice([0.0, 1e-4])
        radius = rng.choice([6600.0, 7000.0, 26560.0, 42164.0])
        r = [radius * c for c in unit(rng)]
        rw = rng.choice([0.0, 0.0, 1e-3, 1.0])
        args = [fl(s), fl(s + sw), fl(xp), fl(xp + pw), fl(yp), fl(yp + pw)]
        for c in r:
            args += [fl(c), fl(c + rw)]
        out.append(f"teme {d} " + " ".join(args))
    # Polar motion of 10 arcseconds, where the order of the two rotations moves the position by
    # 1.6e-5 km.
    out.append("teme 60000 " + " ".join(fl(a) for a in
                                       [0.0, 0.0, 10.0, 10.0, 10.0, 10.0, 7000.0, 7000.0, 0.0, 0.0,
                                        0.0, 0.0]))
    good = [0.0, 1.0, 0.1, 0.1, 0.3, 0.3, 7000.0, 7000.0, 0.0, 0.0, 0.0, 0.0]
    for i, bad in [(0, nan), (3, inf), (6, 7001.0)]:
        args = list(good)
        args[i] = bad
        out.append("teme 60000 " + " ".join(fl(a) for a in args) + " expect 1")
    out.append("teme 4294967296 " + " ".join(fl(a) for a in good) + " expect 1")
    big = list(good)
    big[6:10] = [-1.7e308, 1.7e308, -1.7e308, 1.7e308]
    out.append("teme 60000 " + " ".join(fl(a) for a in big) + " expect 2")
    # Geodetic coordinates: latitudes uniform on the sphere and near the poles, heights from
    # below the ellipsoid to beyond geostationary orbit, and boxes.
    heights = [-5.0, 0.0, 0.3, 10.0, 400.0, 20000.0, 35786.0]
    for _ in range(150):
        lat = math.asin(rng.uniform(-1, 1))
        lon = rng.uniform(-math.pi, math.pi)
        h = rng.choice(heights)
        w = rng.choice([0.0, 0.0, 1e-9, 1e-5])
        hw = rng.choice([0.0, 1e-3, 1.0])
        out.append("cart " + " ".join(fl(v) for v in
                                      [lat, lat + w, lon, lon + w, h, h + hw]))
    for lat, lon, h in [(math.pi / 2, 0.0, 0.0), (-math.pi / 2, 1.0, 1.0), (0.0, math.pi, 0.0),
                        (2.0, 7.0, -100.0)]:
        out.append("cart " + " ".join(fl(v) for v in [lat, lat, lon, lon, h, h]))
    for args, status in [([nan, 0, 0, 0, 0, 0], 1), ([1, 0, 0, 0, 0, 0], 1),
                         ([0, 0, 0, 0, inf, inf], 1),
                         ([0, 0, 0, 0, 1.7976931348623157e308, 1.7976931348623157e308], 2)]:
        out.append("cart " + " ".join(fl(float(v)) for v in args) + f" expect {status}")
    for _ in range(250):
        lat = math.asin(rng.uniform(-1, 1))
        lon = rng.uniform(-math.pi, math.pi)
        h = rng.choice(heights)
        p = geod_point(lat, lon, h)
        w = rng.choice([0.0, 0.0, 1e-6, 1e-3, 1.0])
        out.append("geod " + " ".join(f"{fl(c)} {fl(c + w)}" for c in p))
    special = [
        geod_point(math.radians(89.999), 0.3, 0.0),   # 0.11 km from the polar axis
        geod_point(math.radians(-89.9999), -2.0, 1.0),
        geod_point(math.radians(89.9), 1.0, 2.0),
        geod_point(0.0, 0.5, 0.0),                      # on the equator
        geod_point(0.0, math.pi, 0.0),                  # on the negative x-axis
        geod_point(1e-9, math.pi - 1e-12, 0.0),
        [6378.137, 0.0, 0.0], [0.0, 6378.137, 0.0], [-6378.137, 0.0, 1.0],
        [50.0, 0.0, 0.0], [0.0, -30.0, 50.0], [20.0, 20.0, -45.0],   # inside D, near the center
        [42.75, 0.0, 5.0],                              # the u-equation with a slope bound of 0.05
        [-7000.0, 0.0, 10.0],                           # x < 0 on the x-axis
        [1.0, 0.0, -42.845],                            # the v-equation below the equator
        [1e-6, 0.0, 6356.0],                            # 1 mm from the polar axis
    ]
    for p in special:
        out.append("geod " + " ".join(f"{fl(c)} {fl(c)}" for c in p))
    boxes = [
        ([6378.0, 6379.0], [-1.0, 1.0], [-1.0, 1.0]),          # equator, straddling z = 0
        ([-6379.0, -6378.0], [-1.0, 1.0], [10.0, 11.0]),       # across the negative x-axis
        ([0.5, 1.0], [0.5, 2.0], [6356.0, 6357.0]),             # near the north pole
        ([-1.0, -0.5], [-2.0, -0.5], [-6357.0, -6356.0]),       # near the south pole
        ([100.0, 101.0], [0.0, 1.0], [6356.0, 6357.0]),
        ([6378.0, 6379.0], [0.0, 1.0], [0.0, 1.0]),
    ]
    for bx, by, bz in boxes:
        out.append("geod " + " ".join(f"{fl(a)} {fl(b)}" for a, b in (bx, by, bz)))
    for args, status in [
            ([30.0, 30.0, 0.0, 0.0, 10.0, 10.0], 3),            # within 42.70 km of the axis and
            ([0.0, 0.0, 0.0, 0.0, 30.0, 30.0], 3),              # 42.85 km of the equator
            ([0.0, 0.0, 0.0, 0.0, 6356.0, 6357.0], 3),          # on the polar axis
            ([-1.0, 1.0, -1.0, 1.0, 6000.0, 6001.0], 3),        # a box that holds the axis
            ([0.0, 0.0, 0.0, 0.0, 0.0, 0.0], 3),
            ([0.0, 0.001, 0.0, 0.0, 6356.0, 6356.0], 3),        # a box that reaches the axis
            # Boxes 1 km wide near the poles across x = 0, whose divisor p + x the intervals do not
            # show above zero.
            ([-1.0, 1.0, 0.5, 2.0, 6356.0, 6357.0], 2),
            ([-1.0, 1.0, -2.0, -0.5, -6357.0, -6356.0], 2),
            ([42.75, 42.75, 0.0, 0.0, 42.80, 42.80], 3),        # in D, outside both tests
            ([1.0, 1.0, 0.0, 0.0, 42.80, 42.80], 3),
            ([nan, 0.0, 0.0, 0.0, 0.0, 0.0], 1),
            ([1.0, 0.0, 0.0, 0.0, 0.0, 0.0], 1),
            ([1e300, 1e300, 0.0, 0.0, 0.0, 0.0], 2)]:
        out.append("geod " + " ".join(fl(v) for v in args) + f" expect {status}")
    print("\n".join(out))


# ### Checks


def contains(lo, hi, x) -> bool:
    return mpf(lo) <= x <= mpf(hi)


def turns(lo, hi, x):
    """x less the whole number of turns that brings it nearest the middle of [lo, hi]."""
    mid = (mpf(lo) + mpf(hi)) / 2
    return x - 2 * mp.pi * mp.floor((x - mid) / (2 * mp.pi) + mpf("0.5"))


def sample(pairs, seed, count=16):
    rng = random.Random(seed)
    points = list(itertools.product(*pairs))
    points += [tuple(rng.uniform(lo, hi) for lo, hi in pairs) for _ in range(count)]
    return points


def results(res, n):
    return [(int(res[1 + 3 * i]), double(res[2 + 3 * i]), double(res[3 + 3 * i])) for i in range(n)]


def check_gmst(a, res):
    d, lo, hi = int(a[0]), double(a[1]), double(a[2])
    status, rlo, rhi = int(res[0]), double(res[1]), double(res[2])
    if status != 0:
        return f"status {status}, expected 0"
    t0, t1 = theta(d, lo), theta(d, hi)
    k = mp.floor(((t0 + t1) / 2 - (mpf(rlo) + mpf(rhi)) / 2) / (2 * mp.pi) + mpf("0.5"))
    for t in (t0, t1):
        if not contains(rlo, rhi, t - 2 * mp.pi * k):
            return f"{mp.nstr(t - 2 * mp.pi * k, 20)} outside [{rlo!r}, {rhi!r}]"
    if 15020 <= d <= 88069 and mpf(rhi) - mpf(rlo) > (t1 - t0) + mpf("1e-11"):
        return f"width {mpf(rhi) - mpf(rlo)} above {t1 - t0} + 1e-11 for a date of 1900 to 2100"
    if not (-1e-9 <= (rlo + rhi) / 2 <= 2 * math.pi + 1e-9 and -1 <= rlo and rhi <= 7):
        return f"[{rlo!r}, {rhi!r}] outside [-1, 7] or its midpoint outside [0, 2 pi]"
    return None


def check_teme(a, res):
    d = int(a[0])
    v = [double(w) for w in a[1:]]
    if int(res[0]) != 0:
        return f"status {res[0]}, expected 0"
    boxes = results(res, 3)
    pairs = [(v[2 * i], v[2 * i + 1]) for i in range(6)]
    for s, xp, yp, x, y, z in sample(pairs, d):
        e = earth_fixed(theta(d, s), xp, yp, (x, y, z))
        for i in range(3):
            st, lo, hi = boxes[i]
            if st != 0 or not contains(lo, hi, e[i]):
                return f"coordinate {i} {mp.nstr(e[i], 20)} outside [{lo!r}, {hi!r}] status {st}"
    if all(lo == hi for lo, hi in pairs):
        bound = 3e-12 * math.sqrt(sum(v[2 * i + 6] ** 2 for i in range(3))) + 1e-9
        for i in range(3):
            if boxes[i][2] - boxes[i][1] > bound:
                return f"width {boxes[i][2] - boxes[i][1]} of a point above {bound} km"
    return None


def check_cart(a, res):
    v = [double(w) for w in a]
    if int(res[0]) != 0:
        return f"status {res[0]}, expected 0"
    boxes = results(res, 3)
    pairs = [(v[2 * i], v[2 * i + 1]) for i in range(3)]
    for lat, lon, h in sample(pairs, bits(v[0])):
        e = position(lat, lon, h)
        for i in range(3):
            st, lo, hi = boxes[i]
            if st != 0 or not contains(lo, hi, e[i]):
                return f"coordinate {i} {mp.nstr(e[i], 20)} outside [{lo!r}, {hi!r}] status {st}"
    if all(lo == hi for lo, hi in pairs):
        for i in range(3):
            if boxes[i][2] - boxes[i][1] > 1e-9:
                return f"width {boxes[i][2] - boxes[i][1]} of a point above 1e-9 km"
    return None


WIDEST = {"lat": 0.0, "lon": 0.0, "h": 0.0}


def check_geod(a, res):
    v = [double(w) for w in a]
    if int(res[0]) != 0:
        return f"status {res[0]}, expected 0"
    (s1, latlo, lathi), (s2, lonlo, lonhi), (s3, hlo, hhi) = results(res, 3)
    if s1 or s2 or s3:
        return "an interval of an accepted result is rejected"
    pairs = [(v[2 * i], v[2 * i + 1]) for i in range(3)]
    lo, hi = (-math.pi, math.pi) if (v[0] + v[1]) / 2 >= 0 else (0.0, 2 * math.pi)
    if not (lo - 1e-9 <= lonlo and lonhi <= hi + 1e-9):
        return f"longitude [{lonlo!r}, {lonhi!r}] outside the range of its formula"
    for x, y, z in sample(pairs, bits(v[0])):
        if not in_domain(x, y, z):
            return f"({x}, {y}, {z}) lies outside D"
        lat, lon, h = geodetic(x, y, z)
        if not contains(latlo, lathi, lat):
            return f"latitude {mp.nstr(lat, 20)} outside [{latlo!r}, {lathi!r}]"
        if not contains(lonlo, lonhi, turns(lonlo, lonhi, lon)):
            return f"longitude {mp.nstr(lon, 20)} outside [{lonlo!r}, {lonhi!r}] modulo 2 pi"
        if not contains(hlo, hhi, h):
            return f"height {mp.nstr(h, 20)} outside [{hlo!r}, {hhi!r}]"
    if all(lo == hi for lo, hi in pairs) and max(math.hypot(v[0], v[2]), abs(v[4])) >= 1000:
        for key, width, bound in [("lat", lathi - latlo, 1e-13), ("lon", lonhi - lonlo, 1e-13),
                                  ("h", hhi - hlo, 1e-9)]:
            WIDEST[key] = max(WIDEST[key], width)
            if width > bound:
                return f"{key} width {width} of a point above {bound}"
    return None


def check(path: str) -> int:
    failures = self_test()
    counts = {}
    checks = {"gmst": check_gmst, "teme": check_teme, "cart": check_cart, "geod": check_geod}
    for line in open(path):
        f = line.split()
        if not f:
            continue
        kind = f[0]
        if kind not in ARITY:
            failures += 1
            print(f"FAIL unknown line: {line.strip()}")
            continue
        args = f[1:1 + ARITY[kind]]
        rest = f[1 + ARITY[kind]:]
        if rest and rest[0] == "expect":
            want, res = int(rest[1]), rest[2:]
            problem = None if int(res[0]) == want else f"status {res[0]}, expected {want}"
        else:
            problem = checks[kind](args, rest)
        counts[kind] = counts.get(kind, 0) + 1
        if problem:
            failures += 1
            print(f"FAIL {line.strip()}: {problem}")
    print(" ".join(f"{k}: {n} cases" for k, n in sorted(counts.items())))
    print("widest geodetic intervals of points: " +
          ", ".join(f"{k} {w:.3g}" for k, w in WIDEST.items()))
    print(f"{failures} failures")
    return 1 if failures else 0


def main() -> int:
    if sys.argv[1:] == ["inputs"]:
        inputs()
        return 0
    if len(sys.argv) == 3 and sys.argv[1] == "check":
        return check(sys.argv[2])
    print(__doc__.split("Usage: ")[1], file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
