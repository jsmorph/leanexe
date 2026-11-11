# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""The reference test of the orbit-determination programs.

The script runs the case executable, `verified-cases-orbit --gibbs` and `--lambert`, with the
command given on its command line, and checks each result against oracles written apart from the
Lean programs:

* a two-body propagator by the universal-variable form of Kepler's equation at 50 digits, which
  gives the true positions and velocities of elliptic, circular, parabolic, and hyperbolic orbits;
* Izzo's time-of-flight equation and velocity formulas at 50 digits, with the root found by
  bisection;
* a transcription of Izzo's own binary64 implementation of Lambert's problem for zero
  revolutions (pykep's `lambert_problem`), with its initial guess, Householder iterations, and
  its Battin, Lagrange, and Lancaster forms of the time of flight.

Every interval endpoint is compared with the 50-digit value as an exact rational, so a check of
containment has no tolerance.  The script prints the tables of the README and exits with status 1
when a check fails.
"""

import math
import random
import subprocess
import sys

from mpmath import mp, mpf, sqrt, cos, sin, cosh, sinh, acos, acosh, asin, asinh, log, pi, hyp2f1

mp.dps = 50
MU = 398600.4418

# ---------------------------------------------------------------------------------------------
# Vectors and binary64 helpers


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def subv(a, b):
    return [x - y for x, y in zip(a, b)]


def scale(c, a):
    return [c * x for x in a]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def norm(a):
    return sqrt(dot(a, a)) if isinstance(a[0], mpf) else math.sqrt(dot(a, a))


def bits(x):
    return int.from_bytes(__import__("struct").pack(">d", x), "big")


def from_bits(b):
    return __import__("struct").unpack(">d", int(b).to_bytes(8, "big"))[0]


def below(v):
    """The largest double at or below the real `v`."""
    f = float(v)
    while mpf(f) > v:
        f = math.nextafter(f, -math.inf)
    return f


def above(v):
    """The smallest double at or above the real `v`."""
    f = float(v)
    while mpf(f) < v:
        f = math.nextafter(f, math.inf)
    return f


def interval(v, w):
    """Binary64 endpoints of an interval that contains `[v - w, v + w]`."""
    return below(v - w), above(v + w)


# ---------------------------------------------------------------------------------------------
# The universal-variable propagator


def stumpff(z):
    if abs(z) < mpf("0.01"):
        c = s = mpf(0)
        term_c, term_s = mpf(1) / 2, mpf(1) / 6
        for k in range(40):
            c += term_c
            s += term_s
            term_c *= -z / ((2 * k + 3) * (2 * k + 4))
            term_s *= -z / ((2 * k + 4) * (2 * k + 5))
        return c, s
    if z > 0:
        q = sqrt(z)
        return (1 - cos(q)) / z, (q - sin(q)) / q ** 3
    q = sqrt(-z)
    return (cosh(q) - 1) / (-z), (sinh(q) - q) / q ** 3


def propagate(r0, v0, t, mu):
    """The state at time `t` of the two-body orbit through `(r0, v0)`."""
    r0n = norm(r0)
    smu = sqrt(mu)
    sigma0 = dot(r0, v0) / smu
    alpha = 2 / r0n - dot(v0, v0) / mu

    def f(chi):
        c, s = stumpff(alpha * chi * chi)
        return sigma0 * chi * chi * c + (1 - alpha * r0n) * chi ** 3 * s + r0n * chi - smu * t

    lo, hi = mpf(0), mpf(1)
    if t < 0:
        lo, hi = mpf(-1), mpf(0)
        while f(lo) > 0:
            lo *= 2
    else:
        while f(hi) < 0:
            hi *= 2
    for _ in range(400):
        m = (lo + hi) / 2
        if f(m) < 0:
            lo = m
        else:
            hi = m
        if hi - lo < mpf(10) ** (-mp.dps + 3) * max(1, abs(hi)):
            break
    chi = (lo + hi) / 2
    z = alpha * chi * chi
    c, s = stumpff(z)
    fl = 1 - chi * chi / r0n * c
    g = t - chi ** 3 * s / smu
    r = add(scale(fl, r0), scale(g, v0))
    rn = norm(r)
    fdot = smu / (rn * r0n) * (alpha * chi ** 3 * s - chi)
    gdot = 1 - chi * chi / rn * c
    return r, add(scale(fdot, r0), scale(gdot, v0))


# ---------------------------------------------------------------------------------------------
# Izzo's equation at 50 digits


def tof(x, lam):
    if x == 1:
        return mpf(2) / 3 * (1 - lam ** 3)
    y = sqrt(1 - lam ** 2 * (1 - x * x))
    if abs(x - 1) < mpf("0.001"):
        # Battin's form, Izzo's equation (20), which has no cancellation near x = 1.
        eta = y - lam * x
        s1 = (1 - lam - x * eta) / 2
        q = mpf(4) / 3 * hyp2f1(3, 1, mpf(5) / 2, s1)
        return (eta ** 3 * q + 4 * lam * eta) / 2
    if x < 1:
        psi = acos(x * y + lam * (1 - x * x))
        return (psi / sqrt(1 - x * x) - x + lam * y) / (1 - x * x)
    psi = acosh(x * y - lam * (x * x - 1))
    return (psi / sqrt(x * x - 1) - x + lam * y) / (1 - x * x)


def root(lam, T):
    lo = mpf(-1) + mpf(10) ** -40
    hi = mpf(2)
    while tof(hi, lam) > T:
        hi *= 2
    while tof(lo, lam) < T:
        lo = (lo - 1) / 2
    for _ in range(400):
        m = (lo + hi) / 2
        if tof(m, lam) > T:
            lo = m
        else:
            hi = m
        if hi - lo < mpf(10) ** -46:
            break
    return (lo + hi) / 2


def izzo_model(r1, r2, t, mu, k):
    """Izzo's λ, T, root, and velocities at 50 digits, with the direction axis `k`."""
    n1, n2 = norm(r1), norm(r2)
    c = norm(subv(r2, r1))
    s = (n1 + n2 + c) / 2
    w = cross(r1, r2)
    sg = 1 if dot(w, k) > 0 else -1
    lam = sg * sqrt(1 - c / s)
    T = sqrt(2 * mu / s ** 3) * t
    x = root(lam, T)
    y = sqrt(1 - lam ** 2 * (1 - x * x))
    gamma = sqrt(mu * s / 2)
    rho = (n1 - n2) / c
    sigma = sqrt(1 - rho ** 2)
    vr1 = gamma * ((lam * y - x) - rho * (lam * y + x)) / n1
    vr2 = -gamma * ((lam * y - x) + rho * (lam * y + x)) / n2
    vt = gamma * sigma * (y + lam * x)
    hh = scale(sg / norm(w), w)
    v1 = add(scale(vr1 / n1, r1), scale(vt / n1 ** 2, cross(hh, r1)))
    v2 = add(scale(vr2 / n2, r2), scale(vt / n2 ** 2, cross(hh, r2)))
    return lam, T, x, v1, v2


# ---------------------------------------------------------------------------------------------
# Izzo's binary64 implementation (pykep's lambert_problem, zero revolutions)


def izzo_float(r1, r2, tof_s, mu, retrograde=False):
    c = [b - a for a, b in zip(r1, r2)]
    c_n = math.sqrt(dot(c, c))
    R1, R2 = math.sqrt(dot(r1, r1)), math.sqrt(dot(r2, r2))
    s = (c_n + R1 + R2) / 2
    ir1 = [a / R1 for a in r1]
    ir2 = [a / R2 for a in r2]
    ih = cross(ir1, ir2)
    nh = math.sqrt(dot(ih, ih))
    ih = [a / nh for a in ih]
    lambda2 = 1.0 - c_n / s
    lam = math.sqrt(lambda2)
    if ih[2] < 0.0:
        lam = -lam
        it1 = cross(ir1, ih)
        it2 = cross(ir2, ih)
    else:
        it1 = cross(ih, ir1)
        it2 = cross(ih, ir2)
    nt1 = math.sqrt(dot(it1, it1))
    nt2 = math.sqrt(dot(it2, it2))
    it1 = [a / nt1 for a in it1]
    it2 = [a / nt2 for a in it2]
    if retrograde:
        lam = -lam
        it1 = [-a for a in it1]
        it2 = [-a for a in it2]
    lambda3 = lam * lambda2
    T = math.sqrt(2.0 * mu / s ** 3) * tof_s

    def hypergeometric_f(z, tol):
        sj, cj, err, j = 1.0, 1.0, 1.0, 0
        while err > tol:
            cj1 = cj * (3.0 + j) * (1.0 + j) / (2.5 + j) * z / (j + 1)
            sj += cj1
            err = abs(cj1)
            cj = cj1
            j += 1
        return sj

    def x2tof2(x):
        a = 1.0 / (1.0 - x * x)
        if a > 0:
            alfa = 2.0 * math.acos(x)
            beta = 2.0 * math.asin(math.sqrt(lam * lam / a))
            if lam < 0.0:
                beta = -beta
            return a * math.sqrt(a) * ((alfa - math.sin(alfa)) - (beta - math.sin(beta))) / 2.0
        alfa = 2.0 * math.acosh(x)
        beta = 2.0 * math.asinh(math.sqrt(-lam * lam / a))
        if lam < 0.0:
            beta = -beta
        return -a * math.sqrt(-a) * ((beta - math.sinh(beta)) - (alfa - math.sinh(alfa))) / 2.0

    def x2tof(x):
        battin, lagrange = 0.01, 0.2
        dist = abs(x - 1)
        if battin < dist < lagrange:
            return x2tof2(x)
        K = lam * lam
        E = x * x - 1.0
        rho = abs(E)
        z = math.sqrt(1 + K * E)
        if dist < battin:
            eta = z - lam * x
            S1 = 0.5 * (1.0 - lam - x * eta)
            Q = 4.0 / 3.0 * hypergeometric_f(S1, 1e-11)
            return (eta ** 3 * Q + 4.0 * lam * eta) / 2.0
        y = math.sqrt(rho)
        g = x * z - lam * E
        if E < 0:
            d = math.acos(g)
        else:
            f = y * (z - lam * x)
            d = math.log(f + g)
        return (x - lam * z - d / y) / E

    def dtdx(x, t):
        l2 = lam * lam
        l3 = l2 * lam
        umx2 = 1.0 - x * x
        y = math.sqrt(1.0 - l2 * umx2)
        y2 = y * y
        y3 = y2 * y
        d1 = 1.0 / umx2 * (3.0 * t * x - 2.0 + 2.0 * l3 * x / y)
        d2 = 1.0 / umx2 * (3.0 * t + 5.0 * x * d1 + 2.0 * (1.0 - l2) * l3 / y3)
        d3 = 1.0 / umx2 * (7.0 * x * d2 + 8.0 * d1 - 6.0 * (1.0 - l2) * l2 * l3 * x / y3 / y2)
        return d1, d2, d3

    T00 = math.acos(lam) + lam * math.sqrt(1.0 - lambda2)
    T1 = 2.0 / 3.0 * (1.0 - lambda3)
    if T >= T00:
        x0 = -(T - T00) / (T - T00 + 4)
    elif T <= T1:
        x0 = T1 * (T1 - T) / (2.0 / 5.0 * (1 - lambda2 * lambda3) * T) + 1
    else:
        x0 = (T / T00) ** (0.69314718055994529 / math.log(T1 / T00)) - 1.0
    err, it = 1.0, 0
    while err > 1e-5 and it < 15:
        t = x2tof(x0)
        d1, d2, d3 = dtdx(x0, t)
        delta = t - T
        d12 = d1 * d1
        xnew = x0 - delta * (d12 - delta * d2 / 2.0) / (d1 * (d12 - delta * d2) + d3 * delta * delta / 6.0)
        err = abs(x0 - xnew)
        x0 = xnew
        it += 1
    x = x0
    gamma = math.sqrt(mu * s / 2.0)
    rho = (R1 - R2) / c_n
    sigma = math.sqrt(1 - rho * rho)
    y = math.sqrt(1.0 - lambda2 + lambda2 * x * x)
    vr1 = gamma * ((lam * y - x) - rho * (lam * y + x)) / R1
    vr2 = -gamma * ((lam * y - x) + rho * (lam * y + x)) / R2
    vt = gamma * sigma * (y + lam * x)
    v1 = [vr1 * a + vt / R1 * b for a, b in zip(ir1, it1)]
    v2 = [vr2 * a + vt / R2 * b for a, b in zip(ir2, it2)]
    return x, v1, v2


# ---------------------------------------------------------------------------------------------
# Running the Lean programs


def run_lean(command, mode, lines):
    text = "".join(" ".join(str(b) for b in ln) + "\n" for ln in lines)
    out = subprocess.run(command + [mode], input=text, capture_output=True, text=True, check=True)
    results = []
    for row in out.stdout.strip().split("\n"):
        w = [int(v) for v in row.split()]
        status = w[0]
        ivs = [(w[i], from_bits(w[i + 1]), from_bits(w[i + 2])) for i in range(1, len(w), 3)]
        results.append((status, ivs))
    if len(results) != len(lines):
        raise SystemExit(f"fail: {len(lines)} inputs, {len(results)} results")
    return results


def contains(iv, v):
    status, lo, hi = iv
    return status == 0 and mpf(lo) <= v <= mpf(hi)


failures = []


def check(cond, message):
    if not cond:
        failures.append(message)


# ---------------------------------------------------------------------------------------------
# Gibbs


def random_unit(rng):
    while True:
        v = [mpf(rng.uniform(-1, 1)) for _ in range(3)]
        n = norm(v)
        if mpf("0.1") < n < 1:
            return scale(1 / n, v)


def gibbs_float(r1, r2, r3, mu):
    """Curtis's Algorithm 5.1 in binary64."""
    n1, n2, n3 = (math.sqrt(dot(r, r)) for r in (r1, r2, r3))
    c12, c23, c31 = cross(r1, r2), cross(r2, r3), cross(r3, r1)
    N = add(add(scale(n1, c23), scale(n2, c31)), scale(n3, c12))
    D = add(add(c12, c23), c31)
    S = add(add(scale(n2 - n3, r1), scale(n3 - n1, r2)), scale(n1 - n2, r3))
    nn, dn = math.sqrt(dot(N, N)), math.sqrt(dot(D, D))
    f = math.sqrt(mu / (nn * dn))
    return scale(f, add(scale(1 / n2, cross(D, r2)), S))


def orbit_kinds(rng):
    """States `(r0, v0)` of elliptic, circular, equatorial, parabolic, and hyperbolic orbits."""
    mu = mpf(MU)
    out = []
    for kind in ["ellipse", "circle", "equatorial", "parabola", "hyperbola"]:
        for _ in range(4):
            rn = mpf(rng.uniform(6800, 42000))
            u = random_unit(rng)
            if kind == "equatorial":
                u = [u[0], u[1], mpf(0)]
                u = scale(1 / norm(u), u)
            r0 = scale(rn, u)
            pole = random_unit(rng) if kind != "equatorial" else [mpf(0), mpf(0), mpf(1)]
            tdir = cross(pole, u)
            tdir = scale(1 / norm(tdir), tdir)
            vc = sqrt(mu / rn)
            speed = {"ellipse": vc * mpf(rng.uniform(1.05, 1.35)), "circle": vc,
                     "equatorial": vc * mpf("1.2"), "parabola": vc * sqrt(2),
                     "hyperbola": vc * mpf(rng.uniform(1.6, 2.2))}[kind]
            flight = mpf(rng.uniform(-0.3, 0.3)) if kind not in ("circle",) else mpf(0)
            v0 = add(scale(speed * cos(flight), tdir), scale(speed * sin(flight), u))
            out.append((kind, r0, v0, rn))
    return out


def gibbs_tests(command):
    rng = random.Random(20261111)
    mu = mpf(MU)
    lines, meta = [], []
    for kind, r0, v0, rn in orbit_kinds(rng):
        for sep in [1, 5, 20, 60]:
            dt = mpf(sep) * pi / 180 * rn ** mpf(1.5) / sqrt(mu)
            states = [propagate(r0, v0, i * dt, mu) for i in range(3)]
            for w in [0, 1e-12, 1e-9, 1e-6, 1e-3]:
                ends = []
                for r, _ in states:
                    for c in r:
                        ends += interval(c, mpf(w) * norm(r))
                lines.append([bits(e) for e in ends] + [bits(MU), bits(MU)])
                meta.append(("forward", kind, sep, w, states))
    # The positions in reverse order: the formula gives the velocity of the reversed motion.
    for kind, r0, v0, rn in orbit_kinds(random.Random(7))[:8]:
        dt = mpf(20) * pi / 180 * rn ** mpf(1.5) / sqrt(mu)
        states = [propagate(r0, v0, i * dt, mu) for i in range(3)][::-1]
        ends = []
        for r, _ in states:
            for c in r:
                ends += interval(c, mpf(1e-9) * norm(r))
        lines.append([bits(e) for e in ends] + [bits(MU), bits(MU)])
        meta.append(("reverse", kind, 20, 1e-9, states))
    # Collinear positions, non-coplanar positions, and wide boxes slightly off the plane.
    kind, r0, v0, rn = orbit_kinds(random.Random(9))[0]
    dt = mpf(20) * pi / 180 * rn ** mpf(1.5) / sqrt(mu)
    states = [propagate(r0, v0, i * dt, mu) for i in range(3)]
    normal = cross(states[0][0], states[1][0])
    normal = scale(1 / norm(normal), normal)
    for label, offset, w in [("off-plane", mpf(100), 1e-9), ("near-plane", mpf(1), 1e-3)]:
        ends = []
        for i, (r, _) in enumerate(states):
            rr = add(r, scale(offset * (1 if i == 2 else 0), normal))
            for c in rr:
                ends += interval(c, mpf(w) * norm(r))
        lines.append([bits(e) for e in ends] + [bits(MU), bits(MU)])
        meta.append((label, kind, 20, w, states))
    col = [[mpf(7000), mpf(0), mpf(0)], [mpf(8000), mpf(0), mpf(0)], [mpf(9000), mpf(0), mpf(0)]]
    lines.append([bits(float(c)) for r in col for c in r for _ in range(2)] + [bits(MU), bits(MU)])
    meta.append(("collinear", "line", 0, 0, None))

    results = run_lean(command, "--gibbs", lines)
    worst_ratio = [0.0]
    table = {}
    counts = {}
    for (label, kind, sep, w, states), (status, ivs) in zip(meta, results):
        counts[(label, status)] = counts.get((label, status), 0) + 1
        if label == "forward":
            if status == 0:
                v2 = states[1][1]
                ok = all(contains(iv, v) for iv, v in zip(ivs, v2))
                check(ok, f"gibbs {kind} sep {sep} w {w}: velocity outside the box")
                rel = max((mpf(hi) - mpf(lo)) / 2 for _, lo, hi in ivs) / norm(v2)
                table.setdefault((sep, w), []).append(rel)
                ratio = rel * (sep * math.pi / 180) ** 3 / max(w, 2.0 ** -52)
                worst_ratio[0] = max(worst_ratio[0], float(ratio))
                check(ratio <= 300, f"gibbs {kind} sep {sep} w {w}: half-width {float(rel):.2e}")
                if w == 0 and sep >= 20:
                    vf = gibbs_float(*[[float(c) for c in r] for r, _ in states], MU)
                    check(norm(subv([mpf(c) for c in vf], v2)) / norm(v2) < 1e-8,
                          f"gibbs binary64 formula {kind} sep {sep}")
            else:
                table.setdefault((sep, w), []).append(None)
                check(w >= 1e-6 or (w >= 1e-9 and sep == 1),
                      f"gibbs {kind} sep {sep} w {w}: status {status}")
        elif label == "reverse":
            check(status == 0 and all(contains(iv, -v) for iv, v in zip(ivs, states[1][1])),
                  f"gibbs reverse {kind}: status {status} or no -v(r2)")
        elif label == "off-plane":
            check(status == 1, f"gibbs off-plane: status {status}, expected 1")
        elif label == "near-plane":
            check(status != 1, f"gibbs near-plane: status 1 for boxes that reach the plane")
        elif label == "collinear":
            check(status == 2, f"gibbs collinear: status {status}, expected 2")
    print("Gibbs: median relative half-width of the velocity box (status 2 counted as s2)")
    print("| Separation | " + " | ".join(f"w = {w:g}" for w in [0, 1e-12, 1e-9, 1e-6, 1e-3]) + " |")
    print("|---|" + "---|" * 5)
    for sep in [1, 5, 20, 60]:
        cells = []
        for w in [0, 1e-12, 1e-9, 1e-6, 1e-3]:
            vals = table.get((sep, w), [])
            ok = sorted(v for v in vals if v is not None)
            n2 = sum(1 for v in vals if v is None)
            cell = f"{float(ok[len(ok) // 2]):.1e}" if ok else "-"
            if n2:
                cell += f" (s2 in {n2})"
            cells.append(cell)
        print(f"| {sep}° | " + " | ".join(cells) + " |")
    print("Gibbs statuses:", {f"{k[0]}:{k[1]}": v for k, v in sorted(counts.items())})
    print(f"Gibbs: largest half-width times separation cubed over box width: {worst_ratio[0]:.1f}")


# ---------------------------------------------------------------------------------------------
# Lambert


def lambert_line(r1b, r2b, tb, mub, k):
    ends = []
    for lo, hi in r1b + r2b + [tb, mub]:
        ends += [lo, hi]
    return [bits(e) for e in ends] + [bits(c) for c in k]


def box_corners(boxes, rng, count):
    """The center and `count` random corners of a list of intervals."""
    center = [(mpf(lo) + mpf(hi)) / 2 for lo, hi in boxes]
    pts = [center]
    for _ in range(count):
        pts.append([mpf(lo) if rng.random() < 0.5 else mpf(hi) for lo, hi in boxes])
    return pts


def lambert_tests(command):
    rng = random.Random(11112026)
    mu = mpf(MU)
    lines, meta = [], []
    z = [0.0, 0.0, 1.0]
    for theta in [5, 45, 90, 135, 175, 185, 225, 270, 315, 355]:
        for ratio in [1.0, 1.6, 3.0]:
            for Tstar in [0.05, 0.4, 1.2, 3.0, 20.0, 1e3]:
                for w in [0.0, 1e-9, 1e-6]:
                    n1 = rng.uniform(6800, 20000)
                    pole = random_unit(rng)
                    if pole[2] < 0:
                        pole = scale(-1, pole)
                    u1 = random_unit(rng)
                    u1 = subv(u1, scale(dot(u1, pole), pole))
                    u1 = scale(1 / norm(u1), u1)
                    v1d = cross(pole, u1)
                    th = mpf(theta) * pi / 180
                    r1 = [float(c) for c in scale(n1, u1)]
                    r2 = [float(c) for c in scale(n1 * ratio, add(scale(cos(th), u1),
                                                                   scale(sin(th), v1d)))]
                    # the axis: z for some cases, a tilted axis with the same sign as the pole
                    # for others, and an axis whose z component has the opposite sign
                    choice = rng.randrange(3)
                    if choice == 0:
                        k = z
                    elif choice == 1:
                        k = [float(c) for c in add(pole, scale(mpf("0.3"), random_unit(rng)))]
                    else:
                        k = [float(c) for c in add(scale(mpf(1), pole),
                                                     [mpf(0), mpf(0), -2 * pole[2] - mpf("0.5")])]
                    r1m = [mpf(c) for c in r1]
                    r2m = [mpf(c) for c in r2]
                    s = (norm(r1m) + norm(r2m) + norm(subv(r2m, r1m))) / 2
                    t = float(mpf(Tstar) / sqrt(2 * mu / s ** 3))
                    r1b = [interval(mpf(c), mpf(w) * norm(r1m)) for c in r1]
                    r2b = [interval(mpf(c), mpf(w) * norm(r2m)) for c in r2]
                    tb = interval(mpf(t), mpf(w) * abs(mpf(t)))
                    mub = (MU, MU)
                    lines.append(lambert_line(r1b, r2b, tb, mub, k))
                    meta.append(("grid", theta, ratio, Tstar, w, r1b, r2b, tb, mub, k, r1, r2, t))
    # Excluded geometries and invalid inputs.
    special = [
        ("angle pi", [7000.0, 0, 0], [-7000.0, 0, 0], 2700.0, z, 2),
        ("plane holds k", [7000.0, 0, 0], [0, 7500.0, 0], 2700.0, [1.0, 0, 0], 2),
        ("long time", [7000.0, 0, 0], [0, 7500.0, 0],
         4e23 / math.sqrt(2 * MU / ((7000.0 + 7500.0 + math.hypot(7000.0, 7500.0)) / 2) ** 3), z, 3),
        ("negative time", [7000.0, 0, 0], [0, 7500.0, 0], -1.0, z, 1),
    ]
    for label, r1, r2, t, k, expected in special:
        lines.append(lambert_line([(c, c) for c in r1], [(c, c) for c in r2], (t, t), (MU, MU), k))
        meta.append(("special", label, expected))

    results = run_lean(command, "--lambert", lines)
    widths = {}
    statuses = {}
    worst_izzo = 0.0
    worst_prop = mpf(0)
    for m, (status, ivs) in zip(meta, results):
        if m[0] == "special":
            check(status == m[2], f"lambert {m[1]}: status {status}, expected {m[2]}")
            continue
        _, theta, ratio, Tstar, w, r1b, r2b, tb, mub, k, r1, r2, t = m
        statuses[status] = statuses.get(status, 0) + 1
        if status != 0:
            check(w > 0 and (abs(theta - 180) <= 5 or Tstar >= 1e3 or theta in (5, 355)),
                  f"lambert theta {theta} ratio {ratio} T {Tstar} w {w}: status {status}")
            continue
        boxes = r1b + r2b + [tb, mub]
        km = [mpf(c) for c in k]
        for pt in box_corners(boxes, rng, 4 if w > 0 else 0):
            pr1, pr2, pt_, pmu = pt[0:3], pt[3:6], pt[6], pt[7]
            lam, T, x, v1, v2 = izzo_model(pr1, pr2, pt_, pmu, km)
            check(contains(ivs[0], x), f"lambert theta {theta} T {Tstar} w {w}: x outside")
            check(all(contains(iv, v) for iv, v in zip(ivs[1:4], v1)),
                  f"lambert theta {theta} T {Tstar} w {w}: v1 outside")
            check(all(contains(iv, v) for iv, v in zip(ivs[4:7], v2)),
                  f"lambert theta {theta} T {Tstar} w {w}: v2 outside")
        lam, T, x, v1, v2 = izzo_model([mpf(c) for c in r1], [mpf(c) for c in r2], mpf(t), mu, km)
        # the premise: the 50-digit solution reaches r2 at time t with v2, in the direction of k
        if Tstar <= 20:
            pr, pv = propagate([mpf(c) for c in r1], v1, mpf(t), mu)
            perr = max(norm(subv(pr, [mpf(c) for c in r2])) / norm(pr), norm(subv(pv, v2)) / norm(v2))
            worst_prop = max(worst_prop, perr)
            check(perr < mpf(10) ** -30, f"lambert premise theta {theta} T {Tstar}: {perr}")
            check(dot(cross([mpf(c) for c in r1], v1), km) > 0, f"lambert h.k theta {theta}")
        lo, hi = mpf(ivs[0][1]), mpf(ivs[0][2])
        rel = (hi - lo) / max(1, abs(x))
        key = "near 1" if abs(x - 1) < mpf("0.01") else "other"
        widths.setdefault((w, key), []).append(rel)
        if w == 0 and key == "other":
            check(rel <= 1e-11, f"lambert theta {theta} T {Tstar}: x width {float(rel):.2e} "
                  f"r1 {r1} r2 {r2} t {t!r} k {k} x {float(x)} lambda {float(lam)}")
        if w == 0 and k == z and abs(theta - 180) > 5:
            xf, v1f, v2f = izzo_float(r1, r2, t, MU)
            for iv, v in zip(ivs[1:4] + ivs[4:7], v1f + v2f):
                d = max(mpf(0), mpf(iv[1]) - mpf(v), mpf(v) - mpf(iv[2])) / norm(v1)
                worst_izzo = max(worst_izzo, float(d))
            check(worst_izzo < 1e-8, f"lambert Izzo float theta {theta} T {Tstar}: {worst_izzo:.2e}")
    print("Lambert: statuses of the grid", statuses)
    print("Lambert: largest relative width of the interval of x")
    for (w, key), vals in sorted(widths.items()):
        print(f"  w = {w:g}, x {key}: {float(max(vals)):.1e} over {len(vals)} results")
    print(f"Lambert: largest distance of Izzo's binary64 velocities from the boxes, relative: "
          f"{worst_izzo:.1e}")
    print(f"Lambert: largest relative error of the propagated 50-digit solution: "
          f"{float(worst_prop):.1e}")


def round_trip():
    """States propagated for less than one revolution: the solution of Izzo's equation recovers
    the initial velocity, which tests the uniqueness side of Lambert's theorem."""
    rng = random.Random(4242)
    mu = mpf(MU)
    worst = mpf(0)
    count = 0
    for kind, r0, v0, rn in orbit_kinds(rng) + orbit_kinds(rng) + orbit_kinds(rng):
        h = cross(r0, v0)
        alpha = 2 / norm(r0) - dot(v0, v0) / mu
        if alpha > 0:
            period = 2 * pi / sqrt(mu * alpha ** 3)
            t = period * mpf(rng.uniform(0.05, 0.9))
        else:
            t = rn ** mpf(1.5) / sqrt(mu) * mpf(rng.uniform(0.2, 3))
        r1, v1 = r0, v0
        r2, v2 = propagate(r0, v0, t, mu)
        if abs(dot(cross(r1, r2), h)) < mpf(10) ** -10 * norm(r1) * norm(r2) * norm(h):
            continue
        k = add(scale(1 / norm(h), h), scale(mpf("0.4"), random_unit(rng)))
        if dot(k, h) <= 0:
            continue
        _, _, _, w1, w2 = izzo_model(r1, r2, t, mu, k)
        err = max(norm(subv(w1, v1)) / norm(v1), norm(subv(w2, v2)) / norm(v2))
        worst = max(worst, err)
        count += 1
        check(err < mpf(10) ** -30, f"round trip {kind}: {err}")
    print(f"Lambert round trip: {count} states, largest relative difference {float(worst):.1e}")


def main():
    if len(sys.argv) < 2:
        raise SystemExit("usage: reference.py <command of verified-cases-orbit>")
    command = sys.argv[1:]
    gibbs_tests(command)
    lambert_tests(command)
    round_trip()
    if failures:
        for f in failures[:60]:
            print("fail:", f)
        print(f"fail: {len(failures)} checks")
        sys.exit(1)
    print("all checks passed")


if __name__ == "__main__":
    main()
