# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy==2.5.3"]
# ///
"""Checks the results of Demos.PassiveSafety.check against numerical integration of the
Hill-Clohessy-Wiltshire equations.

Each line of the input, which `verified-cases-passivesafety --bits` prints, holds a case's name,
its expected status and scenario, the number of input values, the bit patterns of the values, the
fuel, the bit pattern of the accuracy, and the result: status, scenario, and the bit patterns of
stop, sep, and rc.  The script

1. compares the closed form of the requirements with a fourth-order Runge-Kutta integration of the
   equations from random states, and fails when they differ by more than 1e-6 of the state's size;
2. fails when a case's status or scenario differs from the expected one;
3. for each accepted case, integrates every scenario from the corners of the box of initial states
   and from random states in it, with velocity changes drawn from the corners and the interiors
   of the burns' boxes, and fails when the least separation over [0, T] falls below `sep`, or the
   least radial and cross-track distance over one period after the scenario's last burn falls
   below `rc`, by more than 1e-6, or when `sep` or `rc` lies below its threshold;
4. for each accepted case, integrates every scenario from the centres of the boxes together with
   the change of the state from each input's half-width, computes at each sample the distance of
   the box that holds each component's values over the boxes, the bound that the program's
   interval at a single time approaches, and fails when the least of these componentwise bounds
   exceeds `sep` or `rc` by more than the accuracy plus SLACK times the componentwise bound, a gap
   that a search that stops at its threshold leaves;
5. for each case rejected with status 3 or 4, integrates the scenario that the result names from
   the same samples and reports whether a sample violates the threshold.

The integration samples each coast every 1/4000 of the orbital period or of the horizon, whichever
is shorter, and integrates again with a step 100 times smaller over the two steps around each
state's least sample.  A sampled minimum is at least the trajectory's minimum, so a bound above
it is wrong.  The script prints, for each case, the bounds, the sampled minima, the componentwise
bounds, and their differences.
Usage: uv run tests/passivesafety/reference.py CASES"""
import math
import struct
import sys

import numpy as np

TOLERANCE = 1e-6
SLACK = 1e-6
SEP = [0, 1, 2]
RC = [0, 2]


def double(bits: str) -> float:
    return struct.unpack("<d", struct.pack("<Q", int(bits)))[0]


def field(n: float, s: np.ndarray) -> np.ndarray:
    x, y, z, vx, vy, vz = s.T
    return np.stack(
        [vx, vy, vz, 3 * n * n * x + 2 * n * vy, -2 * n * vx, -n * n * z], axis=1
    )


def rk4(n: float, s: np.ndarray, h: float) -> np.ndarray:
    k1 = field(n, s)
    k2 = field(n, s + 0.5 * h * k1)
    k3 = field(n, s + 0.5 * h * k2)
    k4 = field(n, s + h * k3)
    return s + (h / 6) * (k1 + 2 * k2 + 2 * k3 + k4)


def closed_form(n: float, t: float, s: np.ndarray) -> np.ndarray:
    x, y, z, vx, vy, vz = s
    p = n * t
    sn, c = math.sin(p), math.cos(p)
    return np.array(
        [
            (4 - 3 * c) * x + sn / n * vx + 2 / n * (1 - c) * vy,
            6 * (sn - p) * x + y - 2 / n * (1 - c) * vx + (4 * sn - 3 * p) / n * vy,
            c * z + sn / n * vz,
            3 * n * sn * x + c * vx + 2 * sn * vy,
            -6 * n * (1 - c) * x - 2 * sn * vx + (4 * c - 3) * vy,
            -n * sn * z + c * vz,
        ]
    )


def model_test(rng: np.random.Generator) -> float:
    """The largest difference between the closed form and the integration, relative to the
    largest component of the closed form's state."""
    worst = 0.0
    for n in (0.0011313, 7.2921e-5):
        period = 2 * math.pi / n
        s0 = rng.normal(size=(20, 6)) * np.array([100, 100, 100, 0.1, 0.1, 0.1])
        t = 3 * period
        steps = 20000
        s = s0.copy()
        for _ in range(steps):
            s = rk4(n, s, t / steps)
        for i in range(len(s0)):
            ref = closed_form(n, t, s0[i])
            worst = max(worst, float(np.max(np.abs(s[i] - ref)) / np.max(np.abs(ref))))
    return worst


def runs(N: int, j: int, k: int) -> bool:
    if j == 0:
        return True
    if j <= N:
        return k + 1 != j
    return k + 1 < j - N


def separation(q: np.ndarray) -> np.ndarray:
    return np.sqrt(q[:, 0] ** 2 + q[:, 1] ** 2 + q[:, 2] ** 2)


def rc_distance(q: np.ndarray) -> np.ndarray:
    return np.sqrt(q[:, 0] ** 2 + q[:, 2] ** 2)


def coast_min(n, s, duration, step, dist):
    """The least of `dist` over a coast of `duration` from the states `s`, and the states at its
    end."""
    best = dist(s)
    if duration <= 0:
        return best, s
    steps = max(1, math.ceil(duration / step))
    h = duration / steps
    start = s.copy()
    first = np.zeros(len(s), dtype=int)
    cur = s
    for k in range(1, steps + 1):
        nxt = rk4(n, cur, h)
        d = dist(nxt)
        better = d < best
        best = np.where(better, d, best)
        start[better] = cur[better]
        first = np.where(better, k - 1, first)
        cur = nxt
    window = np.minimum(2 * h, (steps - first) * h)
    fine = h / 100
    q = start.copy()
    for i in range(1, 201):
        q = rk4(n, q, fine)
        within = i * fine <= window * (1 + 1e-12)
        best = np.where(within, np.minimum(best, dist(q)), best)
    return best, cur


def scenario_minima(n, horizon, burns, executed, s0, dv, step):
    """The least separation over [0, horizon] of each state, and the least radial and
    cross-track distance over one period after the last executed burn."""
    s = s0.copy()
    t = 0.0
    least = np.full(len(s), np.inf)
    for k, (tb, _, _) in enumerate(burns):
        if not executed[k]:
            continue
        m, s = coast_min(n, s, tb - t, step, separation)
        least = np.minimum(least, m)
        t = tb
        s = s.copy()
        s[:, 3:] += dv[:, k, :]
    m, end = coast_min(n, s, horizon - t, step, separation)
    least = np.minimum(least, m)
    rc, _ = coast_min(n, s, 2 * math.pi / n, step, rc_distance)
    return least, rc


def bound_min(n, cols, duration, step, comps):
    """The least componentwise bound over a coast of `duration` from the columns `cols`, and the
    columns at its end.  Row 0 of `cols` is the state from the centres of the boxes, and each other
    row the change of the state from one input's half-width, so that each component ranges over
    row 0 plus or minus the sum of the other rows' magnitudes."""

    def bound(c):
        least = np.maximum(np.abs(c[0, comps]) - np.sum(np.abs(c[1:, comps]), axis=0), 0.0)
        return math.sqrt(float(np.sum(least**2)))

    best = bound(cols)
    if duration <= 0:
        return best, cols
    steps = max(1, math.ceil(duration / step))
    h = duration / steps
    cur, start, first = cols, cols, 0
    for k in range(1, steps + 1):
        nxt = rk4(n, cur, h)
        d = bound(nxt)
        if d < best:
            best, start, first = d, cur, k - 1
        cur = nxt
    window = min(2 * h, (steps - first) * h)
    fine = h / 100
    q = start
    for i in range(1, 201):
        q = rk4(n, q, fine)
        if i * fine <= window * (1 + 1e-12):
            best = min(best, bound(q))
    return best, cur


def componentwise_minima(n, horizon, burns, executed, box_lo, box_hi, step):
    """The least componentwise bound of the separation over [0, horizon], and of the radial and
    cross-track distance over one period after the last executed burn."""
    cols = np.zeros((7 + 3 * len(burns), 6))
    cols[0] = (box_lo + box_hi) / 2
    for i in range(6):
        cols[1 + i, i] = (box_hi[i] - box_lo[i]) / 2
    t = 0.0
    least = math.inf
    for k, (tb, lo, hi) in enumerate(burns):
        if not executed[k]:
            continue
        m, cols = bound_min(n, cols, tb - t, step, SEP)
        least = min(least, m)
        t = tb
        cols = cols.copy()
        cols[0, 3:] += (lo + hi) / 2
        for i in range(3):
            cols[7 + 3 * k + i, 3 + i] = (hi[i] - lo[i]) / 2
    m, _ = bound_min(n, cols, horizon - t, step, SEP)
    least = min(least, m)
    rc, _ = bound_min(n, cols, 2 * math.pi / n, step, RC)
    return least, rc


def corners(lo, hi):
    dim = len(lo)
    return np.array(
        [[hi[i] if mask >> i & 1 else lo[i] for i in range(dim)] for mask in range(2**dim)]
    )


def sample_boxes(box_lo, box_hi, burns, rng):
    """The corners of the box of initial states and 200 random states in it, each with velocity
    changes from the corners of the burns' boxes for even samples and from their interiors for
    odd ones."""
    s0 = np.concatenate([corners(box_lo, box_hi), rng.uniform(box_lo, box_hi, (200, 6))])
    M = len(s0)
    dv = np.zeros((M, len(burns), 3))
    for k, (_, lo, hi) in enumerate(burns):
        c = corners(lo, hi)
        picked = c[rng.integers(0, len(c), size=M)]
        inner = rng.uniform(lo, hi, size=(M, 3))
        dv[:, k, :] = np.where((np.arange(M) % 2 == 0)[:, None], picked, inner)
    return s0, dv


def check_case(name, expected, xs, acc, result, rng):
    status, scenario, stop, sep, rc = result
    n, horizon, dmin, drc = xs[0:4]
    box_lo = np.array(xs[4:16:2])
    box_hi = np.array(xs[5:16:2])
    N = (len(xs) - 16) // 7
    burns = []
    for k in range(N):
        b = xs[16 + 7 * k : 23 + 7 * k]
        burns.append((b[0], np.array(b[1:7:2]), np.array(b[2:7:2])))
    line = f"{name} expected {expected[0]} at {expected[1]}, status {status} at {scenario}"
    if (status, scenario) != expected:
        print(f"FAIL {line}")
        return False
    if status not in (0, 3, 4):
        print(f"ok   {line} stop {stop:.6g}")
        return True
    period = 2 * math.pi / n
    step = min(period, horizon) / 4000
    s0, dv = sample_boxes(box_lo, box_hi, burns, rng)
    if status == 0:
        least_sep = math.inf
        least_rc = math.inf
        comp_sep = math.inf
        comp_rc = math.inf
        for j in range(2 * N + 1):
            executed = [runs(N, j, k) for k in range(N)]
            m, r = scenario_minima(n, horizon, burns, executed, s0, dv, step)
            least_sep = min(least_sep, float(np.min(m)))
            least_rc = min(least_rc, float(np.min(r)))
            cs, cr = componentwise_minima(n, horizon, burns, executed, box_lo, box_hi, step)
            comp_sep = min(comp_sep, cs)
            comp_rc = min(comp_rc, cr)
        sound = (least_sep >= sep - TOLERANCE and least_rc >= rc - TOLERANCE and
                 sep >= dmin and rc >= drc)
        close = (comp_sep - sep <= acc + SLACK * max(1.0, comp_sep) and
                 comp_rc - rc <= acc + SLACK * max(1.0, comp_rc))
        ok = sound and close
        print(
            f"{'ok  ' if ok else 'FAIL'} {line} acc {acc:.3g} sep {sep:.6g} sampled "
            f"{least_sep:.6g} componentwise {comp_sep:.6g} rc {rc:.6g} sampled {least_rc:.6g} "
            f"componentwise {comp_rc:.6g}, excess over acc {comp_sep - sep - acc:.3g} and "
            f"{comp_rc - rc - acc:.3g}{'' if close else ' (gap above the accuracy)'}"
        )
        return ok
    executed = [runs(N, scenario, k) for k in range(N)]
    m, r = scenario_minima(n, horizon, burns, executed, s0, dv, step)
    if status == 3:
        least, threshold, what = float(np.min(m)), dmin, "separation"
    else:
        least, threshold, what = float(np.min(r)), drc, "radial and cross-track distance"
    verdict = "a sample violates it" if least < threshold else "no sample violates it"
    print(f"ok   {line} stop {stop:.6g} least sampled {what} {least:.6g}, threshold "
          f"{threshold:g}: {verdict}")
    return True


def main() -> int:
    rng = np.random.default_rng(20261111)
    worst = model_test(rng)
    failures = 0 if worst < 1e-6 else 1
    print(f"{'ok  ' if worst < 1e-6 else 'FAIL'} closed form against integration: "
          f"largest relative difference {worst:.3g}")
    for line in open(sys.argv[1]):
        f = line.split()
        if not f:
            continue
        name, expected, count = f[0], (int(f[1]), int(f[2])), int(f[3])
        xs = [double(b) for b in f[4 : 4 + count]]
        acc = double(f[5 + count])
        status, scenario = int(f[6 + count]), int(f[7 + count])
        stop, sep, rc = (double(b) for b in f[8 + count : 11 + count])
        if not check_case(name, expected, xs, acc, (status, scenario, stop, sep, rc), rng):
            failures += 1
    print(f"{failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
