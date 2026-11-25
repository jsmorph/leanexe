# /// script
# requires-python = ">=3.12"
# dependencies = ["matplotlib==3.11.2"]
# ///
"""Draws the containment test of the conjunction program from REPORT, the report of
tests/conjunction/reference.py that tests/conjunction/run.sh writes to
build/conjunction/reference.txt.  For each input of `pc` and each of 16, 256, and 4,096 panels, a
bar runs from (lo - ref)/ref to (hi - ref)/ref, the relative errors of the interval's ends, where
ref is the reference value that reference.py computes at 50 digits.  A bar that crosses or touches
the line at 0 shows an interval that contains the reference value.

The rows hold the inputs in decreasing order of the reference value, and inputs with equal
reference values in their order in REPORT, with the bars of each row in increasing order of the
panel count.  The table gives each input and its reference value to two significant digits.  The
script computes each relative error from REPORT's decimals as an exact fraction, since some values
lie below the smallest positive double, so a lower endpoint of 0 gives exactly -1.  The axis is
symmetric-logarithmic, linear within the threshold, the largest power of ten at or below the
smallest nonzero relative error, so every nonzero end lies in the logarithmic part.  It runs from
-2 to 2: a lower end is at least -1, since the program's lower endpoints are at least 0, and an
end beyond 2 is drawn as an arrow at the axis's edge with its value written beside it.  The
format of OUT, SVG or PNG, follows its extension.  The exit status is 0 when the figure is drawn,
1 when a result is rejected or a reference value lies outside its interval, and 2 for a usage
error.

Usage: uv run tests/conjunction/figure.py REPORT OUT
"""

import math
import re
import sys
from fractions import Fraction

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

matplotlib.rcParams["svg.hashsalt"] = "conjunction-figure"

INK, MUTED, GRID = "#111111", "#555555", "#dddddd"
PANELS = {16: "#d55e00", 256: "#0072b2", 4096: "#009e73"}
DODGE = {16: -0.28, 256: 0.0, 4096: 0.28}
BAR, LIMIT = 0.22, 2

LINE = re.compile(r"(ok  |FAIL) m=\((\S+),(\S+)\) C=\((\S+),(\S+),(\S+)\) r=(\S+) n=(\d+) "
                  r"status=(\d+) ref=(\S+) lo=(\S+) hi=(\S+) width=\S+")

W, ROW, TOP, BOTTOM = 7.3, 0.36, 1.1, 0.6
TABLE = [0.1, 0.88, 1.33, 3.0]
LEFT, RIGHT = 3.95, 6.55


def read(path):
    """The inputs in REPORT's order, each with its reference value and its interval at each
    panel count, and the lines that fail the containment."""
    cases, failures = {}, []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            match = LINE.fullmatch(line)
            if not match:
                if not re.fullmatch(r"\d+ failures", line):
                    raise ValueError(f"{path}: unknown line {line}")
                continue
            tag, *inputs, n, status, ref, lo, hi = match.groups()
            ref, lo, hi = Fraction(ref), Fraction(lo), Fraction(hi)
            if tag != "ok  " or status != "0" or not lo <= ref <= hi:
                failures.append(line)
            case = cases.setdefault(tuple(inputs), {"ref": ref, "intervals": {}})
            if case["ref"] != ref:
                raise ValueError(f"{path}: two reference values for {inputs}")
            case["intervals"][int(n)] = (lo, hi)
    for inputs, case in cases.items():
        if set(case["intervals"]) != set(PANELS):
            raise ValueError(f"{path}: {inputs} has the panel counts {sorted(case['intervals'])}")
    return cases, failures


def log10(x):
    """The base-10 logarithm of a positive fraction, for any magnitude."""
    return math.log10(x.numerator) - math.log10(x.denominator)


def number(x):
    return f"{int(x)}" if x == int(x) else f"{x:g}"


def label(inputs):
    """The miss vector, the radius, and the covariance, as σ = (σ1, σ2) for (σ1², 0, σ2²)."""
    m1, m2, c11, c12, c22, r = (float(x) for x in inputs)
    m = f"({number(m1)}, {number(m2)})".replace("-", "−")
    if c12 == 0:
        cov = f"σ = ({number(math.sqrt(c11))}, {number(math.sqrt(c22))})"
    else:
        cov = f"C = ({number(c11)}, {number(c12)}, {number(c22)})".replace("-", "−")
    return m, number(r), cov


def power(e):
    return f"$10^{{{e}}}$".replace("-", "−")


def scientific(x):
    """x to two significant digits, as a multiple of a power of ten."""
    e = math.floor(log10(x))
    mantissa = float(x / Fraction(10) ** e)
    if mantissa >= 9.95:
        mantissa, e = mantissa / 10, e + 1
    return f"{mantissa:.1f} × {power(e)}"


def tick(t):
    if t == 0:
        return "0"
    e = round(math.log10(abs(t)))
    return ("−" if t < 0 else "") + ("1" if e == 0 else power(e))


def draw(cases, path):
    rows = sorted(cases.items(), key=lambda item: -item[1]["ref"])
    errors = [{n: ((lo - case["ref"]) / case["ref"], (hi - case["ref"]) / case["ref"])
               for n, (lo, hi) in case["intervals"].items()} for _, case in rows]
    smallest = min(abs(x) for row in errors for ends in row.values() for x in ends if x != 0)
    threshold = 10.0 ** math.floor(log10(smallest))
    k = len(rows)
    H = TOP + k * ROW + BOTTOM
    fig = plt.figure(figsize=(W, H))
    ax = fig.add_axes([LEFT / W, BOTTOM / H, (RIGHT - LEFT) / W, k * ROW / H])
    ax.set_xscale("symlog", linthresh=threshold, linscale=1)
    for y, ((inputs, case), row) in enumerate(zip(rows, errors)):
        for n, (low, high) in row.items():
            if low < -LIMIT:
                raise ValueError(f"{inputs} at {n} panels: a lower end below -{LIMIT}")
            right = min(high, LIMIT)
            ax.barh(y + DODGE[n], float(right - low), left=float(low), height=BAR,
                    color=PANELS[n], linewidth=0, zorder=2)
            if high > LIMIT:
                ax.plot(LIMIT, y + DODGE[n], marker=">", color=PANELS[n], markersize=4.5,
                        clip_on=False, zorder=3)
                ax.annotate(scientific(high), (LIMIT, y + DODGE[n]), xytext=(7, 0),
                            textcoords="offset points", ha="left", va="center", fontsize=7,
                            color=INK, annotation_clip=False)
        cells = (*label(inputs), scientific(case["ref"]))
        for x, text in zip(TABLE, cells):
            fig.text(x / W, (BOTTOM + (k - y - 0.5) * ROW) / H, text, fontsize=7.5, color=INK,
                     va="center")
    for x, text in zip(TABLE, ("Miss\nvector m", "Radius\nr", "Covariance", "Reference\nvalue")):
        fig.text(x / W, (BOTTOM + k * ROW + 0.08) / H, text, fontsize=8, color=MUTED,
                 va="bottom")
    ax.axvline(0, color=INK, linewidth=1.0, zorder=4)
    for y in range(k - 1):
        ax.axhline(y + 0.5, color=GRID, linewidth=0.4, zorder=0)
    ax.set_xlim(-LIMIT, LIMIT)
    ax.set_ylim(k - 0.5, -0.5)
    ax.set_yticks([])
    decades = range(0, math.floor(math.log10(threshold)) - 1, -2)
    ticks = [0] + [s * 10.0 ** d for d in decades for s in (-1, 1)]
    ax.set_xticks(ticks, [tick(t) for t in ticks])
    ax.tick_params(axis="x", colors=INK, labelsize=8)
    ax.grid(axis="x", color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)
    for spine in ("top", "right", "left"):
        ax.spines[spine].set_visible(False)
    ax.set_xlabel("(interval's end − reference value) / reference value", fontsize=9, color=INK)
    fig.text(0.1 / W, 1 - 0.24 / H, f"Containment test of pc: {k} inputs at 16, 256, and 4,096 "
             "panels, against the reference value at 50 digits", fontsize=9, color=MUTED,
             va="baseline")
    handles = [Line2D([], [], color=INK, linewidth=1.0, label="Reference value")]
    handles += [Patch(color=color, linewidth=0, label=f"{n:,} panels")
                for n, color in PANELS.items()]
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(0.1 / W - 0.01, 1 - 0.3 / H),
               ncol=4, frameon=False, fontsize=8.5, handlelength=1.6, columnspacing=1.4)
    fig.savefig(path, metadata={"Date": None} if path.endswith(".svg") else None, dpi=150)


def main():
    if len(sys.argv) != 3:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    cases, failures = read(sys.argv[1])
    if failures:
        for line in failures:
            print(f"figure.py: {sys.argv[1]}: a rejected result or a reference value outside "
                  f"its interval: {line}", file=sys.stderr)
        return 1
    draw(cases, sys.argv[2])
    return 0


if __name__ == "__main__":
    sys.exit(main())
