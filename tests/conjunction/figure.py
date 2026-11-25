# /// script
# requires-python = ">=3.12"
# dependencies = ["matplotlib==3.11.2"]
# ///
"""Draws the containment test of the conjunction program from REPORT, the report of
tests/conjunction/reference.py that tests/conjunction/run.sh writes to
build/conjunction/reference.txt: for each input of `pc`, the intervals at 16, 256, and 4,096 panels
against the reference value of the probability, which reference.py computes at 50 digits, and each
interval's relative width, its width divided by the reference value.

The rows hold the inputs in decreasing order of the reference value, and inputs with equal
reference values in their order in REPORT.  The left panel's axis is the base-10 logarithm of the
probability, computed from the exact decimals, so it places reference values below the smallest
positive double, and it draws an interval whose lower endpoint is 0 as a bar from the panel's left
edge.  The right panel gives the relative widths on a logarithmic axis up to 10, and for a row
with relative widths above 10 it writes the smallest and the largest of them.  Every value comes
from REPORT, read as exact decimals.  The format of OUT, SVG or PNG, follows its extension.  The
exit status is 0 when the figure is drawn, 1 when a result is rejected or a reference value lies
outside its interval, and 2 for a usage error.

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

matplotlib.rcParams["svg.hashsalt"] = "conjunction-figure"

INK, MUTED, GRID = "#111111", "#555555", "#dddddd"
PANELS = {16: ("#d55e00", "o"), 256: ("#0072b2", "s"), 4096: ("#009e73", "^")}
DODGE = {16: -0.26, 256: 0.0, 4096: 0.26}
CEILING = 10

LINE = re.compile(r"(ok  |FAIL) m=\((\S+),(\S+)\) C=\((\S+),(\S+),(\S+)\) r=(\S+) n=(\d+) "
                  r"status=(\d+) ref=(\S+) lo=(\S+) hi=(\S+) width=\S+")

W, ROW, TOP, BOTTOM = 7.3, 0.27, 0.95, 0.55
TABLE = [0.1, 1.05, 1.75]
A_LEFT, A_RIGHT = 3.55, 4.9
B_LEFT, B_RIGHT = 5.2, 7.1


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
    e = math.floor(log10(x))
    mantissa = float(x / Fraction(10) ** e)
    if mantissa >= 9.95:
        mantissa, e = mantissa / 10, e + 1
    return f"{mantissa:.1f} × {power(e)}"


def draw(cases, path):
    rows = sorted(cases.items(), key=lambda item: -item[1]["ref"])
    k = len(rows)
    H = TOP + k * ROW + BOTTOM
    fig = plt.figure(figsize=(W, H))

    def axes(left, right):
        return fig.add_axes([left / W, BOTTOM / H, (right - left) / W, k * ROW / H])

    a, b = axes(A_LEFT, A_RIGHT), axes(B_LEFT, B_RIGHT)
    logs = [log10(case["ref"]) for _, case in rows]
    logs += [log10(hi) for _, case in rows for _, hi in case["intervals"].values() if hi > 0]
    left = math.floor(min(logs) / 50) * 50 - 10
    widths = []
    for y, (_, case) in enumerate(rows):
        for n, (lo, hi) in case["intervals"].items():
            color, _ = PANELS[n]
            a.plot([log10(lo) if lo > 0 else left, log10(hi)], [y + DODGE[n]] * 2, color=color,
                   linewidth=2.2, solid_capstyle="butt", zorder=2)
            if lo == 0:
                a.plot(left, y + DODGE[n], marker="<", color=color, markersize=4, clip_on=False,
                       zorder=3)
        a.plot([log10(case["ref"])] * 2, [y - 0.42, y + 0.42], color=INK, linewidth=1.2,
               zorder=4)
        widths.append({n: (hi - lo) / case["ref"] for n, (lo, hi) in case["intervals"].items()})
    least = min(w for row in widths for w in row.values())
    bounds = (10 ** math.floor(log10(least)), CEILING)
    for y, ((inputs, _), row) in enumerate(zip(rows, widths)):
        for n, w in row.items():
            if w <= CEILING:
                color, marker = PANELS[n]
                b.plot(float(w), y + DODGE[n], marker=marker, color=color, markersize=4.6,
                       markeredgecolor="white", markeredgewidth=0.4, linestyle="none", zorder=3)
        above = sorted(w for w in row.values() if w > CEILING)
        if above:
            text = scientific(above[0])
            if len(above) > 1:
                text += f" to {scientific(above[-1])}"
            b.text(CEILING, y, f"{text} →", ha="right", va="center", fontsize=7.5, color=INK,
                   bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.5})
        for x, text in zip(TABLE, label(inputs)):
            fig.text(x / W, (BOTTOM + (k - y - 0.5) * ROW) / H, text, fontsize=8, color=INK,
                     va="center")
    for x, text in zip(TABLE, ("Miss vector m", "Radius r", "Covariance")):
        fig.text(x / W, (BOTTOM + k * ROW + 0.08) / H, text, fontsize=8.5, color=MUTED,
                 va="bottom")
    a.set_xlim(left, 10)
    b.set_xscale("log")
    b.set_xlim(*bounds)
    for ax in (a, b):
        ax.set_ylim(k - 0.5, -0.5)
        ax.set_yticks(range(k), [""] * k)
        ax.tick_params(axis="y", length=0)
        ax.tick_params(axis="x", colors=INK, labelsize=8.5)
        ax.grid(axis="x", color=GRID, linewidth=0.6)
        ax.set_axisbelow(True)
        for spine in ("top", "right", "left"):
            ax.spines[spine].set_visible(False)
        for y in range(k - 1):
            ax.axhline(y + 0.5, color=GRID, linewidth=0.4, zorder=0)
    ticks = range(0, left, -200)
    a.set_xticks(list(ticks), [power(t) for t in ticks])
    a.set_xlabel("Probability", fontsize=9, color=INK)
    b.set_xlabel("Relative width", fontsize=9, color=INK)
    fig.text(0.1 / W, 1 - 0.24 / H, f"Containment test of pc: {k} inputs at 16, 256, and 4,096 "
             "panels, against the reference value at 50 digits", fontsize=9, color=MUTED,
             va="baseline")
    handles = [Line2D([], [], color=INK, linewidth=1.2, label="Reference value")]
    handles += [Line2D([], [], color=color, marker=marker, linewidth=2.2, markersize=4.6,
                       markeredgecolor="white", markeredgewidth=0.4, label=f"{n:,} panels")
                for n, (color, marker) in PANELS.items()]
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(0.1 / W - 0.01, 1 - 0.3 / H),
               ncol=4, frameon=False, fontsize=8.5, handlelength=2.0, columnspacing=1.4)
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
