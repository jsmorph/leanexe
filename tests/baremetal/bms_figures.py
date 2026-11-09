# /// script
# requires-python = ">=3.12"
# dependencies = ["matplotlib==3.11.2"]
# ///
"""Draws the two figures of a BMS board run for Demos/Bms/README.md from the run's files
PREFIX.in, PREFIX.out, and PREFIX.log, read by bms_report.py.

DIR/run.png covers the whole run: the scenario groups, the state of each answer, the permit
bits of the answers beside the coils that the bridge energized, and the diagnostic code of each
answer whose code is not 0, by family.  DIR/start.png covers the first FIRST seconds: the cell
voltages against V_max and V_min, the pack and bus voltages, the permits and coils, and the state
of each answer, with notes computed from the records and answers.  Every value comes from the run's
files.

Usage: uv run tests/baremetal/bms_figures.py PREFIX DIR [FIRST]
"""

import os
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

import bms_proto as bp
from bms_proto import FAULT, NORMAL, PRECHARGE, RESET_REQUIRED, STATES
from bms_report import (BAND, GRID, INK, INK2, MUTED, SERIES, STATE_COLORS, SURFACE, broken,
                        limit, load, spans, style)
from uart_bms import RELAYS

# Scenario groups by their first and last scenario numbers, as Demos/Bms/requirements.md's
# fault-injection schedule orders them.
GROUPS = [
    (1, 4, "Start and restart"),
    (5, 14, "Readings at and beyond each limit"),
    (15, 25, "Format and channel faults"),
    (26, 27, "Lost answers,\nsilent bridge"),
    (28, 30, "Contactor and\nprecharge faults"),
    (31, 32, "Stop,\nstandby"),
    (33, 37, "Board resets and the precharge limit"),
]

FAMILIES = [
    ("0x0001 board reset", lambda c: c == 0x0001),
    ("0x10xx format and channel", lambda c: 0x1000 <= c < 0x2000),
    ("0x20xx readings", lambda c: 0x2000 <= c < 0x3000),
    ("0x30xx contacts and precharge", lambda c: 0x3000 <= c < 0x4000),
    ("0x5001 stop", lambda c: c == 0x5001),
]

W, LEFT, RIGHT = 16.0, 2.3, 1.35
LANE = 0.2
PERMIT, COIL = SERIES[0], SERIES[1]


def layout(panels, top, bottom):
    """Axes for panels (title, height, legend) stacked under a strip of height top."""
    heads = [0.6 if legend else 0.36 for _, _, legend in panels]
    gap = 0.3
    H = top + sum(h for _, h, _ in panels) + sum(heads) + gap * (len(panels) - 1) + bottom
    fig = plt.figure(figsize=(W, H), facecolor=SURFACE)
    width = (W - LEFT - RIGHT) / W
    axes, y = [], top
    for (title, h, _), head in zip(panels, heads):
        y += head
        ax = fig.add_axes([LEFT / W, 1 - (y + h) / H, width, h / H])
        fig.text(LEFT / W, 1 - (y - head + 0.22) / H, title, fontsize=11, fontweight="bold",
                 color=INK, va="baseline")
        axes.append(ax)
        y += h + gap
    strip = fig.add_axes([LEFT / W, 1 - top / H, width, (top - 0.08) / H]) if top else None
    return fig, axes, strip


def legend(ax, handles):
    ax.legend(handles=handles, loc="lower left", bbox_to_anchor=(0, 1.0), ncol=len(handles),
              frameon=False, borderaxespad=0.15, handlelength=1.6, columnspacing=1.8,
              fontsize=9.5, labelcolor=INK2)


def lanes(ax, labels):
    ax.set_ylim(len(labels) - 0.5, -0.5)
    ax.set_yticks(range(len(labels)), labels)
    ax.tick_params(axis="y", colors=INK2, labelsize=9.5)


def states(ax, steps):
    for t, t1, a in steps:
        ax.broken_barh([(t, t1 - t)], (a.state - 0.32, 0.64), facecolor=STATE_COLORS[a.state],
                       linewidth=0)
        ax.vlines(t, a.state - 0.32, a.state + 0.32, color=STATE_COLORS[a.state], linewidth=1.6)
    lanes(ax, STATES)


def relays(ax, steps, run, end):
    labels = []
    for r, name in enumerate(RELAYS):
        permit = [(t, t1 - t) for t, t1, a in steps if a.permit >> r & 1]
        coil = [(t, t1 - t) for t, t1, m in spans(run.coils, [], end) if m >> r & 1]
        ax.broken_barh(permit, (2 * r - 0.32, 0.64), facecolor=PERMIT, linewidth=0)
        ax.vlines([t for t, _ in permit], 2 * r - 0.32, 2 * r + 0.32, color=PERMIT,
                  linewidth=1.6)
        ax.broken_barh(coil, (2 * r + 1 - 0.32, 0.64), facecolor=COIL, linewidth=0)
        labels += [f"{name} permit", f"{name} coil"]
    for y in (1.5, 3.5):
        ax.axhline(y, color=GRID, linewidth=0.8)
    lanes(ax, labels)
    legend(ax, [Patch(color=PERMIT, label="Permit bit of the latest answer, until the next answer "
                                          "or a board reset"),
                Patch(color=COIL, label="Coil energized by the bridge")])


def resets(axes, run, end, label):
    """Dashed lines at the board resets before end, and label(t) for each."""
    for t in run.resets:
        if t > end:
            continue
        for ax in axes:
            ax.axvline(t, color=INK2, linewidth=0.9, linestyle=(0, (2, 2)), zorder=4)
        label(t)


def answer_steps(run, end):
    return [(t, min(t1, end), a) for t, t1, a in
            spans([(r.t, r.answer) for p in run.parts for r in p.replies if r.answer],
                  run.resets, run.end) if t < end]


def overview(run, path):
    end = run.end
    steps = answer_steps(run, end)
    panels = [("State of each answer", 5 * LANE + 0.1, False),
              ("Relays", 6 * LANE + 0.1, True),
              ("Diagnostic code of each answer whose code is not 0x0000, by family",
               len(FAMILIES) * LANE + 0.1, True)]
    fig, axes, strip = layout(panels, 0.75, 0.75)
    for ax in axes:
        style(ax, end)
    strip.set_xlim(0, end)
    strip.set_ylim(0, 1)
    strip.axis("off")
    for k, (first, last, name) in enumerate(GROUPS):
        t0, t1 = run.scenarios[first - 1][0], run.scenarios[last - 1][1]
        for ax in axes:
            if k % 2:
                ax.axvspan(t0, t1, color=BAND, linewidth=0, zorder=0)
        strip.axvspan(t0, t1, ymin=0, ymax=1, color=BAND if k % 2 else SURFACE, linewidth=0)
        strip.text((t0 + t1) / 2, 0.5, f"{name}\n{first}–{last}", ha="center", va="center",
                   fontsize=9, color=INK2, linespacing=1.25)
    strip.text(-0.008, 0.5, "Scenarios", transform=strip.transAxes, ha="right", va="center",
               fontsize=9.5, color=INK2)

    states(axes[0], steps)
    relays(axes[1], steps, run, end)

    ax = axes[2]
    for t, t1, a in steps:
        for k, (_, member) in enumerate(FAMILIES):
            if member(a.code):
                ax.broken_barh([(t, t1 - t)], (k - 0.32, 0.64), facecolor=STATE_COLORS[a.state],
                               linewidth=0)
    lanes(ax, [name for name, _ in FAMILIES])
    legend(ax, [Patch(color=STATE_COLORS[FAULT], label="Answer in FAULT"),
                Patch(color=STATE_COLORS[RESET_REQUIRED], label="Answer in RESET_REQUIRED")])
    ax.tick_params(axis="x", labelbottom=True, labelsize=9.5)
    ax.set_xlabel("Seconds from the start of the run", color=INK2, fontsize=10, labelpad=8)
    resets(axes, run, end, lambda t: axes[0].text(t, -0.62, " board reset", ha="left",
                                                   va="bottom", fontsize=8.5, color=INK2))
    fig.savefig(path, dpi=150, facecolor=SURFACE)
    plt.close(fig)


def note(ax, x, y, text, dx=0.0, dy=0.0, ha="left"):
    ax.annotate(text, (x, y), (x + dx, y + dy), textcoords="data", ha=ha, va="center",
                fontsize=9, color=INK2,
                arrowprops=dict(arrowstyle="-", color=MUTED, linewidth=0.8, shrinkA=2, shrinkB=3))


def start(run, path, first):
    end = first
    steps = answer_steps(run, end)
    recs = [(t, sc) for t, sc in run.records if t < end]
    times = [t for t, _ in recs]
    panels = [("Cell voltages, mV", 2.0, True),
              ("Pack and bus voltages, V", 1.5, True),
              ("Relays", 6 * LANE + 0.1, True),
              ("State of each answer", 5 * LANE + 0.1, False)]
    fig, axes, strip = layout(panels, 0.7, 0.75)
    for ax in axes:
        style(ax, end)
    strip.set_xlim(0, end)
    strip.set_ylim(0, 1)
    strip.axis("off")
    shown = [(k, s) for k, s in enumerate(run.scenarios) if s[0] < end]
    for k, (t0, t1, name, _) in shown:
        t1 = min(t1, end)
        for ax in axes:
            if k % 2:
                ax.axvspan(t0, t1, color=BAND, linewidth=0, zorder=0)
        if t1 - t0 >= 0.2:
            strip.text((t0 + t1) / 2, 0.75 if k % 2 == 0 else 0.25, f"{k + 1} {name}",
                       ha="center", va="center", fontsize=9, color=INK2)
    strip.text(-0.008, 0.5, "Scenario", transform=strip.transAxes, ha="right", va="center",
               fontsize=9.5, color=INK2)

    ax = axes[0]
    for k in range(4):
        ax.plot(*broken(times, [sc.cells[k] for _, sc in recs]), color=SERIES[k], linewidth=1.4,
                marker="o", markersize=2.2, zorder=3)
    ax.set_ylim(2350, 3800)
    ax.set_yticks(range(2400, 3801, 200), [f"{v:,}" for v in range(2400, 3801, 200)])
    ax.grid(axis="y", color=GRID, linewidth=0.6)
    limit(ax, bp.V_MAX, f"V_max {bp.V_MAX:,}")
    limit(ax, bp.V_MIN, f"V_min {bp.V_MIN:,}")
    legend(ax, [Line2D([], [], color=SERIES[k], linewidth=2, label=f"Cell {k}")
                for k in range(4)])
    answers = [(r.t, r.answer, r.segment) for p in run.parts for r in p.replies if r.answer]
    marked = []
    for t, sc in recs:
        hi, lo = max(sc.cells), min(sc.cells)
        if hi >= bp.V_MAX or lo <= bp.V_MIN:
            v = hi if hi >= bp.V_MAX else lo
            reply = next(a for ta, a, _ in answers if ta > t)
            verdict = (f"answered {STATES[reply.state]} {reply.code:#06x}"
                       if reply.state == FAULT else f"answered {STATES[reply.state]}")
            marked.append((t, v, f"{v:,} mV, {verdict}"))
    groups = []
    for t, v, text in marked:
        above = v >= bp.V_MAX
        if groups and groups[-1][-1][0] > t - 1.0 and (groups[-1][-1][1] >= bp.V_MAX) == above:
            groups[-1].append((t, v, text))
        else:
            groups.append([(t, v, text)])
    for group in groups:
        for i, (t, v, text) in enumerate(group):
            # Later notes sit nearer the cells' traces, so the leader lines do not cross.
            y = 3120 - 120 * i if v >= bp.V_MAX else 2700 + 120 * (len(group) - 1 - i)
            note(ax, t, v, text, dx=-0.15, dy=y - v, ha="right")

    ax = axes[1]
    ax.plot(*broken(times, [sc.pack / 1000 for _, sc in recs]), color=SERIES[0], linewidth=1.4,
            zorder=3)
    ax.plot(*broken(times, [sc.bus / 1000 for _, sc in recs]), color=SERIES[1], linewidth=1.4,
            marker="o", markersize=2.2, zorder=3)
    ax.set_ylim(-0.5, 15.5)
    ax.set_yticks(range(0, 16, 5))
    ax.grid(axis="y", color=GRID, linewidth=0.6)
    legend(ax, [Line2D([], [], color=SERIES[0], linewidth=2, label="Pack"),
                Line2D([], [], color=SERIES[1], linewidth=2, label="Bus, on the load side")])
    pre = next(t for t, _, a in steps if a.state == PRECHARGE)
    nor = next(t for t, _, a in steps if a.state == NORMAL)
    bus0 = next(sc.bus for t, sc in recs if t >= pre)
    busn = max((t, sc) for t, sc in recs if t < nor)[1]
    note(ax, pre, bus0 / 1000, "PRECHARGE: the bus charges through PRE", dx=0.45, dy=4.0)
    note(ax, nor, busn.bus / 1000,
         f"NORMAL: bus {busn.bus:,} mV, pack {busn.pack:,} mV, within tol_pc", dx=0.3, dy=-6.5)

    relays(axes[2], steps, run, end)
    states(axes[3], steps)
    axes[3].tick_params(axis="x", labelbottom=True, labelsize=9.5)
    axes[3].set_xlabel("Seconds from the start of the run", color=INK2, fontsize=10, labelpad=8)

    def gap(t):
        resume = min(tr for tr, _ in recs if tr > t)
        axes[0].text(t + 0.06, 3000, f"board reset by the bridge:\nno record from {t:.2f} s "
                     f"to {resume:.2f} s", ha="left", va="center", fontsize=9, color=INK2)
    resets(axes, run, end, gap)
    expiry = next((it for it in run.items if type(it).__name__ == "Expiry" and it.t < end), None)
    if expiry is not None:
        axes[2].text(expiry.t + 0.08, 2.0, f"leases end at {expiry.t:.2f} s, and the bridge "
                     f"releases {' and '.join(expiry.relays)}", ha="left", va="center",
                     fontsize=9, color=INK2)
    fig.savefig(path, dpi=150, facecolor=SURFACE)
    plt.close(fig)


def main():
    if len(sys.argv) not in (3, 4):
        raise SystemExit(__doc__.strip().splitlines()[-1])
    prefix, out = sys.argv[1:3]
    first = float(sys.argv[3]) if len(sys.argv) == 4 else 8.0
    run = load(prefix)
    os.makedirs(out, exist_ok=True)
    overview(run, os.path.join(out, "run.png"))
    start(run, os.path.join(out, "start.png"), first)
    print(f"{os.path.join(out, 'run.png')}, {os.path.join(out, 'start.png')}")


if __name__ == "__main__":
    main()
