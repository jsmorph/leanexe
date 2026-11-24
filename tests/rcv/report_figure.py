# /// script
# requires-python = ">=3.12"
# dependencies = ["matplotlib==3.11.2"]
# ///
"""Draws the rounds of a tabulator's report, as the Oakland module or the Maine module writes it,
with one panel per round.

Each panel shows the votes of every counted candidate in index order, the inactive ballots, and a
line at half of the round's continuing ballots, which a winner's votes exceed.  From round 2 on,
each candidate's bar separates the votes of the previous round from the votes gained in the round.
A candidate's bar names its elimination or its election, and a candidate eliminated earlier shows
the round of its elimination.  A Maine report adds a first panel for the initial test, with the
first counts and a line at half of the ballots.  Every value comes from the report.  The format of
OUT, SVG or PNG, follows its extension.

Usage: uv run tests/rcv/report_figure.py REPORT OUT
"""

import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

matplotlib.rcParams["svg.hashsalt"] = "report_figure"

INK, MUTED, GRID = "#111111", "#555555", "#dddddd"
HELD, GAINED = "#3a3a3a", "#a8a8a8"
ELIMINATION = {"lowest": "eliminated, fewest votes", "batch": "eliminated in a batch",
               "order": "eliminated by the tie-break order"}

W, LEFT, RIGHT = 7.3, 1.75, 0.2
ROW, HEAD, GAP, TOP, BOTTOM = 0.3, 0.42, 0.12, 0.62, 0.5


def read(path):
    """The report's candidates, ballots, first counts, rounds, and winner."""
    report = {"contest": None, "names": {}, "ballots": None, "first": {}, "rounds": [],
              "winner": None}
    rounds = report["rounds"]
    with open(path, encoding="utf-8") as f:
        for line in f:
            word, _, rest = line.rstrip("\n").partition(" ")
            fields = rest.split()
            if word == "contest":
                report["contest"] = rest
            elif word == "candidate":
                index, _, name = rest.split(" ", 2)
                report["names"][int(index)] = name
            elif word == "ballots":
                report["ballots"] = int(rest)
            elif word == "first":
                report["first"][int(fields[0])] = int(fields[1])
            elif word == "round":
                rounds.append({"continuing": None, "votes": {}, "inactive": {}, "eliminate": None,
                               "tie": []})
            elif word == "continuing":
                rounds[-1]["continuing"] = int(rest)
            elif word == "votes":
                rounds[-1]["votes"][int(fields[0])] = int(fields[1])
            elif word == "inactive":
                rounds[-1]["inactive"][fields[0]] = int(fields[1])
            elif word == "tie":
                rounds[-1]["tie"] = [int(i) for i in fields]
            elif word == "eliminate":
                rounds[-1]["eliminate"] = (fields[0], [int(i) for i in fields[1:]])
            elif word == "winner":
                report["winner"] = None if rest == "none" else int(rest)
            elif word == "error":
                raise ValueError(f"{path} is an error report: {line.strip()}")
    if not rounds and not report["first"]:
        raise ValueError(f"{path} has no rounds and no initial test")
    return report


def number(n):
    """n with thousands separators, and with one decimal when n is not whole."""
    return f"{n:,.0f}" if n == int(n) else f"{n:,.1f}"


def counted(report):
    if report["first"]:
        return sorted(report["first"])
    return sorted(report["rounds"][0]["votes"])


def split(r, label, previous, now):
    """The part of now held from previous and the part gained, with the bar's label."""
    if now < previous:
        raise ValueError(f"round {r}: {label} fell from {previous} to {now}")
    gained = now - previous
    return previous, gained, number(now) + (f" (+{number(gained)})" if gained else "")


def panels(report):
    """Each panel's title, half line, its label, the index of its inactive row, and its rows
    (label, held, gained, note)."""
    names, ballots, rounds = report["names"], report["ballots"], report["rounds"]
    candidates = counted(report)
    out = []
    if report["first"]:
        rows = []
        for i in candidates:
            f = report["first"][i]
            won = not rounds and report["winner"] == i
            rows.append((names[i], f, 0, number(f) + (", winner" if won else "")))
        out.append((f"Initial test: candidates ranked first alone, of {number(ballots)} ballots",
                    ballots / 2, f"Half of {number(ballots)}: {number(ballots / 2)}", None, rows))
    gone = {}
    for r, rnd in enumerate(rounds, 1):
        before = rounds[r - 2] if r > 1 else None
        rows = []
        for i in candidates:
            if i in gone:
                rows.append((names[i], 0, 0, f"eliminated in round {gone[i]}"))
                continue
            v = rnd["votes"][i]
            held, gained, text = split(r, f"votes of candidate {i}",
                                       before["votes"][i] if before else v, v)
            notes = [text]
            if rnd["eliminate"] and i in rnd["eliminate"][1]:
                notes.append(ELIMINATION[rnd["eliminate"][0]])
            elif i in rnd["tie"]:
                notes.append("tied")
            if r == len(rounds) and report["winner"] == i:
                notes.append("winner")
            rows.append((names[i], held, gained, ", ".join(notes)))
        if rnd["eliminate"]:
            for i in rnd["eliminate"][1]:
                gone[i] = r
        inactive = sum(rnd["inactive"].values())
        rows.append(("Inactive ballots", *split(r, "inactive ballots", sum(
            before["inactive"].values()) if before else inactive, inactive)))
        t = rnd["continuing"]
        out.append((f"Round {r}: {number(t)} continuing ballots", t / 2,
                    f"Half of {number(t)}: {number(t / 2)}", len(rows) - 1, rows))
    return out


def draw(report, path):
    drawn = panels(report)
    heights = [len(rows) * ROW for *_, rows in drawn]
    H = TOP + sum(heights) + HEAD * len(drawn) + GAP * (len(drawn) - 1) + BOTTOM
    fig = plt.figure(figsize=(W, H))
    width = (W - LEFT - RIGHT) / W
    most = max(held + gained for *_, rows in drawn for _, held, gained, _ in rows)
    xmax = most * 1.5
    y = TOP
    axes = []
    for (title, half, label, inactive, rows), h in zip(drawn, heights):
        y += HEAD
        ax = fig.add_axes([LEFT / W, 1 - (y + h) / H, width, h / H])
        fig.text(LEFT / W, 1 - (y - HEAD + 0.24) / H, title, fontsize=9.5, fontweight="bold",
                 color=INK, va="baseline")
        for k, (name, held, gained, note) in enumerate(rows):
            if k == inactive:
                ax.barh(k, held, height=0.62, facecolor="white", edgecolor=HELD, hatch="////",
                        linewidth=0)
                ax.barh(k, gained, left=held, height=0.62, facecolor="white", edgecolor=GAINED,
                        hatch="////", linewidth=0)
            else:
                ax.barh(k, held, height=0.62, color=HELD, linewidth=0)
                ax.barh(k, gained, left=held, height=0.62, color=GAINED, linewidth=0)
            ax.text(held + gained + most * 0.012, k, note, va="center", fontsize=8.5,
                    color=MUTED if held + gained == 0 else INK, zorder=4,
                    bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.4})
        ax.axvline(half, color=INK, linewidth=1.0, linestyle=(0, (4, 2)), zorder=3)
        ax.text(half, -0.62, label, ha="center", va="bottom", fontsize=8, color=INK,
                bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.6})
        ax.set_ylim(len(rows) - 0.5, -0.5)
        ax.set_yticks(range(len(rows)), [name for name, _, _, _ in rows], fontsize=8.5)
        ax.set_xlim(0, xmax)
        ax.grid(axis="x", color=GRID, linewidth=0.6)
        ax.set_axisbelow(True)
        for side in ("top", "right"):
            ax.spines[side].set_visible(False)
        ax.tick_params(axis="y", length=0, colors=INK)
        ax.tick_params(axis="x", colors=INK, labelsize=8.5)
        ax.xaxis.set_major_formatter(lambda x, _: number(int(x)))
        axes.append(ax)
        y += h + GAP
    for ax in axes[:-1]:
        ax.tick_params(axis="x", labelbottom=False)
    axes[-1].set_xlabel("Ballots", fontsize=9, color=INK)
    fig.text(LEFT / W, 1 - 0.24 / H, f"{report['contest']}: {number(report['ballots'])} ballots",
             fontsize=9, color=MUTED, va="baseline")
    fig.legend(handles=[Patch(color=HELD, label="Votes"),
                        Patch(color=GAINED, label="Gained in the round"),
                        Patch(facecolor="white", edgecolor=HELD, hatch="////", linewidth=0,
                              label="Inactive ballots")],
               loc="upper left", bbox_to_anchor=(LEFT / W - 0.01, 1 - 0.3 / H), ncol=3,
               frameon=False, fontsize=8.5, handlelength=1.6, columnspacing=1.4)
    fig.savefig(path, metadata={"Date": None} if path.endswith(".svg") else None, dpi=150)


def main():
    if len(sys.argv) != 3:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    draw(read(sys.argv[1]), sys.argv[2])
    return 0


if __name__ == "__main__":
    sys.exit(main())
