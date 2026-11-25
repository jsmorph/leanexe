# /// script
# requires-python = ">=3.12"
# dependencies = ["matplotlib==3.11.2"]
# ///
"""Draws what the theorems of Demos/ManifestCheck cover: the host's inputs, the stages of `main`
from the manifest's bytes and the files' bytes to the output lines and the status, the theorem
and the specification of each stage, the parts trusted without proof, and an example with a
changed file.  Every statement comes from Demos/ManifestCheck/README.md, the theorems and
specifications that it names, docs/trusted-base.md, and tests/manifest-check/run.sh.  The format
of OUT, SVG or PNG, follows its extension.

Usage: uv run tests/manifest-check/diagram.py OUT
"""

import sys
import textwrap

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Rectangle

matplotlib.rcParams["svg.hashsalt"] = "manifest-check-diagram"
matplotlib.rcParams["hatch.linewidth"] = 0.6

INK, MUTED, EDGE, SPEC, HATCH = "#111111", "#444444", "#1f4e79", "#dbe9f6", "#d55e00"
W, MARGIN = 7.3, 0.1
SIZE, LINE, PAD, GAP = 8.0, 0.139, 0.07, 0.17
STAGE_X, STAGE_W = 2.5, 4.4
HOST_W = 2.0

STAGES = [
    ("Read the manifest",
     "exec_main: open it relative to descriptor 3, ask its size with fd_filestat_get, read until a "
     "buffer of that size is full, and require a last read to return no bytes.",
     "ManifestRun in Meets: the status is the errno of a failed call, 61 for a size of 2^32 "
     "bytes or more, and 1 when the bytes disagree with the size."),
    ("Parse",
     "parse_eq: parse computes parseSpec.",
     "parseSpec: lines in sha256sum's format, 64 hex digits, a space, a space or *, and a name.  "
     "A line outside the format refuses the whole manifest: status 1 and no output."),
    ("For each line in order: open, read, and close the file",
     "exec_main: open the name read-only relative to descriptor 3, read to the end, and close the "
     "file before the next open.",
     "FileCheck, Confined, and Handled in Meets: a failed open, read, or close gives FAILED, and "
     "the checks continue."),
    ("Hash",
     "stream_spec: update and finish give the SHA-256 digest of the bytes that the reads "
     "returned.",
     "The transcription of FIPS 180-4, checked against NIST's CAVP vectors."),
    ("Compare",
     "hexMatches_eq: hexMatches computes hexMatchesSpec.",
     "hexMatchesSpec and DigestOf in Meets: OK exactly when the open, the reads to the end, and "
     "the close succeed and the 64 hex digits, of either case, give the digest's 32 bytes."),
    ("Write the output line",
     "render_eq: render computes renderSpec, and writeAll writes the rest of the line after a "
     "short write.",
     "renderSpec and LineWrites in Meets: the line NAME:\u00a0OK or NAME:\u00a0FAILED and a "
     "newline, where NAME is the name's bytes."),
]

HOSTS = [
    (0, "Command line: one argument, the manifest's name."),
    (0, "Manifest: the size that fd_filestat_get reports and the bytes that the reads return."),
    (2, "Name resolution: the host confines each open beneath descriptor 3, by openat2 with "
        "RESOLVE_BENEATH on Linux and by cap-std in Wasmtime."),
    (3, "Each file: the bytes that the reads of its name return, which the host takes from the "
        "file."),
    (5, "Standard output: the bytes that each write takes."),
]

THEOREM = ("Under every host, exec_main states that every run of main and its exit has events "
           "that meet Meets: Run (the verdicts and the status), Confined (the opens), and Handled "
           "(the descriptors).  start_ends carries it to the module's _start, where a run that "
           "stops at a trap or a rejected exit meets SoFar, and manifest_elf_meets, under "
           "premises on Linux's replies, to the AArch64 Linux executable as NMeets over its "
           "system calls.")

LEGEND = [("proved", "Proved: the theorem named in the box holds"),
          ("spec", "Specification that the theorem names, trusted to state the request or "
                   "the standard"),
          ("host", "Trusted without proof")]

OUTPUT = ("Standard output: one line for each manifest line, in order.  Status 0 when every line "
          "says OK, 1 when one says FAILED, 77 when the writes of a line stop with bytes left, and "
          "the errno of a write that fails.")

TRUSTED = ("Also trusted without proof: Lean's kernel, for the module Talos's semantics, the "
           "decoder, the model of WASI Preview 1, and Wasmtime's agreement with it, and for the "
           "executable Linux 7.0's system calls and loader and the AArch64 instruction model, as "
           "docs/trusted-base.md lists them.")

EXAMPLE_TITLE = ("Example: the first two of the seven lines of the driver's manifest of mixed "
                 "verdicts")
EXAMPLE = [
    ("Manifest line, <...> for its 64 hex digits", "File's bytes at the check", "Output line"),
    ('<SHA-256 of "hello\\n">  a.txt', "hello\\n", "a.txt: OK"),
    ('<SHA-256 of "original\\n">  changed.txt', "originaL\\n", "changed.txt: FAILED"),
]
EXAMPLE_NOTE = ("The driver takes changed.txt's digest and then rewrites the file.  The run on the "
                "whole manifest exits with status 1, as sha256sum -c does.")


def wrap(text, width, size=SIZE):
    return textwrap.wrap(text, int(width * 72 / (size * 0.6)))


def block(ax, x, y, width, text, size=SIZE, bold=False, color=INK):
    """Writes text wrapped to width from the top left (x, y) and returns its height."""
    step = LINE * size / SIZE
    wrapped = wrap(text, width, size)
    for k, line in enumerate(wrapped):
        ax.text(x, y + (k + 0.78) * step, line, fontsize=size, color=color, va="baseline",
                fontweight="bold" if bold else "normal", zorder=3)
    return len(wrapped) * step


def box(ax, x, y, w, h, kind):
    if kind == "proved":
        ax.add_patch(Rectangle((x, y), w, h, facecolor="white", edgecolor=EDGE, linewidth=0.9,
                               zorder=1))
    elif kind == "spec":
        ax.add_patch(Rectangle((x, y), w, h, facecolor=SPEC, edgecolor="none", zorder=2))
    else:
        ax.add_patch(Rectangle((x, y), w, h, facecolor="white", edgecolor=HATCH, hatch="////",
                               linewidth=0.8, zorder=1))
        ax.add_patch(Rectangle((x + 0.05, y + 0.05), w - 0.1, h - 0.1, facecolor="white",
                               edgecolor="none", zorder=2))


def arrow(ax, start, end):
    ax.add_patch(FancyArrowPatch(start, end, arrowstyle="-|>", mutation_scale=8, color=EDGE,
                                 linewidth=0.9, shrinkA=0, shrinkB=0, zorder=3))


def stage(ax, y, title, body, spec):
    """Draws a stage from y and returns its height."""
    x, inner = STAGE_X + PAD, STAGE_W - 2 * PAD
    h = PAD + block(ax, x, y + PAD, inner, title, size=SIZE + 0.6, bold=True) + 0.02
    h += block(ax, x, y + h, inner, body) + 0.05
    tag = block(ax, x + PAD, y + h + PAD - 0.01, inner - 2 * PAD, spec) + 2 * PAD - 0.02
    box(ax, x, y + h, inner, tag, "spec")
    h += tag + PAD
    box(ax, STAGE_X, y, STAGE_W, h, "proved")
    return h


def draw(path):
    fig = plt.figure(figsize=(W, 10))
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, W)
    ax.axis("off")
    y = 0.12
    key = y
    for kind, label in LEGEND:
        box(ax, MARGIN, key + 0.01, 0.28, 0.16, kind)
        key += block(ax, MARGIN + 0.36, key, STAGE_X - MARGIN - 0.5, label) + 0.08
    theorem = block(ax, STAGE_X, y, STAGE_W, THEOREM)
    y = max(y + theorem, key - 0.08) + 0.08
    ax.plot([STAGE_X, STAGE_X + STAGE_W], [y, y], color=EDGE, linewidth=0.9)
    y += 0.17
    tops, heights = [], []
    for title, body, spec in STAGES:
        tops.append(y)
        heights.append(stage(ax, y, title, body, spec))
        y += heights[-1] + GAP
    out = block(ax, STAGE_X + PAD, y + PAD, STAGE_W - 2 * PAD, OUTPUT) + 2 * PAD
    box(ax, STAGE_X, y, STAGE_W, out, "proved")
    middle = STAGE_X + STAGE_W / 2
    for k in range(len(STAGES)):
        arrow(ax, (middle, tops[k] + heights[k]), (middle, tops[k + 1] if k + 1 < len(tops) else y))
    right, outer = STAGE_X + STAGE_W, STAGE_X + STAGE_W + 0.2
    first, last = tops[2] + heights[2] / 2, tops[5] + heights[5] / 2
    ax.plot([right, outer, outer], [last, last, first], color=EDGE, linewidth=0.9, zorder=3)
    arrow(ax, (outer, first), (right, first))
    ax.text(outer + 0.05, (first + last) / 2, "next line", fontsize=SIZE, color=INK, rotation=90,
            va="center", ha="left")
    y += out + 0.22
    below = tops[0]
    for target, text in HOSTS:
        h = len(wrap(text, HOST_W - 2 * PAD - 0.1)) * LINE + 2 * PAD + 0.1
        top = max(below, tops[target] + heights[target] / 2 - h / 2)
        box(ax, MARGIN, top, HOST_W, h, "host")
        block(ax, MARGIN + PAD + 0.05, top + PAD + 0.05, HOST_W - 2 * PAD - 0.1, text)
        end = min(max(top + h / 2, tops[target] + 0.12), tops[target] + heights[target] - 0.12)
        arrow(ax, (MARGIN + HOST_W, top + h / 2), (STAGE_X, end))
        below = top + h + 0.1
    y = max(y, below + 0.12)
    y += block(ax, MARGIN, y, W - 2 * MARGIN, TRUSTED, color=MUTED) + 0.2
    top = y
    y += PAD + block(ax, MARGIN + PAD, y + PAD, W - 2 * MARGIN - 2 * PAD, EXAMPLE_TITLE,
                     size=SIZE + 0.6, bold=True) + 0.06
    columns = [MARGIN + PAD, MARGIN + PAD + 3.2, MARGIN + PAD + 4.95]
    for k, row in enumerate(EXAMPLE):
        for x, cell in zip(columns, row):
            ax.text(x, y + 0.78 * LINE, cell, fontsize=SIZE, color=INK if k else MUTED,
                    family="monospace" if k else "sans-serif", va="baseline")
        y += LINE + (0.05 if k == 0 else 0.01)
    y += 0.05
    y += block(ax, MARGIN + PAD, y, W - 2 * MARGIN - 2 * PAD, EXAMPLE_NOTE) + PAD
    ax.add_patch(Rectangle((MARGIN, top), W - 2 * MARGIN, y - top, facecolor="none",
                           edgecolor=EDGE, linewidth=0.6))
    height = y + 0.12
    fig.set_size_inches(W, height)
    ax.set_ylim(height, 0)
    fig.savefig(path, metadata={"Date": None} if path.endswith(".svg") else None, dpi=150)


def main():
    if len(sys.argv) != 2:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    draw(sys.argv[1])
    return 0


if __name__ == "__main__":
    sys.exit(main())
