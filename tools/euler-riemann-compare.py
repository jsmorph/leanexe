#!/usr/bin/env python3
import argparse
from io import StringIO
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def read_fields(directory):
    inputs = [p for p in [directory / "cells.csv", directory / "cells.csv.gz"] if p.exists()]
    if len(inputs) != 1:
        raise ValueError("expected one cell CSV, plain or gzip-compressed")
    data = np.genfromtxt(inputs[0], delimiter=",", names=True, usecols=(4, 10))
    n = int(round(np.sqrt(data.size)))
    if n * n != data.size:
        raise ValueError("cell count must be square")
    return n, [data[name].reshape(n, n) for name in ["density", "pressure"]]


def render(coarse, fine, output):
    runs = [read_fields(directory) for directory in [coarse, fine]]
    if runs[0][0] >= runs[1][0]:
        raise ValueError("expected coarse then fine grids")
    outputs = [output.with_suffix(suffix) for suffix in [".png", ".svg", ".pdf"]]
    if any(p.exists() for p in outputs):
        raise FileExistsError("preserve existing figures; select a fresh output prefix")
    plt.rcParams.update({"font.size": 10, "svg.fonttype": "none", "svg.hashsalt": "euler-riemann-comparison-v1"})
    figure, axes = plt.subplots(2, 2, figsize=(10.2, 9), layout="constrained")
    for column, (title, cmap) in enumerate(zip(["Density", "Pressure"], ["viridis", "magma"])):
        vmin = min(fields[column].min() for _, fields in runs)
        vmax = max(fields[column].max() for _, fields in runs)
        levels = np.linspace(vmin, vmax, 18)[1:-1]
        for row, (n, fields) in enumerate(runs):
            axis, field = axes[row, column], fields[column]
            x = (np.arange(n) + 0.5) / n
            image = axis.imshow(field, extent=(0, 1, 0, 1), origin="lower", interpolation="nearest", cmap=cmap, vmin=vmin, vmax=vmax)
            axis.contour(x, x, field, levels=levels, colors="white", linewidths=0.3, alpha=0.45)
            axis.set(title=f"{title}: {n} × {n}", xlabel="x", ylabel="y", xticks=[0, 0.2, 0.4, 0.6, 0.8, 1], yticks=[0, 0.2, 0.4, 0.6, 0.8, 1])
            axis.set_aspect("equal")
        figure.colorbar(image, ax=axes[:, column], shrink=0.8, pad=0.025)
    figure.suptitle("2D Euler Riemann problem: t = 0.8", fontsize=13)
    figure.savefig(outputs[0], dpi=220, metadata={"Software": "Matplotlib 3.10.8"})
    svg = StringIO()
    figure.savefig(svg, format="svg", metadata={"Date": None, "Creator": "Matplotlib 3.10.8"})
    outputs[1].write_text("\n".join(line.rstrip() for line in svg.getvalue().splitlines()) + "\n")
    figure.savefig(outputs[2], metadata={"CreationDate": None, "ModDate": None, "Creator": "Matplotlib 3.10.8"})
    plt.close(figure)
    for target in outputs:
        print(target)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("coarse", type=Path)
    parser.add_argument("fine", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    render(args.coarse, args.fine, args.output)
