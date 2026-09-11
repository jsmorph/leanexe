#!/usr/bin/env python3
import argparse
from io import StringIO
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def render(directory):
    inputs = [p for p in [directory / "cells.csv", directory / "cells.csv.gz"] if p.exists()]
    if len(inputs) != 1:
        raise ValueError("expected one cell CSV, plain or gzip-compressed")
    data = np.genfromtxt(inputs[0], delimiter=",", names=True)
    n = int(round(np.sqrt(data.size)))
    if n * n != data.size:
        raise ValueError("cell count must be square")
    fields = [data["density"].reshape(n, n), data["pressure"].reshape(n, n)]
    x = (np.arange(n) + 0.5) / n
    plt.rcParams.update({"font.size": 10, "svg.fonttype": "none", "svg.hashsalt": "euler-riemann-v1"})
    figure, axes = plt.subplots(1, 2, figsize=(10.2, 4.7), layout="constrained")
    for axis, field, title, cmap in zip(axes, fields, ["Density", "Pressure"], ["viridis", "magma"]):
        image = axis.imshow(field, extent=(0, 1, 0, 1), origin="lower", interpolation="nearest", cmap=cmap)
        levels = np.linspace(field.min(), field.max(), 18)[1:-1]
        axis.contour(x, x, field, levels=levels, colors="white", linewidths=0.3, alpha=0.45)
        axis.set(title=title, xlabel="x", ylabel="y", xticks=[0, 0.2, 0.4, 0.6, 0.8, 1], yticks=[0, 0.2, 0.4, 0.6, 0.8, 1])
        axis.set_aspect("equal")
        figure.colorbar(image, ax=axis, shrink=0.83, pad=0.025)
    figure.suptitle(f"2D Euler Riemann problem: t = 0.8, {n} × {n} cells", fontsize=13)
    outputs = [directory / "density-pressure.png", directory / "density-pressure.svg", directory / "density-pressure.pdf"]
    if any(p.exists() for p in outputs):
        raise FileExistsError("preserve existing figures; select a fresh output directory")
    figure.savefig(outputs[0], dpi=220, metadata={"Software": "Matplotlib 3.10.8"})
    svg = StringIO()
    figure.savefig(svg, format="svg", metadata={"Date": None, "Creator": "Matplotlib 3.10.8"})
    outputs[1].write_text("\n".join(line.rstrip() for line in svg.getvalue().splitlines()) + "\n")
    figure.savefig(outputs[2], metadata={"CreationDate": None, "ModDate": None, "Creator": "Matplotlib 3.10.8"})
    plt.close(figure)
    for output in outputs:
        print(output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    render(args.directory)
