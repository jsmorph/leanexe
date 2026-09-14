# A four-state Euler calculation in proved WebAssembly

A single LeanExe-compiled WebAssembly program evolves the four-quadrant problem from the [Lanyon Euler article](https://lanyon.ai/research/euler-equations/).  Initialization, timestep selection, both directional sweeps, retries, allocation, and final output execute inside that program.

![Density and pressure at time 0.8 on the 192-grid](192-run/density-pressure.png)

![Density and pressure at time 0.8 on the 800-grid](800-run/density-pressure.png)

The finer grid resolves thinner fronts and a higher central density maximum.  Front positions and the curved interaction region resemble the [Lanyon density figure](https://lanyon.ai/figs/euler-equations/2d-riem-density-final.png).  This comparison is visual.  Colors show cell values, and white curves show interpolated isolines.  Each panel uses its own color range.

## Problem and method

The domain is the unit square, the initial interfaces are x = y = 0.8, the final time is 0.8, and the ideal-gas ratio of specific heats is γ = 1.4.

| Quadrant | Pressure | Density | x velocity | y velocity |
|----------|---------:|--------:|-----------:|-----------:|
| Top left | 0.3 | 0.5323 | 1.206 | 0 |
| Top right | 1.5 | 1.5 | 0 | 0 |
| Bottom left | 0.029 | 0.138 | 1.206 | 1.206 |
| Bottom right | 0.3 | 0.5323 | 0 | 1.206 |

Each cell stores density, both momenta, and total energy.  Cells cut by an initial interface receive conservative area averages.  The first-order finite-volume method uses Rusanov fluxes, an x sweep followed by a y sweep, and transmissive boundaries implemented by clamping neighbor indices.  Timestep selection targets CFL 0.4.  Each accepted cell update checks a rounded ceiling of 0.5.

## Proof and data

Lean checks the exact 21,767-byte binary through decoding, validation, and translation into Talos execution semantics.  The [artifact theorems](../../proofs/talos/lean/Project/EulerRiemann/ArtifactTranslation.lean) prove termination, exact output, and a 512 MiB linear-memory bound for every runtime grid size from two through eight hundred.  They cover explicit failure returns.  Status zero establishes the specified numerical trace through time 0.8 and final-state admissibility.  Their transitive audits use only `propext`, `Classical.choice`, and `Quot.sound`.  The independent package check passed before execution.  Convergence to a weak solution of the continuous Euler equations remains unproved.

Both runs returned status zero at the exact binary64 encoding of 0.8, using the same binary and one complete solve call per grid.  Host code decodes the returned words and plots the fields.  Runtimes use the run script's monotonic timer and exclude CSV generation and plotting.

| Grid and summary | Runtime | Density range | Pressure range | Data | Export figures |
|------------------|--------:|--------------:|---------------:|------|----------------|
| [192 × 192](192-run/summary.json) | 49.6 s | 0.138–1.490131234 | 0.029–1.476780108 | [Words](192-run/words.u64le), [CSV](192-run/cells.csv.gz) | [SVG](192-run/density-pressure.svg), [PDF](192-run/density-pressure.pdf) |
| [800 × 800](800-run/summary.json) | 61.6 min | 0.138–1.671084032 | 0.029–1.632146140 | [Words](800-run/words.u64le), [CSV](800-run/cells.csv.gz) | [SVG](800-run/density-pressure.svg), [PDF](800-run/density-pressure.pdf) |

The [run script](../../tools/euler-riemann-complete.js) invokes the complete solve export once under the standard runner limits.  Reproduction uses fresh output directories and the existing pinned plotting environment:

```sh
node tools/euler-riemann-complete.js run 192 new-192-directory
tools/leanrun --timeout 2m build/tools/riemann-figures-venv/bin/python tools/euler-riemann-plot.py new-192-directory
node tools/euler-riemann-complete.js run 800 new-800-directory
tools/leanrun --timeout 2m build/tools/riemann-figures-venv/bin/python tools/euler-riemann-plot.py new-800-directory
```
