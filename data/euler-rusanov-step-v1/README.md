# Verified two-cell Euler step data

This dataset records one first-order Rusanov update of the two-cell Sod state
on `[0, 1]`.  The cells have width `1/2`; the time step is `1/8`, so
`dt/dx = 1/4`.  The ideal-gas ratio is `7/5`, the fixed dissipation speed is
`7/4`, and the boundary interfaces use the respective initial end states.
The right pressure input is the binary64 encoding `3fb999999999999a`.

The raw CSV comes from the registered 2,551-byte WebAssembly artifact, SHA-256
`0e4ec3be7480e0490a8637536501ba4b2adf84df66c4a4a45819b0e62d622511`.
It calls `sodQuarterStepCheckedBits` with no arguments and records its seven
returned words in source ABI order.  The status is zero.  Each numerical word
has exactly sixteen hexadecimal digits; neither decimal conversion nor
host floating-point computation determines these words.

| File | Meaning |
|------|---------|
| [euler-rusanov-step-v1.csv](euler-rusanov-step-v1.csv) | Two conservative cell states as exact raw binary64 words. |
| [exact-comparison.csv](exact-comparison.csv) | Exact decoded values, an independent rational stencil reference, and their signed differences. |
| [presentation.csv](presentation.csv) | Host decimal density, momentum, energy, velocity, and pressure for convenient analysis. |
| [cell-averages.svg](cell-averages.svg) | Initial and updated cell averages. |
| [manifest.json](manifest.json) | Artifact and generator identities, output digests, theorem reference, and exact balance residuals. |

The theorem
[`Project.EulerRusanovStep.StepData.artifact_stepV1`](../../proofs/talos/lean/Project/EulerRusanovStep/StepData.lean)
starts from the exact frozen bytes.  It establishes decoding, validation,
`CoreValid`, fuel-independent termination, complete store preservation, the
seven published words, and the existing decoded-real numerical certificate.
The numerical certificate proves that all six payload words are finite and
that both decoded conservative states have positive density and pressure.

Writing `epsilon = 2^-52`, the signed errors relative to the exact-real stencil
applied to the decoded inputs are:

| Cell | Density error | Momentum error | Energy error |
|------|---------------|----------------|--------------|
| Left | `0` | `-3*epsilon/64` | `-7*epsilon/512` |
| Right | `0` | `5*epsilon/64` | `-25*epsilon/512` |

The physical two-cell balance residual is `[0, epsilon/32, -epsilon/16]`.
The momentum and energy residuals are nonzero even though an independently
rounded balance calculation can return zero.  The exact comparison uses
BigInt rational arithmetic and reconstructs the real conservative states and
Rusanov stencil separately from the executable expression tree.  It is
regression evidence; the Lean theorem supplies the formal certificate.

Reproduce and check the existing dataset from the repository root:

```sh
source tools/macos-env.sh
node tools/euler-rusanov-step-data.js check
node test/euler_rusanov_step_data.js
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build Project.EulerRusanovStep.StepData
```

The generator's `write` command creates absent files and accepts existing
identical files.  It refuses to replace differing published data.  CSV
serialization, host decimal values, the SVG, and the independent rational
comparison remain outside the formal proof.  This dataset is one fixed step;
it is not the full 100-cell time integration or a convergence certificate.
