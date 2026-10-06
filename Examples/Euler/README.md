# Euler: two finite-volume solvers for the 2D Euler equations

## What it is

This example holds two solvers for the compressible Euler equations of an ideal gas on the unit
square, run on the four-quadrant Riemann problem with interfaces at x = y = 0.8 to time 0.8, the
configuration that Lax and Liu number 3.  [The first-order solver](Program.lean) uses Rusanov fluxes
and an x sweep followed by a y sweep, with time steps chosen for CFL 0.4.  [The reconstructed
solver](ReconstructedProgram.lean) builds on it with minmod slopes, positivity checks on the
reconstructed faces, and outward-rounded bounds on the signal speeds.  Both use `UInt64` and `Float`
only.  Their arithmetic performs the binary64 operations of the two solvers at commit `eef07963` in
the same order, and on the 192 and 800 grids they return, bit for bit, the output words recorded at
that commit.  [The module definition](Module.lean) compiles both into one 23,012-byte module,
`euler.wasm`, whose `solve` and `reconstructedSolve` exports run a whole calculation, from the
initial grid to the final one, in one call.

## What it shows

The solvers use grids of records, a `LeanExe.repeatWhile` loop over time steps whose grids move from
step to step, retries of rejected steps, and the sound-speed and flux arithmetic of each cell.
Beyond the bytes theorem, the proofs establish complete execution: from a fresh instance with a
memory cap of at least 1,407 pages, both exports return without a trap and end within 1,407 pages,
or 88 MiB.  They also prove properties of the Lean programs: positive density and pressure of the
final states in exact arithmetic, hyperbolicity of the flux at those states, conservation up to a
bounded rounding residual, and, for the reconstructed solver, a CFL bound in exact arithmetic.  The
rounding analysis compares the computed fluxes, updates, and reconstructions with their
exact-arithmetic counterparts, and the conservation theorems also hold with the exact Rusanov flux
through the boundary in place of the computed one.

| Theorem | Statement |
|---------|-----------|
| `euler_bytes` | `encode` succeeds on `euler.module`, and the decoded module implements its 22 functions from `normalized` to `solve`. |
| `euler_solve`, `euler_reconstructed_solve` | The two solve exports implement `solve` and `reconstructedSolve` for any grid size. |
| `euler_solve_total` | From a fresh instance under a cap of at least 1,407 pages, both solve exports return the Lean functions' words without a trap and end within 1,407 pages. |
| `solve_hyperbolic`, `reconstructedSolve_hyperbolic` | Words with status 0 pack a final grid of admissible states, at which the flux in every direction has real eigenvalues and a basis of eigenvectors. |
| `run_balance`, `reconstructedRun_balance` | Along the accepted steps, each conserved total equals its initial value minus the boundary fluxes, plus a rounding residual with a computed bound. |
| `reconstructedRun_steps` | Each accepted step of the reconstructed solver starts from admissible states and has a Courant number of at most 1/2 in exact arithmetic. |
| `run_reference_balance`, `reconstructedRun_reference_balance` | Along the accepted steps, each conserved total equals its initial value minus the exact Rusanov flux through the boundary, plus a residual whose bound, computed from the words of the run, covers the rounding of the updates and the error of the computed boundary flux. |
| `interface_reference_error`, `advanceCell_reference_error` | For states within the state bounds of parameter `M`, which [the first-order record](first-order/README.md#program-and-proofs) states, each first-order interface flux component is within `304 ε M⁵` of the exact Rusanov flux, and each output of an accepted first-order cell update is within `ε M + 1004 ε r M⁵ + 2⁻¹⁰⁷⁴` of the exact update, where `ε = 2⁻⁵²` and `r` is the ratio of time step to cell width. |
| `reconstruct_accuracy`, `reconstruct_linear` | Each reconstructed face is within a bound computed from its words of `center ∓ factor · slope` with the exact minmod slope, and a linear stencil with exact arithmetic gives the exact faces `center ∓ delta / 2`. |
| `directional_wave_identities`, `directional_speed_bound_iff` | In exact arithmetic, the Rusanov flux splits a jump into two waves that sum to the jump, and `\|un\| + c` is the least bound on the absolute eigenvalues of the flux derivative in direction `n`. |

The proofs are in [`Verify.lean`](Verify.lean), [`Total.lean`](Total.lean), and the other Lean files
of this directory, with the exact-arithmetic theory of the equations, the Rusanov flux, and minmod
reconstruction in [`Equations/`](Equations/) and the rounding analysis of the fluxes and updates in
[`Reference/`](Reference/), and they use only the axioms `propext`, `Classical.choice`, and
`Quot.sound`.  The fresh instance is a hypothesis, since
no theorem connects instantiation to it, and convergence to a solution of the continuous equations
is unproved.  The two run records, [the first-order record](first-order/README.md) and [the
reconstructed record](reconstructed/README.md), give the full statements, the figures, and the runs
on the 192 and 800 grids.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Euler.Verify Examples.Euler.Total
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Euler.Module Examples.Euler.euler.module build/euler/euler.wasm
build/tools/leanexe-wasmtime-host call build/euler/euler.wasm solve array-u64 i64:2
uv run tools/euler-run.py build/euler/euler.wasm first 192 build/euler-192
tools/leanrun --timeout 60m lake build euler-native
```

The commands build the proofs, write the module, run a 2 × 2 solve and a 192 × 192 solve, and build
the native runner, with the setup of [the repository README](../../README.md#commands).  The 2 × 2
solve prints twelve words: the status 0, the bits of 0.8, the grid size twice, the four densities,
and the four pressures.  [`tools/euler-run.py`](../../tools/euler-run.py) checks the status, the
final time, and the word count, and records the runtime, the peak resident size, and the SHA-256 of
the words.  The 192 × 192 run took 16.5 seconds, and the SHA-256 of its words, `e097a43d…`, equals
the value in [the first-order record](first-order/README.md#data).  `euler-native N FILE` runs the
same solver as native Lean.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 3,096
cases of [`Cases.lean`](Cases.lean) with native Lean, from single flux evaluations to whole solves
on small grids.

## Related examples

[`Grids`](../Grids/README.md) has arrays of records in the layout of the solvers' grids.
[`Drone`](../Drone/README.md) is the other large program with complete execution and a memory bound,
and [`Increment`](../Increment/README.md) the smallest.  The LTG entries
[`repeat-while`](../../ltg/entries/repeat-while/README.md) and
[`one-array-call`](../../ltg/entries/one-array-call/README.md) use this example's proofs as worked
examples.

## References

- P. D. Lax and X.-D. Liu, "Solution of Two-Dimensional Riemann Problems of Gas Dynamics by Positive
  Schemes," *SIAM Journal on Scientific Computing* 19(2):319–340, 1998.
- A. Kurganov and E. Tadmor, "Solution of Two-Dimensional Riemann Problems for Gas Dynamics
  without Riemann Problem Solvers," *Numerical Methods for Partial Differential Equations*
  18(5):584–608, 2002.
- V. V. Rusanov, "The Calculation of the Interaction of Non-Stationary Shock Waves and Obstacles,"
  *USSR Computational Mathematics and Mathematical Physics* 1(2):304–320, 1962.
- B. van Leer, "Towards the Ultimate Conservative Difference Scheme. V. A Second-Order Sequel to
  Godunov's Method," *Journal of Computational Physics* 32(1):101–136, 1979.
- E. F. Toro, *Riemann Solvers and Numerical Methods for Fluid Dynamics*, 3rd ed., Springer, 2009.
- [The Lanyon Euler article](https://lanyon.ai/research/euler-equations/), whose figures the run
  records compare.
