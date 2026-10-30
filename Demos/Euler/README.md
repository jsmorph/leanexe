# Euler: two finite-volume solvers for the 2D Euler equations

## Two solvers on a four-quadrant Riemann problem

This example holds two solvers for the compressible Euler equations of an ideal gas on the unit
square, run on the four-quadrant Riemann problem with interfaces at x = y = 0.8 to time 0.8, the
configuration that Lax and Liu number 3.  [The first-order solver](Program.lean) uses Rusanov fluxes
and an x sweep followed by a y sweep, with time steps chosen for CFL 0.4.  [The reconstructed
solver](ReconstructedProgram.lean) builds on it with minmod slopes, positivity checks on the
reconstructed faces, and outward-rounded bounds on the signal speeds.  Both use `UInt64` and `Float`
only.  [The module definition](Module.lean) compiles both into one 23,012-byte module,
`euler.wasm`, whose `solve` and `reconstructedSolve` exports run a whole calculation, from the
initial grid to the final one, in one call.

The solvers import [checked outward rounding](../../Library/Numerics/Bounds/README.md) and [minmod](../../Library/Numerics/Limiters/README.md), including their mathematical proofs, from the library.

## Theorems about the bytes and the solvers

The solvers use grids of records, a `LeanExe.repeatWhile` loop over time steps whose grids move from
step to step, retries of rejected steps, and the sound-speed and flux arithmetic of each cell.
Beyond the bytes theorem, the proofs establish total execution: from a fresh instance with a
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
| `euler_solve_call` | From the store in which the verified compiler's module starts, under a cap that holds the closed form of the solvers' allocation bound, at most 1,563 pages for every grid, both solve exports return the Lean functions' words without a trap, as [the calls of the verified module](#calls-of-the-verified-module) describe. |
| `solve_hyperbolic`, `reconstructedSolve_hyperbolic` | Words with status 0 pack a final grid of admissible states, at which the flux in every direction has real eigenvalues and a basis of eigenvectors. |
| `run_balance`, `reconstructedRun_balance` | Along the accepted steps, each conserved total equals its initial value minus the boundary fluxes, plus a rounding residual with a computed bound. |
| `reconstructedRun_steps` | Each accepted step of the reconstructed solver starts from admissible states and has a Courant number of at most 1/2 in exact arithmetic. |
| `run_reference_balance`, `reconstructedRun_reference_balance` | Along the accepted steps, each conserved total equals its initial value minus the exact Rusanov flux through the boundary, plus a residual whose bound, computed from the words of the run, covers the rounding of the updates and the error of the computed boundary flux. |
| `interface_reference_error`, `advanceCell_reference_error` | For states within the state bounds of parameter `M`, which [the first-order record](first-order/README.md#program-and-proofs) states, each first-order interface flux component is within `304 ε M⁵` of the exact Rusanov flux, and each output of an accepted first-order cell update is within `ε M + 1004 ε r M⁵ + 2⁻¹⁰⁷⁴` of the exact update, where `ε = 2⁻⁵²` and `r` is the ratio of time step to cell width. |
| `reconstruct_accuracy`, `reconstruct_linear` | Each reconstructed face is within a bound computed from its words of `center ∓ factor · slope` with the exact minmod slope, and a linear stencil with exact arithmetic gives the exact faces `center ∓ delta / 2`. |
| `directional_wave_identities`, `directional_speed_bound_iff` | In exact arithmetic, the Rusanov flux splits a jump into two waves that sum to the jump, and `\|un\| + c` is the least bound on the absolute eigenvalues of the flux derivative in direction `n`. |

The proofs are in [`Verify.lean`](Verify.lean), [`Total.lean`](Total.lean), and the other Lean files
of this directory, with the exact-arithmetic theory of the equations, the Rusanov flux, and minmod
reconstruction in [`Equations/`](Equations) and the rounding analysis of the fluxes and updates in
[`Reference/`](Reference), and they use only the axioms `propext`, `Classical.choice`, and
`Quot.sound`.  The fresh instance is a hypothesis, since
no theorem connects instantiation to it, and convergence to a solution of the continuous equations
is unproved.  The two run records, [the first-order record](first-order/README.md) and [the
reconstructed record](reconstructed/README.md), give the full statements, the figures, and the runs
on the 192 and 800 grids.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Demos.Euler.Verify Demos.Euler.Total
mkdir -p build/euler
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Demos.Euler.Module Demos.Euler.euler.module build/euler/euler.wasm
build/tools/leanexe-wasmtime-host call build/euler/euler.wasm solve array-u64 i64:2
uv run tools/euler-run.py build/euler/euler.wasm first 192 build/euler-192
tools/leanrun --timeout 60m lake build euler-native
```

The commands build the proofs, write the module, run a 2 × 2 solve and a 192 × 192 solve, and build
the native runner, with the setup of [the repository README](../../README.md#commands).  The 2 × 2
solve prints twelve words: the status 0, the bits of 0.8, the grid size twice, the four densities,
and the four pressures.  [`tools/euler-run.py`](../../tools/euler-run.py) checks the status, the
final time, and the word count, and records the runtime and the peak resident size.  The 192 × 192
run took 16.5 seconds.  `euler-native N FILE` runs the
same solver as native Lean.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 3,096
cases of [`Cases.lean`](Cases.lean) with native Lean, from single flux evaluations to whole solves
on small grids.

## Calls of the verified module

[The verified compiler's Euler module](Verified.lean) compiles [the buffered solvers](Buffered.lean)
under the names `solve` and `reconstructedSolve`.  Each keeps three grids in the states of its
loops.  A sweep writes its cells into one of them with `set!` instead of building a new grid, and
an accepted try rotates the three grids so that the new grid comes first.  [The equality
proofs](BufferedSpec.lean) show that `Demos.Euler.Buffered.solve` and `reconstructedSolve` equal
`Demos.Euler.solve` and `Demos.Euler.reconstructedSolve` for every argument.  `loop_set` equates a
loop of `set!` over a grid of the right size with the build of a new grid, and `repeatWhile_map`
maps each loop of the buffered solvers onto the loop of the program, under the invariant that the
three grids have one size.  The module also compiles the sweeps, tries, and timesteps of the
programs, which build a new grid for each sweep, because the module cases call them.

The bound that `verified_compile` generates for a buffered solver charges nothing for a `set!` on
a grid that the loop owns and nothing for the moves of the rotation.  It charges the three initial
grids and the packed result, for any number of tries.  `solve_bound` and
`reconstructedSolve_bound` in [the call theorems](VerifiedCall.lean) bound both by
`solveBytes n`, which is `3 (48 c + 56) + 16 c + 88` bytes, where `c` is the cell count
`cells n`: `n * n` for `n` from 2 to 800, and 0 otherwise.  `48 c + 56` bytes hold a grid of
`6 c + 1` words with its 48-byte header, and `16 c + 88` bytes hold the packed result.  On the 800
grid, `solveBytes n` is 102,400,256 bytes.  `solvePages n` is the number of pages that hold the
heap base, 4096 bytes, and `solveBytes n` bytes above it, and `solvePages_le` states that it is at
most 1,563 for every grid.

| Grid | Cells | `solveBytes n` | `solvePages n` |
|---|---|---|---|
| 16 × 16 | 256 | 41,216 | 1 |
| 32 × 32 | 1,024 | 164,096 | 3 |
| 192 × 192 | 36,864 | 5,898,496 | 91 |
| 800 × 800 | 640,000 | 102,400,256 | 1,563 |

`euler_solve_call` states that the module's bytes decode to the module, whose exports `solve` and
`reconstructedSolve` are entries 28 and 66, and that `solvePages n` is at most 1,563.  From
the store in which the module starts, with a memory cap of `cap` pages, at most 65,535 and at
least `solvePages n`, the export `solve` returns without a trap the address of a new array that
holds `Demos.Euler.solve n`.  The call leaves a ready store, as `Verified.Ready` states it, whose
`top` lies at most `solveBytes n` bytes above the heap base.  The theorem states the same of
`reconstructedSolve` and `Demos.Euler.reconstructedSolve n trials` under the same cap.
`solve_callSpec` and `reconstructedSolve_callSpec` state the calls from every ready store with
room for `solveBytes n` within its cap.

`euler_solve_total`, the LeanExe module's theorem, holds under 1,407 pages for every grid and
states that memory ends within them.  `euler_solve_call` states no final page count, because no
theorem of the verified compiler bounds the pages to which memory grows, as [the journal
entry](../../devnotes.md#2026-10-30-the-verified-total-theorems-of-the-euler-solvers-and-the-drone-planner)
explains.  `advanceStep_bound` and `reconstructedAdvanceStep_bound` bound the timesteps that build
new grids by two grids for each try, through `loopCost_le_mul`.  On Wasmtime, the buffered solvers
return the words of the earlier module's solvers in the same time, from 0.2 seconds on the 32 grid
to 119 seconds for the reconstructed solver on the 192 grid, as [the journal
entry](../../devnotes.md#2026-10-30-the-buffered-euler-solvers-and-a-call-theorem-for-every-grid)
records.  `tools/leanrun --timeout 60m lake build Demos.Euler.VerifiedCall` builds the call
theorems.

## Related examples

[The verified compiler's Euler module](Verified.lean) compiles the functions of both solvers with
`verified_compile`, with the buffered solvers in place of the runs.  Its generated execution and
byte theorems compute both solvers, and [the calls of the verified module](#calls-of-the-verified-module) carry its
trap-free theorems to the store in which it starts.  `tests/verified/run.sh --cases euler` builds
and emits the verified compiler's module and runs the existing corpus against it.

[`Grids`](../../Examples/Grids/README.md) has arrays of records in the layout of the solvers' grids.
[`Drone`](../Drone/README.md) is the other large program with total execution and a memory bound,
and [`Increment`](../../Examples/Increment/README.md) the smallest.  The LTG entries
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
- Lanyon.AI, [The Euler Equations of Gas Dynamics](https://lanyon.ai/research/euler-equations/).
