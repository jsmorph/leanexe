# Euler: two finite-volume solvers for the 2D Euler equations

## Solvers on a four-quadrant Riemann problem

This example holds solvers for the compressible Euler equations of an ideal gas on the unit
square, run on the four-quadrant Riemann problem with interfaces at x = y = 0.8 to time 0.8, the
configuration that Lax and Liu number 3.  [The first-order solver](Program.lean) uses Rusanov fluxes
and an x sweep followed by a y sweep, with time steps chosen for CFL 0.4.  [The reconstructed
solver](ReconstructedProgram.lean) builds on it with minmod slopes, positivity checks on the
reconstructed faces, and outward-rounded bounds on the signal speeds.  The solvers take [checked
outward rounding](../../Library/Numerics/Bounds/README.md) and
[minmod](../../Library/Numerics/Limiters/README.md) from the library, whose mathematical proofs the
theorems of this directory use.  Both use `UInt64` and `Float` only.  [The verified
module](Verified.lean) compiles both with `verified_compile`, and its exports `solve` and
`reconstructedSolve` run a whole calculation, from the initial grid to the final one, in one call.

## Theorems about the module and the solvers

`euler_solve_call` carries the module's generated theorems to the Lean solvers through `solve_eq`
and `reconstructedSolve_eq`, which equate the buffered solvers that the module compiles with the
programs.  The other theorems state properties of the Lean programs: positive density and pressure
of the final states in exact arithmetic, hyperbolicity of the flux at those states, conservation up
to a bounded rounding residual, and, for the reconstructed solver, a CFL bound in exact
arithmetic.  The rounding analysis compares the computed fluxes, updates, and reconstructions with
their exact-arithmetic counterparts, and the conservation theorems also hold with the exact Rusanov
flux through the boundary in place of the computed one.

| Theorem | Statement |
|---------|-----------|
| `euler_solve_call` | From the store in which the module starts, under a memory cap of at least `solvePages n` and at most 65,535 pages, both solve exports return the words of `solve` and `reconstructedSolve` without a trap, as [the calls of the verified module](#calls-of-the-verified-module) describe. |
| `solve_eq`, `reconstructedSolve_eq` | `Demos.Euler.Buffered.solve` and `reconstructedSolve`, which the module compiles, equal `solve` and `reconstructedSolve` for every argument. |
| `solve_hyperbolic`, `reconstructedSolve_hyperbolic` | Words with status 0 pack a final grid of admissible states, at which the flux in every direction has real eigenvalues and a basis of eigenvectors. |
| `run_balance`, `reconstructedRun_balance` | Along the accepted steps, each conserved total equals its initial value minus the boundary fluxes, plus a rounding residual with a computed bound. |
| `reconstructedRun_steps` | Each accepted step of the reconstructed solver starts from admissible states and has a Courant number of at most 1/2 in exact arithmetic. |
| `run_reference_balance`, `reconstructedRun_reference_balance` | Along the accepted steps, each conserved total equals its initial value minus the exact Rusanov flux through the boundary, plus a residual whose bound, computed from the words of the run, covers the rounding of the updates and the error of the computed boundary flux. |
| `interface_reference_error`, `advanceCell_reference_error` | For states within the state bounds of parameter `M`, which [the first-order record](first-order/README.md#program-and-proofs) states, each first-order interface flux component is within `304 ε M⁵` of the exact Rusanov flux, and each output of an accepted first-order cell update is within `ε M + 1004 ε r M⁵ + 2⁻¹⁰⁷⁴` of the exact update, where `ε = 2⁻⁵²` and `r` is the ratio of time step to cell width. |
| `reconstruct_accuracy`, `reconstruct_linear` | Each reconstructed face is within a bound computed from its words of `center ∓ factor · slope` with the exact minmod slope, and a linear stencil with exact arithmetic gives the exact faces `center ∓ delta / 2`. |
| `directional_wave_identities`, `directional_speed_bound_iff` | In exact arithmetic, the Rusanov flux splits a jump into two waves that sum to the jump, and `\|un\| + c` is the least bound on the absolute eigenvalues of the flux derivative in direction `n`. |

The proofs are in the Lean files of this directory, with the exact-arithmetic theory of the
equations, the Rusanov flux, and minmod reconstruction in [`Equations/`](Equations) and the
rounding analysis of the fluxes and updates in [`Reference/`](Reference), and they use only the
axioms `propext`, `Classical.choice`, and `Quot.sound`.  `euler_solve_call` holds of the modeled
store in which the module starts, and instantiation by a WebAssembly engine lies outside the
proofs, as [the verified compiler manual](../../docs/verified-manual.md#outside-the-proofs) states.
Convergence to a solution of the continuous equations is unproved.  [The first-order
record](first-order/README.md) and [the reconstructed record](reconstructed/README.md) give the
full statements, the figures, and the runs on the 192 and 800 grids.

## Calls of the verified module

[The verified module](Verified.lean) compiles [the buffered solvers](Buffered.lean) under the names
`solve` and `reconstructedSolve`.  Each keeps three grids in the states of its loops.  A sweep
writes its cells into one of them with `set!` instead of building a new grid, and an accepted try
rotates the three grids so that the new grid comes first.  [The equality proofs](BufferedSpec.lean)
show that `Demos.Euler.Buffered.solve` and `reconstructedSolve` equal `Demos.Euler.solve` and
`Demos.Euler.reconstructedSolve` for every argument.  `loop_set` equates a loop of `set!` over a
grid of the right size with the build of a new grid, and `repeatWhile_map` maps each loop of the
buffered solvers onto the loop of the program, under the invariant that the three grids have one
size.  The module also compiles the sweeps, tries, and timesteps of the programs, which build a new
grid for each sweep, because the module cases call them.

The bound that `verified_compile` generates for a function counts the bytes by which `top` can
rise during a call and ignores the reuse of freed blocks, as [the verified compiler
manual](../../docs/verified-manual.md#bounds-and-total-execution) describes.  For a buffered solver,
it charges nothing for a `set!` on a grid that the loop owns and nothing for the moves of the
rotation.  It charges the three initial grids and the packed result, for any number of tries.
`solve_bound` and `reconstructedSolve_bound` in [the call theorems](VerifiedCall.lean) bound both
by `solveBytes n`, which is `3 (48 c + 56) + 16 c + 88` bytes, where `c` is the cell count
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

`euler_solve_call` states no final page count, because no theorem of the verified compiler bounds
the pages to which memory grows, as [the journal entry on the call
theorems](../../devnotes.md#2026-10-30-the-verified-total-theorems-of-the-euler-solvers-and-the-drone-planner)
explains.  `advanceStep_bound` and `reconstructedAdvanceStep_bound` bound the timesteps that build
new grids by two grids for each try, through `loopCost_le_mul`.  On Wasmtime, the buffered solvers
took from 0.2 seconds on the 32 grid to 119 seconds for the reconstructed solver on the 192 grid,
as [the journal entry on the buffered
solvers](../../devnotes.md#2026-10-30-the-buffered-euler-solvers-and-a-call-theorem-for-every-grid)
records.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Demos.Euler.VerifiedCall Demos.Euler.SpeedCounterexample \
  Demos.Euler.Hyperbolic Demos.Euler.Reference.Boundary Demos.Euler.Reference.Update \
  Demos.Euler.ReconstructionAccuracy Demos.Euler.Equations.ReconstructionCounterexample
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Demos.Euler.Verified Demos.Euler.Verified.compiled.module build/verified/euler.wasm
tools/leanrun --timeout 10m lake env lean Demos/Euler/File.lean
build/tools/leanexe-wasmtime-host call build/verified/euler.wasm solve array-u64 i64:2
uv run tools/euler-run.py build/verified/euler.wasm first 192 build/euler/first-192
tools/leanrun --timeout 60m lake build euler-native
tests/verified/run.sh --cases euler
```

The commands build the proofs, write the module, check its file theorems, run a 2 × 2 solve and a
192 × 192 solve, build the native runner, and run the module cases, with the setup of [the
repository README](../../README.md#commands).  `euler_file` and `euler_file_decode` in [the file
module](File.lean) state that `build/verified/euler.wasm` holds the encoding of the module and
decodes to it.  The 2 × 2 solve prints twelve words: the status, the bits of the final time, the
grid size twice, the four densities, and the four pressures.
[`tools/euler-run.py`](../../tools/euler-run.py) checks the status, the final time, and the word
count, and records the runtime and the peak resident size.  `euler-native N FILE` runs the
first-order solver as native Lean, and `euler-native N FILE TRIALS` the reconstructed solver.

`tests/verified/run.sh --cases euler` builds, writes, and validates the module, and it runs
[`tests/modules/run.sh`](../../tests/modules/run.sh) with `--module euler`, which compares 3,096
cases of [`Cases.lean`](Cases.lean), from single flux evaluations to whole solves on small grids,
between the Wasmtime host and native Lean.  `tests/native/verified.sh --module euler` runs the same
cases on the module's translation to C compiled with CompCert.
`tests/baremetal/verified.sh --module euler` runs them under QEMU without an operating system and
checks the stack of each call against its bound.

## Related examples

[`Grids`](../../Examples/Grids/README.md) has arrays of records in the layout of the solvers'
grids.  [`Drone`](../Drone/README.md) is the other large program with a call theorem that bounds
the rise of `top`.  [`Increment`](../../Examples/Increment/README.md) proves a call theorem of the
same kind for a program that adds one to each word of an array of at most eight words.

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
