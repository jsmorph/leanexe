# Checked conservative grid step

[The source](../../../../../LeanExe/Examples/EulerGridStep.lean) accepts a flat
array of conservative triples and uses transmissive end states. A checked
maximum-speed scan supports adaptive time steps. The step reads the old grid
and fills a separate result array: a leading status, followed by six words
per cell (density, momentum, energy, pressure, signal speed, rounded Courant).
Malformed shape or invalid ratio returns `#[1]`. A cell rejection sets status
one and stops; its partially written payload must not be used as a new grid.
Input reads use total `getD` with zero defaults, which preserves strict calls
to the existing checked-cell function without changing the compiler.

[Model.lean](Model.lean) names the finite scan and fill recurrences.
[Safety.lean](Safety.lean) proves output size, preservation of earlier words,
persistence of rejection, and acceptance of every requested cell computation
when the fill returns status zero. These model theorems use standard logical
axioms. [Payload.lean](Payload.lean) proves exact correspondence of all six
fields and preservation by subsequent cells. [Outputs.lean](Outputs.lean)
transfers accepted state, pressure, speed and Courant safety to the actual
returned array and proves its expected length. Scan bounds, generated-WAT
array execution and frozen-byte verification remain open; this is not yet a
registered complete source case or artifact package.

[The focused regression](../../../../../test/euler_grid_step.js) passes 31
compiled cases covering single-cell boundaries, moving uniform states,
two-cell and initial 100-cell Sod grids, malformed shape, bad states, invalid
ratios, CFL rejection and final-state rejection. IR/WAT checks confirm that
the array wrapper reuses one cell-call boundary without additional floating
point arithmetic. A preliminary compiled 100-cell run reaches t=0.2 in 93
steps and matches all 300 final raw state words of the independent host
calculation. That run is runtime evidence; runner proofs and a maintained
scientific data package are still pending.

Run focused checks serially:

```sh
source tools/macos-env.sh
tools/leanrun --timeout 2m lake --no-ansi build LeanExe.Examples.EulerGridStep
tools/leanrun --timeout 2m lake -d proofs/talos/lean --no-ansi build Project.EulerGridStep.Outputs
node test/euler_grid_step.js
```
