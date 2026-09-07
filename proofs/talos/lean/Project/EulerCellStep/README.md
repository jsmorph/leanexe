# Checked conservative cell update

[The source](../../../../../LeanExe/Examples/EulerCellStep.lean) takes a positive
binary64 ratio dt/dx and three neighboring conservative states. It computes
two checked dynamic Rusanov interfaces, selects their maximum signal speed,
and checks the rounded Courant number against 1/2. Three checked scalar
updates retain the subtraction/multiplication/subtraction association. The
new state must pass the checked thermodynamic calculation before acceptance.

The seven result words are status, density, momentum, energy, pressure,
signal speed and Courant number. Rejection returns status one and six
positive-zero words. [Model.lean](Model.lean) mirrors this IEEE recurrence.
[Safety.lean](Safety.lean) proves all three scalar update intermediates
finite on acceptance, accepted-state finiteness and physical admissibility,
positive finite pressure, a decoded rounded Courant number in (0, 1/2], and positive finite selected speed.
Its five public theorems use only standard logical axioms. The sufficient
state domain remains absolute momentum at most density and energy at least
density; the new-state check can reject a physically admissible state outside
that conservative domain. No unconditional invariant-preservation or
stability theorem is asserted.

[The regression](../../../../../test/euler_cell_step.js) contains 16 scalar
updates and 27 full cell cases, including the two adjacent ratios that both
round to CFL 1/2, the first ratio above the ceiling, overflow in each update
stage, published invalid states, and final-state rejection after valid
incoming states and CFL. Fixed host words serve as regression evidence.
[Update.lean](Update.lean) proves every scalar path, and
[Execution.lean](Execution.lean) composes the complete cell calculation with
exact words and complete store preservation for all ten raw inputs.
[Spec.lean](Spec.lean) attaches model state/Courant/speed safety to execution.
All public execution proofs use only standard logical axioms. The generated
4,592-byte binary awaits frozen-package verification; the array step and
repeated Sod runner follow.

Run focused checks serially:

```sh
source tools/macos-env.sh
tools/leanrun --timeout 2m lake --no-ansi build LeanExe.Examples.EulerCellStep
node tools/talos-proof.js check euler_cell_step
node test/euler_cell_step.js
```
