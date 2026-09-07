# Checked conservative Euler thermodynamics

[The source](../../../../../LeanExe/Examples/EulerConservative.lean) accepts
raw density, momentum, and total-energy binary64 words. It returns seven
words: status, velocity, pressure, signal speed, and the three physical flux
components. Rejection returns status one and six positive-zero words.

The first implementation uses a conservative sufficient domain: all inputs
finite, density positive, absolute momentum at most density, and energy at
least density. The energy word must be positive before unsigned ordering.
The source checks every rounded intermediate, including a positive finite
radicand before square root and a finite enthalpy before acceptance.

[Guard.lean](Guard.lean) proves accepted input words decode to physically
admissible Euler states, with exact internal energy at least density/2.
[Safety.lean](Safety.lean) proves accepted pure Talos model status implies
that input guard and finiteness of all twelve rounded intermediates.
[Execution.lean](Execution.lean) proves total exact generated-WAT execution
for every three raw input words, with complete store preservation and exact
seven-word output. [Spec.lean](Spec.lean) attaches input admissibility and
intermediate finiteness to that execution. The helper proofs are parameterized
by a closed module layout for later composition. All public theorems use
only propext, Classical.choice, and Quot.sound (or a subset).

[The focused regression](../../../../../test/euler_conservative.js) checks six
accepted results and 32 rejections in compiled Wasmtime execution, plus exact
IR/WAT arithmetic counts. It covers the Sod states, signed zero, adjacent
guard boundaries, invalid values, intermediate underflow/overflow, and the
published cancellation and one-sided-NaN examples.

The generated module is 2,019 bytes; source/cache regeneration is checked.
The frozen binary package, dynamic Rusanov interface, array step, and
100-cell runner remain pending. It makes no general
roundoff, invariant-domain preservation, stability, or PDE convergence claim.

Run the focused checks serially from the repository root:

```sh
source tools/macos-env.sh
tools/leanrun --timeout 5m lake --no-ansi build LeanExe.Examples.EulerConservative
node tools/talos-proof.js check euler_conservative
node test/euler_conservative.js
```
