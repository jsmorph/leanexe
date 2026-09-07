# Checked dynamic Rusanov interface

[The source](../../../../../LeanExe/Examples/EulerDynamicFlux.lean) accepts
six raw words representing two conservative states and returns status, mass
flux, momentum flux, energy flux and signal speed. Rejection is status one
with four positive-zero words.

Both sides must pass [the checked thermodynamic calculation](../EulerConservative/README.md)
before selecting the larger positive signal-speed encoding. Each component
then computes one explicitly associated Rusanov flux and checks all six
rounded intermediates. The sufficient input domain is unchanged: finite
states with positive density, absolute momentum at most density, and energy
at least density. The implementation rejects invalid states and overflow.

[Safety.lean](Safety.lean) proves component intermediate/result finiteness,
both-side acceptance and physical admissibility, finite accepted fluxes,
and positive finite selected speed. The speed-order lemma bounds both decoded
computed speeds. [Component.lean](Component.lean) proves all scalar component
paths, and [Execution.lean](Execution.lean) composes two state calls and three
component calls into total exact generated-WAT execution for all six raw
inputs, with five exact result words and complete store preservation.
[Spec.lean](Spec.lean) attaches the model safety properties to execution.
All public execution/safety theorems use only the standard logical axioms.
The 3,167-byte module passes source/cache regeneration; its frozen-byte
package remains pending. No general roundoff, invariant-domain preservation,
stability or convergence claim is made.

[The regression](../../../../../test/euler_dynamic_flux.js) checks 15 component
cases and 61 interfaces in compiled Wasmtime execution, plus IR/WAT operation
counts. It includes five fixed accepted interface results, nonfinite inputs
in all six positions, both orientations of the published cancellation and
one-sided-NaN examples, and viscosity overflow from individually accepted sides.

Run these focused checks serially:

```sh
source tools/macos-env.sh
tools/leanrun --timeout 2m lake --no-ansi build LeanExe.Examples.EulerDynamicFlux
node tools/talos-proof.js check euler_dynamic_flux
node test/euler_dynamic_flux.js
```
