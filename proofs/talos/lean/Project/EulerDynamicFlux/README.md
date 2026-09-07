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
computed speeds. These are pure IEEE model theorems; the exact generated-WAT
and frozen-byte interface proofs remain pending. They make no general
roundoff, invariant-domain preservation, stability or convergence claim.

[The regression](../../../../../test/euler_dynamic_flux.js) checks 15 component
cases and 61 interfaces in compiled Wasmtime execution, plus IR/WAT operation
counts. It includes five fixed accepted interface results, nonfinite inputs
in all six positions, both orientations of the published cancellation and
one-sided-NaN examples, and viscosity overflow from individually accepted sides.

Run these focused checks serially:

```sh
source tools/macos-env.sh
tools/leanrun --timeout 2m lake --no-ansi build LeanExe.Examples.EulerDynamicFlux
tools/leanrun --timeout 2m lake -d proofs/talos/lean --no-ansi build Project.EulerDynamicFlux.Safety
node test/euler_dynamic_flux.js
```
