# Checked 2D directional Rusanov flux

The conservative state has four raw binary64 words: density, normal momentum,
transverse momentum and total energy. Both momentum components contribute to
kinetic energy. The y direction uses the same function with the momentum roles
exchanged. The [source](../../../../../LeanExe/Examples/Euler2DDynamicFlux.lean)
returns status, mass flux, normal-momentum flux, transverse-momentum flux,
energy flux and the selected signal speed.

[Spec.lean](Spec.lean) proves termination and exact six-word results for every
eight-word input and initial store, preserving the complete store. Accepted
results have physically admissible left/right states, four finite flux fields
and positive finite alpha. Every component uses the same checked six-operation
scalar Rusanov formula as the 1D interface. Its proof now takes only a minimal
scalar/component layout; the old public theorem signature is preserved.
These are sufficient-domain, rounded-operation safety claims, not a proof of
PDE convergence or unconditional acceptance.

The [frozen package](../../../../artifacts/euler2_d_dynamic_flux/394dd856d26b0eae32388a451765e7c2b623812376d585a896d87b820d0ef734/manifest.json)
contains 3,514 bytes, SHA-256
394dd856d26b0eae32388a451765e7c2b623812376d585a896d87b820d0ef734.
Function17 is the public flux; function5 is the 2D side and function9 is the
shared scalar component. Public execution/safety audits use only propext,
Classical.choice and Quot.sound. Exact-artifact cache witnesses follow the
existing independent artifact policy.

The focused [Wasmtime regression](../../../../../test/euler_2d_dynamic_flux.js)
checks all six raw results for 71 cases: discontinuities in either order,
nonzero transverse transport, signed zero, adjacent guard words, underflow,
overflow and nonfinite inputs in every slot. It checks emitted f64 opcode
counts as well. Runtime comparisons supplement the theorems. The four-component
cell update and complete 2D visualization remain in the
[active plan](../../../../../plans/euler-rusanov.md).
