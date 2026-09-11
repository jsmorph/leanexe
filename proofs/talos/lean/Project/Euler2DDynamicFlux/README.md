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

The [frozen package](../../../../artifacts/euler2_d_dynamic_flux/a35295b198aba7800be2f36c10c73d928225b11ac8a1fce8eb00f6848aef2995/manifest.json)
contains 4,495 bytes, SHA-256
a35295b198aba7800be2f36c10c73d928225b11ac8a1fce8eb00f6848aef2995.
Function 25 is the public flux.  Function 13 is the 2D side, and function 17
is the shared scalar component.  [Helper Execution](Helpers.lean) transports
the component proof through the function-index change.  Public execution/safety audits use only propext,
Classical.choice and Quot.sound. Exact-artifact cache witnesses follow the
existing independent artifact policy.

The focused [Wasmtime test](../../../../../test/euler_2d_dynamic_flux.js)
checks all six raw results for 75 cases: discontinuities in either order,
nonzero transverse transport, signed zero, adjacent guard words, underflow,
overflow, the four Riemann quadrant states, and nonfinite inputs in every
slot.  It checks emitted f64 opcode counts as well.  Runtime comparisons
supplement the theorems.  The [Euler plan](../../../../../plans/euler-rusanov.md)
records the visualization work.
