# Checked 2D directional cell update

The [source](../../../../../LeanExe/Examples/Euler2DCellStep.lean) takes thirteen
raw binary64 words: dt/dx, then three neighboring four-component states
(density, normal momentum, transverse momentum, total energy). It computes
two dynamic Rusanov interfaces, checks the rounded CFL in (0,1/2], advances
all four conserved quantities, and checks the complete updated state. The y
sweep exchanges normal/transverse roles and uses dt/dy.

[Specification](Spec.lean) proves terminating WASM execution of function 35
for every raw input and initial store, complete store preservation, and exact
eight-word results: status, density, both momenta, energy, pressure, alpha and
Courant number. An accepted result satisfies the sufficient physical-state
domain, has strictly positive finite pressure/speed, and its rounded Courant
number decodes to a real value in (0,1/2]. Rejection returns status1 and seven
zero words. Acceptance is checked, not assumed for arbitrary incoming states.

The scalar update body is identical to the old1D operation except its local
function/type index. Its generalized [proof](../EulerCellStep/Update.lean)
preserves the old public signature. Public execution/safety audits use only
propext, Classical.choice and Quot.sound.

The [exact package](../../../../artifacts/euler2_d_cell_step/5bf42c31171b77f5480a15f48e26117b7956b5718fcfe3fb6f0d2dd5b75ed942/manifest.json)
contains 6,171 bytes, SHA-256
5bf42c31171b77f5480a15f48e26117b7956b5718fcfe3fb6f0d2dd5b75ed942.
Its existing-policy generated decoder/validator witnesses are separate from
the standard-axiom public behavior proofs.

The [focused test](../../../../../test/euler_2d_cell_step.js) covers
84 cases, including moving transverse momentum, signed zero, subnormal time
ratio, exact and adjacent CFL words, every nonfinite input slot, invalid
neighbors, the four Riemann states, and an updated state accepted beyond the
original sufficient domain.  All raw
results and emitted opcode counts are checked under the pinned Wasmtime C API.
The independent [host oracle](../../../../../tools/euler-2d-oracle.mjs) is
regression evidence; no claim is made that its JavaScript implementation is
formally proved. [Sweep.lean](Sweep.lean) proves axis exchange, clamped neighbor selection,
accepted-grid safety and every actual cell call. [Runner.lean](Runner.lean)
proves the accepted x/y time-step trace for arbitrary finite ratio lists and
certifies the four-quadrant and circular-pulse initial states. [ArtifactRunner.lean](ArtifactRunner.lean)
transfers that contract to the exact cell bytes. The native grid/time
orchestration remains outside formal proof. The [completed dataset and
visualizations](../../../../../data/euler-2d-v1/README.md) contain two 192²
runs with full raw-word comparisons, 21-frame animations and SVG/PNG posters.
