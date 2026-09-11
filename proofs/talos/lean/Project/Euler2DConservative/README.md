# Checked two-dimensional conservative state

[Source](../../../../../LeanExe/Examples/Euler2DConservative.lean) and
[Model](Model.lean) compute normal velocity, transverse kinetic energy,
pressure, normal signal speed, and all four directional physical fluxes from
(rho, normal momentum, transverse momentum, total energy). Swapping momentum
roles supplies the other Cartesian direction. Both kinetic terms contribute
to pressure; the transverse flux is transverse momentum times normal velocity.

The guard accepts the union of two sufficient domains.  The original branch
requires positive finite density and energy, finite momenta with magnitudes
at most density, and energy greater than density.  The second branch uses
an exact common power-of-two normalization and checks the residual
rho times energy minus half the squared momentum norm.  Its rounded residual
must exceed eight arithmetic epsilons, while its proved error is at most
five epsilons.  [Guard](Guard.lean) proves positive exact internal energy
for either accepted branch.  The second branch accepts the four states in
the requested Lanyon Riemann problem.
[Safety](Safety.lean) proves all 16 rounded thermodynamic intermediates finite and accepted
input states physically admissible. [Outputs](Outputs.lean) proves positive
finite rounded pressure and signal speed.

The shared [strict magnitude-order lemma](../ProofKit/F64StrictOrder.lean)
handles sign-cleared encodings, including zero/subnormal/exponent boundaries.
All public numerical audits use only the accepted standard logical axioms.
The [exact generated-WAT execution](Execution.lean) and [public safety contract](Spec.lean)
pass for all raw inputs, including every rejection branch and complete store
preservation. [Helpers](Helpers.lean) reuses the three shared scalar guard
proofs under a minimal layout; [StateGuard](StateGuard.lean) handles both
branches.  [Guard Operations](GuardOperations.lean) and
[Energy Guard Execution](EnergyGuard.lean) prove the normalization path.

The 3,193-byte [frozen package](../../../../artifacts/euler2_d_conservative/607008ccfe4c7cc7c721aa459eb7c5442cbeb569b7281b9958f2cdce87132a1d/manifest.json)
has public entry index 13.  [ArtifactTranslation](ArtifactTranslation.lean) connects the
exact bytes to the execution module; generated decoder-cache witnesses follow
the existing policy, while public execution/numerical audits use standard
axioms only. The [focused test](../../../../../test/euler_2d_conservative.js)
passes 54 Wasmtime vectors, all output words, and the 22 f64 operation counts.
