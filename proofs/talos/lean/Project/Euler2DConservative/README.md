# Checked two-dimensional conservative state

[Source](../../../../../LeanExe/Examples/Euler2DConservative.lean) and
[Model](Model.lean) compute normal velocity, transverse kinetic energy,
pressure, normal signal speed, and all four directional physical fluxes from
(rho, normal momentum, transverse momentum, total energy). Swapping momentum
roles supplies the other Cartesian direction. Both kinetic terms contribute
to pressure; the transverse flux is transverse momentum times normal velocity.

The explicit sufficient domain is positive finite density and energy, finite
momenta with both magnitudes at most density, and energy strictly greater than
density. This is narrower than all admissible Euler states.
[Guard](Guard.lean) proves exact decoded internal energy at least E-rho>0.
[Safety](Safety.lean) proves all16 rounded intermediates finite and accepted
input states physically admissible. [Outputs](Outputs.lean) proves positive
finite rounded pressure and signal speed.

The shared [strict magnitude-order lemma](../ProofKit/F64StrictOrder.lean)
handles sign-cleared encodings, including zero/subnormal/exponent boundaries.
All public numerical audits use only the accepted standard logical axioms.
The [exact generated-WAT execution](Execution.lean) and [public safety contract](Spec.lean)
pass for all raw inputs, including every rejection branch and complete store
preservation. [Helpers](Helpers.lean) reuses the three shared scalar guard
proofs under a minimal layout; [StateGuard](StateGuard.lean) handles both
momenta and the strict energy boundary.

The2,212-byte [frozen package](../../../../artifacts/euler2_d_conservative/e37380d998ff2029b9901f4accdcd1d569b3bd4a423b25d91ba31aca6dbfb3b9/manifest.json)
passes its independent embedded-byte, decoder, validator, translation and
behavioral gate. [ArtifactTranslation](ArtifactTranslation.lean) connects the
exact bytes to the execution module; generated decoder-cache witnesses follow
the existing policy, while public execution/numerical audits use standard
axioms only. The [focused test](../../../../../test/euler_2d_conservative.js)
passes44 Wasmtime vectors, all output words and the16 f64 operation counts.
Dynamic interfaces and directional updates remain.
