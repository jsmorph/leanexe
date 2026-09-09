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
Source and pure-model builds pass. Generated-WAT execution, exact bytes,
dynamic interfaces and directional updates are still pending.
