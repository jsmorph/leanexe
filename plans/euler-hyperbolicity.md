# Two-dimensional Euler hyperbolicity

The user authorized this development on 2026-09-14.  The target is the
four-component conservative Euler system with exact gamma 7/5.  For every
state with positive density and pressure and every unit spatial direction,
prove that the derivative of the physical directional flux has a complete
real eigenbasis.  Its characteristic values are un-c, un, un, and un+c.
The middle eigenspace contains independent contact and shear vectors.

## Proof sequence

- [x] Define the real physical fluxes using the existing pressure and state definitions.
- [x] Prove the four-component x-flux derivative.
- [x] Prove the eigenrelation, invertibility, and complete eigenbasis.
- [x] Prove rotation identities and hyperbolicity in every unit direction.
- [x] Apply the theorem to accepted states, intermediate grids, and the exact WASM result.
- [x] Check the independent artifact package, audit axioms, and update the theorem inventory.

The existing one-dimensional derivative and eigenbasis proofs supply the
calculus and matrix proof structure.  Proofs use the installed dependencies
and standard local leanrunner limits, with one Lean job at a time.  Small
algebraic lemmas isolate elaboration costs.  The exact-real characteristic
speed bound and a bound for the rounded executable speed are separate
statements.  The latter remains subsequent work.

The focused independent artifact check passed on 2026-09-14 for the
production binary with SHA-256
`baefc44ed83f46607b7c938a6bc6912fb3fd21442df00c0d0f48c8454bee4310`.
The new registered behavior theorem is `Project.EulerRiemann.Spec.solve_hyperbolic`.
All eight manifest audits contain only propext, Classical.choice, and
Quot.sound.  The [proof inventory](../proofs/talos/README.md#two-dimensional-euler-hyperbolicity)
links each checked layer.

## References

The [existing derivative proof](../proofs/talos/lean/Project/EulerRusanov/RealJacobian.lean)
and [existing eigenbasis proof](../proofs/talos/lean/Project/EulerRusanov/RealEigenbasis.lean)
are checked local examples.  The [Lanyon article](https://lanyon.ai/research/euler-equations/)
states the Euler fluxes and the intended characteristic structure.
