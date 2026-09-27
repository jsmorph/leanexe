import Project.EulerRusanov.RealJacobian
import Project.EulerRusanov.RealEigenbasis
import Project.EulerRusanov.RealGuardBridge
import Project.EulerRusanov.RealStencil

/-!
# Exact-real conservative Euler mathematics

This umbrella exposes the conservative-coordinate flux, its genuine Fréchet
derivative, the complete strictly ordered eigenbasis for admissible states, the
raw-guard bridge to real admissibility and spectral bounds, and the exact-real
two-cell transmissive update.  It is intentionally separate from the
executable IEEE64 and WebAssembly theorems: importing this module makes no
claim that exact-real matrix, square-root, or stencil-update operations were
executed by the artifact.
-/
