import Project.EulerRusanov.RealJacobian
import Project.EulerRusanov.RealEigenbasis

/-!
# Exact-real conservative Euler mathematics

This umbrella exposes the conservative-coordinate flux, its genuine Fréchet
derivative, and the complete strictly ordered eigenbasis for admissible states.
It is intentionally separate from the executable IEEE64 and WebAssembly
theorems: importing this module makes no claim that exact-real matrix or square
root operations were executed by the artifact.
-/
