import Project.EulerRusanov.Program
import Project.EulerRusanov.Model
import Project.EulerRusanov.Bounds
import Project.EulerRusanov.ScaledRoundoff
import Project.EulerRusanov.Numerical
import Project.EulerRusanov.Execution

/-!
# Guarded Euler Rusanov artifact

This root keeps the generated program, checked mathematical foundation,
componentwise Euler roundoff theorem, and exact fuel-independent execution
theorem buildable together.  Exact-byte artifact registration remains a
separate boundary.
-/
