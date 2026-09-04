import Project.EulerRusanov.Program
import Project.EulerRusanov.Model
import Project.EulerRusanov.Bounds
import Project.EulerRusanov.ScaledRoundoff
import Project.EulerRusanov.WasmNumerical
import Project.EulerRusanov.InterfaceData

/-!
# Guarded Euler Rusanov artifact

This root keeps the generated program, checked mathematical foundation,
componentwise Euler roundoff theorem, and exact fuel-independent execution
theorem buildable together, together with their WAT-level numerical
composition.  It also imports the frozen interface dataset and its theorem
transferring all eight rows through the exact registered artifact bytes.
-/
