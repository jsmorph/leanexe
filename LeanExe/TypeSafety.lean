import LeanExe.TypeSafety.Core
import LeanExe.TypeSafety.Machine
import LeanExe.TypeSafety.Safety

/-!
An independently specified and proved type-safety core. The theorem
`LeanExe.TypeSafety.closed_type_safety` establishes preservation and absence of
stuck states for all finite executions of well-typed closed core expressions.

This module makes no extraction, layout, ownership, or WebAssembly correctness
claim. Direct calls, recursion, arrays, byte arrays, and heap effects remain
outside this initial fragment.
-/
