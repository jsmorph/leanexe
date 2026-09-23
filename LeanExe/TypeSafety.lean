import LeanExe.TypeSafety.Core
import LeanExe.TypeSafety.Machine
import LeanExe.TypeSafety.Safety

/-!
An independently specified and proved type-safety core. The theorem
`LeanExe.TypeSafety.closed_type_safety` establishes preservation and absence of
stuck states for all finite executions of well-typed closed core expressions
under a well-typed program. Direct calls have finite argument lists and may be
recursive; the theorem does not claim termination.

This module makes no extraction, layout, ownership, or WebAssembly correctness
claim. Arrays, byte arrays, heap effects, compiler-specific recursion recognizers,
and all arithmetic other than bounded-natural addition remain outside this core.
-/
