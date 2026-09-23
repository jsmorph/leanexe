import LeanExe.TypeSafety.Core
import LeanExe.TypeSafety.ArrayValues
import LeanExe.TypeSafety.Machine
import LeanExe.TypeSafety.Safety
import LeanExe.TypeSafety.Profile

/-!
An independently specified and proved type-safety core. The theorem
`LeanExe.TypeSafety.closed_type_safety` establishes preservation and absence of
stuck states for all finite executions of well-typed closed core expressions
under a well-typed program. Direct calls have finite argument lists and may be
recursive; the theorem does not claim termination.

`ProfileTyped` and `ProfileProgramTyped` add a decidable syntactic relevance
restriction. The profile uses `split` to bind both product fields, rejects
`fst`/`snd`, and requires introduced variables and function parameters to occur.
`profile_type_safety` inherits the core theorem without changing its runtime
invariant or asserting all-path use.

This module makes no extraction, layout, ownership, or WebAssembly correctness
claim. Persistent abstract arrays have checked operations and a bounded length;
their physical storage is outside this model. Byte arrays, heap effects,
compiler-specific recursion recognizers, and all arithmetic other than
bounded-natural addition remain outside this core.
-/
