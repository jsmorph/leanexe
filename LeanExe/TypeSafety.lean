import LeanExe.TypeSafety.Formation
import LeanExe.TypeSafety.NatOperations
import LeanExe.TypeSafety.WordOperations
import LeanExe.TypeSafety.Core
import LeanExe.TypeSafety.ArrayValues
import LeanExe.TypeSafety.Machine
import LeanExe.TypeSafety.Safety
import LeanExe.TypeSafety.Profile
import LeanExe.TypeSafety.Typing

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

Nominal recursive declarations have checked formation and exhaustive constructor
patterns. `Typing` proves soundness and completeness of structural inference,
expression type uniqueness, and exact executable program/profile admission.
Public admission validates all ambient tables; raw inference intentionally
corresponds to the declarative expression judgment without that extra boundary.

This module makes no extraction, layout, ownership, or WebAssembly correctness
claim. Persistent abstract arrays have checked operations and a bounded length;
their physical storage is outside this model. Byte arrays, heap effects,
compiler-specific recursion recognizers, natural-number pattern elimination,
word bitwise operations and shifts, and floating-point arithmetic remain outside
this core. Word literals, modular arithmetic, unsigned comparisons, and explicit
conversions are included for widths 8, 32, and 64.
The bounded-natural family covers add/subtract/multiply/divide/remainder/min/max
and equality/order comparisons with precise operation-tagged overflow.
-/
