import TestSupport.Native.Common
import Demos.Euler.Verified

/-!
The theorems that `verified_compile` adds for the Euler solvers, the exit criterion of milestone
M5.  The translation of the Euler module contains every one of its functions, and the two
solvers, `solve` and `reconstructedSolve`, have their theorems `p.f.native`, which carry the
verified compiler's theorems to the C functions of the translation.
-/

namespace TestSupport.Native.Euler

open LClight LeanExe.Native Demos.Euler.Verified

theorem euler_all : compiled.translation.funcs.length = compiled.module.funcs.length := by
  rw [translate_funcs_eq compiled.translation_eq compiled.translation_funcs, compiled.funcs_count]
  rfl

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.solve.implements A X cap compiled.translation :=
  compiled.solve.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.reconstructedSolve.implements A X cap compiled.translation :=
  compiled.reconstructedSolve.native A X

end TestSupport.Native.Euler
