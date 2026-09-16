import LeanExe.KernelCheck.Levels

namespace LeanExe.KernelCheck.LevelsTest

universe u v

example : Sort (u + 1) := Sort u
example (A : Sort u) (B : A → Sort v) : Sort (imax u v) := (a : A) → B a
example (A : Type u) (B : Type v) : Type (max u v) := A × B

#guard validateLevels #[0, 0, 0] 0 0 == 0
#guard validateLevels #[2, 0, 0, 1, 0, 0, 3, 0, 1, 4, 2, 0] 1 3 == 0
#guard validateLevels #[] 0 0 == 4
#guard validateLevels #[2, 0, 0] 0 0 == 4
#guard validateLevels #[0, 0, 0, 1, 1, 0] 0 1 == 4
#guard validateLevels #[0, 0, 0, 4, 0, 2] 0 1 == 4

end LeanExe.KernelCheck.LevelsTest
