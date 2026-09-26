import Project.Compiler.KernelReduction
open Project.Compiler

theorem deliberate_false_equality : (0 : Nat) = 1 := by
  kernel_rfl
