import Project.Smalltalk.BootGuard

namespace Project.Smalltalk.BootDispatch
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.BootGuard

abbrev rejected := BootGuard.rejected
abbrev accepted := @BootGuard.accepted

theorem boot_rejected (p s : Array UInt64) (bad : rejected p s = true) : boot p s = fail s 10 := by
  have guard : (!programValid p || read s 2 != 0 || read s 0 != 0) = true := bad
  simp only [boot, guard, ite_true]

theorem boot_accepted (p s : Array UInt64) (good : rejected p s = false) : boot p s = bootValid p s := by
  have guard : (!programValid p || read s 2 != 0 || read s 0 != 0) = false := good
  simp only [boot, guard, Bool.false_eq_true, ite_false]

end Project.Smalltalk.BootDispatch
