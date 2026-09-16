import LeanExe.KernelCheck.Universe

namespace LeanExe.KernelCheck

example : Sort 0 := (p : Prop) → p → p
example : Sort 2 := (α : Type) → α → α

#guard maxLevel 2 7 == 7
#guard maxLevel 7 2 == 7
#guard imaxLevel 7 0 == 0
#guard imaxLevel 7 2 == 7
#guard imaxLevel 0 7 == 7
#guard checkLevelOp 0 7 0 0 == 1
#guard checkLevelOp 1 7 0 0 == 0
#guard checkLevelOp 1 18446744073709551615 0 0 == 0
#guard checkLevelOp 0 18446744073709551615 0 18446744073709551615 == 0
#guard checkLevelOp 2 0 0 0 == 3

end LeanExe.KernelCheck
