import LeanExe.KernelCheck.Pi

namespace LeanExe.KernelCheck

example : Sort 0 := (p : Prop) → p → p
example : Sort 2 := (α : Type) → α → α
set_option maxUniverseOffset 128 in
example (p : Prop) : Sort 0 := (α : Sort 100) → p

def identityType : Array UInt64 := #[0,0,0,1,0,0,1,1,0,2,1,2,2,0,3]
#guard (inferPi identityType #[] 4 100)[0]! == 0
#guard (inferPi #[0,0,0,1,0,0,2,1,1,2,0,2] #[] 3 100)[0]! == 1

end LeanExe.KernelCheck
