import LeanExe.KernelCheck.Binding

namespace LeanExe.KernelCheck

#guard checkScope #[1,0,0] 0 0 10 == 1
#guard checkScope #[1,0,0] 0 1 10 == 0
#guard checkScope #[0,0,0,1,0,0,3,0,1] 2 0 10 == 0
#guard checkScope #[1,0,0,3,0,0] 1 0 10 == 1
#guard shiftGraph #[1,0,0] 0 0 1 10 == #[0,1,1,0,0,1,1,0]
#guard shiftGraph #[1,18446744073709551615,0] 0 0 1 10 == #[2]
#guard shiftGraph #[0,0,0] 0 0 1 0 == #[5]

end LeanExe.KernelCheck
