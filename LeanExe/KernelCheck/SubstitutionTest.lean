import LeanExe.KernelCheck.Substitution

namespace LeanExe.KernelCheck

#guard instantiateGraph #[0,0,0,1,0,0] 1 0 10 == #[0,0,0,0,0,1,0,0]
#guard instantiateGraph #[1,1,0,0,0,0] 0 1 10 == #[0,2,1,1,0,0,0,0,1,0,0]
#guard instantiateGraph #[0,0,0,1,0,0,1,1,0,3,0,2] 3 1 10 ==
  #[0,5,0,0,0,1,0,0,1,1,0,3,0,2,1,1,0,3,0,4]

end LeanExe.KernelCheck
