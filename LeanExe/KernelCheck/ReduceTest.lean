import LeanExe.KernelCheck.Reduce

namespace LeanExe.KernelCheck

#guard reduceHead #[0,0,0,1,0,0,3,0,1,4,2,0] 3 20 ==
  #[0,0,0,0,0,1,0,0,3,0,1,4,2,0]
#guard reduceHead #[0,0,0,1,0,0,4,1,1,3,0,2,4,3,3] 4 50 == #[5]

end LeanExe.KernelCheck
