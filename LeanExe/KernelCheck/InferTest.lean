import LeanExe.KernelCheck.Infer

namespace LeanExe.KernelCheck

#guard inferOpen #[0,0,0] #[] 0 10 == #[0,1,0,0,0,0,1,0]
-- A : Sort 1, x : A |- x : A. The output type is bvar 1, not bvar 0.
#guard inferOpen #[0,1,0,1,0,0] #[0,1] 1 20 ==
  #[0,3,0,1,0,1,0,0,0,2,0,1,1,0]
#guard inferOpen #[1,0,0] #[] 0 20 == #[1]
#guard inferOpen #[0,0,0,1,0,0] #[0,1,1] 1 20 == #[1]
#guard inferOpen #[0,0,0] #[1] 0 20 == #[4]

end LeanExe.KernelCheck
