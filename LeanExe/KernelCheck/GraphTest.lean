import LeanExe.KernelCheck.Graph

namespace LeanExe.KernelCheck

#guard validateGraph #[0, 0, 0] 0 == 0
#guard validateGraph #[1, 0, 0] 0 == 0 -- structural validation admits open terms
#guard validateGraph #[0, 0, 0, 1, 0, 0, 2, 1, 1, 2, 0, 2] 3 == 0
#guard validateGraph #[] 0 == 4
#guard validateGraph #[0, 0] 0 == 4
#guard validateGraph #[9, 0, 0] 0 == 4
#guard validateGraph #[0, 0, 1] 0 == 4
#guard validateGraph #[2, 0, 0] 0 == 4

end LeanExe.KernelCheck
