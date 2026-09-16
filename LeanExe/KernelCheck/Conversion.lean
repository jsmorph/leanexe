import LeanExe.KernelCheck.Check

namespace LeanExe.KernelCheck

def checkConversion (g : Array UInt64) (term claimed fuel : UInt64) : UInt64 :=
  checkProof g term claimed fuel

end LeanExe.KernelCheck
