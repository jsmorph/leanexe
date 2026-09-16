import LeanExe.KernelCheck.Infer

namespace LeanExe.KernelCheck

/-- M0.5 uses the same validated-context boundary as atomic inference. -/
def inferPi (g ctx : Array UInt64) (root fuel : UInt64) : Array UInt64 :=
  inferOpen g ctx root fuel

end LeanExe.KernelCheck
