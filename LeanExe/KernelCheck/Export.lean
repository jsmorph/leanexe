import LeanExe.KernelCheck.Check

namespace LeanExe.KernelCheck

/-- Host decoding supplies both roots. All typing decisions stay in WASM. -/
def checkExport (g : Array UInt64) (term claimed fuel : UInt64) : UInt64 :=
  checkProof g term claimed fuel

end LeanExe.KernelCheck
