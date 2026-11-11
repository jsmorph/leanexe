import Demos.Gate.Assignment
import LeanExe.Pipeline.Int64

namespace Demos.Gate.Assignment

open LeanExe.Pipeline

instance : Flat Check (UInt64 × UInt64 × UInt64) := ⟨fun r => (r.status, r.row, r.col)⟩

end Demos.Gate.Assignment
