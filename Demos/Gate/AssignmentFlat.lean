module

public import Demos.Gate.Assignment
public import LeanExe.Pipeline.Int64

@[expose] public section

namespace Demos.Gate.Assignment

open LeanExe.Pipeline

instance : Flat Check (UInt64 × UInt64 × UInt64) := ⟨fun r => (r.status, r.row, r.col)⟩

end Demos.Gate.Assignment
