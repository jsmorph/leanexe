module

public import Demos.Gate.GateProgram
public import Library.Numerics.Interval.Encoding

@[expose] public section

namespace Demos.Gate

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Elim (UInt64 × Array Interval × Array Interval × Interval) :=
  ⟨fun e => (e.status, e.a, e.r, e.acc)⟩

instance : Flat Gate (UInt64 × Float × Float × UInt64) :=
  ⟨fun r => (r.status, r.lo, r.hi, r.verdict)⟩

end Demos.Gate
