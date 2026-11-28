module

public import Demos.Gate.Program
public import Library.Numerics.Interval.Encoding

@[expose] public section

namespace Demos.Gate

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Terms (Interval × Interval) := ⟨fun s => (s.acc, s.term)⟩

instance : Flat Quantile (UInt64 × Float × Float) := ⟨fun q => (q.status, q.lo, q.hi)⟩

instance : Flat Ends (Float × Float) := ⟨fun b => (b.lo, b.hi)⟩

end Demos.Gate
