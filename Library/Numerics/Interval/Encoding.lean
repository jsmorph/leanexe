module

public import Library.Numerics.Interval.Program
public import Library.Numerics.Bounds.Encoding

@[expose] public section

namespace Library.Numerics.Interval

instance : LeanExe.Pipeline.Flat Interval (UInt64 × Float × Float) :=
  ⟨fun i => (i.status, i.lo, i.hi)⟩

end Library.Numerics.Interval
