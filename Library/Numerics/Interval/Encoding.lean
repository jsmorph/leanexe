import Library.Numerics.Interval.Program
import Library.Numerics.Bounds.Encoding

namespace Library.Numerics.Interval

instance : LeanExe.Pipeline.Flat Interval (UInt64 × Float × Float) :=
  ⟨fun i => (i.status, i.lo, i.hi)⟩

end Library.Numerics.Interval
