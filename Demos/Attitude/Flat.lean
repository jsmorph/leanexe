import Demos.Attitude.Program
import Library.Numerics.Interval.Encoding

namespace Demos.Attitude

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Estimate (UInt64 × Interval × Interval × Interval × Interval × Interval ×
    Interval × Interval × Interval × Interval × Float) :=
  ⟨fun e => (e.status, e.m11, e.m12, e.m13, e.m21, e.m22, e.m23, e.m31, e.m32, e.m33, e.err)⟩

end Demos.Attitude
