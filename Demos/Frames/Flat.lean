import Demos.Frames.Program
import Library.Numerics.Interval.Encoding

namespace Demos.Frames

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Angle (UInt64 × Float × Float) := ⟨fun a => (a.status, a.lo, a.hi)⟩

instance : Flat Vec (UInt64 × Interval × Interval × Interval) := ⟨fun v => (v.status, v.x, v.y, v.z)⟩

end Demos.Frames
