import Demos.Orbit.LambertBox
import Library.Numerics.Interval.Encoding

namespace Demos.Orbit

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Search (Float × Float × Bool) := ⟨fun s => (s.a, s.b, s.done)⟩

instance : Flat Transfer
    (UInt64 × Interval × Interval × Interval × Interval × Interval × Interval × Interval) :=
  ⟨fun t => (t.status, t.x, t.v1x, t.v1y, t.v1z, t.v2x, t.v2y, t.v2z)⟩

end Demos.Orbit
