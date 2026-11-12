import Demos.Orbit.GibbsBox
import Library.Numerics.Interval.Encoding

namespace Demos.Orbit

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Velocity (UInt64 × Interval × Interval × Interval) :=
  ⟨fun v => (v.status, v.vx, v.vy, v.vz)⟩

end Demos.Orbit
