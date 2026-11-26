module

public import Demos.Orbit.GibbsBox
public import Library.Numerics.Interval.Encoding

@[expose] public section

namespace Demos.Orbit

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Velocity (UInt64 × Interval × Interval × Interval) :=
  ⟨fun v => (v.status, v.vx, v.vy, v.vz)⟩

end Demos.Orbit
