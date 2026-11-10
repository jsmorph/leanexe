import Demos.Sgp4.Tle
import Library.Numerics.Interval.Encoding

namespace Demos.Sgp4

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Box (UInt64 × Interval × Interval × Interval × Interval × Interval × Interval) :=
  ⟨fun b => (b.status, b.x, b.y, b.z, b.vx, b.vy, b.vz)⟩

instance : Flat Tle.Fields
    (UInt64 × Interval × Interval × Interval × Interval × Interval × Interval × Interval) :=
  ⟨fun f => (f.status, f.n, f.e, f.incl, f.node, f.argp, f.m, f.bstar)⟩

end Demos.Sgp4
