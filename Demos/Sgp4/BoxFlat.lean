import Demos.Sgp4.Box
import Library.Numerics.Interval.Encoding

namespace Demos.Sgp4

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Box (UInt64 × Interval × Interval × Interval × Interval × Interval × Interval) :=
  ⟨fun b => (b.status, b.x, b.y, b.z, b.vx, b.vy, b.vz)⟩

end Demos.Sgp4
