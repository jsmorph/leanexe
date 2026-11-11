import Demos.Frames.Program
import Demos.Frames.Time
import Library.Numerics.Interval.Encoding

namespace Demos.Frames

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Angle (UInt64 × Float × Float) := ⟨fun a => (a.status, a.lo, a.hi)⟩

instance : Flat Vec (UInt64 × Interval × Interval × Interval) := ⟨fun v => (v.status, v.x, v.y, v.z)⟩

instance : Flat Coords (UInt64 × Interval × Interval × Interval) :=
  ⟨fun c => (c.status, c.lat, c.lon, c.h)⟩

instance : Flat Scan (UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun s => (s.status, s.last, s.dat0, s.dat1)⟩

instance : Flat Times (UInt64 × UInt64 × Interval × Interval × Interval) :=
  ⟨fun t => (t.status, t.dat, t.tai, t.tt, t.ut1)⟩

end Demos.Frames
