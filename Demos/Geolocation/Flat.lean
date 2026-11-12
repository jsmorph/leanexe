import Demos.Geolocation.Program
import Library.Numerics.Interval.Encoding

namespace Demos.Geolocation

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Box (Float × Float × Float × Float × Float × Float × UInt64) :=
  ⟨fun b => (b.plo, b.phi, b.llo, b.lhi, b.hlo, b.hhi, b.mark)⟩

instance : Flat Verdict (Bool × Bool) := ⟨fun v => (v.out, v.inner)⟩

instance : Flat Search (Array Box × UInt64 × UInt64 × UInt64) :=
  ⟨fun s => (s.boxes, s.status, s.tests, s.levels)⟩

instance : Flat State (Interval × Interval × Interval × Interval × Interval × Interval) :=
  ⟨fun s => (s.x, s.y, s.z, s.u, s.v, s.w)⟩

end Demos.Geolocation
