import Demos.Screening.Program
import Library.Numerics.Interval.Encoding

namespace Demos.Screening

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Obj (Interval × Interval × Interval × Interval × Interval × Interval × Interval ×
    Interval × Interval × Interval × Interval × Interval × Interval × Interval × Interval) :=
  ⟨fun o => (o.a, o.e, o.beta, o.px, o.py, o.pz, o.qx, o.qy, o.qz, o.n, o.m0, o.epoch, o.speed,
    o.perigee, o.apogee)⟩

instance : Flat Span (Float × Float) := ⟨fun s => (s.lo, s.hi)⟩

instance : Flat Cell (Float × Float × Float × Float) := ⟨fun c => (c.lo1, c.hi1, c.lo2, c.hi2)⟩

instance : Flat Found (Float × Float × UInt64) := ⟨fun f => (f.lo, f.hi, f.certain)⟩

instance : Flat Search (Array Span × UInt64 × UInt64 × UInt64) :=
  ⟨fun s => (s.cells, s.status, s.tests, s.levels)⟩

instance : Flat PathSearch (Array Cell × UInt64 × UInt64) :=
  ⟨fun s => (s.cells, s.verdict, s.tests)⟩

instance : Flat Merge (Array Found × Found × Bool) := ⟨fun m => (m.out, m.cur, m.has)⟩

end Demos.Screening
