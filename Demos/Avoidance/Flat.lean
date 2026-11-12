import Demos.Avoidance.Program
import Library.Numerics.Interval.Encoding

namespace Demos.Avoidance

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Cell (Float × Float × Float × Float × Float × Float × Interval × UInt64) :=
  ⟨fun c => (c.lx, c.hx, c.ly, c.hy, c.lz, c.hz, c.bound, c.depth)⟩

instance : Flat Search (Array Cell × UInt64 × Interval × Bool × UInt64 × Bool) :=
  ⟨fun q => (q.cells, q.next, q.hull, q.seen, q.budget, q.above)⟩

instance : Flat Outcome (Interval × Bool) := ⟨fun o => (o.bound, o.above)⟩

end Demos.Avoidance
