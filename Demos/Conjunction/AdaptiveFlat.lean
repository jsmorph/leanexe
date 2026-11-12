import Demos.Conjunction.Adaptive
import Demos.Conjunction.AccuracyFlat

namespace Demos.Conjunction.Adaptive

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat March (UInt64 × UInt64 × Float × Float × Float × Interval) :=
  ⟨fun m => (m.state, m.used, m.root, m.t, m.h, m.sum)⟩

instance : Flat Marches (March × March × March) := ⟨fun m => (m.a, m.b, m.c)⟩

end Demos.Conjunction.Adaptive
