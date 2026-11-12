import Demos.PassiveSafety.Program
import Library.Numerics.Interval.Encoding

namespace Demos.PassiveSafety

open LeanExe.Pipeline

instance : Flat Result (UInt64 × UInt64 × Float × Float × Float) :=
  ⟨fun r => (r.status, r.scenario, r.stop, r.sep, r.rc)⟩

instance : Flat March (UInt64 × Float × Float × Float × Float) :=
  ⟨fun m => (m.status, m.t, m.h, m.low, m.best)⟩

instance : Flat Scan (UInt64 × UInt64 × Float × Float × Float × Float × Float) :=
  ⟨fun s => (s.status, s.scenario, s.stop, s.sepLow, s.rcLow, s.sepBest, s.rcBest)⟩

end Demos.PassiveSafety
