import Demos.Conjunction.Program
import Library.Numerics.Interval.Encoding

namespace Demos.Conjunction

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat Setup (Interval × Interval × Interval × Interval × Interval × Interval) :=
  ⟨fun s => (s.m1, s.m2, s.twoC11, s.rho, s.k, s.r2)⟩

instance : Flat Assessment (UInt64 × Float × Float × UInt64) :=
  ⟨fun a => (a.status, a.lo, a.hi, a.verdict)⟩

end Demos.Conjunction
