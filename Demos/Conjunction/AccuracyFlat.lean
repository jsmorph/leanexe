import Demos.Conjunction.Accuracy
import Demos.Conjunction.Flat

namespace Demos.Conjunction.Accuracy

open LeanExe.Pipeline

instance : Flat Radius (UInt64 × Float × Float) := ⟨fun r => (r.status, r.lo, r.hi)⟩

instance : Flat Bracket (UInt64 × Float × Float) := ⟨fun b => (b.found, b.lo, b.hi)⟩

end Demos.Conjunction.Accuracy
