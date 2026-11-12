import Demos.Events.Program
import Demos.Screening.Flat

namespace Demos.Events

open LeanExe.Pipeline Library.Numerics.Interval Demos.Screening

instance : Flat Ev (UInt64 × Obj × Interval × Interval × Interval × Interval × Interval ×
    Interval × Interval × Interval × Interval × Interval × Interval × Interval) :=
  ⟨fun e => (e.code, e.o, e.d0, e.ca, e.sa, e.radius, e.b1, e.b2, e.b3, e.nb, e.l1, e.l2, e.w1,
    e.w2)⟩

end Demos.Events
