import Examples.Drone.Program
import LeanExe.Pipeline.Implements

/-! A `Choice` is represented as its three words, the time, the excess, and the parent. -/

namespace Examples.Drone

instance : LeanExe.Pipeline.Flat Choice (UInt64 × UInt64 × UInt64) :=
  ⟨fun c => (c.time, c.excess, c.parent)⟩

end Examples.Drone
