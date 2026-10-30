import Demos.Energy.Program
import LeanExe.Pipeline.Implements

/-! Representations for the verified compiler: a status is the index of its constructor, and a
decision is the tuple of its status, setpoint, and expiry. -/

namespace Demos.Energy

open LeanExe.Pipeline

instance : Flat Status UInt64 := ⟨fun s => s.ctorIdx.toUInt64⟩

instance : Flat Decision (Status × UInt64 × UInt64) := ⟨fun d => (d.status, d.setpoint, d.expiry)⟩

end Demos.Energy
