import Examples.Grids.Program
import LeanExe.Pipeline.Implements

/-! How the theorems of both compilers represent the records of the grids: a phase as the word of
its constructor index, and a state, a cell, and a mass as their fields in declaration order.
These instances are part of what the theorems in `Verify.lean` and `Compiled.lean` state. -/

namespace Examples.Grids

open LeanExe.Pipeline

instance : Flat Phase UInt64 := ⟨fun | .solid => 0 | .liquid => 1 | .gas => 2⟩
instance : Flat Conserved (Float × Float × Float × Float) :=
  ⟨fun s => (s.density, s.mx, s.my, s.energy)⟩
instance : Flat Cell (UInt64 × Conserved × Float × UInt64 × Bool × Phase) :=
  ⟨fun c => (c.index, c.state, c.pressure, c.status, c.ok, c.phase)⟩
instance : Flat Mass Float := ⟨Mass.value⟩

end Examples.Grids
