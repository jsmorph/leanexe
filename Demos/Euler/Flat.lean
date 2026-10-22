import Demos.Euler.ReconstructedProgram
import LeanExe.Pipeline.Implements

namespace Demos.Euler

open LeanExe.Pipeline

instance : Flat Conserved (Float × Float × Float × Float) :=
  ⟨fun q => (q.density, q.mx, q.my, q.energy)⟩
instance : Flat Cell (Conserved × Float × UInt64) := ⟨fun c => (c.state, c.pressure, c.status)⟩
instance : Flat Side (UInt64 × Float × Float × Float × Float × Float × Float × Float) :=
  ⟨fun s => (s.status, s.velocity, s.pressure, s.speed, s.massFlux, s.momentumFlux,
    s.transverseFlux, s.energyFlux)⟩
instance : Flat Component (UInt64 × Float) := ⟨fun c => (c.status, c.value)⟩
instance : Flat Flux (UInt64 × Float × Float × Float × Float × Float) :=
  ⟨fun f => (f.status, f.mass, f.momentum, f.transverse, f.energy, f.alpha)⟩
instance : Flat Updated (UInt64 × Float × Float × Float × Float × Float × Float × Float) :=
  ⟨fun u => (u.status, u.density, u.momentum, u.transverse, u.energy, u.pressure, u.alpha,
    u.courant)⟩
instance : Flat Checked (UInt64 × Float) := ⟨fun c => (c.status, c.value)⟩
instance : Flat Faces (UInt64 × Conserved × Conserved × Float) :=
  ⟨fun f => (f.status, f.left, f.right, f.factor)⟩
instance : Flat Slope (UInt64 × Conserved) := ⟨fun s => (s.status, s.state)⟩

end Demos.Euler
