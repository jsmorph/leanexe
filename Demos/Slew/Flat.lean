import Demos.Slew.Program
import LeanExe.Pipeline.Implements

/-! Representations for the verified compiler: a vector is its three floats, a quaternion its
four, the dimensions their six words, and the search state the tuple of its fields, two arrays of
words, two arrays of Booleans, a Boolean, and a word. -/

namespace Demos.Slew

open LeanExe.Pipeline

instance : Flat V3 (Float × Float × Float) := ⟨fun v => (v.x, v.y, v.z)⟩

instance : Flat Q4 (Float × Float × Float × Float) := ⟨fun q => (q.w, q.x, q.y, q.z)⟩

instance : Flat Dims (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun d => (d.nb, d.nc, d.nw, d.coneOff, d.wayOff, d.total)⟩

instance : Flat Search (Array UInt64 × Array UInt64 × Array Bool × Array Bool × Bool × UInt64) :=
  ⟨fun s => (s.cost, s.parent, s.done, s.ok, s.finished, s.examined)⟩

end Demos.Slew
