import Demos.Attitude.QProgram
import Library.Numerics.Interval.Encoding

namespace Demos.Attitude.QMethod

open LeanExe.Pipeline Library.Numerics.Interval

instance : Flat M4 (Interval × Interval × Interval × Interval × Interval × Interval × Interval ×
    Interval × Interval × Interval) :=
  ⟨fun m => (m.a00, m.a01, m.a02, m.a03, m.a11, m.a12, m.a13, m.a22, m.a23, m.a33)⟩

instance : Flat M3 (Interval × Interval × Interval × Interval × Interval × Interval) :=
  ⟨fun m => (m.c00, m.c01, m.c02, m.c11, m.c12, m.c22)⟩

instance : Flat M2 (Interval × Interval × Interval) := ⟨fun m => (m.d00, m.d01, m.d11)⟩

instance : Flat Acc (Bool × M4 × Interval × Interval) := ⟨fun s => (s.ok, s.k, s.rho, s.mu)⟩

instance : Flat Q4 (Float × Float × Float × Float) := ⟨fun q => (q.w, q.x, q.y, q.z)⟩

instance : Flat Jac (Float × Float × Float × Float × Float × Float × Float × Float × Float ×
    Float × Q4 × Q4 × Q4 × Q4) :=
  ⟨fun j => (j.a00, j.a01, j.a02, j.a03, j.a11, j.a12, j.a13, j.a22, j.a23, j.a33, j.v0, j.v1,
    j.v2, j.v3)⟩

end Demos.Attitude.QMethod
