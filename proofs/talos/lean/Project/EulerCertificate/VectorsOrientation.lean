import Project.EulerCertificate.VectorsSpec
import Project.EulerRiemann.NumericsGridBalance

namespace Project.EulerCertificate.Vectors
open Project.EulerCertificate.Flux (Vector)
open Project.EulerRiemann.Conservation (normalComponent)

theorem get_orient (axis : Bool) (a : Vector) (i : Fin 4) :
    Flux.get (orient axis a) i = Flux.get a (normalComponent axis i) := by
  cases axis <;> fin_cases i <;> rfl

theorem Valid.orient {a : Vector} {x : Fin 4 → ℝ} (ha : Valid a x) (axis : Bool) :
    Valid (orient axis a) (fun i => x (normalComponent axis i)) := by
  intro i
  rw [get_orient]
  exact ha (normalComponent axis i)

#print axioms Valid.orient
end Project.EulerCertificate.Vectors
