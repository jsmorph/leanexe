import Project.EulerCertificate.Boundary
import Project.EulerCertificate.VectorsOrientation
import Project.EulerReconstructed.LineBalance

namespace Project.EulerCertificate.Boundary
open Project.EulerRiemann.Traversal (Cell asGrid)
open Project.EulerRiemann.Conservation (normalComponent)
open Project.EulerReconstructed.Conservation (paddedState lineLeft lineRight lineReferenceFlux)
open Project.EulerRiemann.OutwardNumerics (faceRowFlux faceRowReference)

theorem padded_eq {n : Nat} (hn : 0 < n) (axis : Bool) (grid : Array Cell)
    (index : Fin n) (k : Nat) :
    padded n axis grid index.val k = paddedState hn axis (asGrid n grid) index k := by
  cases axis <;> rfl

theorem face_eq {n : Nat} (hn : 0 < n) (trials : Nat) (axis : Bool) (grid : Array Cell)
    (index : Fin n) (k : Nat) :
    face n trials axis grid index.val k = Vectors.orient axis
      (Flux.interface (faceRowFlux (lineLeft hn trials axis (asGrid n grid) index)
        (lineRight hn trials axis (asGrid n grid) index) k).alpha
        (lineLeft hn trials axis (asGrid n grid) index k)
        (lineRight hn trials axis (asGrid n grid) index k)) := by
  simp only [face, padded_eq hn, lineLeft, lineRight,
    Project.EulerReconstructed.Numerics.rowLeft, Project.EulerReconstructed.Numerics.rowRight,
    faceRowFlux]

theorem face_valid {n : Nat} (hn : 0 < n) (trials : Nat) (axis : Bool) (grid : Array Cell)
    (index : Fin n) (k : Nat) :
    Vectors.Valid (face n trials axis grid index.val k) (fun i =>
      faceRowReference (lineLeft hn trials axis (asGrid n grid) index)
        (lineRight hn trials axis (asGrid n grid) index) k (normalComponent axis i)) := by
  rw [face_eq hn]
  exact Vectors.Valid.orient (Flux.interface_valid _ _ _) axis

theorem line_valid {n : Nat} (hn : 0 < n) (trials : Nat) (axis : Bool) (grid : Array Cell)
    (index : Fin n) :
    Vectors.Valid (line n trials axis grid index.val) (fun i =>
      lineReferenceFlux hn trials axis (asGrid n grid) index (normalComponent axis i)) :=
  (face_valid hn trials axis grid index 0).sub (face_valid hn trials axis grid index n)

#print axioms face_valid
#print axioms line_valid
end Project.EulerCertificate.Boundary
