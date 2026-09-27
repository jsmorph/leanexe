import Project.EulerCertificate.Vectors
import Project.EulerRiemann.Traversal
import Project.EulerRiemann.Time

namespace Project.EulerCertificate.Totals
open Project.EulerCertificate.Flux (Vector)
open Project.EulerRiemann.Traversal (Cell)

def addCell (acc : Vector) (cell : Cell) : Vector :=
  Vectors.add acc (Vectors.state cell.state)

def sum (grid : Array Cell) : Vector :=
  let initial := Vectors.zero
  grid.foldl (fun acc cell => addCell acc cell) initial

def physical (n : Nat) (grid : Array Cell) : Vector :=
  let size := Project.EulerRiemann.Time.smallNaturalBits n
  Vectors.divPositive (Vectors.divPositive (sum grid) size) size

end Project.EulerCertificate.Totals
