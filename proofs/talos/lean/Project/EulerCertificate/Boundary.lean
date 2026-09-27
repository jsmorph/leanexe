import Project.EulerCertificate.Totals
import Project.EulerRiemann.Reconstruction
import Project.EulerRiemann.OutwardFlux

namespace Project.EulerCertificate.Boundary
open Project.EulerCertificate.Flux (Vector)
open Project.EulerRiemann.Traversal (Cell)
open Project.Euler2DCellStep.Sweep (State orient)

def padded (n : Nat) (axis : Bool) (grid : Array Cell) (line k : Nat) : State :=
  let coordinate := min (k - 2) (n - 1)
  let index := if axis then coordinate * n + line else line * n + coordinate
  orient axis grid[index]!.state

def face (n trials : Nat) (axis : Bool) (grid : Array Cell) (line k : Nat) : Vector :=
  let a := padded n axis grid line k
  let b := padded n axis grid line (k + 1)
  let c := padded n axis grid line (k + 2)
  let d := padded n axis grid line (k + 3)
  let left := (Project.EulerRiemann.Reconstruction.reconstruct trials a b c).right
  let right := (Project.EulerRiemann.Reconstruction.reconstruct trials b c d).left
  let flux := Project.EulerRiemann.OutwardNumerics.fluxCheckedBits
    left.density left.mx left.my left.energy right.density right.mx right.my right.energy
  Vectors.orient axis (Flux.interface flux.alpha left right)

def line (n trials : Nat) (axis : Bool) (grid : Array Cell) (index : Nat) : Vector :=
  let left := face n trials axis grid index 0
  let right := face n trials axis grid index n
  Vectors.sub left right

def sum (n trials : Nat) (axis : Bool) (grid : Array Cell) : Vector :=
  let initial := Vectors.zero
  grid.foldl (fun acc cell =>
    let flux := line n trials axis grid cell.index
    Vectors.add acc flux) initial 0 n

def physicalStep (n trials : Nat) (dt : UInt64) (grid middle : Array Cell) : Vector :=
  let flux := Vectors.add (sum n trials false grid) (sum n trials true middle)
  Vectors.divPositive (Vectors.scale flux dt) (Project.EulerRiemann.Time.smallNaturalBits n)

end Project.EulerCertificate.Boundary
