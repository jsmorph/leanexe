import Project.EulerRiemann.FrozenOutwardSpeed
import Project.EulerRiemann.FrozenTraversal

namespace Project.EulerRiemann.Frozen.OutwardMaximum
open Project.ProofKit.F64Outward (Checked rejected)
open Project.Euler2DCellStep.Sweep (State)
open Traversal (Cell)

def merge (left right : Checked) : Checked :=
  if left.status == 0 && right.status == 0 then
    ⟨0, max left.value right.value⟩
  else rejected

def interfaceUpper (left right : State) : Checked :=
  merge (OutwardSpeed.speedUpper left.density left.mx left.my left.energy)
    (OutwardSpeed.speedUpper right.density right.mx right.my right.energy)

def cellUpper (state : State) : Checked :=
  merge (OutwardSpeed.speedUpper state.density state.mx state.my state.energy)
    (OutwardSpeed.speedUpper state.density state.my state.mx state.energy)

def scanCell (acc : Checked) (cell : Cell) : Checked :=
  merge acc (cellUpper cell.state)

def gridUpper (grid : Array Cell) : Checked :=
  grid.foldl (fun acc cell => scanCell acc cell) ⟨0, 0⟩

end Project.EulerRiemann.Frozen.OutwardMaximum
