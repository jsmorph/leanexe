import Project.EulerRiemann.Traversal
import Project.EulerRiemann.ReconstructedStep

namespace Project.EulerReconstructed.Traversal
open Project.EulerRiemann.Traversal (Cell neighborIndex accepted)
open Project.Euler2DCellStep.Sweep (State orient)

structure Stencil where
  farLeft : State
  left : State
  center : State
  right : State
  farRight : State
  deriving Inhabited

def cellStencil (n : Nat) (axis : Bool) (grid : Array Cell) (cell : Cell) : Stencil :=
  let leftIndex := neighborIndex n cell.index axis false
  let farLeftIndex := neighborIndex n leftIndex axis false
  let rightIndex := neighborIndex n cell.index axis true
  let farRightIndex := neighborIndex n rightIndex axis true
  ⟨orient axis grid[farLeftIndex]!.state, orient axis grid[leftIndex]!.state,
    orient axis cell.state, orient axis grid[rightIndex]!.state, orient axis grid[farRightIndex]!.state⟩

def updateCell (n fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Array Cell) (cell : Cell) : Cell :=
  let input := cellStencil n axis grid cell
  let out := Project.EulerRiemann.OutwardNumerics.reconstructedStepCheckedBits fuel ratio
    input.farLeft input.left input.center input.right input.farRight
  let next := orient axis ⟨out.density, out.momentum, out.transverse, out.energy⟩
  ⟨cell.index, next, out.pressure, out.status⟩

def sweep (n fuel : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell) : Array Cell :=
  grid.map (fun cell => updateCell n fuel axis ratio grid cell)

def step (n fuel : Nat) (ratio : UInt64) (grid : Array Cell) : Array Cell :=
  let middle := sweep n fuel false ratio grid
  if accepted middle then
    let next := sweep n fuel true ratio middle
    let _ := LeanExe.Runtime.release middle
    next
  else middle

end Project.EulerReconstructed.Traversal
