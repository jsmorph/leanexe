import Project.EulerRiemann.Traversal
import Project.EulerRiemann.Time

namespace Project.EulerRiemann.TraversalTest
open Traversal

def words (grid : Array Cell) : Array UInt64 :=
  grid.foldl (fun result cell => result ++ #[cell.index.toUInt64,
    cell.state.density, cell.state.mx, cell.state.my, cell.state.energy,
    cell.pressure, cell.status]) #[]

def sample (n : Nat) (advance : Bool) : Array UInt64 :=
  if 2 ≤ n ∧ n ≤ 5 then
    let initial := initialCells n
    let grid := if advance then step n 0x3FB999999999999A initial else initial
    let result := scan grid
    #[result.status, result.alpha] ++ words grid
  else #[]

end Project.EulerRiemann.TraversalTest
