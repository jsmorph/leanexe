import Project.EulerRiemann.Traversal

namespace Project.EulerRiemann.Output
open Traversal

def pack (n : Nat) (time status : UInt64) (grid : Array Cell) : Array UInt64 :=
  let density := grid.map (fun cell => cell.state.density)
  let pressure := grid.map (fun cell => cell.pressure)
  let fields := density ++ pressure
  let _ := LeanExe.Runtime.release density
  let _ := LeanExe.Runtime.release pressure
  let result := #[status, time, n.toUInt64, n.toUInt64] ++ fields
  let _ := LeanExe.Runtime.release fields
  result

end Project.EulerRiemann.Output
