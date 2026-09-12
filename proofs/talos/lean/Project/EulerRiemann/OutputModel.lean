import Project.EulerRiemann.Output
import Project.EulerRiemann.TraversalSweep

namespace Project.EulerRiemann.Output
open Traversal

theorem pack_toList (n : Nat) (time status : UInt64) (grid : Array Cell) :
    (pack n time status grid).toList =
      [status, time, n.toUInt64, n.toUInt64] ++
        (grid.toList.map (fun cell => cell.state.density) ++
          grid.toList.map (fun cell => cell.pressure)) := by
  simp [pack]

theorem pack_size (n : Nat) (time status : UInt64) (grid : Array Cell) :
    (pack n time status grid).size = 4 + 2 * grid.size := by
  simp [pack]
  omega

theorem pack_indexed_size (n : Nat) (time status : UInt64) (grid : Array Cell)
    (h : Indexed n grid) : (pack n time status grid).size = 4 + 2 * (n * n) := by
  rw [pack_size, h.1]

theorem pack_size_le (n : Nat) (time status : UInt64) (grid : Array Cell)
    (hn : n ≤ 800) (h : Indexed n grid) :
    (pack n time status grid).size ≤ 1280004 := by
  rw [pack_indexed_size n time status grid h]
  have hm := Nat.mul_le_mul hn hn
  omega

#print axioms pack_toList
#print axioms pack_size
#print axioms pack_indexed_size
#print axioms pack_size_le

end Project.EulerRiemann.Output
