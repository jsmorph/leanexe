import Project.EulerRiemann.InitialMapLoop
import Project.EulerRiemann.TraversalInitial

namespace Project.EulerRiemann.Execution

def InitialPrefix (n count : Nat) (grid : Array Traversal.Cell) : Prop :=
  grid.toList = (List.range count).map (Traversal.initialCell n)

theorem InitialPrefix.size {n count : Nat} {grid : Array Traversal.Cell}
    (h : InitialPrefix n count grid) : grid.size = count := by
  simpa only [Array.length_toList, List.length_map, List.length_range] using congrArg List.length h

theorem InitialPrefix.cell {n count : Nat} {grid : Array Traversal.Cell}
    (h : InitialPrefix n count grid) (index : Nat) (hi : index < grid.size) :
    grid[index] = Traversal.initialCell n index := by
  have hIndex : index < count := by rw [← h.size]; exact hi
  have hGet := congrArg (fun values : List Traversal.Cell => values[index]?) h
  simpa only [Array.getElem?_toList, Array.getElem?_eq_getElem hi, List.getElem?_map,
    List.getElem?_range hIndex, Option.map_some, Option.some.injEq] using hGet

theorem InitialPrefix.doubled {n count : Nat} {grid : Array Traversal.Cell}
    (h : InitialPrefix n count grid) :
    InitialPrefix n (count + count) (grid ++ initialMapOutput n grid.size grid) := by
  unfold InitialPrefix initialMapOutput
  rw [Array.toList_append, Array.toList_map, h.size, h]
  have hMap : ((List.range count).map (Traversal.initialCell n)).map
      (fun cell => Traversal.initialCell n (cell.index + count)) =
      ((List.range count).map (fun i => count + i)).map (Traversal.initialCell n) := by
    simp only [List.map_map, Function.comp_def, Traversal.initialCell_index]
    congr 1
    funext i
    rw [Nat.add_comm]
  rw [hMap, ← List.map_append, ← List.range_add]

theorem InitialPrefix.extracted {n count : Nat} {grid : Array Traversal.Cell}
    (h : InitialPrefix n count grid) (size : Nat) (hSize : size ≤ count) :
    InitialPrefix n size (grid.extract 0 size) :=
  Traversal.extract_initial_prefix n count size grid h hSize

#print axioms InitialPrefix.size
#print axioms InitialPrefix.cell
#print axioms InitialPrefix.doubled
#print axioms InitialPrefix.extracted

end Project.EulerRiemann.Execution
