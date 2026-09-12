import Project.EulerRiemann.InitialMapDataPrefix
import Project.EulerRiemann.InitialMapLoop

namespace Project.EulerRiemann.Execution
open Wasm

theorem initial_map_data_shape : initialMapDataProgram =
    InitialAllocationSite.map.installProgram ++
      [.constI64 0, .localSet 51, .block 0 0 [.loop 0 0 initialMapLoop]] := by
  change (initialGrowBody.drop 45).take (8 + 1) = _
  rw [List.take_add_one, List.getElem?_drop]
  change (initialGrowBody.drop 45).take 8 ++ (initialGrowBody[53]?).toList = _
  rw [initial_map_data_prefix_shape, initial_map_region]
  rfl

#print axioms initial_map_data_shape

end Project.EulerRiemann.Execution
