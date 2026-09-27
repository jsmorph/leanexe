import Project.EulerRiemann.InitialArrayInstall

namespace Project.EulerRiemann.Execution
open Wasm

def initialMapDataProgram : Wasm.Program := (initialGrowBody.drop 45).take 9

theorem initial_map_data_prefix_shape : (initialGrowBody.drop 45).take 8 =
    InitialAllocationSite.map.installProgram ++ [.constI64 0, .localSet 51] := by
  rfl

#print axioms initial_map_data_prefix_shape

end Project.EulerRiemann.Execution
