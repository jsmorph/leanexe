import Project.EulerGridStep.InitializationShape
import Project.EulerGridStep.GridLoopAdvance

namespace Project.EulerGridStep.Execution
open Wasm

def gridLoopCode : Wasm.Program :=
  match (gridValidBody[94]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => body
  | _ => []

theorem grid_loop_shape : gridValidBody[94]? = some (.block 0 0 [.loop 0 0 gridLoopCode]) := rfl

theorem grid_valid_regions : gridValidBody = gridValidBody.take 78 ++
    (gridValidBody.drop 78).take 16 ++ [.block 0 0 [.loop 0 0 gridLoopCode]] ++ gridValidBody.drop 95 := by
  have hTake : gridValidBody.take 78 ++ (gridValidBody.drop 78).take 16 = gridValidBody.take 94 := by
    rw [List.take_drop]
    simpa only [List.take_take, show min 78 94 = 78 from rfl, Nat.reduceAdd] using List.take_append_drop 78 (gridValidBody.take 94)
  have hLoop : gridValidBody.take 95 = gridValidBody.take 94 ++ [.block 0 0 [.loop 0 0 gridLoopCode]] := by
    simpa only [grid_loop_shape, Option.toList_some] using (List.take_add_one (l := gridValidBody) (i := 94))
  rw [hTake, ← hLoop]
  exact (List.take_append_drop 95 gridValidBody).symm

#print axioms grid_loop_shape
#print axioms grid_valid_regions
end Project.EulerGridStep.Execution
