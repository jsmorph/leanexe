import Project.EulerGridStep.InitializationShape
import Project.EulerGridStep.GridLoopAdvance

namespace Project.EulerGridStep.Execution
open Wasm

def gridLoopCode : Wasm.Program :=
  match (gridValidBody[92]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => body
  | _ => []

theorem grid_loop_shape : gridValidBody[92]? = some (.block 0 0 [.loop 0 0 gridLoopCode]) := rfl

theorem grid_valid_regions : gridValidBody = gridValidBody.take 78 ++
    (gridValidBody.drop 78).take 14 ++ [.block 0 0 [.loop 0 0 gridLoopCode]] ++ gridValidBody.drop 93 := by
  have hTake : gridValidBody.take 78 ++ (gridValidBody.drop 78).take 14 = gridValidBody.take 92 := by
    rw [List.take_drop]
    simpa only [List.take_take, show min 78 92 = 78 from rfl, Nat.reduceAdd] using List.take_append_drop 78 (gridValidBody.take 92)
  have hLoop : gridValidBody.take 93 = gridValidBody.take 92 ++ [.block 0 0 [.loop 0 0 gridLoopCode]] := by
    simpa only [grid_loop_shape, Option.toList_some] using (List.take_add_one (l := gridValidBody) (i := 92))
  rw [hTake, ← hLoop]
  exact (List.take_append_drop 93 gridValidBody).symm

#print axioms grid_loop_shape
#print axioms grid_valid_regions
end Project.EulerGridStep.Execution
