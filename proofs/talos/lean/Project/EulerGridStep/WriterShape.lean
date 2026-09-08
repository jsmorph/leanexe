import Project.EulerGridStep.CellFieldCall

namespace Project.EulerGridStep.Execution
open Wasm

def writerAcceptedBody : Wasm.Program :=
  match (func34[10]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

def writerRejectedBody : Wasm.Program :=
  match (func34[10]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ _ body _ _) => body
  | _ => []

def writerFirstCall : Wasm.Program :=
  [.localGet 0, .localSet 10, .localGet 1, .localSet 11, .localGet 2, .localSet 12,
    .constI64 0, .localSet 13, .localGet 4, .localSet 14,
    .localGet 10, .localGet 11, .localGet 12, .localGet 13, .localGet 14, .call 27]

def writerNextCall (field : Nat) : Wasm.Program :=
  let offset := 9 * field + 6
  [.localSet (offset + 1), .localSet offset,
    .localGet offset, .localSet (offset + 2), .localGet (offset + 1), .localSet (offset + 3),
    .localGet (offset + 2), .localSet (offset + 4), .localGet (offset + 3), .localSet (offset + 5),
    .localGet 2, .localSet (offset + 6), .constI64 (UInt64.ofNat field), .localSet (offset + 7),
    .localGet (4 + field), .localSet (offset + 8),
    .localGet (offset + 4), .localGet (offset + 5), .localGet (offset + 6),
    .localGet (offset + 7), .localGet (offset + 8), .call 27]

def writerReleaseTail : Wasm.Program := writerAcceptedBody.drop 126

theorem writer_function_shape : func34 = func34.take 10 ++
    [.iff 0 0 writerAcceptedBody writerRejectedBody, .localGet 65, .localGet 66] := rfl

theorem writer_stage0_shape : writerAcceptedBody =
    writerFirstCall ++ writerAcceptedBody.drop 16 := rfl

theorem writer_stage1_shape : writerAcceptedBody.drop 16 =
    writerNextCall 1 ++ writerAcceptedBody.drop 38 := rfl

theorem writer_stage2_shape : writerAcceptedBody.drop 38 =
    writerNextCall 2 ++ writerAcceptedBody.drop 60 := rfl

theorem writer_stage3_shape : writerAcceptedBody.drop 60 =
    writerNextCall 3 ++ writerAcceptedBody.drop 82 := rfl

theorem writer_stage4_shape : writerAcceptedBody.drop 82 =
    writerNextCall 4 ++ writerAcceptedBody.drop 104 := rfl

theorem writer_stage5_prefix : (writerAcceptedBody.drop 104).take 22 = writerNextCall 5 := rfl

theorem writer_stage5_shape : writerAcceptedBody.drop 104 =
    writerNextCall 5 ++ writerAcceptedBody.drop 126 := by
  calc
    _ = (writerAcceptedBody.drop 104).take 22 ++ (writerAcceptedBody.drop 104).drop 22 :=
      (List.take_append_drop 22 _).symm
    _ = _ := by rw [writer_stage5_prefix, List.drop_drop]



theorem writer_frame_shape : func34Def.params.length = 10 ∧ func34Def.locals.length = 72 :=
  ⟨rfl, rfl⟩

#print axioms writer_function_shape
#print axioms writer_stage0_shape
#print axioms writer_stage1_shape
#print axioms writer_stage2_shape
#print axioms writer_stage3_shape
#print axioms writer_stage4_shape
#print axioms writer_stage5_shape
#print axioms writer_frame_shape
end Project.EulerGridStep.Execution
