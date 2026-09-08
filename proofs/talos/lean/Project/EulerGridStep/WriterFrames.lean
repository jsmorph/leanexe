import Project.EulerGridStep.WriterCalls

namespace Project.EulerGridStep.Execution
open Wasm

/-- Exact cell-writer frame after each completed field call, before the next handoff. -/
def writerStageFrame (roots : Nat → UInt64) (unused : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) : Nat → Locals
  | 0 =>
      { writerFirstFrame (writerEntryFrame unused (roots 0) index cell)
          unused (roots 0) index cell.density with values := [.i64 (roots 1), .i64 (roots 1)] }
  | field + 1 =>
      { writerNextFrame (writerStageFrame roots unused index cell field) (field + 1)
          (roots (field + 1)) index ((Model.payload cell).getD (field + 1) 0) with
        values := [.i64 (roots (field + 2)), .i64 (roots (field + 2))] }

@[simp] theorem writerStageFrame_params (roots : Nat → UInt64) (unused : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (field : Nat) :
    (writerStageFrame roots unused index cell field).params = writerParameters unused (roots 0) index cell := by
  induction field with
  | zero => rfl
  | succ field ih => simpa only [writerStageFrame, writerNextFrame] using ih

@[simp] theorem writerStageFrame_locals (roots : Nat → UInt64) (unused : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (field : Nat) :
    (writerStageFrame roots unused index cell field).locals.length = 72 := by
  induction field with
  | zero => simp [writerStageFrame, writerFirstFrame, writerEntryFrame]
  | succ field ih => simpa [writerStageFrame, writerNextFrame] using ih

@[simp] theorem writerStageFrame_values (roots : Nat → UInt64) (unused : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (field : Nat) :
    (writerStageFrame roots unused index cell field).values =
      [.i64 (roots (field + 1)), .i64 (roots (field + 1))] := by
  cases field <;> rfl

#print axioms writerStageFrame_params
#print axioms writerStageFrame_locals
#print axioms writerStageFrame_values
end Project.EulerGridStep.Execution
