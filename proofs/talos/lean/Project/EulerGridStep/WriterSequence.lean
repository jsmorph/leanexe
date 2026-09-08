import Project.EulerGridStep.WriterFrames

namespace Project.EulerGridStep.Execution
open Wasm

/-- The emitted pointer argument differs only for the first field call. -/
def writerCallUnused (unused : UInt64) (roots : Nat → UInt64) (field : Nat) : UInt64 :=
  if field = 0 then unused else roots field

/-- Exact six-call control flow, abstract over the store invariant and allocation plan. -/
theorem writer_sequence_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (unused : UInt64) (roots : Nat → UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (P : Nat → Store Unit → Prop) (hInitial : P 0 initial)
    (hCall : ∀ field < 6, ∀ current, P field current →
      TerminatesWith env m 27 current
        [.i64 ((Model.payload cell).getD field 0), .i64 (UInt64.ofNat field),
          .i64 (UInt64.ofNat index), .i64 (roots field), .i64 (writerCallUnused unused roots field)]
        (fun final values => values = [.i64 (roots (field + 1)), .i64 (roots (field + 1))] ∧
          P (field + 1) final))
    (Q : Assertion Unit) (after : Wasm.Program)
    (hNext : ∀ final, P 6 final →
      wp m (writerAcceptedBody.drop 126 ++ after) Q final (writerStageFrame roots unused index cell 5) env) :
    wp m (writerAcceptedBody ++ after) Q initial (writerEntryFrame unused (roots 0) index cell) env := by
  rw [writer_stage0_shape]
  simp only [List.append_assoc]
  apply writer_first_call_spec m env initial (writerEntryFrame unused (roots 0) index cell)
    unused (roots 0) (roots 1) index cell (P 1) rfl rfl rfl
    (by simpa [writerCallUnused, Model.payload] using hCall 0 (by decide) initial hInitial) Q _
  intro current1 hP1
  change wp m (writerAcceptedBody.drop 16 ++ after) Q current1
    (writerStageFrame roots unused index cell 0) env
  rw [writer_stage1_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current1 (writerStageFrame roots unused index cell 0)
    unused (roots 0) (roots 1) (roots 2) index 1 cell (P 2)
    (by decide) (by decide) (writerStageFrame_params roots unused index cell 0)
    (writerStageFrame_locals roots unused index cell 0)
    (writerStageFrame_values roots unused index cell 0)
    (by simpa only [writerCallUnused, Nat.reduceEqDiff, ite_false] using hCall 1 (by decide) current1 hP1) Q _
  intro current2 hP2
  change wp m (writerAcceptedBody.drop 38 ++ after) Q current2
    (writerStageFrame roots unused index cell 1) env
  rw [writer_stage2_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current2 (writerStageFrame roots unused index cell 1)
    unused (roots 0) (roots 2) (roots 3) index 2 cell (P 3)
    (by decide) (by decide) (writerStageFrame_params roots unused index cell 1)
    (writerStageFrame_locals roots unused index cell 1)
    (writerStageFrame_values roots unused index cell 1)
    (by simpa only [writerCallUnused, Nat.reduceEqDiff, ite_false] using hCall 2 (by decide) current2 hP2) Q _
  intro current3 hP3
  change wp m (writerAcceptedBody.drop 60 ++ after) Q current3
    (writerStageFrame roots unused index cell 2) env
  rw [writer_stage3_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current3 (writerStageFrame roots unused index cell 2)
    unused (roots 0) (roots 3) (roots 4) index 3 cell (P 4)
    (by decide) (by decide) (writerStageFrame_params roots unused index cell 2)
    (writerStageFrame_locals roots unused index cell 2)
    (writerStageFrame_values roots unused index cell 2)
    (by simpa only [writerCallUnused, Nat.reduceEqDiff, ite_false] using hCall 3 (by decide) current3 hP3) Q _
  intro current4 hP4
  change wp m (writerAcceptedBody.drop 82 ++ after) Q current4
    (writerStageFrame roots unused index cell 3) env
  rw [writer_stage4_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current4 (writerStageFrame roots unused index cell 3)
    unused (roots 0) (roots 4) (roots 5) index 4 cell (P 5)
    (by decide) (by decide) (writerStageFrame_params roots unused index cell 3)
    (writerStageFrame_locals roots unused index cell 3)
    (writerStageFrame_values roots unused index cell 3)
    (by simpa only [writerCallUnused, Nat.reduceEqDiff, ite_false] using hCall 4 (by decide) current4 hP4) Q _
  intro current5 hP5
  change wp m (writerAcceptedBody.drop 104 ++ after) Q current5
    (writerStageFrame roots unused index cell 4) env
  rw [writer_stage5_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current5 (writerStageFrame roots unused index cell 4)
    unused (roots 0) (roots 5) (roots 6) index 5 cell (P 6)
    (by decide) (by decide) (writerStageFrame_params roots unused index cell 4)
    (writerStageFrame_locals roots unused index cell 4)
    (writerStageFrame_values roots unused index cell 4)
    (by simpa only [writerCallUnused, Nat.reduceEqDiff, ite_false] using hCall 5 (by decide) current5 hP5) Q _
  intro current6 hP6
  change wp m (writerAcceptedBody.drop 126 ++ after) Q current6
    (writerStageFrame roots unused index cell 5) env
  exact hNext current6 hP6

#print axioms writer_sequence_spec
end Project.EulerGridStep.Execution
