import Project.EulerGridStep.WriterReleaseFrame

namespace Project.EulerGridStep.Execution
open Wasm

/-- Allocation-independent control for the writer's five generated release calls. -/
theorem writer_release_sequence_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (unused : UInt64) (roots : Nat → UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (P : Nat → Store Unit → Prop)
    (hInitial : P 5 initial)
    (hNonzero : ∀ count, 1 ≤ count → count ≤ 5 → roots count ≠ 0)
    (hCall : ∀ count, 1 ≤ count → count ≤ 5 → ∀ current, P count current →
      TerminatesWith env m 40 current [.i64 (roots count)]
        (fun final values => values = [] ∧ P (count - 1) final))
    (Q : Assertion Unit) (after : Wasm.Program)
    (hNext : ∀ final, P 0 final → wp m after Q final (writerReleaseFrame roots unused index cell) env) :
    wp m (writerReleaseTail ++ after) Q initial (writerStageFrame roots unused index cell 5) env := by
  rw [writer_release_setup_shape]
  simp only [List.append_assoc]
  apply writer_release_setup_spec m env initial (writerStageFrame roots unused index cell 5) (roots 6)
    (by simp [writerParameters]) (writerStageFrame_locals roots unused index cell 5)
    (writerStageFrame_values roots unused index cell 5) Q _
  change wp m (writerReleaseTail.drop 6 ++ after) Q initial (writerReleaseFrame roots unused index cell) env
  rw [writer_release_stage0_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env initial (writerReleaseFrame roots unused index cell)
    51 (roots 5) (P 4) rfl
    (writerReleaseFrame_pointer roots unused index 5 cell (by decide) (by decide))
    (hNonzero 5 (by decide) (by decide))
    (hCall 5 (by decide) (by decide) initial hInitial) Q _
  intro current4 hP4
  rw [writer_release_stage1_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env current4 (writerReleaseFrame roots unused index cell)
    42 (roots 4) (P 3) rfl
    (writerReleaseFrame_pointer roots unused index 4 cell (by decide) (by decide))
    (hNonzero 4 (by decide) (by decide))
    (hCall 4 (by decide) (by decide) current4 hP4) Q _
  intro current3 hP3
  rw [writer_release_stage2_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env current3 (writerReleaseFrame roots unused index cell)
    33 (roots 3) (P 2) rfl
    (writerReleaseFrame_pointer roots unused index 3 cell (by decide) (by decide))
    (hNonzero 3 (by decide) (by decide))
    (hCall 3 (by decide) (by decide) current3 hP3) Q _
  intro current2 hP2
  rw [writer_release_stage3_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env current2 (writerReleaseFrame roots unused index cell)
    24 (roots 2) (P 1) rfl
    (writerReleaseFrame_pointer roots unused index 2 cell (by decide) (by decide))
    (hNonzero 2 (by decide) (by decide))
    (hCall 2 (by decide) (by decide) current2 hP2) Q _
  intro current1 hP1
  rw [writer_release_stage4_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env current1 (writerReleaseFrame roots unused index cell)
    15 (roots 1) (P 0) rfl
    (writerReleaseFrame_pointer roots unused index 1 cell (by decide) (by decide))
    (hNonzero 1 (by decide) (by decide))
    (hCall 1 (by decide) (by decide) current1 hP1) Q _
  intro current0 hP0
  rw [writer_release_end, List.nil_append]
  exact hNext current0 hP0

#print axioms writer_release_sequence_spec
end Project.EulerGridStep.Execution
