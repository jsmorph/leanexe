import Project.EulerGridStep.WriterFrames

namespace Project.EulerGridStep.Execution
open Wasm
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- The emitted six-call sequence keeps all seven arrays live until its release tail. -/
theorem writer_copies_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (free : List UInt64)
    (hi : 1 + 6 * index + 5 < output.size)
    (hState : BufferState initial output.size (cellLive roots output index cell 0)
      ([roots 1, roots 2, roots 3, roots 4, roots 5, roots 6] ++ free) allocs releases frees)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b →
      ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hFree : ∀ a ≤ 6, ∀ other ∈ free, ObjectsSeparate (roots a) output.size other output.size)
    (Q : Assertion Unit) (after : Wasm.Program)
    (hNext : ∀ final, BufferState final output.size (cellLive roots output index cell 6)
        free (allocs + 6) releases frees →
      wp m (writerAcceptedBody.drop 126 ++ after) Q final
        (writerStageFrame roots unused index cell 5) env) :
    wp m (writerAcceptedBody ++ after) Q initial (writerEntryFrame unused (roots 0) index cell) env := by
  have hCall0 := cell_field_call layout env initial unused allocs releases frees
    roots output index 0 cell ([roots 2, roots 3, roots 4, roots 5, roots 6] ++ free) (by decide) hi hState hSlots (by
      intro other hOther
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hOther
      rcases hOther with rfl | rfl | rfl | rfl | rfl | hOther
      · exact hSlots 1 (by decide) 2 (by decide) (by decide)
      · exact hSlots 1 (by decide) 3 (by decide) (by decide)
      · exact hSlots 1 (by decide) 4 (by decide) (by decide)
      · exact hSlots 1 (by decide) 5 (by decide) (by decide)
      · exact hSlots 1 (by decide) 6 (by decide) (by decide)
      · exact hFree 1 (by decide) other hOther)
  rw [writer_stage0_shape]
  simp only [List.append_assoc]
  apply writer_first_call_spec m env initial (writerEntryFrame unused (roots 0) index cell) unused (roots 0) (roots 1) index cell
    (fun final => BufferState final output.size (cellLive roots output index cell 1)
      ([roots 2, roots 3, roots 4, roots 5, roots 6] ++ free) (allocs + 1) releases frees) rfl rfl rfl hCall0 Q _
  intro current1 hState1
  change wp m (writerAcceptedBody.drop 16 ++ after) Q current1
    (writerStageFrame roots unused index cell 0) env
  have hCall1 := cell_field_call layout env current1 (roots 1) (allocs + 1) releases frees
    roots output index 1 cell ([roots 3, roots 4, roots 5, roots 6] ++ free) (by decide) hi hState1 hSlots (by
      intro other hOther
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hOther
      rcases hOther with rfl | rfl | rfl | rfl | hOther
      · exact hSlots 2 (by decide) 3 (by decide) (by decide)
      · exact hSlots 2 (by decide) 4 (by decide) (by decide)
      · exact hSlots 2 (by decide) 5 (by decide) (by decide)
      · exact hSlots 2 (by decide) 6 (by decide) (by decide)
      · exact hFree 2 (by decide) other hOther)
  rw [writer_stage1_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current1 (writerStageFrame roots unused index cell 0)
    unused (roots 0) (roots 1) (roots 2) index 1 cell
    (fun final => BufferState final output.size (cellLive roots output index cell 2)
      ([roots 3, roots 4, roots 5, roots 6] ++ free) (allocs + 2) releases frees) (by decide) (by decide)
    (writerStageFrame_params roots unused index cell 0)
    (writerStageFrame_locals roots unused index cell 0)
    (writerStageFrame_values roots unused index cell 0)
    (by simpa only [UInt64.add_assoc, show (1 : UInt64) + 1 = 2 from by decide] using hCall1) Q _
  intro current2 hState2
  change wp m (writerAcceptedBody.drop 38 ++ after) Q current2
    (writerStageFrame roots unused index cell 1) env
  have hCall2 := cell_field_call layout env current2 (roots 2) (allocs + 2) releases frees
    roots output index 2 cell ([roots 4, roots 5, roots 6] ++ free) (by decide) hi hState2 hSlots (by
      intro other hOther
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hOther
      rcases hOther with rfl | rfl | rfl | hOther
      · exact hSlots 3 (by decide) 4 (by decide) (by decide)
      · exact hSlots 3 (by decide) 5 (by decide) (by decide)
      · exact hSlots 3 (by decide) 6 (by decide) (by decide)
      · exact hFree 3 (by decide) other hOther)
  rw [writer_stage2_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current2 (writerStageFrame roots unused index cell 1)
    unused (roots 0) (roots 2) (roots 3) index 2 cell
    (fun final => BufferState final output.size (cellLive roots output index cell 3)
      ([roots 4, roots 5, roots 6] ++ free) (allocs + 3) releases frees) (by decide) (by decide)
    (writerStageFrame_params roots unused index cell 1)
    (writerStageFrame_locals roots unused index cell 1)
    (writerStageFrame_values roots unused index cell 1)
    (by simpa only [UInt64.add_assoc, show (2 : UInt64) + 1 = 3 from by decide] using hCall2) Q _
  intro current3 hState3
  change wp m (writerAcceptedBody.drop 60 ++ after) Q current3
    (writerStageFrame roots unused index cell 2) env
  have hCall3 := cell_field_call layout env current3 (roots 3) (allocs + 3) releases frees
    roots output index 3 cell ([roots 5, roots 6] ++ free) (by decide) hi hState3 hSlots (by
      intro other hOther
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hOther
      rcases hOther with rfl | rfl | hOther
      · exact hSlots 4 (by decide) 5 (by decide) (by decide)
      · exact hSlots 4 (by decide) 6 (by decide) (by decide)
      · exact hFree 4 (by decide) other hOther)
  rw [writer_stage3_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current3 (writerStageFrame roots unused index cell 2)
    unused (roots 0) (roots 3) (roots 4) index 3 cell
    (fun final => BufferState final output.size (cellLive roots output index cell 4)
      ([roots 5, roots 6] ++ free) (allocs + 4) releases frees) (by decide) (by decide)
    (writerStageFrame_params roots unused index cell 2)
    (writerStageFrame_locals roots unused index cell 2)
    (writerStageFrame_values roots unused index cell 2)
    (by simpa only [UInt64.add_assoc, show (3 : UInt64) + 1 = 4 from by decide] using hCall3) Q _
  intro current4 hState4
  change wp m (writerAcceptedBody.drop 82 ++ after) Q current4
    (writerStageFrame roots unused index cell 3) env
  have hCall4 := cell_field_call layout env current4 (roots 4) (allocs + 4) releases frees
    roots output index 4 cell ([roots 6] ++ free) (by decide) hi hState4 hSlots (by
      intro other hOther
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hOther
      rcases hOther with rfl | hOther
      · exact hSlots 5 (by decide) 6 (by decide) (by decide)
      · exact hFree 5 (by decide) other hOther)
  rw [writer_stage4_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current4 (writerStageFrame roots unused index cell 3)
    unused (roots 0) (roots 4) (roots 5) index 4 cell
    (fun final => BufferState final output.size (cellLive roots output index cell 5)
      ([roots 6] ++ free) (allocs + 5) releases frees) (by decide) (by decide)
    (writerStageFrame_params roots unused index cell 3)
    (writerStageFrame_locals roots unused index cell 3)
    (writerStageFrame_values roots unused index cell 3)
    (by simpa only [UInt64.add_assoc, show (4 : UInt64) + 1 = 5 from by decide] using hCall4) Q _
  intro current5 hState5
  change wp m (writerAcceptedBody.drop 104 ++ after) Q current5
    (writerStageFrame roots unused index cell 4) env
  have hCall5 := cell_field_call layout env current5 (roots 5) (allocs + 5) releases frees
    roots output index 5 cell free (by decide) hi hState5 hSlots (by
      intro other hOther
      exact hFree 6 (by decide) other hOther)
  rw [writer_stage5_shape]
  simp only [List.append_assoc]
  apply writer_next_call_spec m env current5 (writerStageFrame roots unused index cell 4)
    unused (roots 0) (roots 5) (roots 6) index 5 cell
    (fun final => BufferState final output.size (cellLive roots output index cell 6)
      free (allocs + 6) releases frees) (by decide) (by decide)
    (writerStageFrame_params roots unused index cell 4)
    (writerStageFrame_locals roots unused index cell 4)
    (writerStageFrame_values roots unused index cell 4)
    (by simpa only [UInt64.add_assoc, show (5 : UInt64) + 1 = 6 from by decide] using hCall5) Q _
  intro current6 hState6
  change wp m (writerAcceptedBody.drop 126 ++ after) Q current6
    (writerStageFrame roots unused index cell 5) env
  exact hNext current6 hState6

#print axioms writer_copies_spec
end Project.EulerGridStep.Execution
