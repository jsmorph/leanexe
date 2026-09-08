import Project.EulerGridStep.WriterReleaseFrame
import Project.EulerGridStep.CellReleaseFramed

namespace Project.EulerGridStep.Execution
open Wasm

/-- The five exact releases carry a property preserved by their complete memory results. -/
theorem writer_releases_framed_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (free : List UInt64)
    (hState : BufferState initial output.size (cellLive roots output index cell 6)
      free allocs releases frees)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b →
      ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hFree : ∀ a ≤ 6, ∀ other ∈ free, ObjectsSeparate (roots a) output.size other output.size)
    (P : Store Unit → Prop) (hP : P initial)
    (hPreserve : ∀ count, 1 ≤ count → count ≤ 5 →
      ∀ (current final : Store Unit) (next : UInt64), P current →
      ReleaseResult current final (roots count) (fieldRequest output.size) next
        (cellPrefix output index cell count) → P final)
    (Q : Assertion Unit) (after : Wasm.Program)
    (hNext : ∀ final, BufferState final output.size (cellKept roots output index cell 0)
        ([roots 1, roots 2, roots 3, roots 4, roots 5] ++ free) allocs (releases + 5) (frees + 5) → P final →
      wp m after Q final (writerReleaseFrame roots unused index cell) env) :
    wp m (writerReleaseTail ++ after) Q initial (writerStageFrame roots unused index cell 5) env := by
  have hNonzero : ∀ k ≤ 6, roots k ≠ 0 := by
    intro k hk hz
    have hLive := hState.liveAt ⟨roots k, cellPrefix output index cell k⟩
      (cellLive_contains roots output index cell 6 k hk)
    have h48 := hLive.2.1.root48
    rw [hz] at h48
    simp at h48
  rw [writer_release_setup_shape]
  simp only [List.append_assoc]
  apply writer_release_setup_spec m env initial (writerStageFrame roots unused index cell 5) (roots 6)
    (by simp [writerParameters]) (writerStageFrame_locals roots unused index cell 5)
    (writerStageFrame_values roots unused index cell 5) Q _
  change wp m (writerReleaseTail.drop 6 ++ after) Q initial
    (writerReleaseFrame roots unused index cell) env
  have hCall0 := cell_release_call_framed layout env initial allocs releases frees
    roots output index 5 cell free (by decide) (by decide) hState hSlots (by
      intro other hOther
      exact hFree 5 (by decide) other hOther) P (fun final hResult =>
      hPreserve 5 (by decide) (by decide) initial final (free.headD 0) hP hResult)
  rw [writer_release_stage0_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env initial (writerReleaseFrame roots unused index cell)
    51 (roots 5)
    (fun final => BufferState final output.size (cellKept roots output index cell 4)
      ([roots 5] ++ free) allocs (releases + 1) (frees + 1) ∧ P final) rfl
    (writerReleaseFrame_pointer roots unused index 5 cell (by decide) (by decide))
    (hNonzero 5 (by decide))
    hCall0 Q _
  intro current1 ⟨hState1, hP1⟩
  have hCall1 := cell_release_call_framed layout env current1 allocs (releases + 1) (frees + 1)
    roots output index 4 cell ([roots 5] ++ free) (by decide) (by decide) hState1 hSlots (by
      intro other hOther
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hOther
      rcases hOther with rfl | hOther
      · exact hSlots 4 (by decide) 5 (by decide) (by decide)
      · exact hFree 4 (by decide) other hOther) P (fun final hResult =>
      hPreserve 4 (by decide) (by decide) current1 final (roots 5) hP1 hResult)
  rw [writer_release_stage1_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env current1 (writerReleaseFrame roots unused index cell)
    42 (roots 4)
    (fun final => BufferState final output.size (cellKept roots output index cell 3)
      ([roots 4, roots 5] ++ free) allocs (releases + 2) (frees + 2) ∧ P final) rfl
    (writerReleaseFrame_pointer roots unused index 4 cell (by decide) (by decide))
    (hNonzero 4 (by decide))
    (by simpa only [Nat.reduceSub, List.cons_append, List.nil_append, UInt64.add_assoc, show (1 : UInt64) + 1 = 2 from by decide] using hCall1) Q _
  intro current2 ⟨hState2, hP2⟩
  have hCall2 := cell_release_call_framed layout env current2 allocs (releases + 2) (frees + 2)
    roots output index 3 cell ([roots 4, roots 5] ++ free) (by decide) (by decide) hState2 hSlots (by
      intro other hOther
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hOther
      rcases hOther with rfl | rfl | hOther
      · exact hSlots 3 (by decide) 4 (by decide) (by decide)
      · exact hSlots 3 (by decide) 5 (by decide) (by decide)
      · exact hFree 3 (by decide) other hOther) P (fun final hResult =>
      hPreserve 3 (by decide) (by decide) current2 final (roots 4) hP2 hResult)
  rw [writer_release_stage2_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env current2 (writerReleaseFrame roots unused index cell)
    33 (roots 3)
    (fun final => BufferState final output.size (cellKept roots output index cell 2)
      ([roots 3, roots 4, roots 5] ++ free) allocs (releases + 3) (frees + 3) ∧ P final) rfl
    (writerReleaseFrame_pointer roots unused index 3 cell (by decide) (by decide))
    (hNonzero 3 (by decide))
    (by simpa only [Nat.reduceSub, List.cons_append, List.nil_append, UInt64.add_assoc, show (2 : UInt64) + 1 = 3 from by decide] using hCall2) Q _
  intro current3 ⟨hState3, hP3⟩
  have hCall3 := cell_release_call_framed layout env current3 allocs (releases + 3) (frees + 3)
    roots output index 2 cell ([roots 3, roots 4, roots 5] ++ free) (by decide) (by decide) hState3 hSlots (by
      intro other hOther
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hOther
      rcases hOther with rfl | rfl | rfl | hOther
      · exact hSlots 2 (by decide) 3 (by decide) (by decide)
      · exact hSlots 2 (by decide) 4 (by decide) (by decide)
      · exact hSlots 2 (by decide) 5 (by decide) (by decide)
      · exact hFree 2 (by decide) other hOther) P (fun final hResult =>
      hPreserve 2 (by decide) (by decide) current3 final (roots 3) hP3 hResult)
  rw [writer_release_stage3_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env current3 (writerReleaseFrame roots unused index cell)
    24 (roots 2)
    (fun final => BufferState final output.size (cellKept roots output index cell 1)
      ([roots 2, roots 3, roots 4, roots 5] ++ free) allocs (releases + 4) (frees + 4) ∧ P final) rfl
    (writerReleaseFrame_pointer roots unused index 2 cell (by decide) (by decide))
    (hNonzero 2 (by decide))
    (by simpa only [Nat.reduceSub, List.cons_append, List.nil_append, UInt64.add_assoc, show (3 : UInt64) + 1 = 4 from by decide] using hCall3) Q _
  intro current4 ⟨hState4, hP4⟩
  have hCall4 := cell_release_call_framed layout env current4 allocs (releases + 4) (frees + 4)
    roots output index 1 cell ([roots 2, roots 3, roots 4, roots 5] ++ free) (by decide) (by decide) hState4 hSlots (by
      intro other hOther
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hOther
      rcases hOther with rfl | rfl | rfl | rfl | hOther
      · exact hSlots 1 (by decide) 2 (by decide) (by decide)
      · exact hSlots 1 (by decide) 3 (by decide) (by decide)
      · exact hSlots 1 (by decide) 4 (by decide) (by decide)
      · exact hSlots 1 (by decide) 5 (by decide) (by decide)
      · exact hFree 1 (by decide) other hOther) P (fun final hResult =>
      hPreserve 1 (by decide) (by decide) current4 final (roots 2) hP4 hResult)
  rw [writer_release_stage4_shape]
  simp only [List.append_assoc]
  apply writer_release_one_spec m env current4 (writerReleaseFrame roots unused index cell)
    15 (roots 1)
    (fun final => BufferState final output.size (cellKept roots output index cell 0)
      ([roots 1, roots 2, roots 3, roots 4, roots 5] ++ free) allocs (releases + 5) (frees + 5) ∧ P final) rfl
    (writerReleaseFrame_pointer roots unused index 1 cell (by decide) (by decide))
    (hNonzero 1 (by decide))
    (by simpa only [Nat.reduceSub, List.cons_append, List.nil_append, UInt64.add_assoc, show (4 : UInt64) + 1 = 5 from by decide] using hCall4) Q _
  intro current5 ⟨hState5, hP5⟩
  rw [writer_release_end, List.nil_append]
  exact hNext current5 hState5 hP5

#print axioms writer_releases_framed_spec
end Project.EulerGridStep.Execution
