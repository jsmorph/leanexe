import Project.EulerGridStep.CellReleaseCall

namespace Project.EulerGridStep.Execution
open Wasm

/-- Releasing one intermediate preserves the completed result and all earlier live prefixes. -/
theorem cell_release_call_framed {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index count : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (free : List UInt64)
    (hLo : 1 ≤ count) (hHi : count ≤ 5)
    (hState : BufferState initial output.size (cellKept roots output index cell count)
      free allocs releases frees)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b →
      ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hFree : ∀ other ∈ free, ObjectsSeparate (roots count) output.size other output.size)
    (P : Store Unit → Prop)
    (hPreserve : ∀ final,
      ReleaseResult initial final (roots count) (fieldRequest output.size) (free.headD 0)
        (cellPrefix output index cell count) → P final) :
    TerminatesWith env m 40 initial [.i64 (roots count)]
      (fun final values => values = [] ∧
        BufferState final output.size (cellKept roots output index cell (count - 1))
          (roots count :: free) allocs (releases + 1) (frees + 1) ∧ P final) := by
  have hCurrent := hState.liveAt ⟨roots count, cellPrefix output index cell count⟩
    (List.mem_cons_of_mem _ (cellLive_contains roots output index cell count count (by omega)))
  have hKeep : ∀ buffer ∈ cellKept roots output index cell (count - 1),
      buffer ∈ cellKept roots output index cell count := by
    intro buffer hBuffer
    rcases List.mem_cons.mp hBuffer with rfl | hBuffer
    · exact List.mem_cons_self
    · obtain ⟨k, hk, rfl⟩ := cellLive_member roots output index cell (count - 1) buffer hBuffer
      exact List.mem_cons_of_mem _ (cellLive_contains roots output index cell count k (by omega))
  have hLive : ∀ buffer ∈ cellKept roots output index cell (count - 1),
      ObjectsSeparate (roots count) output.size buffer.root output.size := by
    intro buffer hBuffer
    rcases List.mem_cons.mp hBuffer with rfl | hBuffer
    · exact hSlots count (by omega) 6 (by omega) (by omega)
    · obtain ⟨k, hk, rfl⟩ := cellLive_member roots output index cell (count - 1) buffer hBuffer
      exact hSlots count (by omega) k (by omega) (by omega)
  have hCall := release_owned_buffer_state layout env initial (roots count) allocs releases frees
    (cellPrefix output index cell count) (cellKept roots output index cell (count - 1)) free
    (by simpa only [cellPrefix_size] using hCurrent.2.1) hCurrent.2.2
    (by simpa only [cellPrefix_size] using hState.restrict_live _ hKeep)
    (by simpa only [cellPrefix_size] using hLive)
    (by simpa only [cellPrefix_size] using hFree)
  apply hCall.mono
  rintro final values ⟨hValues, hResult, hFinal⟩
  refine ⟨hValues, ?_, hPreserve final ?_⟩
  · simpa only [cellPrefix_size] using hFinal
  · simpa only [cellPrefix_size] using hResult

#print axioms cell_release_call_framed
end Project.EulerGridStep.Execution
