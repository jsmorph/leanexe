import Project.EulerGridStep.ReleaseHeap

namespace Project.EulerGridStep.Execution
open Wasm

theorem release_previous_output_framed {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (oldRoot newRoot allocs releases frees : UInt64)
    (oldOutput newOutput : Array UInt64) (free : List UInt64)
    (hSize : newOutput.size = oldOutput.size)
    (hState : BufferState initial oldOutput.size
      [⟨newRoot, newOutput⟩, ⟨oldRoot, oldOutput⟩] free allocs releases frees)
    (hNew : ObjectsSeparate oldRoot oldOutput.size newRoot oldOutput.size)
    (hFree : ∀ other ∈ free, ObjectsSeparate oldRoot oldOutput.size other oldOutput.size)
    (P : Store Unit → Prop)
    (hPreserve : ∀ final, ReleaseResult initial final oldRoot (fieldRequest oldOutput.size)
      (free.headD 0) oldOutput → P final) :
    TerminatesWith env m 40 initial [.i64 oldRoot]
      (fun final values => values = [] ∧
        BufferState final newOutput.size [⟨newRoot, newOutput⟩]
          (oldRoot :: free) allocs (releases + 1) (frees + 1) ∧
        final.globals.globals[0]? = initial.globals.globals[0]? ∧
        final.mem.pages = initial.mem.pages ∧ P final) := by
  have hOld := hState.liveAt ⟨oldRoot, oldOutput⟩ (by simp)
  have hKeep := hState.restrict_live [⟨newRoot, newOutput⟩] (by
    intro buffer hBuffer
    rcases List.mem_singleton.mp hBuffer with rfl
    exact List.mem_cons_self)
  apply (release_owned_buffer_state_heap layout env initial oldRoot allocs releases frees
    oldOutput [⟨newRoot, newOutput⟩] free hOld.2.1 hOld.2.2 hKeep
    (by
      intro buffer hBuffer
      rcases List.mem_singleton.mp hBuffer with rfl
      exact hNew) hFree).mono
  rintro final values ⟨hValues, hResult, hBuffers, hHeap⟩
  exact ⟨hValues, by simpa only [hSize] using hBuffers, hHeap, hResult.pages,
    hPreserve final hResult⟩

#print axioms release_previous_output_framed
end Project.EulerGridStep.Execution
