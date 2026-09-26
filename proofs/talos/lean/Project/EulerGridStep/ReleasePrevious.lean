import Project.EulerGridStep.ProtectedBuffer
import Project.EulerGridStep.BufferState

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

/-- The loop can return its previous output to the free list while retaining the new result. -/
theorem release_previous_output {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (oldRoot nextRoot allocs releases frees : UInt64)
    (oldOutput nextOutput : Array UInt64) (free : List UInt64)
    (hSize : nextOutput.size = oldOutput.size)
    (hState : BufferState initial oldOutput.size
      [⟨nextRoot, nextOutput⟩, ⟨oldRoot, oldOutput⟩] free allocs releases frees)
    (hNextSeparate : ObjectsSeparate oldRoot oldOutput.size nextRoot oldOutput.size)
    (hFreeSeparate : ∀ root ∈ free, ObjectsSeparate oldRoot oldOutput.size root oldOutput.size)
    (P : Store Unit → Prop)
    (hPreserve : ∀ final, ReleaseResult initial final oldRoot (fieldRequest oldOutput.size)
      (free.headD 0) oldOutput → P final) :
    TerminatesWith env m 40 initial [.i64 oldRoot]
      (fun final values => values = [] ∧
        BufferState final nextOutput.size [⟨nextRoot, nextOutput⟩] (oldRoot :: free)
          allocs (releases + 1) (frees + 1) ∧
        final.mem.pages = initial.mem.pages ∧ P final) := by
  have hOld := hState.liveAt ⟨oldRoot, oldOutput⟩ (by simp)
  have hKeep := hState.restrict_live [⟨nextRoot, nextOutput⟩] (by
    intro buffer hb
    obtain rfl := List.mem_singleton.mp hb
    exact List.mem_cons_self)
  apply (release_owned_buffer_state layout env initial oldRoot allocs releases frees oldOutput
    [⟨nextRoot, nextOutput⟩] free hOld.2.1 hOld.2.2 hKeep (by
      intro buffer hb
      obtain rfl := List.mem_singleton.mp hb
      exact hNextSeparate) hFreeSeparate).mono
  rintro final values ⟨hv, hResult, hBuffers⟩
  exact ⟨hv, by simpa only [hSize] using hBuffers, hResult.pages, hPreserve final hResult⟩

#print axioms release_previous_output
end Project.EulerGridStep.Execution
