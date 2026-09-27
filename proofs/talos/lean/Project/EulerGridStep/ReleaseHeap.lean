import Project.EulerGridStep.BufferState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Complete scalar release retains both the buffer invariant and the fresh heap address. -/
theorem release_owned_buffer_state_heap {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (root allocs releases frees : UInt64)
    (input : Array UInt64) (live : List LiveBuffer) (rest : List UInt64)
    (hHeader : OwnedHeader initial root (fieldRequest input.size))
    (hArray : UInt64Array.At initial root input)
    (hState : BufferState initial input.size live rest allocs releases frees)
    (hLive : ∀ buffer ∈ live, ObjectsSeparate root input.size buffer.root input.size)
    (hFree : ∀ other ∈ rest, ObjectsSeparate root input.size other input.size) :
    TerminatesWith env m 40 initial [.i64 root]
      (fun final values => values = [] ∧
        ReleaseResult initial final root (fieldRequest input.size) (rest.headD 0) input ∧
        BufferState final input.size live (root :: rest) allocs (releases + 1) (frees + 1) ∧
        final.globals.globals[0]? = initial.globals.globals[0]?) := by
  apply (release_owned_to_free_chain layout env initial root releases frees input rest hHeader hArray
    hState.chain hState.freeHead hState.releases hState.frees hFree).mono
  rintro final values ⟨hValues, hResult, hChain, hGlobals⟩
  have hGlobalLength := (List.getElem?_eq_some_iff.mp hState.frees).choose
  refine ⟨hValues, hResult,
    ⟨hResult.preserves_live_buffers input.size live hState.liveAt hLive, hChain, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hGlobals]
    simpa [List.getElem?_set] using hState.allocations
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hResult.pages]
    exact hState.pages
  · rw [hGlobals]
    simp

#print axioms release_owned_buffer_state_heap
end Project.EulerGridStep.Execution
