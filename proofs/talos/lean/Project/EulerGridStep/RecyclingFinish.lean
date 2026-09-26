import Project.EulerGridStep.RecyclingState
import Project.EulerGridStep.ReleaseFramed

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

/-- Releasing the initial buffer preserves the returned output for every pool permutation. -/
theorem recycling_final_release {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (root initialRoot : UInt64)
    (output initialOutput : Array UInt64)
    (hReady : GridFinishReady initial root initialRoot output)
    (hInitial : (⟨initialRoot, initialOutput⟩ : LiveBuffer).At initial output.size) :
    TerminatesWith env m 40 initial [.i64 initialRoot]
      (fun final values => values = [] ∧ UInt64Array.At final root output) := by
  obtain ⟨head, releases, frees, hHead, hReleases, hFrees⟩ := hReady.counters
  apply (release_owned_framed layout env initial initialRoot (fieldRequest output.size) head releases frees
    initialOutput hInitial.2.1 hInitial.2.2 hHead hReleases hFrees).mono
  rintro final values ⟨hv, _, hResult⟩
  refine ⟨hv, hResult.preserves_array root output hReady.outputAt ?_⟩
  simpa only [hInitial.1] using objectsSeparate_symm hReady.separate

#print axioms recycling_final_release
end Project.EulerGridStep.Execution
