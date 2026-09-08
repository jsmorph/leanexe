import Project.EulerGridStep.FreeFrame
import Project.EulerGridStep.Release

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Exact release execution with reusable metadata and live/free buffer framing. -/
theorem release_owned_framed {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (root capacity freeList releases frees : UInt64)
    (input : Array UInt64) (hHeader : OwnedHeader initial root capacity)
    (hArray : UInt64Array.At initial root input)
    (hFreeList : initial.globals.globals[1]? = some (.i64 freeList))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees)) :
    TerminatesWith env m 40 initial [.i64 root]
      (fun final values => values = [] ∧
        final.globals.globals =
          ((initial.globals.globals.set 4 (.i64 (releases + 1))).set 5
            (.i64 (frees + 1))).set 1 (.i64 root) ∧
        ReleaseResult initial final root capacity freeList input) := by
  apply (release_owned_exact layout env initial root capacity freeList releases frees input
    hHeader hArray hFreeList hReleases hFrees).mono
  rintro final values ⟨hValues, hMem, hGlobals⟩
  exact ⟨hValues, hGlobals,
    release_result_of_memory initial final root capacity freeList input hHeader hArray hMem⟩

#print axioms release_owned_framed
end Project.EulerGridStep.Execution
