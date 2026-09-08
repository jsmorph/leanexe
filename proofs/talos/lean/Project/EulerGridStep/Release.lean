import Project.EulerGridStep.AllocationMemory
import Project.EulerGridStep.Helpers
import Project.Runtime.FixedArraySpec

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Reuse the runtime's scalar-array release proof at the exact grid-module call boundary. -/
theorem release_owned_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (root capacity freeList releases frees : UInt64)
    (input : Array UInt64) (hHeader : OwnedHeader initial root capacity)
    (hArray : UInt64Array.At initial root input)
    (hFreeList : initial.globals.globals[1]? = some (.i64 freeList))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees)) :
    TerminatesWith env m 40 initial [.i64 root]
      (fun final values => values = [] ∧
        final.mem = (initial.mem.write64 (root - 40).toUInt32 0).write64 (root - 8).toUInt32 freeList ∧
        final.globals.globals =
          ((initial.globals.globals.set 4 (.i64 (releases + 1))).set 5
            (.i64 (frees + 1))).set 1 (.i64 root)) := by
  exact Project.Runtime.release_frees_fixed_array_zero_mask env m 40 initial root freeList releases frees
    input.size 1 (typeIdx := some 40)
    (by simpa [layout.noImports] using layout.release) (by simp [layout.noImports])
    (by have := hArray.1; omega) (by decide) hHeader.root48 hHeader.root32
    (by have := hArray.2.1; omega) hHeader.magic hHeader.refcount hHeader.kind
    hArray.lengthRead hHeader.stride hHeader.mask hFreeList hReleases hFrees

#print axioms release_owned_exact
end Project.EulerGridStep.Execution
