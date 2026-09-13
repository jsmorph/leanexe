import Project.EulerRiemann.OutputAppendData
import Project.EulerRiemann.WordAllocationBounds
import Project.EulerRiemann.HeapWordsFinish

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayCopy

theorem output_append_owned_spec (header : Bool) (env : HostEnv Unit)
    (initial : Store Unit) (heap : Heap) (frame : Locals)
    (source upper : FreeNode) (need : UInt64) (left right : Array UInt64)
    (hHeap : heap.At initial) (hLeft : heap.OwnsWords initial source left)
    (hRight : heap.OwnsWords initial upper right)
    (hNeed : 8 * (left.size + right.size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hCounter : frame.validIndex 44) (hValues : frame.values = [])
    (hSource : frame.get 36 = some (.i64 source.root))
    (hUpper : frame.get 37 = some (.i64 upper.root))
    (hTarget : frame.get 52 = some (.i64 (allocatedRoot heap.top need heap.nodes)))
    (hTotalCount : frame.get 40 = some (.i64 (UInt64.ofNat (left.size + right.size))))
    (hLeftCount : frame.get 41 = some (.i64 (UInt64.ofNat left.size)))
    (hRightCount : frame.get 42 = some (.i64 (UInt64.ofNat right.size)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final source left →
      (heap.allocate need).OwnsWords final upper right →
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes) (left ++ right) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need 1) final
        (allocatedRoot heap.top need heap.nodes).toNat
        ((allocatedRoot heap.top need heap.nodes).toNat + 8 * (left.size + right.size + 1)) →
      wp module rest Q final
        (counterFrame (resultFrame frame 43 (allocatedRoot heap.top need heap.nodes)) 44 right.size
          (by simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hCounter)) env) :
    wp module (outputAppendDataProgram header ++ rest) Q
      (heap.allocateArrayStore initial need 1) frame env := by
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun hNone => (hBump hNone).le
  have hBounds := heap.allocate_word_bounds initial need 1 (left.size + right.size) hHeap hNeed hFit
  apply output_append_data_spec header env _ frame source.root upper.root
    (allocatedRoot heap.top need heap.nodes) left right hParams hLocals hCounter hValues
    hSource hUpper hTarget hTotalCount hLeftCount hRightCount
    (hLeft.arrayAllocated need 1 hHeap hFit).buffer.values
    (hRight.arrayAllocated need 1 hHeap hFit).buffer.values hBounds.1 hBounds.2
    (hLeft.allocate_word_disjoint need _ hNeed hFit)
    (hRight.allocate_word_disjoint need _ hNeed hFit) Q rest
  intro final hWrites _ _ hResult
  have hFinished := heap.finishWords initial final need (left ++ right) hHeap
    (by simpa only [Array.size_append] using hNeed) hBump
    (by simpa only [Array.size_append] using hWrites) hResult
  exact hNext final hFinished.1
    (hLeft.arrayWritten need 1 _ hHeap hNeed hFit hWrites)
    (hRight.arrayWritten need 1 _ hHeap hNeed hFit hWrites) hFinished.2 hWrites

#print axioms output_append_owned_spec

end Project.EulerRiemann.Execution
