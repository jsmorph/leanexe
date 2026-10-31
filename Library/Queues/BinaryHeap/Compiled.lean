import Library.Queues.BinaryHeap.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of the binary heap.  The compiler unfolds `step` into the loop of
`heapQueue`, whose state owns the outputs and the heap's array, so each insertion and removal
changes the arrays in place, and the generated bound counts only their growth.  `heapQueue_callSpec`
composes the generated `compiled.heapQueue.trapFree` with `heapQueue_eq`. -/

namespace Library.Queues.BinaryHeap

open Wasm LeanExe.Pipeline Library.Sorting.Heapsort

verified_compile compiled := [swap, siftDown, siftUp, heapQueue]

theorem heapQueue_export :
    ({ name := "heapQueue", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- From a ready store with room for `compiled.heapQueue.bound xs` bytes, function 5, the export
`heapQueue`, returns without a trap the owned array `expected xs`, the outputs of the operations,
and leaves a ready store. -/
theorem heapQueue_callSpec :
    Verified.CallSpec compiled.module compiled.tables 5 expected compiled.heapQueue.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.heapQueue.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, hxs⟩ => heapQueue_eq x (show _ < 2 ^ 64 from hxs.values.size_lt)

#print axioms heapQueue_callSpec

end Library.Queues.BinaryHeap
