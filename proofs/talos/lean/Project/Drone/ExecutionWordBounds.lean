import Project.Drone.ExecutionPreserveWords

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.EulerRiemann.Execution

theorem borrowed_root_ne_zero {heap : Heap} {store : Store Unit} {node : FreeNode} {words : Array UInt64}
    (h : BorrowedWords heap store node words) : node.root ≠ 0 := by
  intro hz
  have hb := h.rootBound
  rw [hz] at hb
  contradiction

theorem owned_root_ne_zero {heap : Heap} {store : Store Unit} {node : FreeNode} {words : Array UInt64}
    (h : heap.OwnsWords store node words) : node.root ≠ 0 :=
  borrowed_root_ne_zero (borrow_owned h)

#print axioms owned_root_ne_zero
end Project.Drone.Execution
