import Project.LebU32.LoopState

namespace Project.LebU32.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem RunningStorage.bump_bounds {seed : Heap} {initial current : Store Unit} {count : Nat}
    {bytes : ByteArray} (h : RunningStorage seed initial current count bytes)
    (hCount : count ≤ 4) (hFit : seed.top.toNat + 112 < 4294967296)
    (hMemory : seed.top.toNat + 112 ≤ initial.mem.pages * 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap «module» 0) :
    takeFirstFitFrom 0 (PackedPush.need bytes) (runningHeap seed count).nodes = none →
      (runningHeap seed count).top.toNat + 48 + (PackedPush.need bytes).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages (runningHeap seed count).top (PackedPush.need bytes) ≤ current.memoryCap «module» 0 := by
  rw [byte_push_need bytes (by rw [h.size]; omega)]
  intro hNone
  have hBound := running_bump_bound seed count hFit hNone
  refine ⟨by change (runningHeap seed count).top.toNat + 48 + 8 < 4294967296; omega, ?_⟩
  rw [h.cap]
  apply Nat.le_trans _ hCap
  change ((runningHeap seed count).top.toNat + 48 + 8 - 1) / 65536 + 1 ≤ initial.mem.pages
  omega

theorem running_allocation_root (seed : Heap) (count : Nat) (bytes : ByteArray)
    (hCount : count ≤ 4) (hSize : bytes.size = count) :
    allocatedRoot (runningHeap seed count).top (PackedPush.need bytes) (runningHeap seed count).nodes =
      (byteNode seed count).root := by
  rw [byte_push_need bytes (by omega)]
  exact congrArg FreeNode.root (running_allocate_node seed count hCount)

#print axioms RunningStorage.bump_bounds
end Project.LebU32.Spec
