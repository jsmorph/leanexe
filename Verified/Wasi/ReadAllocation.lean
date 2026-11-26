module

public import Verified.Wasi.ReadCode
public import Verified.LocalFrame
public import Verified.Wasi.RuntimeFrame

@[expose] public section

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem read_allocation_buffer {before after : Store World} {heap : Heap} {capacity : UInt64}
    (hHeap : heap.At (PureTransport.erase before))
    (hCount : capacity.toNat ≤ 4294967296) (hFits : heap.Fits (allocSize capacity))
    (hStore : PureTransport.erase after =
      heap.allocateStore (PureTransport.erase before) (allocSize capacity) 1) :
    let heap' := heap.allocate (allocSize capacity)
    let root := FixedArrayAllocate.root heap.top (allocSize capacity) heap.free
    Step heap (PureTransport.erase before) (fun _ => True)
        heap' (PureTransport.erase after) [block (PureTransport.erase after) root] ∧
      Heap.Buffer heap' (PureTransport.erase after) root
        (Bytes.snapshot (PureTransport.erase after) root capacity.toNat) ∧
      capacity.toNat ≤ capacityAt (PureTransport.erase after) root ∧
      heap'.top.toNat ≤ heap.top.toNat + allocCost (allocSize capacity).toNat := by
  dsimp only
  rw [hStore]
  have hBlock := hHeap.allocate_block 1 hFits
  have hCapacity := allocated_capacity (allocSize capacity) heap.free
  have hMinimum := Bytes.allocSize_minimum capacity
  have hCount' := le_allocSize hCount
  refine ⟨Step.allocate 1 hHeap hFits, Bytes.block_snapshot hBlock (by omega) _ (by omega),
    ?_, Heap.allocate_top hFits⟩
  rw [hBlock.capacity_eq]
  omega

end Verified.Wasi
