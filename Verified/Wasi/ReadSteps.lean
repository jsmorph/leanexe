import Verified.Wasi.ReadBuffer
import Verified.Bytes.Release

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem read_fresh_step {World : Type} {initial before after : Store World}
    {heap0 heap : Heap} {root : UInt64} {capacity : Nat} {previous : LeanExe.Bytes}
    (hAllocate : Step heap0 (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase before) [block (PureTransport.erase before) root])
    (hBuffer : Heap.Buffer heap (PureTransport.erase before) root previous)
    (hCapacity : capacity ≤ capacityAt (PureTransport.erase before) root)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity)]) :
    Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase after) (Bytes.regions (PureTransport.erase after) root) := by
  have hRead := hFrame.readStep hAllocate.at_ (read_payload_region hBuffer hCapacity)
  have hBoth := hAllocate.transBoth hRead
    (keep := fun region => regionsDisjoint region ABI.scratch) (by
      intro region hScratch
      refine ⟨hScratch, fun hApart => ⟨hScratch, ?_⟩⟩
      have hBlock := hApart _ (List.mem_singleton_self _)
      have hBase := hBuffer.object.base
      simp only [regionsDisjoint, block] at hBlock ⊢
      omega)
  have hCapacityEq := read_capacity hBuffer hFrame
  simpa only [Bytes.regions, ite_eq_right hBuffer.nonzero,
    block_eq hCapacityEq, List.append_nil] using hBoth

theorem read_discard_step {World : Type} {initial before after : Store World}
    {heap0 heap : Heap} {root length : UInt64} {bytes : LeanExe.Bytes}
    (hBefore : Step heap0 (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase before) (Bytes.regions (PureTransport.erase before) root))
    (hBytes : Bytes.Rep heap (PureTransport.erase before) root length bytes)
    (hAfter : PureTransport.erase after =
      Bytes.releasedStore heap (PureTransport.erase before) root) :
    Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
      (Bytes.releasedHeap heap (PureTransport.erase before) root)
      (PureTransport.erase after) [] := by
  rw [hAfter]
  exact hBefore.trans (hBytes.release_step hBefore.at_).1
    (fun _ hScratch => ⟨hScratch, fun hApart => hApart⟩)

theorem read_discard_top {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (hHeap : heap.At store) (hBytes : Bytes.Rep heap store root length bytes) :
    (Bytes.releasedHeap heap store root).top = heap.top :=
  (hBytes.release_step hHeap).2

end Verified.Wasi
