import Verified.Wasi.ReadSteps

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

def ReadReady (heap : Heap) (store : Store Unit) (root capacity : UInt64) : Prop :=
  (root = 0 ∧ capacity = 0) ∨
    ∃ previous, Bytes.Allocated heap store root previous ∧ capacity.toNat ≤ capacityAt store root

theorem ReadReady.address {heap : Heap} {store : Store Unit} {root capacity : UInt64}
    (h : ReadReady heap store root capacity) : root.toNat + capacity.toNat < 4294967296 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨previous, hBuffer, hCapacity⟩
  · decide
  · have := hBuffer.object.address
    omega

theorem ReadReady.memory {heap : Heap} {store : Store Unit} {root capacity : UInt64}
    (h : ReadReady heap store root capacity) (hHeap : heap.At store) :
    root.toNat + capacity.toNat ≤ store.mem.pages * 65536 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨previous, hBuffer, hCapacity⟩
  · change 0 ≤ _
    omega
  · have := hBuffer.object.below
    have := hHeap.top
    omega

theorem read_zero_frame {before after : Store World}
    (h : GuestFrame before after [ABI.scratch, (0, 0)]) :
    GuestFrame before after [ABI.scratch] := by
  refine ⟨h.resources, h.pages, ?_⟩
  intro address hOutside
  apply h.bytes
  intro region hRegion
  rcases List.mem_cons.mp hRegion with rfl | hRegion
  · exact hOutside ABI.scratch (List.mem_singleton_self _)
  · obtain rfl := List.mem_singleton.mp hRegion
    dsimp only [InRange]
    omega

theorem ReadReady.frame_step {World : Type} {initial before after : Store World}
    {heap0 heap : Heap} {root capacity : UInt64}
    (h : ReadReady heap (PureTransport.erase before) root capacity)
    (hBefore : Step heap0 (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase before) (Bytes.regions (PureTransport.erase before) root))
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity.toNat)]) :
    Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase after) (Bytes.regions (PureTransport.erase after) root) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨previous, hBuffer, hCapacity⟩
  · have hScratch := read_zero_frame hFrame
    simpa only [Bytes.regions, ite_true] using
      hBefore.trans (hScratch.scratchStep hBefore.at_)
        (fun _ hApart => ⟨hApart, fun _ => hApart⟩)
  · apply read_fresh_step _ hBuffer hCapacity hFrame
    simpa only [Bytes.regions, ite_eq_right hBuffer.nonzero] using hBefore

theorem ReadReady.reply_rep {World : Type} {host : Host World} {before after : Store World}
    {heap : Heap} {root capacity errno : UInt64} {committed : LeanExe.Bytes}
    (h : ReadReady heap (PureTransport.erase before) root capacity)
    (hHeap : heap.At (PureTransport.erase before))
    (hRead : host.read before.host capacity (.returned errno committed) after.host)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity.toNat)])
    (hData : errno = 0 → Bytes.At after.mem root committed) :
    Bytes.Rep heap (PureTransport.erase after) root
      (readResult errno committed).bytes.size (readResult errno committed).bytes := by
  rcases h with ⟨rfl, rfl⟩ | ⟨previous, hBuffer, hCapacity⟩
  · have hEmptyData := Host.read_zero hRead
    have hCommitted : committed = LeanExe.Bytes.empty := by
      cases committed with
      | mk data =>
        change data = ByteArray.empty at hEmptyData
        cases hEmptyData
        rfl
    rw [hCommitted]
    simpa only [readResult, LeanExe.Bytes.size_empty, ite_self] using
      Bytes.Rep.empty heap (PureTransport.erase after)
  · exact (read_buffer hBuffer hHeap hCapacity hRead hFrame hData).2.1.rep

end Verified.Wasi
