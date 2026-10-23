import Verified.Wasi.HostSpec
import Verified.Wasi.PureTransport
import Verified.HeapStep
import Verified.Bytes.Step
import LeanExe.Pipeline.Records

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem GuestFrame.weaken {before after : Store World}
    {first second : List (Nat × Nat)} (h : GuestFrame before after first)
    (hSubset : ∀ region ∈ first, region ∈ second) : GuestFrame before after second :=
  ⟨h.resources, h.pages, fun address hOutside =>
    h.bytes address fun region hRegion => hOutside region (hSubset region hRegion)⟩

theorem GuestFrame.heap {before after : Store World} {writable : List (Nat × Nat)}
    {heap : Heap} (h : GuestFrame before after writable)
    (hHeap : heap.At (PureTransport.erase before))
    (hSeparate : ∀ node ∈ heap.free, ∀ region ∈ writable,
      regionsDisjoint node.region region) : heap.At (PureTransport.erase after) := by
  refine ⟨by change after.globals.globals = heap.globals; rw [h.globals]; exact hHeap.globals,
    ?_, hHeap.base,
    by change heap.top.toNat ≤ after.mem.pages * 65536; rw [h.pages]; exact hHeap.top,
    by change after.mem.pages ≤ 65535; rw [h.pages]; exact hHeap.pages,
    hHeap.above, hHeap.below⟩
  apply FreeListMemory.frame_headers hHeap.freeList
    (by change before.mem.pages ≤ after.mem.pages; rw [h.pages])
  intro node hNode address hLow hHigh
  apply h.bytes
  intro region hRegion
  have hApart := hSeparate node hNode region hRegion
  have hBase := hHeap.above node hNode
  dsimp only [regionsDisjoint, FreeNode.region, InRange] at hApart ⊢
  omega

theorem GuestFrame.step {before after : Store World} {writable : List (Nat × Nat)}
    {heap : Heap} (h : GuestFrame before after writable)
    (hHeap : heap.At (PureTransport.erase before))
    (hSeparate : ∀ node ∈ heap.free, ∀ region ∈ writable,
      regionsDisjoint node.region region) :
    Step heap (PureTransport.erase before)
      (fun kept => ∀ region ∈ writable, regionsDisjoint kept region)
      heap (PureTransport.erase after) [] := by
  refine ⟨h.heap hHeap hSeparate, h.memoryCaps, ?_⟩
  intro kept hRegion _ hKeep
  refine ⟨?_, hRegion, nofun⟩
  intro address hLow hHigh
  apply h.bytes
  intro region hRegion
  have hApart := hKeep region hRegion
  dsimp only [regionsDisjoint, InRange] at hApart ⊢
  omega

theorem GuestFrame.trans {initial middle final : Store World} {writable : List (Nat × Nat)}
    (first : GuestFrame initial middle writable) (second : GuestFrame middle final writable) :
    GuestFrame initial final writable := by
  refine ⟨?_, second.pages.trans first.pages, ?_⟩
  · calc
      final.mapHost (fun _ => ()) = { middle.mapHost (fun _ => ()) with mem := final.mem } :=
        second.resources
      _ = { initial.mapHost (fun _ => ()) with mem := final.mem } := by rw [first.resources]
  · intro address hOutside
    exact (second.bytes address hOutside).trans (first.bytes address hOutside)

theorem GuestFrame.ofScratchWrites {before after : Store World}
    (h : Memory.WritesRange before after 0 16) : GuestFrame before after [ABI.scratch] := by
  refine ⟨congrArg (fun store : Store World => store.mapHost (fun _ => ())) h.1, h.2.1, ?_⟩
  intro address hOutside
  apply h.2.2
  right
  have hScratch := hOutside ABI.scratch (List.mem_singleton_self _)
  dsimp only [ABI.scratch, InRange] at hScratch
  omega

theorem GuestFrame.scratchWrites {before after : Store World}
    (h : GuestFrame before after [ABI.scratch]) :
    Memory.WritesRange (PureTransport.erase before) (PureTransport.erase after) 0 16 := by
  refine ⟨h.resources, h.pages, ?_⟩
  intro address hOutside
  exact h.bytes address fun region hRegion => by
    obtain rfl := List.mem_singleton.mp hRegion
    dsimp only [InRange, ABI.scratch]
    omega

theorem GuestFrame.scratchHeap {before after : Store World} {heap : Heap}
    (h : GuestFrame before after [ABI.scratch]) (hHeap : heap.At (PureTransport.erase before)) :
    heap.At (PureTransport.erase after) := by
  refine hHeap.writesApart h.scratchWrites ?_
  intro node hNode
  have hBase := hHeap.above node hNode
  right
  dsimp only [FreeNode.region]
  omega

theorem GuestFrame.scratchStep {before after : Store World} {heap : Heap}
    (h : GuestFrame before after [ABI.scratch]) (hHeap : heap.At (PureTransport.erase before)) :
    Step heap (PureTransport.erase before) (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase after) [] :=
  Step.ofWritesRange (h.scratchHeap hHeap) h.scratchWrites (by decide) (by decide)

theorem GuestFrame.scratchRep {before after : Store World} {heap : Heap}
    {root length : UInt64} {bytes : LeanExe.Bytes}
    (h : GuestFrame before after [ABI.scratch]) (hHeap : heap.At (PureTransport.erase before))
    (hRep : Bytes.Rep heap (PureTransport.erase before) root length bytes) :
    Bytes.Rep heap (PureTransport.erase after) root length bytes := by
  refine (hRep.step (h.scratchStep hHeap) ?_).1
  intro region hRegion
  rcases hRep.buffer with hNull | hBuffer
  · obtain ⟨rfl, _⟩ := hNull
    simp [Bytes.regions] at hRegion
  · simp only [Bytes.regions, ite_eq_right hBuffer.nonzero, List.mem_singleton] at hRegion
    subst region
    have hBase := hBuffer.object.base
    right
    dsimp only [ABI.scratch, block]
    omega

end Verified.Wasi
