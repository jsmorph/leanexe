import Project.ClobDepth.Program
import Project.ClobDepth.Representation
import Project.EulerRiemann.HeapFrame
import Project.ProofKit.FixedArrayRelease
import Project.ProofKit.FixedArrayInMemory

/-! The depth fold uses the shared free-list heap model.  Its buffers have
stride two; the heap's allocation and separation laws are stride independent. -/
namespace Project.ClobDepth.HeapProof
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.EulerRiemann.Execution

structure LevelBuffer (store : Store Unit) (node : FreeNode)
    (levels : List LevelL) : Prop where
  rootBound : 48 ≤ node.root.toNat
  capacity : fixedArrayBytes levels.length 2 ≤ node.capacity.toNat
  addressBound : node.root.toNat + node.capacity.toNat < 4294967296
  memoryBound : node.root.toNat + node.capacity.toNat ≤ store.mem.pages * 65536
  contents : OwnedLevelArrayAt store node.root node.capacity levels

structure OwnsLevels (heap : Heap) (store : Store Unit) (node : FreeNode)
    (levels : List LevelL) : Prop where
  buffer : LevelBuffer store node levels
  below : node.root.toNat + node.capacity.toNat ≤ heap.top.toNat
  separated : ∀ other ∈ heap.nodes, regionsDisjoint node.region other.region

theorem LevelBuffer.frame {initial final : Store Unit} {node : FreeNode}
    {levels : List LevelL} (h : LevelBuffer initial node levels)
    (hPages : final.mem.pages = initial.mem.pages)
    (hBytes : ∀ a, node.root.toNat - 48 ≤ a →
      a < node.root.toNat + node.capacity.toNat → final.mem.bytes a = initial.mem.bytes a) :
    LevelBuffer final node levels := by
  refine ⟨h.rootBound, h.capacity, h.addressBound, ?_, ?_⟩
  · rw [hPages]; exact h.memoryBound
  · exact h.contents.frame_region (by have := h.capacity; have := h.addressBound; omega)
      h.rootBound h.capacity hPages hBytes

theorem OwnsLevels.protects {heap : Heap} {store : Store Unit} {node : FreeNode}
    {levels : List LevelL} (h : OwnsLevels heap store node levels) :
    heap.Protects (node.root.toNat - 48) (node.root.toNat + node.capacity.toNat) := by
  refine ⟨h.below, ?_⟩
  intro other hOther
  have hSep := h.separated other hOther
  have hRoot := h.buffer.rootBound
  simp only [regionsDisjoint, FreeNode.region] at hSep
  omega

theorem OwnsLevels.frame {before after : Heap} {initial final : Store Unit}
    {node : FreeNode} {levels : List LevelL}
    (h : OwnsLevels before initial node levels) (hFrame : before.Frame initial after final)
    (hPages : final.mem.pages = initial.mem.pages) (hHeap : after.At final) :
    OwnsLevels after final node levels := by
  have hProtected := hFrame.protects _ _ h.protects
  refine ⟨h.buffer.frame hPages (hFrame.bytes _ _ h.protects), hProtected.below, ?_⟩
  intro other hOther
  have hSep := hProtected.separated other hOther
  have hRoot := h.buffer.rootBound
  have hOther := (hHeap.freeList.mem_bounds hOther).1
  simp only [regionsDisjoint, FreeNode.region]
  omega

/-- Data writes preserve free-list headers when the destination is separated
from every free chunk.  This weaker memory frame composes with the existing
level-copy proofs, which expose pages, globals, and bytes separately. -/
theorem heap_written {heap : Heap} {initial final : Store Unit} {node : FreeNode}
    (hHeap : heap.At initial)
    (hPages : final.mem.pages = initial.mem.pages)
    (hGlobals : final.globals.globals = initial.globals.globals)
    (hRoot : 48 ≤ node.root.toNat)
    (hSep : ∀ other ∈ heap.nodes, regionsDisjoint node.region other.region)
    (hBytes : ∀ a, a < node.root.toNat ∨ node.root.toNat + node.capacity.toNat ≤ a →
      final.mem.bytes a = initial.mem.bytes a) : heap.At final := by
  refine ⟨hGlobals.trans hHeap.globals, ?_, hHeap.below⟩
  apply FreeListMemory.frame_headers hHeap.freeList (by rw [hPages])
  intro other hOther a hLow hHigh
  have hSeparated := hSep other hOther
  have hOtherRoot := (hHeap.freeList.mem_bounds hOther).1
  simp only [regionsDisjoint, FreeNode.region] at hSeparated
  exact hBytes a (by omega)

theorem allocated_pages_eq (heap : Heap) (store : Store Unit) (need stride : UInt64)
    (hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ store.mem.pages * 65536) :
    (heap.allocateArrayStore store need stride).mem.pages = store.mem.pages := by
  exact Nat.le_antisymm (heap.allocateArrayStore_pages_bound store need stride
    store.mem.pages (Nat.le_refl _) hFit) (heap.allocateArrayStore_pages_ge store need stride)

theorem allocation_program (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (need stride previous current capacity next result : UInt64)
    (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 ∧
      heap.top.toNat + 48 + need.toNat ≤ store.mem.pages * 65536)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp Project.ClobDepth.module rest Q (heap.allocateArrayStore store need stride)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (allocatedRoot heap.top need heap.nodes)) env) :
    wp Project.ClobDepth.module (FixedArrayAllocate.program start stride ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  apply FixedArrayAllocate.program_in_memory Project.ClobDepth.module env store params saved tail
    start hStart heap.top need stride previous current capacity next result heap.allocations heap.nodes
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals]) hHeap.freeList hBump hPages rfl
  intro previous current capacity next
  simpa only [Heap.allocateArrayStore, allocatedRoot_shared] using hNext previous current capacity next

#print axioms LevelBuffer.frame
#print axioms OwnsLevels.frame
#print axioms heap_written
#print axioms allocation_program
end Project.ClobDepth.HeapProof
