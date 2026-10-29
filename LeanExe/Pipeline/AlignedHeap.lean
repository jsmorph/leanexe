import LeanExe.Pipeline.RuntimeSpec
import LeanExe.ProofKit.AlignedExec

/-!
Alignment of the allocator's state.  `Heap.Aligned heap` states that `top` and the root and
capacity of every free block are multiples of 8.  `alloc` requests `allocSize bytes`, a multiple
of 8, so the block it returns has an aligned payload pointer, and the heap after the allocation is
aligned again.  The arithmetic is in `UInt64`, whose modulus `2 ^ 64` is a multiple of 8, so the
residues modulo 8 hold whether or not a sum wraps.
-/

namespace LeanExe.Pipeline

open Wasm LeanExe.Runtime LeanExe.ProofKit

/-- `top` and the root and capacity of every free block are multiples of 8. -/
structure Heap.Aligned (heap : Heap) : Prop where
  top : heap.top.toNat % 8 = 0
  roots : ∀ node ∈ heap.free, node.root.toNat % 8 = 0
  capacities : ∀ node ∈ heap.free, node.capacity.toNat % 8 = 0

theorem allocSize_mod8 (bytes : UInt64) : (allocSize bytes).toNat % 8 = 0 := by
  unfold allocSize
  split
  · rfl
  · simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.reduceToNat]
    omega

/-- The payload pointer that allocation returns is a multiple of 8. -/
theorem Heap.Aligned.root {heap : Heap} {need : UInt64} (ha : heap.Aligned)
    (hn : need.toNat % 8 = 0) :
    (FixedArrayAllocate.root heap.top need heap.free).toNat % 8 = 0 := by
  unfold FixedArrayAllocate.root
  split
  · rename_i choice hTake
    have hMem := takeFirstFitFrom_some_mem hTake
    have hr := ha.roots _ hMem
    have hc := ha.capacities _ hMem
    unfold reuseRoot
    split
    · exact UInt64.sub_mod8 (UInt64.add_mod8 hr hc) hn
    · exact hr
  · exact UInt64.add_mod8 ha.top rfl

/-- The capacity of the block that allocation of a multiple of 8 bytes returns is a multiple of
8. -/
theorem Heap.Aligned.capacity_alloc {heap : Heap} {need : UInt64} (ha : heap.Aligned)
    (hn : need.toNat % 8 = 0) : (allocatedCapacity need heap.free).toNat % 8 = 0 := by
  unfold allocatedCapacity
  split
  · rename_i choice hTake
    split
    · exact hn
    · exact ha.capacities _ (takeFirstFitFrom_some_mem hTake)
  · exact hn

/-- Allocation of a multiple of 8 bytes keeps the heap aligned. -/
theorem Heap.Aligned.allocate {heap : Heap} {need : UInt64} (ha : heap.Aligned)
    (hn : need.toNat % 8 = 0) : (heap.allocate need).Aligned := by
  have hBoth : ∀ node ∈ allocatedNodes need heap.free,
      node.root.toNat % 8 = 0 ∧ node.capacity.toNat % 8 = 0 := by
    intro node hNode
    unfold allocatedNodes at hNode
    split at hNode
    · rename_i choice hTake
      split at hNode
      · obtain ⟨skipped, tail, hNodes, hShrink⟩ := shrinkFirstFit_decompose hTake
        rw [hShrink] at hNode
        rcases List.mem_append.mp hNode with hSkipped | hRest
        · have hm : node ∈ heap.free := by rw [hNodes]; exact List.mem_append_left _ hSkipped
          exact ⟨ha.roots _ hm, ha.capacities _ hm⟩
        · rcases List.mem_cons.mp hRest with rfl | hTail
          · have hm := takeFirstFitFrom_some_mem hTake
            exact ⟨ha.roots choice.node hm,
              UInt64.sub_mod8 (UInt64.sub_mod8 (ha.capacities _ hm) hn) rfl⟩
          · have hm : node ∈ heap.free := by
              rw [hNodes]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hTail)
            exact ⟨ha.roots _ hm, ha.capacities _ hm⟩
      · have hm := takeFirstFitFrom_some_remaining_mem hTake hNode
        exact ⟨ha.roots _ hm, ha.capacities _ hm⟩
    · exact ⟨ha.roots _ hNode, ha.capacities _ hNode⟩
  refine ⟨?_, fun node h => (hBoth node h).1, fun node h => (hBoth node h).2⟩
  show (allocatedTop heap.top need heap.free).toNat % 8 = 0
  unfold allocatedTop
  split
  · exact ha.top
  · exact UInt64.add_mod8 (UInt64.add_mod8 ha.top rfl) hn

/-- The block that `alloc` returns for a request of `bytes` bytes has an aligned payload
pointer, and the heap after it is aligned. -/
theorem Heap.Aligned.alloc {heap : Heap} (ha : heap.Aligned) (bytes : UInt64) :
    (FixedArrayAllocate.root heap.top (allocSize bytes) heap.free).toNat % 8 = 0 ∧
      (heap.allocate (allocSize bytes)).Aligned :=
  ⟨ha.root (allocSize_mod8 bytes), ha.allocate (allocSize_mod8 bytes)⟩

/-- The address of word `i` of an array, after its length word, is aligned when the array's
address is. -/
theorem elementAddress_mod8 {p : UInt64} (hp : p.toNat % 8 = 0) (i : Nat) :
    (p + UInt64.ofNat (8 * (i + 1))).toUInt32.toNat % 8 = 0 := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

end LeanExe.Pipeline
