import LeanExe.Pipeline.RuntimeSpec
import LeanExe.ProofKit.AlignedExec

/-!
Alignment of the allocator's state.  `Heap.Aligned heap` states that `top` and the root and
capacity of every free block are multiples of 8.  `alloc` requests `allocSize bytes`, a multiple
of 8, so the block it returns has an aligned payload pointer, and the heap after the allocation is
aligned again.  Releasing a block whose root and capacity are multiples of 8 keeps the heap
aligned, since the merges of `insertFree` add capacities and the 48 bytes of a header.  The
arithmetic is in `UInt64`, whose modulus `2 ^ 64` is a multiple of 8, so the
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

/-- The blocks of `joinNodes block rest` have roots and capacities that are multiples of 8 when
`block` and the blocks of `rest` do: a merge adds the capacities and the 48 bytes of a header. -/
theorem joinNodes_aligned {block : FreeNode} (hRoot : block.root.toNat % 8 = 0)
    (hCap : block.capacity.toNat % 8 = 0) :
    ∀ {rest : List FreeNode}, (∀ n ∈ rest, n.root.toNat % 8 = 0 ∧ n.capacity.toNat % 8 = 0) →
      ∀ n ∈ joinNodes block rest, n.root.toNat % 8 = 0 ∧ n.capacity.toNat % 8 = 0
  | [], _, n, hn => by
    simp only [joinNodes, List.mem_singleton] at hn
    subst hn
    exact ⟨hRoot, hCap⟩
  | next :: rest, hr, n, hn => by
    simp only [joinNodes] at hn
    split at hn
    · rcases List.mem_cons.mp hn with rfl | hn
      · exact ⟨hRoot, UInt64.add_mod8 (UInt64.add_mod8 hCap rfl) (hr next List.mem_cons_self).2⟩
      · exact hr n (List.mem_cons_of_mem _ hn)
    · rcases List.mem_cons.mp hn with rfl | hn
      · exact ⟨hRoot, hCap⟩
      · exact hr n hn

theorem insertFree_aligned {root capacity : UInt64} {nodes : List FreeNode}
    (hRoot : root.toNat % 8 = 0) (hCap : capacity.toNat % 8 = 0)
    (h : ∀ n ∈ nodes, n.root.toNat % 8 = 0 ∧ n.capacity.toNat % 8 = 0) :
    ∀ n ∈ insertFree root capacity nodes, n.root.toNat % 8 = 0 ∧ n.capacity.toNat % 8 = 0 := by
  have hSplit := nodes_split root nodes
  have hBelow : ∀ n ∈ belowNodes root nodes, n.root.toNat % 8 = 0 ∧ n.capacity.toNat % 8 = 0 :=
    fun n hn => h n (by rw [hSplit]; exact List.mem_append_left _ hn)
  have hAbove : ∀ n ∈ aboveNodes root nodes, n.root.toNat % 8 = 0 ∧ n.capacity.toNat % 8 = 0 :=
    fun n hn => h n (by rw [hSplit]; exact List.mem_append_right _ hn)
  unfold insertFree
  split
  · exact joinNodes_aligned (block := { root, capacity }) hRoot hCap hAbove
  · rename_i p hp
    have hpAl := hBelow p (List.mem_of_getLast? hp)
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact hBelow n ((List.dropLast_sublist _).subset hn)
    · exact joinNodes_aligned hpAl.1 hpAl.2
        (joinNodes_aligned (block := { root, capacity }) hRoot hCap hAbove) n hn

/-- Releasing a block whose root and capacity are multiples of 8 keeps the heap aligned. -/
theorem Heap.Aligned.release {heap : Heap} {ptr capacity : UInt64} (ha : heap.Aligned)
    (hp : ptr.toNat % 8 = 0) (hc : capacity.toNat % 8 = 0) :
    (heap.release ptr capacity).Aligned := by
  have h := insertFree_aligned hp hc fun n hn => ⟨ha.roots n hn, ha.capacities n hn⟩
  exact ⟨ha.top, fun n hn => (h n hn).1, fun n hn => (h n hn).2⟩

end LeanExe.Pipeline
