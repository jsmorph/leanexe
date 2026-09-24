import Project.ClobDepth.Func3Heap
import Project.ClobDepth.Release
import Project.ClobDepth.Func6Fold

namespace Project.ClobDepth.FoldHeap
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation Project.ClobDepth.HeapProof
  Project.ClobDepth.Func6Fold Project.EulerRiemann.Execution

/-- A new result may be released without changing any region live on entry. -/
def Born (initial : Heap) (node : FreeNode) : Prop :=
  ∀ lo hi, initial.Protects lo hi →
    hi ≤ node.root.toNat - 48 ∨ node.root.toNat + node.capacity.toNat ≤ lo

structure State (initial : Heap) (st0 : Store Unit) (os : List OrderL)
    (side saved : UInt64) (heap : Heap) (st : Store Unit)
    (node : FreeNode) (owner : UInt64) (k : Nat) : Prop where
  heapAt : heap.At st
  pages : st.mem.pages = st0.mem.pages
  frame : initial.Frame st0 heap st
  owned : OwnsLevels heap st node (foldLevels os side k)
  born : Born initial node
  owner : owner = saved ∨ owner = node.root
  allocations : heap.allocations = initial.allocations + 2 + UInt64.ofNat (matchCount os side k)
  retains : heap.retains = initial.retains
  top : heap.top.toNat ≤ initial.top.toNat + 112 + k * stepBytes os.length

theorem allocate_top_le (heap : Heap) (need : UInt64)
    (hFit : heap.top.toNat + 48 + need.toNat < 4294967296) :
    (heap.allocate need).top.toNat ≤ heap.top.toNat + 48 + need.toNat := by
  change (allocatedTop heap.top need heap.nodes).toNat ≤ _
  rw [allocatedTop_toNat _ _ _ (fun _ => hFit.le)]
  split <;> omega

theorem capacity_le (levels : List LevelL) (price qty : UInt64)
    (hLength : levels.length < 4294967296) :
    (Func3.capacity levels price qty).toNat ≤ fixedArrayBytes (levels.length+1) 2 := by
  have hLen := addLevelL_length_le levels price qty
  unfold Func3.capacity
  rw [fixedArrayBytesU_toNat _ 2 (by rw [size_eq]; omega) (by decide)
    (by unfold fixedArrayBytes; rw [size_eq]; omega)]
  unfold fixedArrayBytes
  omega

theorem State.skip {initial heap : Heap} {st0 st : Store Unit} {os : List OrderL}
    {side saved owner : UInt64} {node : FreeNode} {k : Nat}
    (h : State initial st0 os side saved heap st node owner k)
    (hk : k < os.length) (hSide : os[k]!.oside ≠ side) :
    State initial st0 os side saved heap st node owner (k+1) := by
  refine ⟨h.heapAt, h.pages, h.frame, ?_, h.born, h.owner, ?_, h.retains, ?_⟩
  · simpa only [foldLevels_succ os side k hk, if_neg hSide] using h.owned
  · simpa only [matchCount_succ os side k hk, if_neg hSide, Nat.add_zero] using h.allocations
  · have := h.top
    have := Nat.mul_le_mul_right (stepBytes os.length) (show k ≤ k+1 by omega)
    omega

theorem State.update {initial heap : Heap} {st0 st st1 : Store Unit} {os : List OrderL}
    {side saved owner : UInt64} {node : FreeNode} {k : Nat}
    (h : State initial st0 os side saved heap st node owner k)
    (hk : k < os.length) (hSide : os[k]!.oside = side)
    (hBudget32 : initial.top.toNat + 112 + os.length * stepBytes os.length < 4294967296)
    (hUpdate : AllocatedResult st heap
      (Func3.capacity (foldLevels os side k) os[k]!.oprice os[k]!.oqty) st1
      (addLevelL (foldLevels os side k) os[k]!.oprice os[k]!.oqty)) :
    let need := Func3.capacity (foldLevels os side k) os[k]!.oprice os[k]!.oqty
    let fresh := allocatedNode heap.top need heap.nodes
    let nextHeap := heap.allocate need
    State initial st0 os side saved
      (if owner = saved then nextHeap else nextHeap.release node)
      (if owner = saved then st1 else nextHeap.releaseStore st1 node)
      fresh fresh.root (k+1) := by
  dsimp only
  let levels := foldLevels os side k
  let need := Func3.capacity levels os[k]!.oprice os[k]!.oqty
  let fresh := allocatedNode heap.top need heap.nodes
  have hLen := (foldLevels_length_le os side k (by omega)).trans (matchCount_le os side k)
  change levels.length ≤ k at hLen
  have hCount : os.length < 4294967296 := by
    unfold stepBytes at hBudget32
    nlinarith
  have hLen' := addLevelL_length_le levels os[k]!.oprice os[k]!.oqty
  have hNeed : need.toNat = fixedArrayBytes
      (addLevelL levels os[k]!.oprice os[k]!.oqty).length 2 := by
    apply fixedArrayBytesU_toNat
    · rw [size_eq]; omega
    · decide
    · unfold fixedArrayBytes; rw [size_eq]
      have := h.top
      unfold stepBytes at hBudget32
      have : os.length ≤ os.length * (56 + 16 * os.length) := by nlinarith
      omega
  have hNeedLe : 48 + need.toNat ≤ stepBytes os.length := by
    rw [hNeed]
    unfold fixedArrayBytes stepBytes
    omega
  have hTop := h.top
  have hMul : (k+1)*stepBytes os.length ≤ os.length*stepBytes os.length :=
    Nat.mul_le_mul_right _ (by omega)
  have hFit : heap.top.toNat + 48 + need.toNat < 4294967296 := by
    rw [Nat.succ_mul] at hMul
    omega
  have hTopNext := allocate_top_le heap need hFit
  have hFrame := h.frame.trans hUpdate.frame
  have hBorn : Born initial fresh := by
    intro lo hi hProtected
    exact (h.frame.protects lo hi hProtected).allocated_disjoint need (fun _ => hFit.le)
  have hOwned : OwnsLevels (heap.allocate need) st1 fresh (foldLevels os side (k+1)) := by
    simpa only [foldLevels_succ os side k hk, if_pos hSide] using hUpdate.owned
  have hSep := allocated_region_disjoint heap.top need node heap.nodes h.owned.buffer.rootBound
    h.owned.separated h.owned.below (fun _ => hFit.le)
  have hOld := h.owned.frame hUpdate.frame hUpdate.pages hUpdate.heapAt
  have hTopBound : (heap.allocate need).top.toNat ≤
      initial.top.toNat + 112 + (k+1)*stepBytes os.length := by
    rw [Nat.succ_mul]; omega
  have hAllocations : (heap.allocate need).allocations =
      initial.allocations + 2 + UInt64.ofNat (matchCount os side (k+1)) := by
    simp only [Heap.allocate, h.allocations, matchCount_succ os side k hk, if_pos hSide,
      UInt64.ofNat_add, UInt64.add_assoc]
    rfl
  by_cases hSaved : owner = saved
  · simp only [if_pos hSaved]
    exact ⟨hUpdate.heapAt, hUpdate.pages.trans h.pages, hFrame, hOwned,
      hBorn, Or.inr rfl, hAllocations, h.retains, hTopBound⟩
  · simp only [if_neg hSaved]
    refine ⟨release_heap st1 (heap.allocate need) node levels hUpdate.heapAt hOld,
      hUpdate.pages.trans h.pages,
      hFrame.released node hOld.buffer.rootBound (by have := hOld.buffer.addressBound; omega) h.born,
      hOwned.released node hOld.buffer.rootBound (by have := hOld.buffer.addressBound; omega) (by
        unfold regionsDisjoint at hSep ⊢
        exact hSep.symm),
      hBorn, Or.inr rfl, hAllocations, h.retains, hTopBound⟩

#print axioms State.update
end Project.ClobDepth.FoldHeap
