import Project.ClobMatchFuel.MemoryFrame

namespace Project.ClobMatchFuel.MemoryBelow
open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.AllocatorFrame

def BytesEqBelow (before after : Mem) (limit : Nat) : Prop :=
  ∀ a, a < limit → after.bytes a = before.bytes a

theorem BytesEqBelow.refl (mem : Mem) (limit : Nat) :
    BytesEqBelow mem mem limit := fun _ _ => rfl

theorem BytesEqBelow.trans (first : BytesEqBelow a b limit)
    (second : BytesEqBelow b c limit) : BytesEqBelow a c limit :=
  fun address hAddress => (second address hAddress).trans (first address hAddress)

theorem BytesEqBelow.of_outsideFlatWords
    {before after : Store Unit} {ptr : UInt64} {words limit : Nat}
    (hStart : limit ≤ ptr.toNat)
    (hOutside : MemEqOutsideFlatWords before after ptr words) :
    BytesEqBelow before.mem after.mem limit :=
  fun a ha => hOutside a (Or.inl (ha.trans_le hStart))

theorem fixedArrayAllocFitStore_bytesBelow
    {st : Store Unit} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} {stride limit : UInt64}
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hLimit : 48 ≤ limit.toNat)
    (hAbove : ∀ node ∈ nodes, limit.toNat + 48 ≤ node.root.toNat) :
    BytesEqBelow st.mem
      (BookAllocFit.fixedArrayAllocFitStore st choice stride).mem limit.toNat := by
  have hCapacity : (limit - 48).toNat = limit.toNat - 48 := by
    rw [toNat_sub_le limit 48 (by simpa using hLimit)]
    rfl
  have hSeparate : FreeListSeparatedFromFixedArray nodes 48 (limit - 48) := by
    intro node hNode
    have hStart := hAbove node hNode
    left
    simp only [fixedArrayRegion, FreeNode.region, hCapacity]
    change 0 + (48 + (limit.toNat - 48)) ≤ node.root.toNat - 48
    omega
  intro a ha
  exact fixedArrayAllocFitMem_bytes hList hTake hSeparate (by simp)
    (by change a < 48 + (limit - 48).toNat; rw [hCapacity]; omega)

theorem fixedArrayAllocBumpStore_bytesBelow
    (st : Store Unit) (g0 need stride : UInt64) (limit : Nat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hStart : limit ≤ g0.toNat) :
    BytesEqBelow st.mem
      (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).mem limit :=
  fun a ha => fixedArrayAllocBumpStore_bytes_below st g0 need stride a
    hFit32 (ha.trans_le hStart)

theorem fixedArrayReleaseMem_bytesBelow
    (st : Store Unit) (ptr capacity head : UInt64) (limit : Nat)
    (hPtr48 : 48 ≤ ptr.toNat)
    (hPtr32 : ptr.toNat + capacity.toNat < 4294967296)
    (hStart : limit + 48 ≤ ptr.toNat) :
    BytesEqBelow st.mem (fixedArrayReleaseMem st ptr head) limit := by
  intro a ha
  exact ReleaseFrame.fixedArrayReleaseMem_bytes st ptr capacity head (0, limit) a
    hPtr48 hPtr32 (Or.inr (by simp only [fixedArrayRegion]; omega))
    (Nat.zero_le a) (by simpa using ha)

def AllocationEffect (before after : Store Unit) (heap : UInt64)
    (nodes nextNodes : List FreeNode) (roots : List UInt64) : Prop :=
  ∀ floor : UInt64, 48 ≤ floor.toNat → floor.toNat ≤ heap.toNat →
    (∀ node ∈ nodes, floor.toNat + 48 ≤ node.root.toNat) →
    BytesEqBelow before.mem after.mem floor.toNat ∧
    (∀ root ∈ roots, floor.toNat + 48 ≤ root.toNat) ∧
    (∀ node ∈ nextNodes, floor.toNat + 48 ≤ node.root.toNat)

theorem AllocationEffect.fit
    {before after : Store Unit} {heap need stride : UInt64}
    {nodes : List FreeNode} {choice : FreeChoice} {words : Nat}
    (hList : FreeListAt before.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hOutside : MemEqOutsideFlatWords
      (BookAllocFit.fixedArrayAllocFitStore before choice stride) after
      choice.node.root words) :
    AllocationEffect before after heap nodes choice.remaining [choice.node.root] := by
  intro floor hFloor hHeap hNodes
  have hRoot := hNodes choice.node (takeFirstFitFrom_some_mem hTake)
  refine ⟨(fixedArrayAllocFitStore_bytesBelow hList hTake hFloor hNodes).trans
    (BytesEqBelow.of_outsideFlatWords (by omega) hOutside), ?_, ?_⟩
  · simpa using hRoot
  · intro node hNode
    exact hNodes node (takeFirstFitFrom_some_remaining_mem hTake hNode)

theorem AllocationEffect.bump
    {before after : Store Unit} {heap need stride root : UInt64}
    {nodes : List FreeNode} {words : Nat}
    (hFit32 : heap.toNat + 48 + need.toNat < 4294967296)
    (hRoot : root.toNat = heap.toNat + 48)
    (hOutside : MemEqOutsideFlatWords
      (BookAllocBump.fixedArrayAllocBumpStore before heap need stride) after
      root words) :
    AllocationEffect before after heap nodes nodes [root] := by
  intro floor hFloor hHeap hNodes
  refine ⟨(fixedArrayAllocBumpStore_bytesBelow before heap need stride
    floor.toNat hFit32 hHeap).trans
      (BytesEqBelow.of_outsideFlatWords (by omega) hOutside), ?_, hNodes⟩
  simpa using (show floor.toNat + 48 ≤ root.toNat by omega)

theorem AllocationEffect.trans
    {before middle after : Store Unit} {heap nextHeap : UInt64}
    {nodes middleNodes finalNodes : List FreeNode} {firstRoots lastRoots : List UInt64}
    (first : AllocationEffect before middle heap nodes middleNodes firstRoots)
    (last : AllocationEffect middle after nextHeap middleNodes finalNodes lastRoots)
    (hHeap : heap.toNat ≤ nextHeap.toNat) :
    AllocationEffect before after heap nodes finalNodes (firstRoots ++ lastRoots) := by
  intro floor hFloor hStart hNodes
  obtain ⟨hFirst, hFirstRoots, hMiddleNodes⟩ := first floor hFloor hStart hNodes
  obtain ⟨hLast, hLastRoots, hFinalNodes⟩ :=
    last floor hFloor (hStart.trans hHeap) hMiddleNodes
  refine ⟨hFirst.trans hLast, ?_, hFinalNodes⟩
  intro root hRoot
  rcases List.mem_append.mp hRoot with hFirstRoot | hLastRoot
  · exact hFirstRoots root hFirstRoot
  · exact hLastRoots root hLastRoot

#print axioms fixedArrayAllocFitStore_bytesBelow
#print axioms fixedArrayReleaseMem_bytesBelow
#print axioms AllocationEffect.trans
end Project.ClobMatchFuel.MemoryBelow
