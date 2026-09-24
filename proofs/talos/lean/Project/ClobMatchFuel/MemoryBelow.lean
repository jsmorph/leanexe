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

#print axioms fixedArrayAllocFitStore_bytesBelow
#print axioms fixedArrayReleaseMem_bytesBelow
end Project.ClobMatchFuel.MemoryBelow
