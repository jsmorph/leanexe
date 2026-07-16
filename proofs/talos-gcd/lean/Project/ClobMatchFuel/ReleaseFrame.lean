import Project.ClobMatchFuel.AllocatorFrame

/-!
# Fixed-array release frames

The matching loop releases consumed fixed arrays onto the allocator free list.
This module preserves disjoint live arrays through the two header writes and
constructs the resulting `FreeListAt` representation.
-/

namespace Project.ClobMatchFuel.ReleaseFrame

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def releasedNode (ptr capacity : UInt64) : FreeNode :=
  { root := ptr, capacity }

theorem fixedArrayReleaseMem_bytes
    (st : Store Unit) (ptr capacity freeHead : UInt64)
    (region : Nat × Nat) (a : Nat)
    (hPtr48 : 48 ≤ ptr.toNat)
    (hPtr32 : ptr.toNat + capacity.toNat < 4294967296)
    (hsep : regionsDisjoint (fixedArrayRegion ptr capacity) region)
    (haLow : region.1 ≤ a) (haHigh : a < region.1 + region.2) :
    (fixedArrayReleaseMem st ptr freeHead).bytes a = st.mem.bytes a := by
  have hAddress (offset : UInt64) (hOffset : offset.toNat ≤ 48)
      (hOffset8 : 8 ≤ offset.toNat) :
      ((ptr - offset).toUInt32).toNat = ptr.toNat - offset.toNat := by
    rw [toUInt32_toNat, toNat_sub_le ptr offset (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hOutside (offset : UInt64) (hOffset : offset.toNat ≤ 48)
      (hOffset8 : 8 ≤ offset.toNat) :
      a < ((ptr - offset).toUInt32).toNat ∨
        ((ptr - offset).toUInt32).toNat + 8 ≤ a := by
    rw [hAddress offset hOffset hOffset8]
    unfold regionsDisjoint fixedArrayRegion at hsep
    omega
  unfold fixedArrayReleaseMem
  calc
    _ = (st.mem.write64 ((ptr - 40).toUInt32) 0).bytes a :=
      write64_bytes_ne _ _ _ (hOutside 8 (by decide) (by decide))
    _ = st.mem.bytes a :=
      write64_bytes_ne _ _ _ (hOutside 40 (by decide) (by decide))

theorem OwnedOrderArrayAt.frame_release
    {before after : Store Unit}
    {released releasedCapacity freeHead source sourceCapacity : UInt64}
    {os : List OrderL}
    (hReleased48 : 48 ≤ released.toNat)
    (hReleased32 :
      released.toNat + releasedCapacity.toNat < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hsep : regionsDisjoint (fixedArrayRegion released releasedCapacity)
      (fixedArrayRegion source sourceCapacity))
    (hMem : after.mem = fixedArrayReleaseMem before released freeHead)
    (hOwned : OwnedOrderArrayAt before source sourceCapacity os) :
    OwnedOrderArrayAt after source sourceCapacity os := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        after.mem.bytes a = before.mem.bytes a := by
    intro a haLow haHigh
    rw [hMem]
    exact fixedArrayReleaseMem_bytes before released releasedCapacity freeHead
      (fixedArrayRegion source sourceCapacity) a hReleased48 hReleased32 hsep
      (by simpa [fixedArrayRegion] using haLow) (by
        unfold fixedArrayRegion
        omega)
  have hPages : after.mem.pages = before.mem.pages := by
    rw [hMem]
    rfl
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    OrdersAt.frame_region hSource32 hSource48 hSourceCapacity hPages hBytes
      hOwned.2⟩

theorem OwnedTradeArrayAt.frame_release
    {before after : Store Unit}
    {released releasedCapacity freeHead source sourceCapacity : UInt64}
    {ts : List TradeL}
    (hReleased48 : 48 ≤ released.toNat)
    (hReleased32 :
      released.toNat + releasedCapacity.toNat < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hsep : regionsDisjoint (fixedArrayRegion released releasedCapacity)
      (fixedArrayRegion source sourceCapacity))
    (hMem : after.mem = fixedArrayReleaseMem before released freeHead)
    (hOwned : OwnedTradeArrayAt before source sourceCapacity ts) :
    OwnedTradeArrayAt after source sourceCapacity ts := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        after.mem.bytes a = before.mem.bytes a := by
    intro a haLow haHigh
    rw [hMem]
    exact fixedArrayReleaseMem_bytes before released releasedCapacity freeHead
      (fixedArrayRegion source sourceCapacity) a hReleased48 hReleased32 hsep
      (by simpa [fixedArrayRegion] using haLow) (by
        unfold fixedArrayRegion
        omega)
  have hPages : after.mem.pages = before.mem.pages := by
    rw [hMem]
    rfl
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    TradesAt.frame_region hSource32 hSource48 hSourceCapacity hPages hBytes
      hOwned.2⟩

theorem freeListAt_fixedArrayReleaseMem
    (st : Store Unit) (ptr capacity : UInt64) (nodes : List FreeNode)
    (hPtr48 : 48 ≤ ptr.toNat)
    (hPtr32 : ptr.toNat + capacity.toNat < 4294967296)
    (hPtrFit : ptr.toNat + capacity.toNat ≤ st.mem.pages * 65536)
    (hCapacity : st.mem.read64 ((ptr - 32).toUInt32) = capacity)
    (hsep : ∀ node ∈ nodes,
      regionsDisjoint (fixedArrayRegion ptr capacity) node.region)
    (hList : FreeListAt st.mem nodes) :
    FreeListAt (fixedArrayReleaseMem st ptr (freeHead nodes))
      (releasedNode ptr capacity :: nodes) := by
  let writer := releasedNode ptr capacity
  have hWriterRegion : writer.region = fixedArrayRegion ptr capacity := rfl
  have hList40 : FreeListAt
      (st.mem.write64 ((ptr - 40).toUInt32) 0) nodes := by
    apply hList.frame_write64_disjoint (writer := writer)
      (writeOffset := 40) (value := 0) hPtr48 hPtr32
      (by decide) (by decide)
    intro node hmem
    rw [hWriterRegion]
    exact hsep node hmem
  have hList8 : FreeListAt
      ((st.mem.write64 ((ptr - 40).toUInt32) 0).write64
        ((ptr - 8).toUInt32) (freeHead nodes)) nodes := by
    apply hList40.frame_write64_disjoint (writer := writer)
      (writeOffset := 8) (value := freeHead nodes) hPtr48 hPtr32
      (by decide) (by decide)
    intro node hmem
    rw [hWriterRegion]
    exact hsep node hmem
  have hAddress (offset : UInt64) (hOffset : offset.toNat ≤ 48)
      (hOffset8 : 8 ≤ offset.toNat) :
      ((ptr - offset).toUInt32).toNat = ptr.toNat - offset.toNat := by
    rw [toUInt32_toNat, toNat_sub_le ptr offset (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hReadNe (writeOffset readOffset : UInt64)
      (hWriteLow : 8 ≤ writeOffset.toNat)
      (hWriteHigh : writeOffset.toNat ≤ 40)
      (hReadLow : 8 ≤ readOffset.toNat)
      (hReadHigh : readOffset.toNat ≤ 40)
      (hOffsets : writeOffset.toNat + 8 ≤ readOffset.toNat ∨
        readOffset.toNat + 8 ≤ writeOffset.toNat)
      (mem : Mem) (value : UInt64) :
      (mem.write64 ((ptr - writeOffset).toUInt32) value).read64
          ((ptr - readOffset).toUInt32) =
        mem.read64 ((ptr - readOffset).toUInt32) := by
    apply read64_write64_ne
    rw [hAddress writeOffset (by omega) hWriteLow,
      hAddress readOffset (by omega) hReadLow]
    rcases hOffsets with hOffsets | hOffsets <;> omega
  unfold fixedArrayReleaseMem
  change FreeListAt
    ((st.mem.write64 ((ptr - 40).toUInt32) 0).write64
      ((ptr - 8).toUInt32) (freeHead nodes))
    ({ root := ptr, capacity := capacity } :: nodes)
  refine .cons hPtr48 hPtr32 ?_ ?_ ?_ ?_ ?_ hList8
  · exact hPtrFit
  · dsimp only
    rw [hReadNe 8 40 (by decide) (by decide) (by decide) (by decide)
        (by decide), Mem.read64_write64_same]
  · dsimp only
    rw [hReadNe 8 32 (by decide) (by decide) (by decide) (by decide)
        (by decide),
      hReadNe 40 32 (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    exact hCapacity
  · dsimp only
    exact Mem.read64_write64_same _ _ _
  · intro node hmem
    simpa [fixedArrayRegion, FreeNode.region] using hsep node hmem

theorem fixedArrayRoots_ne_of_regionsDisjoint
    {a aCapacity b bCapacity : UInt64}
    (hsep : regionsDisjoint (fixedArrayRegion a aCapacity)
      (fixedArrayRegion b bCapacity)) :
    a ≠ b := by
  intro hab
  subst b
  unfold regionsDisjoint fixedArrayRegion at hsep
  omega

theorem OwnedOrderArrayAt.root_ne_ownedTradeArrayAt
    {st : Store Unit}
    {orderPtr orderCapacity tradePtr tradeCapacity : UInt64}
    {os : List OrderL} {ts : List TradeL}
    (hOrder : OwnedOrderArrayAt st orderPtr orderCapacity os)
    (hTrade : OwnedTradeArrayAt st tradePtr tradeCapacity ts) :
    orderPtr ≠ tradePtr := by
  intro hptr
  subst tradePtr
  have hStride5 := hOrder.1.2.2.2.2.1
  have hStride4 := hTrade.1.2.2.2.2.1
  rw [hStride5] at hStride4
  exact (by decide : (5 : UInt64) ≠ 4) hStride4

end Project.ClobMatchFuel.ReleaseFrame
