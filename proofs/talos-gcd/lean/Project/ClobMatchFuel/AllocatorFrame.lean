import Project.ClobMatchFuel.BookAllocFit
import Project.ClobMatchFuel.BookAllocBump

/-!
# Allocator frames for live fixed arrays

The matching allocator may reuse a represented free node or extend the heap.
This module proves that either outcome preserves a disjoint refcount-one source
array, including the header needed by the later release call.
-/

namespace Project.ClobMatchFuel.AllocatorFrame

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation

def OwnedOrderArrayAt (st : Store Unit) (ptr capacity : UInt64)
    (os : List OrderL) : Prop :=
  FreshOrderArrayAt st ptr capacity ∧ OrdersAt st ptr os

def OwnedTradeArrayAt (st : Store Unit) (ptr capacity : UInt64)
    (ts : List TradeL) : Prop :=
  FreshTradeArrayAt st ptr capacity ∧ TradesAt st ptr ts

def FreeListSeparatedFromFixedArray (nodes : List FreeNode)
    (ptr capacity : UInt64) : Prop :=
  ∀ node ∈ nodes, regionsDisjoint (fixedArrayRegion ptr capacity) node.region

theorem flatWordsDisjoint_of_fixedArrayRegions
    {aPtr aCapacity bPtr bCapacity : UInt64} {aWords bWords : Nat}
    (ha48 : 48 ≤ aPtr.toNat) (hb48 : 48 ≤ bPtr.toNat)
    (haFit : (aWords + 1) * 8 ≤ aCapacity.toNat)
    (hbFit : (bWords + 1) * 8 ≤ bCapacity.toNat)
    (hsep : regionsDisjoint (fixedArrayRegion aPtr aCapacity)
      (fixedArrayRegion bPtr bCapacity)) :
    flatWordsDisjoint (flatWordsRegion aPtr aWords)
      (flatWordsRegion bPtr bWords) := by
  unfold regionsDisjoint fixedArrayRegion at hsep
  unfold flatWordsDisjoint flatWordsRegion
  omega

theorem MemEqOutsideFlatWords.fixedArray_bytes
    {before after : Store Unit} {target source capacity : UInt64}
    {targetWords : Nat}
    (hsep : regionsDisjoint (flatWordsRegion target targetWords)
      (fixedArrayRegion source capacity))
    (hFrame : MemEqOutsideFlatWords before after target targetWords)
    (a : Nat) (haLow : source.toNat - 48 ≤ a)
    (haHigh : a < source.toNat + capacity.toNat) :
    after.mem.bytes a = before.mem.bytes a := by
  apply hFrame
  unfold regionsDisjoint flatWordsRegion fixedArrayRegion at hsep
  omega

theorem OwnedOrderArrayAt.frame_outsideFlatWords
    {before after : Store Unit}
    {target source sourceCapacity : UInt64} {targetWords : Nat}
    {os : List OrderL}
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hPages : after.mem.pages = before.mem.pages)
    (hsep : regionsDisjoint (flatWordsRegion target targetWords)
      (fixedArrayRegion source sourceCapacity))
    (hFrame : MemEqOutsideFlatWords before after target targetWords)
    (hOwned : OwnedOrderArrayAt before source sourceCapacity os) :
    OwnedOrderArrayAt after source sourceCapacity os := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        after.mem.bytes a = before.mem.bytes a := by
    intro a haLow haHigh
    exact MemEqOutsideFlatWords.fixedArray_bytes hsep hFrame a haLow haHigh
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    OrdersAt.frame_region hSource32 hSource48 hSourceCapacity hPages hBytes
      hOwned.2⟩

theorem OwnedTradeArrayAt.frame_outsideFlatWords
    {before after : Store Unit}
    {target source sourceCapacity : UInt64} {targetWords : Nat}
    {ts : List TradeL}
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hPages : after.mem.pages = before.mem.pages)
    (hsep : regionsDisjoint (flatWordsRegion target targetWords)
      (fixedArrayRegion source sourceCapacity))
    (hFrame : MemEqOutsideFlatWords before after target targetWords)
    (hOwned : OwnedTradeArrayAt before source sourceCapacity ts) :
    OwnedTradeArrayAt after source sourceCapacity ts := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        after.mem.bytes a = before.mem.bytes a := by
    intro a haLow haHigh
    exact MemEqOutsideFlatWords.fixedArray_bytes hsep hFrame a haLow haHigh
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    TradesAt.frame_region hSource32 hSource48 hSourceCapacity hPages hBytes
      hOwned.2⟩

theorem FreeListAt.frame_outsideFlatWords
    {before after : Store Unit} {nodes : List FreeNode}
    {target : UInt64} {targetWords : Nat}
    (hPages : after.mem.pages = before.mem.pages)
    (hsep : ∀ node ∈ nodes,
      regionsDisjoint (flatWordsRegion target targetWords) node.region)
    (hFrame : MemEqOutsideFlatWords before after target targetWords)
    (hList : FreeListAt before.mem nodes) :
    FreeListAt after.mem nodes := by
  refine FreeListAt.frame hPages ?_ hList
  intro node hNode offset hOffset
  obtain ⟨hNode48, hNode32, _⟩ := hList.mem_bounds hNode
  have hNodeSep := hsep node hNode
  have hOffsetLow : 8 ≤ offset.toNat := by
    rcases hOffset with rfl | rfl | rfl <;> decide
  have hOffsetHigh : offset.toNat ≤ 48 := by
    rcases hOffset with rfl | rfl | rfl <;> decide
  apply read64_congr
  intro i hi
  apply hFrame
  rw [toUInt32_toNat, toNat_sub_le _ _ (by omega),
    Nat.mod_eq_of_lt (by omega)]
  unfold regionsDisjoint flatWordsRegion FreeNode.region at hNodeSep
  omega

theorem fixedArrayAllocFitMem_bytes
    {mem : Mem} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} {source sourceCapacity stride : UInt64} {a : Nat}
    (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hsep : FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (haLow : source.toNat - 48 ≤ a)
    (haHigh : a < source.toNat + sourceCapacity.toNat) :
    (BookAllocFit.fixedArrayAllocFitMem mem choice stride).bytes a =
      mem.bytes a := by
  have frameWrite (current : Mem) (writer : FreeNode)
      (hWriter : writer ∈ nodes) (offset value : UInt64)
      (hOffsetLow : 8 ≤ offset.toNat)
      (hOffsetHigh : offset.toNat ≤ 48) :
      (current.write64 ((writer.root - offset).toUInt32) value).bytes a =
        current.bytes a := by
    obtain ⟨hWriter48, hWriter32, _⟩ := hList.mem_bounds hWriter
    have hdisjoint := hsep writer hWriter
    apply write64_bytes_ne
    rw [toUInt32_toNat,
      toNat_sub_le writer.root offset (by omega),
      Nat.mod_eq_of_lt (by omega)]
    unfold FreeListSeparatedFromFixedArray fixedArrayRegion regionsDisjoint
      FreeNode.region at hdisjoint
    omega
  have hChoiceMem : choice.node ∈ nodes :=
    takeFirstFitFrom_some_mem hTake
  have hUnlink : (unlinkFreeChoice mem choice).bytes a = mem.bytes a := by
    by_cases hPrevious : choice.previous = 0
    · simp [unlinkFreeChoice, hPrevious]
    · obtain ⟨skipped, tail, hnodes, hprevious, _, _, _⟩ :=
        takeFirstFitFrom_some_decompose hTake
      have hSkipped : skipped ≠ [] := by
        intro hEmpty
        subst skipped
        simp only [previousRoot] at hprevious
        exact hPrevious hprevious
      let predecessor := skipped.getLast hSkipped
      have hsplit : skipped.dropLast ++ [predecessor] = skipped :=
        List.dropLast_append_getLast hSkipped
      have hPreviousRoot : choice.previous = predecessor.root := by
        rw [hprevious, ← hsplit, previousRoot_append_singleton]
      have hPredecessorMem : predecessor ∈ nodes := by
        rw [hnodes, ← hsplit]
        simp
      rw [unlinkFreeChoice, if_neg hPrevious, hPreviousRoot]
      exact frameWrite mem predecessor hPredecessorMem 8 choice.next
        (by decide) (by decide)
  unfold BookAllocFit.fixedArrayAllocFitMem
  rw [frameWrite _ choice.node hChoiceMem 8 0 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 16 stride (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 24 2 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 32 choice.node.capacity
      (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 40 1 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 48 5501223100278326855
      (by decide) (by decide),
    hUnlink]

theorem ownedOrderArrayAt_fixedArrayAllocFitStore
    {st : Store Unit} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} {source sourceCapacity stride : UInt64}
    {os : List OrderL}
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hCapacity : fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hsep : FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os) :
    OwnedOrderArrayAt
      (BookAllocFit.fixedArrayAllocFitStore st choice stride)
      source sourceCapacity os := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (BookAllocFit.fixedArrayAllocFitStore st choice stride).mem.bytes a =
          st.mem.bytes a := by
    intro a haLow haHigh
    exact fixedArrayAllocFitMem_bytes hList hTake hsep haLow haHigh
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    OrdersAt.frame_region
      (st := st)
      (st' := BookAllocFit.fixedArrayAllocFitStore st choice stride)
      hSource32 hSource48 hCapacity (by
        simp only [BookAllocFit.fixedArrayAllocFitStore,
          BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
          Mem.write64_pages]
        split <;> rfl) hBytes hOwned.2⟩

theorem ownedTradeArrayAt_fixedArrayAllocFitStore
    {st : Store Unit} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} {source sourceCapacity stride : UInt64}
    {ts : List TradeL}
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hCapacity : fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hsep : FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (hOwned : OwnedTradeArrayAt st source sourceCapacity ts) :
    OwnedTradeArrayAt
      (BookAllocFit.fixedArrayAllocFitStore st choice stride)
      source sourceCapacity ts := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (BookAllocFit.fixedArrayAllocFitStore st choice stride).mem.bytes a =
          st.mem.bytes a := by
    intro a haLow haHigh
    exact fixedArrayAllocFitMem_bytes hList hTake hsep haLow haHigh
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    TradesAt.frame_region
      (st := st)
      (st' := BookAllocFit.fixedArrayAllocFitStore st choice stride)
      hSource32 hSource48 hCapacity (by
        simp only [BookAllocFit.fixedArrayAllocFitStore,
          BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
          Mem.write64_pages]
        split <;> rfl) hBytes hOwned.2⟩

theorem fixedArrayAllocBumpStore_bytes_below
    (st : Store Unit) (g0 need stride : UInt64) (a : Nat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (ha : a < g0.toNat) :
    (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).mem.bytes a =
      st.mem.bytes a := by
  exact fixedArrayHeaderMem_bytes_before st.mem g0 need stride a
    (by omega) ha

theorem ownedOrderArrayAt_fixedArrayAllocBumpStore
    {st : Store Unit} {g0 need stride source sourceCapacity : UInt64}
    {os : List OrderL}
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hCapacity : fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os) :
    OwnedOrderArrayAt
      (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride)
      source sourceCapacity os := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).mem.bytes a =
          st.mem.bytes a := by
    intro a _ haHigh
    exact fixedArrayAllocBumpStore_bytes_below st g0 need stride a hFit32
      (by omega)
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    OrdersAt.frame_region
      (st := st)
      (st' := BookAllocBump.fixedArrayAllocBumpStore st g0 need stride)
      hSource32 hSource48 hCapacity rfl hBytes hOwned.2⟩

theorem ownedTradeArrayAt_fixedArrayAllocBumpStore
    {st : Store Unit} {g0 need stride source sourceCapacity : UInt64}
    {ts : List TradeL}
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hCapacity : fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedTradeArrayAt st source sourceCapacity ts) :
    OwnedTradeArrayAt
      (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride)
      source sourceCapacity ts := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (BookAllocBump.fixedArrayAllocBumpStore st g0 need stride).mem.bytes a =
          st.mem.bytes a := by
    intro a _ haHigh
    exact fixedArrayAllocBumpStore_bytes_below st g0 need stride a hFit32
      (by omega)
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    TradesAt.frame_region
      (st := st)
      (st' := BookAllocBump.fixedArrayAllocBumpStore st g0 need stride)
      hSource32 hSource48 hCapacity rfl hBytes hOwned.2⟩

end Project.ClobMatchFuel.AllocatorFrame
