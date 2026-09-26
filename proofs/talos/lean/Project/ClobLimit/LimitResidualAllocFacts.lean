import Project.ClobLimit.LimitResidualAllocation
import Project.ClobMatchFuel.MemoryBelow

namespace Project.ClobLimit.LimitResidualAllocFacts

open Wasm Project.Common Project.Clob Project.ClobLimit Project.Runtime Project.ProofKit
  Project.ClobLimit.MatchInvariant Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame Project.ClobMatchFuel.BookAllocFit

open LimitResidualAllocation

structure Facts (st : Store Unit) (ctx : Context) (data : MatchOutput.OutputData) : Prop where
  root48 : 48 ≤ (root ctx data).toNat
  root32 : (root ctx data).toNat + (capacity ctx data).toNat < 4294967296
  rootFit : (root ctx data).toNat + (capacity ctx data).toNat ≤ st.mem.pages * 65536
  capacityMin : (need ctx).toNat ≤ (capacity ctx data).toNat
  rootAbove : ctx.initialG0.toNat + 48 ≤ (root ctx data).toNat
  pages : (allocated st ctx data).mem.pages = st.mem.pages
  fresh : FreshOrderArrayAt (allocated st ctx data) (root ctx data) (capacity ctx data)
  bookOwned : OwnedOrderArrayAt (allocated st ctx data) data.book data.bookCapacity ctx.result.book
  tradesOwned : OwnedTradeArrayAt (allocated st ctx data) data.trades data.tradesCapacity ctx.result.trades
  bookSeparate : regionsDisjoint (fixedArrayRegion (root ctx data) (capacity ctx data))
    (fixedArrayRegion data.book data.bookCapacity)
  tradesSeparate : regionsDisjoint (fixedArrayRegion (root ctx data) (capacity ctx data))
    (fixedArrayRegion data.trades data.tradesCapacity)
  memoryBelow : Project.ClobMatchFuel.MemoryBelow.BytesEqBelow st.mem
    (allocated st ctx data).mem ctx.initialG0.toNat

theorem derive (st : Store Unit) (ctx : Context) (data : MatchOutput.OutputData)
    (hOutput : MatchOutput.OutputAt ctx st data)
    (hFloor : 48 ≤ ctx.initialG0.toNat)
    (hNeed : 8 ≤ (need ctx).toNat)
    (hFit32 : data.g0.toNat + 48 + (need ctx).toNat < 4294967296)
    (hFit : data.g0.toNat + 48 + (need ctx).toNat ≤ st.mem.pages * 65536) :
    Facts st ctx data := by
  cases hTake : takeFirstFitFrom 0 (need ctx) data.nodes with
  | some choice =>
    have hMember := takeFirstFitFrom_some_mem hTake
    have hBounds := hOutput.freeList.mem_bounds hMember
    have hCapacity := takeFirstFitFrom_some_capacity hTake
    have hCapacityNat : (need ctx).toNat ≤ choice.node.capacity.toNat :=
      UInt64.le_iff_toNat_le.mp hCapacity
    have hFresh := freshFixedArrayAt_fixedArrayAllocFitStore 5 hOutput.freeList hTake
    have hBook := ownedOrderArrayAt_fixedArrayAllocFitStore (stride := 5)
      hOutput.freeList hTake hOutput.book48 hOutput.book32 hOutput.bookCapacity
      hOutput.bookFree hOutput.bookOwned
    have hTrades := ownedTradeArrayAt_fixedArrayAllocFitStore (stride := 5)
      hOutput.freeList hTake hOutput.trades48 hOutput.trades32 hOutput.tradesCapacity
      hOutput.tradesFree hOutput.tradesOwned
    have hBelow := Project.ClobMatchFuel.MemoryBelow.fixedArrayAllocFitStore_bytesBelow
      (stride := 5) hOutput.freeList hTake hFloor hOutput.nodesAbove
    have hPages := fixedArrayAllocFitStore_pages st choice 5
    constructor
    · simpa [root, FixedArrayAllocate.root, hTake] using hBounds.1
    · simpa [root, capacity, FixedArrayAllocate.root, hTake] using hBounds.2.1
    · simpa [root, capacity, FixedArrayAllocate.root, hTake] using hBounds.2.2
    · simpa [capacity, hTake] using hCapacityNat
    · simpa [root, FixedArrayAllocate.root, hTake] using hOutput.nodesAbove choice.node hMember
    · simpa [allocated, FixedArrayAllocate.allocated, FixedArrayAllocateNone.counted, hTake] using hPages
    · simpa [allocated, root, capacity, FixedArrayAllocate.allocated, FixedArrayAllocate.root,
        FixedArrayAllocateNone.counted, hTake, FreshOrderArrayAt, FreshFixedArrayAt] using hFresh
    · simpa [allocated, FixedArrayAllocate.allocated, FixedArrayAllocateNone.counted, hTake,
        OwnedOrderArrayAt, FreshOrderArrayAt, FreshFixedArrayAt, OrdersAt, orderWord] using hBook
    · simpa [allocated, FixedArrayAllocate.allocated, FixedArrayAllocateNone.counted, hTake,
        OwnedTradeArrayAt, FreshTradeArrayAt, FreshFixedArrayAt, TradesAt, tradeWord] using hTrades
    · have hSep := hOutput.bookFree choice.node hMember
      simpa [root, capacity, FixedArrayAllocate.root, hTake, fixedArrayRegion, FreeNode.region,
        regionsDisjoint, or_comm] using hSep
    · have hSep := hOutput.tradesFree choice.node hMember
      simpa [root, capacity, FixedArrayAllocate.root, hTake, fixedArrayRegion, FreeNode.region,
        regionsDisjoint, or_comm] using hSep
    · simpa [allocated, FixedArrayAllocate.allocated, FixedArrayAllocateNone.counted, hTake] using hBelow
  | none =>
    have hNoGrow : FixedArrayBump.requiredPages data.g0 (need ctx) ≤ st.mem.pages := by
      unfold FixedArrayBump.requiredPages
      omega
    have hEnsured : MemoryGrowth.ensured st (FixedArrayBump.requiredPages data.g0 (need ctx)) = st := by
      simp [MemoryGrowth.ensured, hNoGrow]
    have hRoot : (data.g0 + 48).toNat = data.g0.toNat + 48 :=
      fixedArrayBumpRoot_toNat data.g0 (by rw [size_eq]; omega)
    have hFresh := fixedArrayAllocBumpStore_spec st data.g0 (need ctx) 5 hNeed hFit32
    have hBook := ownedOrderArrayAt_fixedArrayAllocBumpStore (stride := 5)
      hFit32 hOutput.book48 hOutput.book32 hOutput.bookCapacity hOutput.bookBelow hOutput.bookOwned
    have hTrades := ownedTradeArrayAt_fixedArrayAllocBumpStore (stride := 5)
      hFit32 hOutput.trades48 hOutput.trades32 hOutput.tradesCapacity hOutput.tradesBelow hOutput.tradesOwned
    have hBelow := Project.ClobMatchFuel.MemoryBelow.fixedArrayAllocBumpStore_bytesBelow
      st data.g0 (need ctx) 5 ctx.initialG0.toNat hFit32 hOutput.heapMono
    constructor
    · simp only [root, FixedArrayAllocate.root, hTake, hRoot]; omega
    · simpa [root, capacity, FixedArrayAllocate.root, hTake, hRoot] using hFit32
    · simpa [root, capacity, FixedArrayAllocate.root, hTake, hRoot] using hFit
    · simp [capacity, hTake]
    · simp only [root, FixedArrayAllocate.root, hTake, hRoot]
      have hMono := hOutput.heapMono
      omega
    · simp [allocated, FixedArrayAllocate.allocated, FixedArrayBump.allocated,
        FixedArrayAllocateNone.counted, hTake, hEnsured, Project.Clob.fixedArrayAllocBumpStore_pages]
    · simpa [allocated, root, capacity, FixedArrayAllocate.allocated, FixedArrayBump.allocated,
        FixedArrayAllocate.root, FixedArrayAllocateNone.counted, hTake, hEnsured,
        FreshOrderArrayAt, FreshFixedArrayAt] using hFresh
    · simpa [allocated, FixedArrayAllocate.allocated, FixedArrayBump.allocated,
        FixedArrayAllocateNone.counted, hTake, hEnsured,
        OwnedOrderArrayAt, FreshOrderArrayAt, FreshFixedArrayAt, OrdersAt, orderWord] using hBook
    · simpa [allocated, FixedArrayAllocate.allocated, FixedArrayBump.allocated,
        FixedArrayAllocateNone.counted, hTake, hEnsured,
        OwnedTradeArrayAt, FreshTradeArrayAt, FreshFixedArrayAt, TradesAt, tradeWord] using hTrades
    · right
      simp only [root, capacity, FixedArrayAllocate.root, hTake, fixedArrayRegion, hRoot]
      have hBook48 := hOutput.book48
      have hBookBelow := hOutput.bookBelow
      omega
    · right
      simp only [root, capacity, FixedArrayAllocate.root, hTake, fixedArrayRegion, hRoot]
      have hTrades48 := hOutput.trades48
      have hTradesBelow := hOutput.tradesBelow
      omega
    · simpa [allocated, FixedArrayAllocate.allocated, FixedArrayBump.allocated,
        FixedArrayAllocateNone.counted, hTake, hEnsured] using hBelow

theorem store_pages (facts : Facts st ctx data) :
    (store st ctx data).mem.pages = st.mem.pages := by
  simp [store, Mem.write64_pages, facts.pages]

theorem store_length (st : Store Unit) (ctx : Context) (data : MatchOutput.OutputData) :
    (store st ctx data).mem.read64 (root ctx data).toUInt32 =
      UInt64.ofNat (ctx.result.book.length + 1) := by
  simp [store, Mem.read64_write64_same]

theorem store_outside (facts : Facts st ctx data) (hNeed : 8 ≤ (need ctx).toNat) :
    MemEqOutsideFlatWords (allocated st ctx data) (store st ctx data) (root ctx data) 0 := by
  have h32 := facts.root32
  have hCapacity := facts.capacityMin
  have hFrame : MemEqOutsideFlatWords (allocated st ctx data) (allocated st ctx data)
      (root ctx data) 0 := fun _ _ => rfl
  simpa [store, toUInt32_eq_ofNat] using
    hFrame.write64 (value := UInt64.ofNat (ctx.result.book.length + 1))
      (by simp only [Nat.zero_add, Nat.one_mul]; omega) (slot := 0) (by omega)

theorem store_fresh (facts : Facts st ctx data) :
    FreshOrderArrayAt (store st ctx data) (root ctx data) (capacity ctx data) := by
  have h32 := facts.root32
  exact FreshFixedArrayAt.write64_data facts.fresh facts.root48
    (by rw [toUInt32_toNat, Nat.mod_eq_of_lt (by omega)])

theorem store_book (facts : Facts st ctx data) (hNeed : 8 ≤ (need ctx).toNat)
    (hOutput : MatchOutput.OutputAt ctx st data) :
    OwnedOrderArrayAt (store st ctx data) data.book data.bookCapacity ctx.result.book := by
  apply OwnedOrderArrayAt.frame_outsideFlatWords hOutput.book48 hOutput.book32
    hOutput.bookCapacity (by simp [store, Mem.write64_pages]) _ (store_outside facts hNeed) facts.bookOwned
  have hSep := facts.bookSeparate
  have h48 := facts.root48
  have hCap := facts.capacityMin
  unfold regionsDisjoint fixedArrayRegion flatWordsRegion at *
  simp only [Nat.zero_add, Nat.one_mul]
  omega

theorem store_trades (facts : Facts st ctx data) (hNeed : 8 ≤ (need ctx).toNat)
    (hOutput : MatchOutput.OutputAt ctx st data) :
    OwnedTradeArrayAt (store st ctx data) data.trades data.tradesCapacity ctx.result.trades := by
  apply OwnedTradeArrayAt.frame_outsideFlatWords hOutput.trades48 hOutput.trades32
    hOutput.tradesCapacity (by simp [store, Mem.write64_pages]) _ (store_outside facts hNeed) facts.tradesOwned
  have hSep := facts.tradesSeparate
  have h48 := facts.root48
  have hCap := facts.capacityMin
  unfold regionsDisjoint fixedArrayRegion flatWordsRegion at *
  simp only [Nat.zero_add, Nat.one_mul]
  omega

theorem store_memoryBelow (facts : Facts st ctx data) (hNeed : 8 ≤ (need ctx).toNat) :
    Project.ClobMatchFuel.MemoryBelow.BytesEqBelow st.mem
      (store st ctx data).mem ctx.initialG0.toNat := by
  apply facts.memoryBelow.trans
  apply Project.ClobMatchFuel.MemoryBelow.BytesEqBelow.of_outsideFlatWords _ (store_outside facts hNeed)
  have h := facts.rootAbove
  omega

end Project.ClobLimit.LimitResidualAllocFacts
