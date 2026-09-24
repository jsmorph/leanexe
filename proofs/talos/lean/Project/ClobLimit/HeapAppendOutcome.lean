import Project.ClobLimit.HeapAppendHeader
import Project.ClobLimit.HeapAppendBounds

namespace Project.ClobLimit.HeapAppendOutcome
open Wasm Project.Common Project.Runtime Project.Clob Project.ClobLimit Project.ProofKit
open Project.ClobMatchFuel.LoopInvariant Project.ClobMatchFuel.LoopResult
open Project.ClobMatchFuel.AllocatorFrame Project.ClobMatchFuel.Allocation
open Project.EulerRiemann.Execution

def root (ctx : Context) (data : OutputData) : UInt64 :=
  allocatedRoot data.g0 (HeapAppendAllocate.need ctx) data.nodes

def capacity (ctx : Context) (data : OutputData) : UInt64 :=
  allocatedCapacity (HeapAppendAllocate.need ctx) data.nodes

def nodes (ctx : Context) (data : OutputData) : List FreeNode :=
  allocatedNodes (HeapAppendAllocate.need ctx) data.nodes

structure At (initial final : Store Unit) (ctx : Context) (data : OutputData) (order : OrderL) : Prop where
  bookOwned : OwnedOrderArrayAt final (root ctx data) (capacity ctx data)
    (ctx.result.book ++ [{ order with oqty := ctx.result.remaining }])
  sourceBookOwned : OwnedOrderArrayAt final data.book data.bookCapacity ctx.result.book
  tradesOwned : OwnedTradeArrayAt final data.trades data.tradesCapacity ctx.result.trades
  freeList : FreeListAt final.mem (nodes ctx data)
  global0 : final.globals.globals[0]? =
    some (.i64 (allocatedTop data.g0 (HeapAppendAllocate.need ctx) data.nodes))
  global1 : final.globals.globals[1]? = some (.i64 (freeHead (nodes ctx data)))
  global2 : final.globals.globals[2]? = some (.i64 (ctx.expectedG2 + 1))
  global4 : final.globals.globals[4]? = some (.i64 ctx.expectedG4)
  global5 : final.globals.globals[5]? = some (.i64 ctx.expectedG5)
  pages : final.mem.pages = initial.mem.pages
  outside : MemEqOutsideFlatWords
    (HeapAppendMemory.allocated initial ctx data (HeapAppendAllocate.need ctx)) final
    (root ctx data) ((ctx.result.book.length + 1) * 5)

theorem of_finish (initial final : Store Unit) (ctx : Context) (data : OutputData) (order : OrderL)
    (geo : HeapResidualFacts.Geometry ctx initial data)
    (hAlloc : HeapAppendMemory.Facts initial
      (HeapAppendMemory.allocated initial ctx data (HeapAppendAllocate.need ctx)) ctx data
      (HeapAppendAllocate.need ctx))
    (hSize : ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤ (capacity ctx data).toNat)
    (hFinish : HeapAppendFacts.FinishState
      (HeapAppendHeader.initialized
        (HeapAppendMemory.allocated initial ctx data (HeapAppendAllocate.need ctx))
        (root ctx data) ctx.result.book.length)
      final (root ctx data - 48) (capacity ctx data) data.book ctx.result.book
      { order with oqty := ctx.result.remaining }) : At initial final ctx data order := by
  let raw := HeapAppendMemory.allocated initial ctx data (HeapAppendAllocate.need ctx)
  have hh := HeapAppendHeader.facts raw ctx data (HeapAppendAllocate.need ctx) hAlloc geo hSize
  have hRoot : root ctx data - 48 + 48 = root ctx data := by simp
  have hOutside : MemEqOutsideFlatWords raw final (root ctx data)
      ((ctx.result.book.length + 1) * 5) := by
    intro address hAddress
    exact (hFinish.outside address (by simpa only [hRoot] using hAddress)).trans
      (hh.outside address hAddress)
  have hPages : final.mem.pages = raw.mem.pages := hFinish.pages.trans hh.pages
  have hGlobals : final.globals.globals = raw.globals.globals := hFinish.globals
  have hTarget48 := hAlloc.root48
  have hSepBook : regionsDisjoint
      (flatWordsRegion (root ctx data) ((ctx.result.book.length + 1) * 5))
      (fixedArrayRegion data.book data.bookCapacity) := by
    have hs := hAlloc.bookSeparated
    have hb := geo.book48
    simp only [regionsDisjoint, fixedArrayRegion, allocatedNode, FreeNode.region] at hs
    simp only [regionsDisjoint, flatWordsRegion, fixedArrayRegion, root]
    change ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
      (allocatedCapacity (HeapAppendAllocate.need ctx) data.nodes).toNat at hSize
    omega
  have hSepTrades : regionsDisjoint
      (flatWordsRegion (root ctx data) ((ctx.result.book.length + 1) * 5))
      (fixedArrayRegion data.trades data.tradesCapacity) := by
    have hs := hAlloc.tradesSeparated
    have ht := geo.trades48
    simp only [regionsDisjoint, fixedArrayRegion, allocatedNode, FreeNode.region] at hs
    simp only [regionsDisjoint, flatWordsRegion, fixedArrayRegion, root]
    change ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
      (allocatedCapacity (HeapAppendAllocate.need ctx) data.nodes).toNat at hSize
    omega
  refine {
    bookOwned := by simpa only [hRoot] using hFinish.bookOwned
    sourceBookOwned := OwnedOrderArrayAt.frame_outsideFlatWords geo.book48 geo.book32
      geo.bookCapacity hPages hSepBook hOutside hAlloc.bookOwned
    tradesOwned := OwnedTradeArrayAt.frame_outsideFlatWords geo.trades48 geo.trades32
      geo.tradesCapacity hPages hSepTrades hOutside hAlloc.tradesOwned
    freeList := FreeListAt.frame_outsideFlatWords hPages ?_ hOutside hAlloc.freeList
    global0 := by rw [hGlobals]; exact hAlloc.global0
    global1 := by rw [hGlobals]; exact hAlloc.global1
    global2 := by rw [hGlobals]; exact hAlloc.global2
    global4 := by rw [hGlobals]; exact hAlloc.global4
    global5 := by rw [hGlobals]; exact hAlloc.global5
    pages := hPages.trans hAlloc.pages
    outside := hOutside }
  intro node hNode
  have hs := hAlloc.freeSeparated node hNode
  have hn := (hAlloc.freeList.mem_bounds hNode).1
  simp only [regionsDisjoint, allocatedNode, FreeNode.region] at hs
  simp only [regionsDisjoint, flatWordsRegion, root, FreeNode.region]
  change ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
    (allocatedCapacity (HeapAppendAllocate.need ctx) data.nodes).toNat at hSize
  omega

#print axioms of_finish
end Project.ClobLimit.HeapAppendOutcome
