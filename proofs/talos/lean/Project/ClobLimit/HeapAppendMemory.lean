import Project.EulerRiemann.ArrayAllocationFrame
import Project.ClobLimit.HeapResidualFacts

namespace Project.ClobLimit.HeapAppendMemory
open Wasm Project.Common Project.Runtime Project.Clob Project.ProofKit
open Project.EulerRiemann.Execution
open Project.ClobMatchFuel.AllocatorFrame Project.ClobMatchFuel.Allocation
open Project.ClobMatchFuel.LoopInvariant Project.ClobMatchFuel.LoopResult

def allocated (st : Store Unit) (ctx : Context) (data : OutputData) (need : UInt64) : Store Unit :=
  FixedArrayAllocateNone.counted (FixedArrayAllocate.allocated st data.g0 need 5 data.nodes)
    ctx.expectedG2

structure Facts (initial result : Store Unit) (ctx : Context) (data : OutputData)
    (need : UInt64) : Prop where
  pages : result.mem.pages = initial.mem.pages
  root48 : 48 ≤ (allocatedRoot data.g0 need data.nodes).toNat
  root32 : (allocatedRoot data.g0 need data.nodes).toNat +
    (allocatedCapacity need data.nodes).toNat < 4294967296
  capacity : need.toNat ≤ (allocatedCapacity need data.nodes).toNat
  fits : (allocatedRoot data.g0 need data.nodes).toNat +
    (allocatedCapacity need data.nodes).toNat ≤ result.mem.pages * 65536
  fresh : FreshOrderArrayAt result (allocatedRoot data.g0 need data.nodes)
    (allocatedCapacity need data.nodes)
  bookOwned : OwnedOrderArrayAt result data.book data.bookCapacity ctx.result.book
  tradesOwned : OwnedTradeArrayAt result data.trades data.tradesCapacity ctx.result.trades
  bookSeparated : regionsDisjoint (fixedArrayRegion data.book data.bookCapacity)
    (allocatedNode data.g0 need data.nodes).region
  tradesSeparated : regionsDisjoint (fixedArrayRegion data.trades data.tradesCapacity)
    (allocatedNode data.g0 need data.nodes).region
  freeList : FreeListAt result.mem (allocatedNodes need data.nodes)
  freeSeparated : ∀ node ∈ allocatedNodes need data.nodes,
    regionsDisjoint (allocatedNode data.g0 need data.nodes).region node.region
  global0 : result.globals.globals[0]? = some (.i64 (allocatedTop data.g0 need data.nodes))
  global1 : result.globals.globals[1]? = some (.i64 (freeHead (allocatedNodes need data.nodes)))
  global2 : result.globals.globals[2]? = some (.i64 (ctx.expectedG2 + 1))
  global4 : result.globals.globals[4]? = some (.i64 ctx.expectedG4)
  global5 : result.globals.globals[5]? = some (.i64 ctx.expectedG5)

theorem facts (st : Store Unit) (ctx : Context) (data : OutputData) (need : UInt64)
    (hOutput : OutputAt ctx st data) (hGeo : HeapResidualFacts.Geometry ctx st data)
    (h32 : data.g0.toNat + 48 + need.toNat < 4294967296)
    (hFit : data.g0.toNat + 48 + need.toNat ≤ st.mem.pages * 65536) :
    Facts st (allocated st ctx data need) ctx data need := by
  let raw := FixedArrayAllocate.allocated st data.g0 need 5 data.nodes
  have hBump : takeFirstFitFrom 0 need data.nodes = none →
      data.g0.toNat + 48 + need.toNat ≤ 4294967296 := fun _ => Nat.le_of_lt h32
  have hPages : raw.mem.pages = st.mem.pages := by
    rw [arrayAllocated_pages]
    exact Nat.le_antisymm
      (allocated_pages_bound st data.g0 need data.nodes st.mem.pages (by omega) (fun _ => hFit))
      (allocated_pages_ge ..)
  have hBounds := allocated_bounds st data.g0 need data.nodes hOutput.freeList hBump
  have hStrict := allocated_strict_bound st data.g0 need data.nodes hOutput.freeList (fun _ => h32)
  have hBookBytes := arrayAllocated_bytes_in_region st data.g0 need 5
    ⟨data.book, data.bookCapacity⟩ data.nodes hGeo.book48 hOutput.freeList
    hGeo.bookFree hGeo.bookBelow hBump
  have hTradeBytes := arrayAllocated_bytes_in_region st data.g0 need 5
    ⟨data.trades, data.tradesCapacity⟩ data.nodes hGeo.trades48 hOutput.freeList
    hGeo.tradesFree hGeo.tradesBelow hBump
  have hg0 := allocatedStore_top st data.g0 need data.nodes hOutput.global0
  have hg1 := allocatedStore_head st data.g0 need data.nodes hOutput.freeList hOutput.global1
  have hg2 := (FixedArrayAllocate.allocated_count st data.g0 need 5 data.nodes).trans hOutput.global2
  have hGlobalLength : 2 < raw.globals.globals.length := by
    have := List.length_pos_of_mem (List.mem_of_getElem? hg2)
    exact (List.getElem_of_getElem? hg2).1
  refine {
    pages := hPages
    root48 := hBounds.1
    root32 := hStrict
    capacity := allocated_capacity need data.nodes
    fits := ?_
    fresh := arrayAllocated_fresh st data.g0 need 5 data.nodes hOutput.freeList hBump
    bookOwned := ⟨?_, ?_⟩
    tradesOwned := ⟨?_, ?_⟩
    bookSeparated := allocated_region_disjoint data.g0 need ⟨data.book, data.bookCapacity⟩
      data.nodes hGeo.book48 hGeo.bookFree hGeo.bookBelow hBump
    tradesSeparated := allocated_region_disjoint data.g0 need ⟨data.trades, data.tradesCapacity⟩
      data.nodes hGeo.trades48 hGeo.tradesFree hGeo.tradesBelow hBump
    freeList := arrayAllocated_freeList st data.g0 need 5 data.nodes hOutput.freeList hGeo.nodesBelow hBump
    freeSeparated := allocated_node_separated st data.g0 need data.nodes hOutput.freeList
      hGeo.nodesBelow hBump
    global0 := ?_
    global1 := ?_
    global2 := ?_
    global4 := ?_
    global5 := ?_ }
  · simpa only [allocated, FixedArrayAllocateNone.counted, arrayAllocated_pages] using hBounds.2.2
  · exact hOutput.bookOwned.1.frame_region (by have := hGeo.book32; omega) hGeo.book48 hBookBytes
  · exact OrdersAt.frame_region hGeo.book32 hGeo.book48 hGeo.bookCapacity hPages hBookBytes hOutput.bookOwned.2
  · exact hOutput.tradesOwned.1.frame_region (by have := hGeo.trades32; omega) hGeo.trades48 hTradeBytes
  · exact TradesAt.frame_region hGeo.trades32 hGeo.trades48 hGeo.tradesCapacity hPages hTradeBytes hOutput.tradesOwned.2
  · simpa [allocated, FixedArrayAllocateNone.counted, arrayAllocated_globals] using hg0
  · simpa [allocated, FixedArrayAllocateNone.counted, arrayAllocated_globals] using hg1
  · simpa [allocated, FixedArrayAllocateNone.counted] using
      (List.getElem?_set_self (a := .i64 (ctx.expectedG2 + 1)) hGlobalLength)
  · simp only [allocated, FixedArrayAllocateNone.counted, List.getElem?_set, show 2 ≠ 4 by decide,
      ite_false, arrayAllocated_globals, allocatedStore_other_global st data.g0 need data.nodes 4 (by decide) (by decide)]
    exact hOutput.global4
  · simp only [allocated, FixedArrayAllocateNone.counted, List.getElem?_set, show 2 ≠ 5 by decide,
      ite_false, arrayAllocated_globals, allocatedStore_other_global st data.g0 need data.nodes 5 (by decide) (by decide)]
    exact hOutput.global5

#print axioms facts
end Project.ClobLimit.HeapAppendMemory
