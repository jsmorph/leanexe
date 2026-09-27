import Project.ClobDepth.Func6

/-! The exported depth function returns two disjoint owned arrays containing
exactly the source side folds.  The valid six-global heap model includes the
free-list and release counters used by the generated cleanup paths. -/
namespace Project.ClobDepth.Func7
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation Project.ClobDepth.HeapProof
  Project.ClobDepth.Func6Fold Project.ClobDepth.FoldHeap Project.EulerRiemann.Execution

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

structure Result (initial : Heap) (st0 st : Store Unit) (os : List OrderL)
    (orders : UInt64) (heap : Heap) (bids asks : FreeNode) : Prop where
  pages : st.mem.pages = st0.mem.pages
  heapAt : heap.At st
  bidsOwned : OwnsLevels heap st bids (depthSideL os 0)
  asksOwned : OwnsLevels heap st asks (depthSideL os 1)
  disjoint : regionsDisjoint bids.region asks.region
  ordersRep : OrdersAt st orders os
  frame : initial.Frame st0 heap st
  allocations : heap.allocations = initial.allocations + 2 + UInt64.ofNat (matchCount os 0 os.length) +
    2 + UInt64.ofNat (matchCount os 1 os.length)
  retains : heap.retains = initial.retains
  top : heap.top.toNat ≤ initial.top.toNat + 224 + 2 * (os.length * stepBytes os.length)

theorem func7_terminates (env : HostEnv Unit) (st : Store Unit) (heap : Heap)
    (orders capacity : UInt64) (os : List OrderL)
    (hHeap : heap.At st) (hLen32 : os.length < 4294967296)
    (hBudget32 : heap.top.toNat + 224 + 2*(os.length*stepBytes os.length) < 4294967296)
    (hBudget : heap.top.toNat + 224 + 2*(os.length*stepBytes os.length) ≤ st.mem.pages*65536)
    (hPages : st.mem.pages ≤ 65536) (hOrders : OrdersAt st orders os)
    (hOrders32 : orders.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hOrders48 : 48 ≤ orders.toNat)
    (hOrdersCap : fixedArrayBytes os.length 5 ≤ capacity.toNat)
    (hProtected : heap.Protects (orders.toNat-48) (orders.toNat+capacity.toNat)) :
    TerminatesWith env «module» 7 st [.i64 orders]
      (fun st2 vs => ∃ heap2 bids asks, Result heap st st2 os orders heap2 bids asks ∧
        vs = [.i64 asks.root, .i64 bids.root]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) ?_ ?_
  · simp [«module»]
  · change wp «module» Project.ClobDepth.func7 _ st
      { params := [.i64 orders],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0], values := [] } env
    simp only [Project.ClobDepth.func7]
    simp (config := { maxSteps := 1000000 }) [wp_simp, Locals.get, Locals.set?, List.length]
    refine wp_call_tw (Func6.func6_terminates env st heap 0 orders 0 capacity os
      hHeap hLen32 (by omega) (by omega) hPages hOrders hOrders32 hOrders48 hOrdersCap hProtected) ?_
    rintro st1 vs ⟨heap1, bids, owner1, hSt1, rfl⟩
    simp (config := { maxSteps := 1000000 }) [wp_simp, Locals.get, Locals.set?, List.length]
    have hOrders1 := OrdersAt.frame_region hOrders32 hOrders48 hOrdersCap hSt1.pages
      (hSt1.frame.bytes _ _ hProtected) hOrders
    have hTop1 := hSt1.top
    refine wp_call_tw (Func6.func6_terminates env st1 heap1 0 orders 1 capacity os
      hSt1.heapAt hLen32 (by omega) (by rw [hSt1.pages]; omega)
      (by rw [hSt1.pages]; exact hPages) hOrders1 hOrders32 hOrders48 hOrdersCap
      (hSt1.frame.protects _ _ hProtected)) ?_
    rintro st2 vs2 ⟨heap2, asks, owner2, hSt2, rfl⟩
    simp (config := { maxSteps := 1000000 }) [wp_simp, Locals.get, Locals.set?,
      List.take, List.drop, List.length, func7Def, Function.numParams]
    refine ⟨heap2, bids, asks, ?_, ⟨rfl, rfl⟩⟩
    refine ⟨hSt2.pages.trans hSt1.pages, hSt2.heapAt,
      hSt1.owned.frame hSt2.frame hSt2.pages hSt2.heapAt, hSt2.owned, ?_, ?_,
      hSt1.frame.trans hSt2.frame, hSt2.allocations.trans (by rw [hSt1.allocations]),
      hSt2.retains.trans hSt1.retains, ?_⟩
    · have hSep := hSt2.born _ _ hSt1.owned.protects
      have hBids := hSt1.owned.buffer.rootBound
      have hAsks := hSt2.owned.buffer.rootBound
      unfold regionsDisjoint FreeNode.region
      omega
    · exact OrdersAt.frame_region hOrders32 hOrders48 hOrdersCap
        (hSt2.pages.trans hSt1.pages) ((hSt1.frame.trans hSt2.frame).bytes _ _ hProtected) hOrders
    · have := hSt2.top
      omega

#print axioms func7_terminates
end Project.ClobDepth.Func7
