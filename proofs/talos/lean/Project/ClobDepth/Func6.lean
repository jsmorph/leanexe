import Project.ClobDepth.HeapLoop
import Project.ClobDepth.InitialHeap

namespace Project.ClobDepth.Func6
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation Project.ClobDepth.HeapProof
  Project.ClobDepth.Func6Fold Project.ClobDepth.FoldHeap Project.EulerRiemann.Execution

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

structure Result (initial : Heap) (st0 : Store Unit) (os : List OrderL) (side : UInt64)
    (heap : Heap) (st : Store Unit) (node : FreeNode) : Prop where
  heapAt : heap.At st
  pages : st.mem.pages = st0.mem.pages
  frame : initial.Frame st0 heap st
  owned : OwnsLevels heap st node (depthSideL os side)
  born : Born initial node
  allocations : heap.allocations = initial.allocations + 2 + UInt64.ofNat (matchCount os side os.length)
  retains : heap.retains = initial.retains
  top : heap.top.toNat ≤ initial.top.toNat + 112 + os.length * stepBytes os.length

theorem func6_terminates (env : HostEnv Unit) (st : Store Unit) (heap : Heap)
    (p0 orders side capacity : UInt64) (os : List OrderL)
    (hHeap : heap.At st) (hLen32 : os.length < 4294967296)
    (hBudget32 : heap.top.toNat + 112 + os.length*stepBytes os.length < 4294967296)
    (hBudget : heap.top.toNat + 112 + os.length*stepBytes os.length ≤ st.mem.pages*65536)
    (hPages : st.mem.pages ≤ 65536) (hOrders : OrdersAt st orders os)
    (hOrders32 : orders.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hOrders48 : 48 ≤ orders.toNat)
    (hOrdersCap : fixedArrayBytes os.length 5 ≤ capacity.toNat)
    (hProtected : heap.Protects (orders.toNat-48) (orders.toNat+capacity.toNat)) :
    TerminatesWith env «module» 6 st [.i64 side, .i64 orders, .i64 p0]
      (fun st1 vs => ∃ heap1 node owner, Result heap st os side heap1 st1 node ∧
        vs = [.i64 node.root, .i64 owner]) := by
  let saved : List Value := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 orders, .i64 (UInt64.ofNat os.length), .i64 0, .i64 (UInt64.ofNat os.length), .i64 0, .i64 orders, .i64 0, .i64 0, .i64 0, .i64 0]
  let tail : List Value := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
  let root1 := allocatedRoot heap.top 8 heap.nodes
  let heap1 := heap.allocate 8
  let st1 := initialized st heap 8 0
  let root2 := allocatedRoot heap1.top 8 heap1.nodes
  have hFirst := EmptyHeap.empty_result st heap hHeap (by omega) (by omega)
  have hTop1 := allocate_top_le heap 8 (by change _ + 48 + 8 < _; omega)
  have hFirstPages : st1.mem.pages = st.mem.pages := hFirst.pages
  have hSecond := EmptyHeap.empty_result st1 heap1 hFirst.heapAt
    (by change _ ≤ _ + 48 + 8 at hTop1; dsimp only [heap1]; omega)
    (by rw [hFirstPages]; change _ ≤ _ + 48 + 8 at hTop1; dsimp only [heap1]; omega)
  obtain ⟨⟨hLenRead, hLenBound⟩, hElems⟩ := hOrders
  refine TerminatesWith.of_wp_entry_for (f := func6Def) ?_ ?_
  · simp [«module»]
  · change wp «module» Project.ClobDepth.func6 _ st
      { params := [.i64 p0, .i64 orders, .i64 side], locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0], values := [] } env
    rw [Entry.func6_decomposition]
    simp only [List.append_assoc, Entry.func6EntryProg, List.cons_append, List.nil_append]
    wp_run_with []
    refine ⟨hLenBound, ?_⟩
    rw [hLenRead]
    change wp «module» (Entry.func6AllocProg ++ _) _ st
      (FixedArraySearch.frame [.i64 p0, .i64 orders, .i64 side] saved tail 0 0 0 0 0 0) env
    apply EmptyHeap.alloc_spec env st heap _ saved tail rfl rfl rfl 0 0 0 0 0 0
      hHeap (by omega) (by omega) hPages
    intro prev1 cur1 cap1 next1
    wp_run_with [EmptyHeap.finishFrame, FixedArraySearch.frame, saved, tail]
    let saved1 := ((saved.set 23 (.i64 root1)).set 0 (.i64 root1)).set 1 (.i64 root1)
    change wp «module» (Entry.func6AllocProg ++ _) _ st1
      (FixedArraySearch.frame [.i64 p0, .i64 orders, .i64 side] saved1 tail
        8 prev1 cur1 cap1 next1 root1) env
    apply EmptyHeap.alloc_spec env st1 heap1 _ saved1 tail rfl rfl rfl
      8 prev1 cur1 cap1 next1 root1 hFirst.heapAt
      (by change _ ≤ _ + 48 + 8 at hTop1; dsimp only [heap1]; omega)
      (by rw [hFirstPages]; change _ ≤ _ + 48 + 8 at hTop1; dsimp only [heap1]; omega)
      (by rw [hFirstPages]; exact hPages)
    intro prev2 cur2 cap2 next2
    wp_run_with [EmptyHeap.finishFrame, FixedArraySearch.frame, saved1, saved, tail]
    simp only [Entry.func6MinProg, List.cons_append, List.nil_append]
    wp_run_with [EmptyHeap.finishFrame, FixedArraySearch.frame, saved1, saved, tail]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run_with [EmptyHeap.finishFrame, FixedArraySearch.frame, saved1, saved, tail]
    apply HeapLoop.loop_spec env heap st _ _ _ os side orders root1 capacity hLen32
      hBudget32 hBudget hPages ⟨⟨hLenRead, hLenBound⟩, hElems⟩ hOrders32 hOrders48 hOrdersCap hProtected
    · refine ⟨0, heap1.allocate 8, allocatedNode heap1.top 8 heap1.nodes, root1,
        Nat.zero_le _, rfl, ?_, initial_state heap st os side hHeap (by omega) (by omega)⟩
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro st2 s2 heap2 node owner hParams hLoc hState
      have hP := hLoc.params
      have hL := hLoc.locals
      have hOwner := getElem_of_some hLoc.owner
      have hRoot := getElem_of_some hLoc.root
      simp only [Entry.func6ResultProg]
      simp (config := { maxSteps := 1000000 }) [wp_simp, Locals.get, Locals.set?,
        List.take, List.drop, List.length, List.length_set, func6Def,
        hP, hL, hLoc.values, hOwner, hRoot]
      exact ⟨heap2, node, ⟨hState.heapAt, hState.pages, hState.frame,
        by simpa only [foldLevels_full] using hState.owned, hState.born, hState.allocations, hState.retains, hState.top⟩, rfl⟩

#print axioms func6_terminates
end Project.ClobDepth.Func6
