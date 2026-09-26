import Project.ClobDepth.FoldHeap

namespace Project.ClobDepth.HeapLoop
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation Project.ClobDepth.HeapProof
  Project.ClobDepth.Func6Fold Project.ClobDepth.FoldHeap Project.EulerRiemann.Execution

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

structure LoopLocalsAt (s : Locals) (side orders owner root saved : UInt64)
    (k count : Nat) : Prop where
  params : s.params.length = 3
  locals : s.locals.length = 44
  values : s.values = []
  side : s.params[2]? = some (.i64 side)
  orders : s.locals[18]? = some (.i64 orders)
  owner : s.locals[1]? = some (.i64 owner)
  root : s.locals[2]? = some (.i64 root)
  saved : s.locals[26]? = some (.i64 saved)
  cursor : s.locals[20]? = some (.i64 (UInt64.ofNat k))
  limit : s.locals[22]? = some (.i64 (UInt64.ofNat count))

def Invariant (initial : Heap) (st0 : Store Unit) (base : Locals) (os : List OrderL)
    (side orders saved : UInt64) : AssertionF Unit := fun st s =>
  ∃ k heap node owner, k ≤ os.length ∧ s.params = base.params ∧
    LoopLocalsAt s side orders owner node.root saved k os.length ∧
    State initial st0 os side saved heap st node owner k

def measure (count : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals[20]? with
  | some (Value.i64 k) => count - k.toNat
  | _ => 0

theorem loop_spec (env : HostEnv Unit) (initial : Heap) (st0 stI : Store Unit)
    (base sI : Locals) (os : List OrderL) (side orders saved capacity : UInt64)
    (hLen32 : os.length < 4294967296)
    (hBudget32 : initial.top.toNat + 112 + os.length * stepBytes os.length < 4294967296)
    (hBudget : initial.top.toNat + 112 + os.length * stepBytes os.length ≤ st0.mem.pages * 65536)
    (hPages : st0.mem.pages ≤ 65536)
    (hOrders : OrdersAt st0 orders os)
    (hOrders32 : orders.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hOrders48 : 48 ≤ orders.toNat)
    (hOrdersCap : fixedArrayBytes os.length 5 ≤ capacity.toNat)
    (hProtected : initial.Protects (orders.toNat-48) (orders.toNat+capacity.toNat))
    (Q : Assertion Unit) (rest : Program)
    (hInv : Invariant initial st0 base os side orders saved stI sI)
    (hDone : ∀ st1 s1 heap node owner, s1.params = base.params →
      LoopLocalsAt s1 side orders owner node.root saved os.length os.length →
      State initial st0 os side saved heap st1 node owner os.length →
      wp «module» rest Q st1 s1 env) :
    wp «module» (.block 0 0 [.loop 0 0 Entry.func6BodyProg] :: rest) Q stI sI env := by
  let count := os.length
  have hCount32 : count < 4294967296 := hLen32
  have hV0 : sI.values = [] := by
    obtain ⟨_, _, _, _, _, _, hLoc, _⟩ := hInv
    exact hLoc.values
  apply wp_block_cons
  apply wp_loop_cons (Inv := Invariant initial st0 base os side orders saved) (μ := measure count)
  · exact hInv
  · rintro st1 s1 ⟨k, heap, node, owner, hkle, hParamsEq, hLocals, hState⟩
    have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
    have hCountU : (UInt64.ofNat count).toNat = count := by u64_omega
    have hP := hLocals.params
    have hL := hLocals.locals
    have hV := hLocals.values
    have hSide' := getElem_of_some hLocals.side
    have hOrders' := getElem_of_some hLocals.orders
    have hOwner' := getElem_of_some hLocals.owner
    have hRoot' := getElem_of_some hLocals.root
    have hSaved' := getElem_of_some hLocals.saved
    have hCursor' := getElem_of_some hLocals.cursor
    have hLimit' := getElem_of_some hLocals.limit
    have hOrdersNow := OrdersAt.frame_region hOrders32 hOrders48 hOrdersCap hState.pages
      (hState.frame.bytes _ _ hProtected) hOrders
    simp only [Entry.func6BodyProg]
    wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
    try simp
    by_cases hEnd : k = count
    · have hge : UInt64.ofNat k ≥ UInt64.ofNat count := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hCountU]
        omega
      rw [if_pos hge]
      try simp
      subst k
      rw [hV0]
      exact hDone st1 ⟨s1.params, s1.locals, []⟩ heap node owner hParamsEq
        ⟨hP, hL, rfl, hLocals.side, hLocals.orders, hLocals.owner,
          hLocals.root, hLocals.saved, hLocals.cursor, hLocals.limit⟩ hState
    · have hklt : k < count := Nat.lt_of_le_of_ne hkle hEnd
      have hkos : k < os.length := by omega
      have hnge : ¬(UInt64.ofNat k ≥ UInt64.ofNat count) := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hCountU]
        omega
      rw [if_neg hnge]
      wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
      try simp
      obtain ⟨⟨hOidR, hOidB⟩, ⟨hTraderR, hTraderB⟩, ⟨hSideR, hSideB⟩,
        ⟨hPriceR, hPriceB⟩, ⟨hQtyR, hQtyB⟩⟩ := hOrdersNow.2 k hkos
      rw [if_neg (Nat.not_lt.mpr hOidB), hOidR,
        if_neg (Nat.not_lt.mpr hTraderB), hTraderR,
        if_neg (Nat.not_lt.mpr hSideB), hSideR,
        if_neg (Nat.not_lt.mpr hPriceB), hPriceR,
        if_neg (Nat.not_lt.mpr hQtyB), hQtyR]
      have hLenLe := (foldLevels_length_le os side k (by omega)).trans (matchCount_le os side k)
      have hTop := hState.top
      have hMul : (k+1)*stepBytes os.length ≤ os.length*stepBytes os.length :=
        Nat.mul_le_mul_right _ (by omega)
      have hRoom : heap.top.toNat + 48 + fixedArrayBytes ((foldLevels os side k).length+1) 2 ≤
          initial.top.toNat + 112 + os.length*stepBytes os.length := by
        rw [Nat.succ_mul] at hMul
        unfold stepBytes fixedArrayBytes at *
        omega
      have hkAdd : UInt64.ofNat k + 1 = UInt64.ofNat (k+1) := by
        apply UInt64.toNat.inj
        rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
          toNat_ofNat_lt (by rw [size_eq]; omega)]
      have hk1U : (UInt64.ofNat (k+1)).toNat = k+1 := by u64_omega
      by_cases hMatch : os[k]!.oside = side
      · rw [if_pos hMatch]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
        try simp
        have hCall := Func3Heap.func3_terminates env st1 heap owner os[k]!.oprice os[k]!.oqty node
          (foldLevels os side k) (by omega) hState.heapAt hState.owned
          (by omega) (by rw [hState.pages]; omega) (by rw [hState.pages]; exact hPages)
        simp only [← List.getElem!_eq_getElem?_getD]
        refine wp_call_tw hCall ?_
        intro st2 vs ⟨hUpdate, hvs⟩
        subst hvs
        let need := Func3.capacity (foldLevels os side k) os[k]!.oprice os[k]!.oqty
        let fresh := allocatedNode heap.top need heap.nodes
        have hStep := hState.update hkos hMatch hBudget32 hUpdate
        wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
        try simp
        simp only [← List.getElem!_eq_getElem?_getD]
        by_cases hSaved : owner = saved
        · simp only [hSaved, ite_self, if_pos, UInt32.zero_and, UInt32.and_zero]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          simp only [hSaved, if_pos] at hStep
          wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
          try simp
          refine ⟨⟨k+1, _, fresh, fresh.root, by omega, hParamsEq, ?_, hStep⟩, ?_⟩
          · refine ⟨hP, ?_, rfl, hLocals.side, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp (config := { maxSteps := 1000000 }) [List.length_set, hL, hOrders',
                hSaved', hLimit', fresh, need, allocatedNode]
          · simp (config := { maxSteps := 1000000 }) [measure, List.length_set, hL, hCursor', hk1U]
            omega
        · have hOwner : owner = node.root := hState.owner.resolve_left hSaved
          have hNonzero : owner ≠ 0 := by
            intro hZero
            have := hState.owned.buffer.rootBound
            rw [← hOwner, hZero] at this
            contradiction
          have hNeedLe := capacity_le (foldLevels os side k) os[k]!.oprice os[k]!.oqty (by omega)
          have hSep := allocated_region_disjoint heap.top need node heap.nodes
            hState.owned.buffer.rootBound hState.owned.separated hState.owned.below
            (fun _ => by dsimp only [need]; omega)
          have hDifferent : owner ≠ allocatedRoot heap.top need heap.nodes := by
            intro hEq
            have hRoot := hState.owned.buffer.rootBound
            have hCap := hState.owned.buffer.capacity
            unfold fixedArrayBytes at hCap
            simp only [regionsDisjoint, FreeNode.region, allocatedNode] at hSep
            rw [← hOwner, hEq] at hRoot hSep
            omega
          dsimp only [need] at hDifferent
          simp only [if_neg hSaved, if_neg hNonzero, if_neg hDifferent]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by decide)]
          wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
          have hOld := hState.owned.frame hUpdate.frame hUpdate.pages hUpdate.heapAt
          rw [hOwner]
          refine wp_call_tw (release_exact env st2 (heap.allocate need) node
            (foldLevels os side k) hUpdate.heapAt hOld) ?_
          rintro st3 vs ⟨rfl, rfl⟩
          simp only [if_neg hSaved] at hStep
          wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
          try simp
          refine ⟨⟨k+1, _, fresh, fresh.root, by omega, hParamsEq, ?_, hStep⟩, ?_⟩
          · refine ⟨hP, ?_, rfl, hLocals.side, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp (config := { maxSteps := 1000000 }) [List.length_set, hL, hOrders',
                hSaved', hLimit', fresh, need, allocatedNode]
          · simp (config := { maxSteps := 1000000 }) [measure, List.length_set, hL, hCursor', hk1U]
            omega
      · rw [if_neg hMatch]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hP, hL, hV, hSide', hOrders', hOwner', hRoot', hCursor', hLimit', hSaved']
        try simp
        refine ⟨⟨k+1, heap, node, owner, by omega, hParamsEq, ?_, hState.skip hkos hMatch⟩, ?_⟩
        · refine ⟨hP, ?_, rfl, hLocals.side, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp (config := { maxSteps := 1000000 }) [List.length_set, hL, hOrders',
              hOwner', hRoot', hSaved', hLimit']
        · simp (config := { maxSteps := 1000000 }) [measure, List.length_set, hL, hCursor', hk1U]
          omega

#print axioms loop_spec
end Project.ClobDepth.HeapLoop
