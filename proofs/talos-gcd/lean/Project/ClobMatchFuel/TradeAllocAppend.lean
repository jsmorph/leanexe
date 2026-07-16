import Project.ClobMatchFuel.TradeAllocCopy
import Project.ClobMatchFuel.TradeAppendFinish

/-!
# Trade allocation and append

This module composes trade allocation, old-trade copying, and the four stores
that append one match.  Both allocator outcomes retain their bounds, source
ownership, and final outside-payload memory frame.
-/

namespace Project.ClobMatchFuel.TradeAllocAppend

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def tradeAllocAppendProg : Wasm.Program :=
  TradeAllocCopy.tradeAllocCopyProg ++ TradeAppendFinish.tradeFinishProg

def fitFrame (base : Locals) (n : Nat) (choice : FreeChoice) : Locals :=
  TradeAllocSearch.tradeAllocSearchFrame base (tradeArrayBytesU (n + 1))
    choice.previous choice.node.root choice.node.capacity choice.next
    choice.node.root

def bumpFrame (base : Locals) (n : Nat) (g0 previous : UInt64) : Locals :=
  TradeAllocSearch.tradeAllocSearchFrame base (tradeArrayBytesU (n + 1))
    previous 0 (g0 + 48 + tradeArrayBytesU (n + 1))
    ((g0 + 48 + tradeArrayBytesU (n + 1) - 1) / 65536 + 1) (g0 + 48)

set_option Elab.async false in
theorem tradeAllocAppendProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (source sourceCapacity liveBook liveBookCapacity g0 g2 capacity next : UInt64)
    (ts : List TradeL) (trade : TradeL) (liveOrders : List OrderL)
    (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[57]? = some (.i64 source))
    (hOldLengthLocal : base.locals[58]? =
      some (.i64 (UInt64.ofNat ts.length)))
    (hTotalLocal : base.locals[59]? =
      some (.i64 (UInt64.ofNat ts.length * 4)))
    (hNewLengthLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat (ts.length + 1))))
    (hTakerLocal : base.locals[63]? = some (.i64 trade.ttakerId))
    (hMakerLocal : base.locals[64]? = some (.i64 trade.tmakerId))
    (hPriceLocal : base.locals[65]? = some (.i64 trade.tprice))
    (hQtyLocal : base.locals[66]? = some (.i64 trade.tqty))
    (hCapacityLocal : base.locals[72]? = some (.i64 capacity))
    (hNextLocal : base.locals[73]? = some (.i64 next))
    (hn : ts.length + 1 < UInt64.size)
    (hbytes : tradeArrayBytes (ts.length + 1) + 7 < UInt64.size)
    (hTotalU : (UInt64.ofNat ts.length * 4).toNat = ts.length * 4)
    (hTotal64 : ts.length * 4 < UInt64.size)
    (htop : (g0 + 48 + tradeArrayBytesU (ts.length + 1)).toNat =
      g0.toNat + 48 + (tradeArrayBytesU (ts.length + 1)).toNat)
    (hFit32 : g0.toNat + 48 +
      (tradeArrayBytesU (ts.length + 1)).toNat < 4294967296)
    (hFit : g0.toNat + 48 +
      (tradeArrayBytesU (ts.length + 1)).toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hSourceFree :
      FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (hLiveBook48 : 48 ≤ liveBook.toNat)
    (hLiveBook32 :
      liveBook.toNat + fixedArrayBytes liveOrders.length 5 < 4294967296)
    (hLiveBookCapacity :
      fixedArrayBytes liveOrders.length 5 ≤ liveBookCapacity.toNat)
    (hLiveBookBelow :
      liveBook.toNat + liveBookCapacity.toNat ≤ g0.toNat)
    (hLiveBookFree :
      FreeListSeparatedFromFixedArray nodes liveBook liveBookCapacity)
    (hNodesBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat)
    (hOwned : OwnedTradeArrayAt st source sourceCapacity ts)
    (hLiveBookOwned :
      OwnedOrderArrayAt st liveBook liveBookCapacity liveOrders)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hFitDone : ∀ choice : FreeChoice,
      takeFirstFitFrom 0 (tradeArrayBytesU (ts.length + 1)) nodes =
          some choice →
      ∀ st1,
        48 ≤ choice.node.root.toNat →
        choice.node.root.toNat + ((ts.length + 1) * 4 + 1) * 8 <
          4294967296 →
        choice.node.root.toNat + ((ts.length + 1) * 4 + 1) * 8 ≤
          (TradeAllocFit.tradeAllocFitStore st choice).mem.pages * 65536 →
        OwnedTradeArrayAt (TradeAllocFit.tradeAllocFitStore st choice)
          source sourceCapacity ts →
        OwnedTradeArrayAt
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade)
          choice.node.root choice.node.capacity (ts ++ [trade]) →
        OwnedOrderArrayAt
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade)
          liveBook liveBookCapacity liveOrders →
        MemEqOutsideFlatWords (TradeAllocFit.tradeAllocFitStore st choice)
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade)
          choice.node.root ((ts.length + 1) * 4) →
        (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).mem.pages =
          (TradeAllocFit.tradeAllocFitStore st choice).mem.pages →
        (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).globals.globals =
          (TradeAllocFit.tradeAllocFitStore st choice).globals.globals.set
            2 (.i64 (g2 + 1)) →
        FreeListAt
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).mem choice.remaining →
        (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).globals.globals[0]? = some (.i64 g0) →
        (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).globals.globals[1]? =
          some (.i64 (freeHead choice.remaining)) →
        wp «module» rest Q
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade)
          (TradeAppendFinish.tradeResultFrame (fitFrame base ts.length choice)
            choice.node.root (ts.length * 4)) env)
    (hBumpDone : ∀ previous : UInt64, ∀ st1,
      48 ≤ (g0 + 48).toNat →
      (g0 + 48).toNat + ((ts.length + 1) * 4 + 1) * 8 < 4294967296 →
      (g0 + 48).toNat + ((ts.length + 1) * 4 + 1) * 8 ≤
        (TradeAllocBump.tradeAllocBumpStore st g0
          (tradeArrayBytesU (ts.length + 1))).mem.pages * 65536 →
      OwnedTradeArrayAt
        (TradeAllocBump.tradeAllocBumpStore st g0
          (tradeArrayBytesU (ts.length + 1))) source sourceCapacity ts →
      OwnedTradeArrayAt
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length trade)
        (g0 + 48) (tradeArrayBytesU (ts.length + 1)) (ts ++ [trade]) →
      OwnedOrderArrayAt
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length trade)
        liveBook liveBookCapacity liveOrders →
      MemEqOutsideFlatWords
        (TradeAllocBump.tradeAllocBumpStore st g0
          (tradeArrayBytesU (ts.length + 1)))
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length trade)
        (g0 + 48) ((ts.length + 1) * 4) →
      (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
          trade).mem.pages =
        (TradeAllocBump.tradeAllocBumpStore st g0
          (tradeArrayBytesU (ts.length + 1))).mem.pages →
      (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
          trade).globals.globals =
        (TradeAllocBump.tradeAllocBumpStore st g0
          (tradeArrayBytesU (ts.length + 1))).globals.globals.set
            2 (.i64 (g2 + 1)) →
      FreeListAt
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
          trade).mem nodes →
      (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
          trade).globals.globals[0]? =
        some (.i64 (g0 + 48 + tradeArrayBytesU (ts.length + 1))) →
      (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
          trade).globals.globals[1]? = some (.i64 (freeHead nodes)) →
      wp «module» rest Q
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length trade)
        (TradeAppendFinish.tradeResultFrame
          (bumpFrame base ts.length g0 previous) (g0 + 48)
          (ts.length * 4)) env) :
    wp «module» (tradeAllocAppendProg ++ rest) Q st base env := by
  unfold tradeAllocAppendProg
  rw [List.append_assoc]
  apply TradeAllocCopy.tradeAllocCopyProg_spec env st base source
    sourceCapacity g0 g2 capacity next ts nodes hParams hLocals hValues
    hSourceLocal hTotalLocal hNewLengthLocal hCapacityLocal hNextLocal hn
    hbytes hTotalU hTotal64 htop hFit32 hFit hPages hSource48 hSource32
    hSourceCapacity hSourceBelow hSourceFree hOwned hg0 hg1 hg2 hList Q
    (TradeAppendFinish.tradeFinishProg ++ rest)
  · intro choice hTake st1 hTarget48 hTarget32 hTargetFit hOwnedSource hInv
    have hState := hInv
    obtain ⟨_, _, _, hCopyPages, hCopyGlobals, _, _, _, _, _⟩ := hState
    apply TradeAppendFinish.tradeFinishProg_spec env
      (TradeAllocFit.tradeAllocFitStore st choice) st1
      (fitFrame base ts.length choice) choice.node.root source g2
      choice.node.capacity ts trade
    · simpa [fitFrame, TradeAllocSearch.tradeAllocSearchFrame] using hParams
    · simpa [fitFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.length_set] using hLocals
    · simpa [fitFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hOldLengthLocal
    · simpa [fitFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hTakerLocal
    · simpa [fitFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hMakerLocal
    · simpa [fitFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hPriceLocal
    · simpa [fitFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hQtyLocal
    · exact hTarget48
    · exact hTarget32
    · exact hTargetFit
    · exact hOwnedSource.2
    · exact hInv
    · intro hTargetFinal hFreshFinal hOutsideFinal
      have hFinalPages :
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).mem.pages =
          (TradeAllocFit.tradeAllocFitStore st choice).mem.pages := by
        simpa [TradeAppendStore.appendTradeStore] using hCopyPages
      have hFinalGlobals :
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).globals.globals =
          (TradeAllocFit.tradeAllocFitStore st choice).globals.globals.set
            2 (.i64 (g2 + 1)) := by
        simpa [TradeAppendStore.appendTradeStore] using hCopyGlobals
      have hChoiceCapacity := takeFirstFitFrom_some_capacity hTake
      have hNeedNat : (tradeArrayBytesU (ts.length + 1)).toNat =
          tradeArrayBytes (ts.length + 1) :=
        fixedArrayBytesU_toNat (ts.length + 1) 4 hn (by decide) (by
          change fixedArrayBytes (ts.length + 1) 4 + 7 < UInt64.size at hbytes
          omega)
      rw [UInt64.le_iff_toNat_le, hNeedNat] at hChoiceCapacity
      have hLiveBookAlloc : OwnedOrderArrayAt
          (TradeAllocFit.tradeAllocFitStore st choice) liveBook
          liveBookCapacity liveOrders :=
        ownedOrderArrayAt_fixedArrayAllocFitStore hList hTake hLiveBook48
          hLiveBook32 hLiveBookCapacity hLiveBookFree hLiveBookOwned
      have hChoiceMem := takeFirstFitFrom_some_mem hTake
      have hLiveBookChoiceSep := hLiveBookFree choice.node hChoiceMem
      have hPayloadLiveBookSep : regionsDisjoint
          (flatWordsRegion choice.node.root ((ts.length + 1) * 4))
          (fixedArrayRegion liveBook liveBookCapacity) := by
        unfold regionsDisjoint fixedArrayRegion FreeNode.region at hLiveBookChoiceSep
        unfold regionsDisjoint flatWordsRegion fixedArrayRegion
        unfold tradeArrayBytes fixedArrayBytes at hChoiceCapacity
        omega
      have hLiveBookFinal : OwnedOrderArrayAt
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade) liveBook liveBookCapacity liveOrders :=
        OwnedOrderArrayAt.frame_outsideFlatWords hLiveBook48 hLiveBook32
          hLiveBookCapacity hFinalPages hPayloadLiveBookSep hOutsideFinal
          hLiveBookAlloc
      have hFinalList : FreeListAt
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).mem choice.remaining :=
        freeListAt_fixedArrayAllocFitStore_after hList hTake
          (by unfold tradeArrayBytes fixedArrayBytes at hChoiceCapacity; omega)
          hFinalPages hOutsideFinal
      have hAllocG0 := fixedArrayAllocFitStore_global0
        (choice := choice) (stride := 4) hg0
      have hAllocG1 := fixedArrayAllocFitStore_global1
        (choice := choice) (stride := 4) hg1 hList hTake
      have hFinalG0 :
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).globals.globals[0]? = some (.i64 g0) := by
        rw [hFinalGlobals]
        simpa [List.getElem?_set] using hAllocG0
      have hFinalG1 :
          (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
            trade).globals.globals[1]? =
          some (.i64 (freeHead choice.remaining)) := by
        rw [hFinalGlobals]
        simpa [List.getElem?_set] using hAllocG1
      exact hFitDone choice hTake st1 hTarget48 hTarget32 hTargetFit
        hOwnedSource ⟨hFreshFinal, hTargetFinal⟩ hLiveBookFinal hOutsideFinal
        hFinalPages hFinalGlobals hFinalList hFinalG0 hFinalG1
  · intro previous st1 hTarget48 hTarget32 hTargetFit hOwnedSource hInv
    have hState := hInv
    obtain ⟨_, _, _, hCopyPages, hCopyGlobals, _, _, _, _, _⟩ := hState
    apply TradeAppendFinish.tradeFinishProg_spec env
      (TradeAllocBump.tradeAllocBumpStore st g0
        (tradeArrayBytesU (ts.length + 1))) st1
      (bumpFrame base ts.length g0 previous) (g0 + 48) source g2
      (tradeArrayBytesU (ts.length + 1)) ts trade
    · simpa [bumpFrame, TradeAllocSearch.tradeAllocSearchFrame] using hParams
    · simpa [bumpFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.length_set] using hLocals
    · simpa [bumpFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hOldLengthLocal
    · simpa [bumpFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hTakerLocal
    · simpa [bumpFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hMakerLocal
    · simpa [bumpFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hPriceLocal
    · simpa [bumpFrame, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hQtyLocal
    · exact hTarget48
    · exact hTarget32
    · exact hTargetFit
    · exact hOwnedSource.2
    · exact hInv
    · intro hTargetFinal hFreshFinal hOutsideFinal
      have hFinalPages :
          (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
            trade).mem.pages =
          (TradeAllocBump.tradeAllocBumpStore st g0
            (tradeArrayBytesU (ts.length + 1))).mem.pages := by
        simpa [TradeAppendStore.appendTradeStore] using hCopyPages
      have hFinalGlobals :
          (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
            trade).globals.globals =
          (TradeAllocBump.tradeAllocBumpStore st g0
            (tradeArrayBytesU (ts.length + 1))).globals.globals.set
              2 (.i64 (g2 + 1)) := by
        simpa [TradeAppendStore.appendTradeStore] using hCopyGlobals
      have hLiveBookAlloc : OwnedOrderArrayAt
          (TradeAllocBump.tradeAllocBumpStore st g0
            (tradeArrayBytesU (ts.length + 1))) liveBook liveBookCapacity
              liveOrders :=
        ownedOrderArrayAt_fixedArrayAllocBumpStore hFit32 hLiveBook48
          hLiveBook32 hLiveBookCapacity hLiveBookBelow hLiveBookOwned
      have hTargetNat : (g0 + 48).toNat = g0.toNat + 48 := by
        rw [UInt64.toNat_add]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        rw [h48, Nat.mod_eq_of_lt (by omega)]
      have hPayloadLiveBookSep : regionsDisjoint
          (flatWordsRegion (g0 + 48) ((ts.length + 1) * 4))
          (fixedArrayRegion liveBook liveBookCapacity) := by
        unfold regionsDisjoint flatWordsRegion fixedArrayRegion
        right
        rw [hTargetNat]
        omega
      have hLiveBookFinal : OwnedOrderArrayAt
          (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length trade)
          liveBook liveBookCapacity liveOrders :=
        OwnedOrderArrayAt.frame_outsideFlatWords hLiveBook48 hLiveBook32
          hLiveBookCapacity hFinalPages hPayloadLiveBookSep hOutsideFinal
          hLiveBookAlloc
      have hFinalList : FreeListAt
          (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
            trade).mem nodes :=
        freeListAt_fixedArrayAllocBumpStore_after hFit32 hNodesBelow hList
          hFinalPages hOutsideFinal
      have hAllocG0 := fixedArrayAllocBumpStore_global0 st g0
        (tradeArrayBytesU (ts.length + 1)) 4 hg0
      have hAllocG1 := fixedArrayAllocBumpStore_global1 st g0
        (tradeArrayBytesU (ts.length + 1)) 4 (freeHead nodes) hg1
      have hFinalG0 :
          (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
            trade).globals.globals[0]? =
          some (.i64 (g0 + 48 + tradeArrayBytesU (ts.length + 1))) := by
        rw [hFinalGlobals]
        simpa [List.getElem?_set] using hAllocG0
      have hFinalG1 :
          (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
            trade).globals.globals[1]? = some (.i64 (freeHead nodes)) := by
        rw [hFinalGlobals]
        simpa [List.getElem?_set] using hAllocG1
      exact hBumpDone previous st1 hTarget48 hTarget32 hTargetFit
        hOwnedSource ⟨hFreshFinal, hTargetFinal⟩ hLiveBookFinal hOutsideFinal
        hFinalPages hFinalGlobals hFinalList hFinalG0 hFinalG1

end Project.ClobMatchFuel.TradeAllocAppend
