import Project.ClobMatchFuel.PartialFinish

/-!
# Partial-fill trade update

The partial-fill path allocates and appends one trade after producing its
replacement book.  This module composes trade preparation, both allocator
outcomes, the payload stores, and result finalization.  Its postcondition keeps
the semantic result arrays and allocator state while hiding scratch locals.
-/

namespace Project.ClobMatchFuel.PartialTradeUpdate

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def partialTradeUpdateProg : Wasm.Program :=
  PartialTradePrepare.partialTradePrepareProg ++
    TradeAllocAppend.tradeAllocAppendProg ++ PartialFinish.partialFinishProg

def PartialResultAt (s : Locals) (book trades : UInt64) : Prop :=
  s.locals[12]? = some (.i64 book) ∧
  s.locals[13]? = some (.i64 trades) ∧
  s.locals[14]? = some (.i64 0) ∧
  s.locals[15]? = some (.i64 1) ∧
  s.params.length = 9 ∧ s.locals.length = 76 ∧ s.values = []

set_option Elab.async false in
theorem partialTradeUpdateProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (newBook newBookCapacity oldBook oldTrades oldTradesCapacity : UInt64)
    (remaining g0 g2 g4 g5 capacity next : UInt64)
    (taker : OrderL) (os : List OrderL) (ts : List TradeL) (i : Nat)
    (newOrders : List OrderL) (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [.i64 newBook])
    (hTakerLocal : base.locals[0]? = some (.i64 taker.oid))
    (hBookLocal : base.locals[6]? = some (.i64 oldBook))
    (hTradesLocal : base.locals[8]? = some (.i64 oldTrades))
    (hRemainingLocal : base.locals[9]? = some (.i64 remaining))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hCapacityLocal : base.locals[72]? = some (.i64 capacity))
    (hNextLocal : base.locals[73]? = some (.i64 next))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
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
    (hOldTrades48 : 48 ≤ oldTrades.toNat)
    (hOldTrades32 :
      oldTrades.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hOldTradesCapacity :
      fixedArrayBytes ts.length 4 ≤ oldTradesCapacity.toNat)
    (hOldTradesBelow :
      oldTrades.toNat + oldTradesCapacity.toNat ≤ g0.toNat)
    (hOldTradesFree :
      FreeListSeparatedFromFixedArray nodes oldTrades oldTradesCapacity)
    (hNewBook48 : 48 ≤ newBook.toNat)
    (hNewBook32 :
      newBook.toNat + fixedArrayBytes newOrders.length 5 < 4294967296)
    (hNewBookCapacity :
      fixedArrayBytes newOrders.length 5 ≤ newBookCapacity.toNat)
    (hNewBookBelow :
      newBook.toNat + newBookCapacity.toNat ≤ g0.toNat)
    (hNewBookFree :
      FreeListSeparatedFromFixedArray nodes newBook newBookCapacity)
    (hNodesBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat)
    (hOrders : OrdersAt st oldBook os)
    (hOldTradesOwned :
      OwnedTradeArrayAt st oldTrades oldTradesCapacity ts)
    (hNewBookOwned :
      OwnedOrderArrayAt st newBook newBookCapacity newOrders)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s newTrades newTradesCapacity nodes1 g0Final,
      PartialResultAt s newBook newTrades →
      OwnedOrderArrayAt st1 newBook newBookCapacity newOrders →
      OwnedTradeArrayAt st1 newTrades newTradesCapacity
        (ts ++ [Model.fillTradeL taker os[i]! remaining]) →
      FreeListAt st1.mem nodes1 →
      st1.globals.globals[0]? = some (.i64 g0Final) →
      st1.globals.globals[1]? = some (.i64 (freeHead nodes1)) →
      st1.globals.globals[2]? = some (.i64 (g2 + 1)) →
      st1.globals.globals[4]? = some (.i64 g4) →
      st1.globals.globals[5]? = some (.i64 g5) →
      wp «module» rest Q st1 s env) :
    wp «module» (partialTradeUpdateProg ++ rest) Q st base env := by
  let trade := Model.fillTradeL taker os[i]! remaining
  unfold partialTradeUpdateProg
  rw [List.append_assoc, List.append_assoc]
  apply PartialTradePrepare.partialTradePrepareProg_spec env st base newBook
    oldBook oldTrades remaining taker os ts i hParams hLocals hValues
    hTakerLocal hBookLocal hTradesLocal hRemainingLocal hIndexLocal hi
    hOrdersLength64 hOrders hOldTradesOwned.2 Q
    (TradeAllocAppend.tradeAllocAppendProg ++
      PartialFinish.partialFinishProg ++ rest)
  apply TradeAllocAppend.tradeAllocAppendProg_spec env st
    (PartialTradePrepare.partialTradePrepareFrame base newBook oldBook oldTrades
      taker os[i]! remaining i ts)
    oldTrades oldTradesCapacity newBook newBookCapacity g0 g2 capacity next ts
    trade newOrders nodes
  · simpa [PartialTradePrepare.partialTradePrepareFrame] using hParams
  · simpa [PartialTradePrepare.partialTradePrepareFrame, List.length_set] using
      hLocals
  · simp [PartialTradePrepare.partialTradePrepareFrame]
  · simp [PartialTradePrepare.partialTradePrepareFrame, hLocals]
  · simp [PartialTradePrepare.partialTradePrepareFrame, hLocals]
  · simp [PartialTradePrepare.partialTradePrepareFrame, hLocals]
  · simp [PartialTradePrepare.partialTradePrepareFrame, hLocals]
  · simp [PartialTradePrepare.partialTradePrepareFrame, trade,
      Model.fillTradeL, hLocals]
  · simp [PartialTradePrepare.partialTradePrepareFrame, trade,
      Model.fillTradeL, hLocals]
  · simp [PartialTradePrepare.partialTradePrepareFrame, trade,
      Model.fillTradeL, hLocals]
  · simp [PartialTradePrepare.partialTradePrepareFrame, trade,
      Model.fillTradeL, hLocals]
  · simpa [PartialTradePrepare.partialTradePrepareFrame,
      List.getElem?_set, hLocals] using hCapacityLocal
  · simpa [PartialTradePrepare.partialTradePrepareFrame,
      List.getElem?_set, hLocals] using hNextLocal
  · exact hn
  · exact hbytes
  · exact hTotalU
  · exact hTotal64
  · exact htop
  · exact hFit32
  · exact hFit
  · exact hPages
  · exact hOldTrades48
  · exact hOldTrades32
  · exact hOldTradesCapacity
  · exact hOldTradesBelow
  · exact hOldTradesFree
  · exact hNewBook48
  · exact hNewBook32
  · exact hNewBookCapacity
  · exact hNewBookBelow
  · exact hNewBookFree
  · exact hNodesBelow
  · exact hOldTradesOwned
  · exact hNewBookOwned
  · exact hg0
  · exact hg1
  · exact hg2
  · exact hList
  · intro choice hTake st1 hTarget48 hTarget32 hTargetFit hOldTradesAlloc
      hNewTradesOwned hNewBookOwned1 hOutside hFinalPages hFinalGlobals
      hFinalList hFinalG0 hFinalG1
    have hFinalG2 :
        (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
          trade).globals.globals[2]? = some (.i64 (g2 + 1)) := by
      have hAllocG2 :
          (TradeAllocFit.tradeAllocFitStore st choice).globals.globals[2]? =
            some (.i64 g2) := by
        by_cases hPrevious : choice.previous = 0
        · simp only [TradeAllocFit.tradeAllocFitStore,
            BookAllocFit.fixedArrayAllocFitStore, hPrevious, if_pos]
          simpa [List.getElem?_set] using hg2
        · simp [TradeAllocFit.tradeAllocFitStore,
            BookAllocFit.fixedArrayAllocFitStore, hPrevious, hg2]
      have hAllocLength :
          2 < (TradeAllocFit.tradeAllocFitStore st choice).globals.globals.length :=
        (List.getElem?_eq_some_iff.mp hAllocG2).1
      rw [hFinalGlobals]
      simp [hAllocLength]
    have hFinalG4 :
        (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
          trade).globals.globals[4]? = some (.i64 g4) := by
      have hAllocG4 := fixedArrayAllocFitStore_global_of_ne_one st choice 4
        4 (.i64 g4) (by decide) hg4
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG4
    have hFinalG5 :
        (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length
          trade).globals.globals[5]? = some (.i64 g5) := by
      have hAllocG5 := fixedArrayAllocFitStore_global_of_ne_one st choice 4
        5 (.i64 g5) (by decide) hg5
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG5
    apply PartialFinish.partialFinishProg_spec env
      (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length trade)
      (TradeAppendFinish.tradeResultFrame
        (TradeAllocAppend.fitFrame
          (PartialTradePrepare.partialTradePrepareFrame base newBook oldBook
            oldTrades taker os[i]! remaining i ts) ts.length choice)
        choice.node.root (ts.length * 4)) choice.node.root
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.fitFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        PartialTradePrepare.partialTradePrepareFrame] using hParams
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.fitFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        PartialTradePrepare.partialTradePrepareFrame, List.length_set] using
        hLocals
    · simp [TradeAppendFinish.tradeResultFrame]
    · apply hDone
        (TradeAppendStore.appendTradeStore st1 choice.node.root ts.length trade)
        _ choice.node.root choice.node.capacity
        choice.remaining g0
      · simp [PartialResultAt, PartialFinish.partialFinishFrame,
          TradeAppendFinish.tradeResultFrame, TradeAppendCopy.tradeCopyFrame,
          TradeAllocAppend.fitFrame, TradeAllocSearch.tradeAllocSearchFrame,
          PartialTradePrepare.partialTradePrepareFrame, hParams, hLocals]
      · exact hNewBookOwned1
      · simpa [trade] using hNewTradesOwned
      · exact hFinalList
      · exact hFinalG0
      · exact hFinalG1
      · exact hFinalG2
      · exact hFinalG4
      · exact hFinalG5
  · intro previous st1 hTarget48 hTarget32 hTargetFit hOldTradesAlloc
      hNewTradesOwned hNewBookOwned1 hOutside hFinalPages hFinalGlobals
      hFinalList hFinalG0 hFinalG1
    have hFinalG2 :
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
          trade).globals.globals[2]? = some (.i64 (g2 + 1)) := by
      have hAllocG2 :
          (TradeAllocBump.tradeAllocBumpStore st g0
            (tradeArrayBytesU (ts.length + 1))).globals.globals[2]? =
              some (.i64 g2) := by
        simp [TradeAllocBump.tradeAllocBumpStore,
          BookAllocBump.fixedArrayAllocBumpStore, hg2]
      have hAllocLength : 2 <
          (TradeAllocBump.tradeAllocBumpStore st g0
            (tradeArrayBytesU (ts.length + 1))).globals.globals.length :=
        (List.getElem?_eq_some_iff.mp hAllocG2).1
      rw [hFinalGlobals]
      simp [hAllocLength]
    have hFinalG4 :
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
          trade).globals.globals[4]? = some (.i64 g4) := by
      have hAllocG4 := fixedArrayAllocBumpStore_global_of_ne_zero st g0
        (tradeArrayBytesU (ts.length + 1)) 4 4 (.i64 g4) (by decide) hg4
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG4
    have hFinalG5 :
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
          trade).globals.globals[5]? = some (.i64 g5) := by
      have hAllocG5 := fixedArrayAllocBumpStore_global_of_ne_zero st g0
        (tradeArrayBytesU (ts.length + 1)) 4 5 (.i64 g5) (by decide) hg5
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG5
    apply PartialFinish.partialFinishProg_spec env
      (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length trade)
      (TradeAppendFinish.tradeResultFrame
        (TradeAllocAppend.bumpFrame
          (PartialTradePrepare.partialTradePrepareFrame base newBook oldBook
            oldTrades taker os[i]! remaining i ts) ts.length g0 previous)
        (g0 + 48) (ts.length * 4)) (g0 + 48)
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.bumpFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        PartialTradePrepare.partialTradePrepareFrame] using hParams
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.bumpFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        PartialTradePrepare.partialTradePrepareFrame, List.length_set] using
        hLocals
    · simp [TradeAppendFinish.tradeResultFrame]
    · apply hDone
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length trade)
        _ (g0 + 48) (tradeArrayBytesU (ts.length + 1)) nodes
        (g0 + 48 + tradeArrayBytesU (ts.length + 1))
      · simp [PartialResultAt, PartialFinish.partialFinishFrame,
          TradeAppendFinish.tradeResultFrame, TradeAppendCopy.tradeCopyFrame,
          TradeAllocAppend.bumpFrame, TradeAllocSearch.tradeAllocSearchFrame,
          PartialTradePrepare.partialTradePrepareFrame, hParams, hLocals]
      · exact hNewBookOwned1
      · simpa [trade] using hNewTradesOwned
      · exact hFinalList
      · exact hFinalG0
      · exact hFinalG1
      · exact hFinalG2
      · exact hFinalG4
      · exact hFinalG5

end Project.ClobMatchFuel.PartialTradeUpdate
