import Project.ClobMatchFuel.FullReleaseTransition

/-!
# Complete full-fill step

A full-fill step allocates both replacement arrays, releases the reachable
tracked source allocation, and updates the recursive locals.  The postcondition
contains the state needed by the next loop iteration.
-/

namespace Project.ClobMatchFuel.FullStep

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame
  Project.ClobMatchFuel.ReleaseFrame

def fullStepProg : Wasm.Program :=
  FullBranch.fullBranchProg ++
    FullReleaseTransition.fullReleaseTransitionProg

def releaseCount (tracker : UInt64) : UInt64 :=
  if tracker = 0 then 0 else 1

set_option Elab.async false in
theorem fullStepProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel book bookCapacity oldTrades oldTradesCapacity remaining : UInt64)
    (g0 g2 g4 g5 capacity next tradeNext oldTradesTracker : UInt64)
    (taker : OrderL) (os : List OrderL) (ts : List TradeL) (i : Nat)
    (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hTakerLocal : base.locals[0]? = some (.i64 taker.oid))
    (hBookLocal : base.locals[6]? = some (.i64 book))
    (hTradesLocal : base.locals[8]? = some (.i64 oldTrades))
    (hRemainingLocal : base.locals[9]? = some (.i64 remaining))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hSourceLocal : base.locals[57]? = some (.i64 book))
    (hPrefixLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat (i * 5))))
    (hSuffixLocal : base.locals[61]? =
      some (.i64 (UInt64.ofNat ((os.length - 1 - i) * 5))))
    (hLengthLocal : base.locals[62]? =
      some (.i64 (UInt64.ofNat (os.length - 1))))
    (hCapacityLocal : base.locals[70]? = some (.i64 capacity))
    (hNextLocal : base.locals[71]? = some (.i64 next))
    (hTradeNextLocal : base.locals[73]? = some (.i64 tradeNext))
    (hFuel : base.get 0 = some (.i64 fuel))
    (hOldBookTracker : base.get 19 = some (.i64 0))
    (hOldTradesTracker : base.get 20 = some (.i64 oldTradesTracker))
    (hCarryOid : base.get 34 = some (.i64 taker.oid))
    (hCarryTrader : base.get 35 = some (.i64 taker.otrader))
    (hCarrySide : base.get 36 = some (.i64 taker.oside))
    (hCarryPrice : base.get 37 = some (.i64 taker.oprice))
    (hCarryQty : base.get 38 = some (.i64 taker.oqty))
    (hTracker : oldTradesTracker = 0 ∨ oldTradesTracker = oldTrades)
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hErasedLength64 : os.length - 1 < UInt64.size)
    (hOrderWords64 : os.length * 5 < UInt64.size)
    (hBookBytes : orderArrayBytes (os.length - 1) + 7 < UInt64.size)
    (hBookTop : (g0 + 48 + orderArrayBytesU (os.length - 1)).toNat =
      g0.toNat + 48 + (orderArrayBytesU (os.length - 1)).toNat)
    (hBookFit32 : g0.toNat + 48 +
      (orderArrayBytesU (os.length - 1)).toNat < 4294967296)
    (hBookFit : g0.toNat + 48 +
      (orderArrayBytesU (os.length - 1)).toNat ≤ st.mem.pages * 65536)
    (hTradeLength64 : ts.length + 1 < UInt64.size)
    (hTradeBytes : tradeArrayBytes (ts.length + 1) + 7 < UInt64.size)
    (hTradeTotalU : (UInt64.ofNat ts.length * 4).toNat = ts.length * 4)
    (hTradeTotal64 : ts.length * 4 < UInt64.size)
    (hTradeTopAtG0 : (g0 + 48 + tradeArrayBytesU (ts.length + 1)).toNat =
      g0.toNat + 48 + (tradeArrayBytesU (ts.length + 1)).toNat)
    (hTradeFit32AtG0 : g0.toNat + 48 +
      (tradeArrayBytesU (ts.length + 1)).toNat < 4294967296)
    (hTradeFitAtG0 : g0.toNat + 48 +
      (tradeArrayBytesU (ts.length + 1)).toNat ≤ st.mem.pages * 65536)
    (hTradeTopAfterBook :
      (g0 + 48 + orderArrayBytesU (os.length - 1) + 48 +
          tradeArrayBytesU (ts.length + 1)).toNat =
        (g0 + 48 + orderArrayBytesU (os.length - 1)).toNat + 48 +
          (tradeArrayBytesU (ts.length + 1)).toNat)
    (hTradeFit32AfterBook :
      (g0 + 48 + orderArrayBytesU (os.length - 1)).toNat + 48 +
        (tradeArrayBytesU (ts.length + 1)).toNat < 4294967296)
    (hTradeFitAfterBook :
      (g0 + 48 + orderArrayBytesU (os.length - 1)).toNat + 48 +
          (tradeArrayBytesU (ts.length + 1)).toNat ≤
        st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hBook48 : 48 ≤ book.toNat)
    (hBook32 : book.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes os.length 5 ≤ bookCapacity.toNat)
    (hBookBelow : book.toNat + bookCapacity.toNat ≤ g0.toNat)
    (hBookFree : FreeListSeparatedFromFixedArray nodes book bookCapacity)
    (hOldTrades48 : 48 ≤ oldTrades.toNat)
    (hOldTrades32 :
      oldTrades.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hOldTradesCapacity :
      fixedArrayBytes ts.length 4 ≤ oldTradesCapacity.toNat)
    (hOldTradesBelow :
      oldTrades.toNat + oldTradesCapacity.toNat ≤ g0.toNat)
    (hOldTradesFree :
      FreeListSeparatedFromFixedArray nodes oldTrades oldTradesCapacity)
    (hNodesBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat)
    (hBookOwned : OwnedOrderArrayAt st book bookCapacity os)
    (hOldTradesOwned :
      OwnedTradeArrayAt st oldTrades oldTradesCapacity ts)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s newBook newBookCapacity newTrades newTradesCapacity
        nodes1 g0Final,
      OwnedOrderArrayAt st1 newBook newBookCapacity (os.eraseIdx i) →
      OwnedTradeArrayAt st1 newTrades newTradesCapacity
        (ts ++ [Model.fillTradeL taker os[i]! os[i]!.oqty]) →
      FreeListAt st1.mem nodes1 →
      st1.globals.globals[0]? = some (.i64 g0Final) →
      st1.globals.globals[1]? = some (.i64 (freeHead nodes1)) →
      st1.globals.globals[2]? = some (.i64 (g2 + 2)) →
      st1.globals.globals[4]? =
        some (.i64 (g4 + releaseCount oldTradesTracker)) →
      st1.globals.globals[5]? =
        some (.i64 (g5 + releaseCount oldTradesTracker)) →
      wp «module» rest Q st1
        (FullTransition.fullTransitionFrame s fuel taker newBook newTrades
          (remaining - os[i]!.oqty) 0 oldTradesTracker) env) :
    wp «module» (fullStepProg ++ rest) Q st base env := by
  unfold fullStepProg
  rw [List.append_assoc]
  apply FullBranch.fullBranchProg_spec env st base fuel book bookCapacity
    oldTrades oldTradesCapacity remaining g0 g2 g4 g5 capacity next tradeNext 0
    oldTradesTracker taker os ts i nodes hParams hLocals hValues hTakerLocal
    hBookLocal hTradesLocal hRemainingLocal hIndexLocal hSourceLocal hPrefixLocal
    hSuffixLocal hLengthLocal hCapacityLocal hNextLocal hTradeNextLocal hFuel
    hOldBookTracker hOldTradesTracker hCarryOid hCarryTrader hCarrySide
    hCarryPrice hCarryQty hi hOrdersLength64 hErasedLength64 hOrderWords64
    hBookBytes hBookTop hBookFit32 hBookFit hTradeLength64 hTradeBytes
    hTradeTotalU hTradeTotal64 hTradeTopAtG0 hTradeFit32AtG0 hTradeFitAtG0
    hTradeTopAfterBook hTradeFit32AfterBook hTradeFitAfterBook hPages hBook48
    hBook32 hBookCapacity hBookBelow hBookFree hOldTrades48 hOldTrades32
    hOldTradesCapacity hOldTradesBelow hOldTradesFree hNodesBelow hBookOwned
    hOldTradesOwned hg0 hg1 hg2 hg4 hg5 hList Q
    (FullReleaseTransition.fullReleaseTransitionProg ++ rest)
  intro st1 s newBook newBookCapacity newTrades newTradesCapacity nodes1 g0Final
    hResult hNewBookOwned hNewTradesOwned hOldTradesOwned1 hBookOwned1
    hNewBook48 hNewBook32 hNewBookCapacity hNewTrades48 hNewTrades32
    hNewTradesCapacity hList1 hPageEq hOldTradesNewBook hOldTradesNewTrades
    hOldTradesNodes hG0 hG1 hG2 hG4 hG5
  rcases hTracker with hNoTracker | hTradeTracker
  · subst oldTradesTracker
    apply FullReleaseTransition.fullReleaseTransitionProg_none env st1 s fuel
      newBook newTrades (remaining - os[i]!.oqty) taker hResult Q rest
    apply hDone st1 s newBook newBookCapacity newTrades newTradesCapacity nodes1
      g0Final hNewBookOwned hNewTradesOwned hList1 hG0 hG1 hG2
    · simpa [releaseCount] using hG4
    · simpa [releaseCount] using hG5
  · subst oldTradesTracker
    have hOldTradesNe : oldTrades ≠ 0 := by
      intro h
      subst oldTrades
      simp at hOldTrades48
    have hOldTradesFull32 :
        oldTrades.toNat + oldTradesCapacity.toNat < 4294967296 := by
      omega
    have hOldTradesFit : oldTrades.toNat + oldTradesCapacity.toNat ≤
        st1.mem.pages * 65536 := by
      rw [hPageEq]
      omega
    apply FullReleaseTransition.fullReleaseTransitionProg_trade env st1 s fuel
      oldTrades oldTradesCapacity newBook newBookCapacity newTrades
      newTradesCapacity (remaining - os[i]!.oqty) g4 g5 taker ts
      (ts ++ [Model.fillTradeL taker os[i]! os[i]!.oqty]) (os.eraseIdx i)
      nodes1 hResult hOldTrades48 hOldTradesFull32 hOldTradesFit
      hOldTradesCapacity hNewBook48 hNewBook32 hNewBookCapacity hNewTrades48
      hNewTrades32 hNewTradesCapacity hOldTradesOwned1 hNewBookOwned
      hNewTradesOwned hOldTradesNewBook hOldTradesNewTrades hOldTradesNodes
      hList1 hG1 hG4 hG5 Q rest
    intro st2 hMem hGlobals hNewBookOwned2 hNewTradesOwned2 hList2
    have hLength : 5 < st1.globals.globals.length :=
      (List.getElem?_eq_some_iff.mp hG5).1
    have hG0After : st2.globals.globals[0]? = some (.i64 g0Final) := by
      rw [hGlobals]
      exact fixedArrayReleaseGlobals_get_of_ne st1 oldTrades g4 g5 0
        (.i64 g0Final) (by decide) (by decide) (by decide) hG0
    have hG1After : st2.globals.globals[1]? = some (.i64 oldTrades) := by
      rw [hGlobals]
      exact fixedArrayReleaseGlobals_global1 st1 oldTrades g4 g5 (by omega)
    have hG2After : st2.globals.globals[2]? = some (.i64 (g2 + 2)) := by
      rw [hGlobals]
      exact fixedArrayReleaseGlobals_get_of_ne st1 oldTrades g4 g5 2
        (.i64 (g2 + 2)) (by decide) (by decide) (by decide) hG2
    have hG4After : st2.globals.globals[4]? = some (.i64 (g4 + 1)) := by
      rw [hGlobals]
      exact fixedArrayReleaseGlobals_global4 st1 oldTrades g4 g5 (by omega)
    have hG5After : st2.globals.globals[5]? = some (.i64 (g5 + 1)) := by
      rw [hGlobals]
      exact fixedArrayReleaseGlobals_global5 st1 oldTrades g4 g5 hLength
    apply hDone st2 s newBook newBookCapacity newTrades newTradesCapacity
      (releasedNode oldTrades oldTradesCapacity :: nodes1) g0Final
      hNewBookOwned2 hNewTradesOwned2 hList2 hG0After hG1After hG2After
    · simpa [releaseCount, hOldTradesNe] using hG4After
    · simpa [releaseCount, hOldTradesNe] using hG5After

end Project.ClobMatchFuel.FullStep
