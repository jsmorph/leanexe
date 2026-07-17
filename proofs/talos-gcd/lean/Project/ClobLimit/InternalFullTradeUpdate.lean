import Project.ClobLimit.InternalFullTradeFinish
import Project.ClobLimit.InternalPartialTradeUpdate
import Project.ClobLimit.InternalIteration

/-!
# Complete full-trade update

The full-fill trade phase prepares the maker trade, reuses the shared
stride-four allocation and append theorem, and computes the next remaining
quantity.  Its postcondition retains all four live arrays and the exact
allocator state.  The resulting locals form the input to the recursive
transition.
-/

namespace Project.ClobLimit.InternalFullTradeUpdate

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobMatchFuel.AllocatorFrame
  Project.ClobLimit.InternalFullTradePrepare
  Project.ClobLimit.InternalFullTradeFinish
  Project.ClobLimit.InternalPartialTradeUpdate
  Project.ClobLimit.InternalPartialTradeCopy
  Project.ClobLimit.InternalPartialTradeFinish

def fullTradeUpdateProg : Wasm.Program :=
  fullTradePrepareProg ++ partialTradeUpdateProg ++ fullTradeFinishProg

def FullTradeResultAt (s : Locals) (fuel : UInt64) (taker : OrderL)
    (book trades remaining : UInt64) : Prop :=
  s.params.length = 11 ∧ s.locals.length = 64 ∧ s.values = [] ∧
  s.get 0 = some (.i64 fuel) ∧
  s.get 26 = some (.i64 taker.oid) ∧
  s.get 27 = some (.i64 taker.otrader) ∧
  s.get 28 = some (.i64 taker.oside) ∧
  s.get 29 = some (.i64 taker.oprice) ∧
  s.get 30 = some (.i64 taker.oqty) ∧
  s.get 36 = some (.i64 book) ∧
  s.get 37 = some (.i64 book) ∧
  s.get 38 = some (.i64 trades) ∧
  s.get 39 = some (.i64 trades) ∧
  s.get 40 = some (.i64 remaining) ∧
  InternalIteration.AllocScratchAt s

set_option Elab.async false in
theorem fullTradeUpdateProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel newBook newBookCapacity oldBook oldBookCapacity : UInt64)
    (oldTrades oldTradesCapacity remaining g0 g2 capacity next : UInt64)
    (taker : OrderL) (oldOrders newOrders : List OrderL)
    (ts : List TradeL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [.i64 newBook])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hCarryOid : base.get 26 = some (.i64 taker.oid))
    (hCarryTrader : base.get 27 = some (.i64 taker.otrader))
    (hCarrySide : base.get 28 = some (.i64 taker.oside))
    (hCarryPrice : base.get 29 = some (.i64 taker.oprice))
    (hCarryQty : base.get 30 = some (.i64 taker.oqty))
    (hTakerLocal : base.params[1]? = some (.i64 taker.oid))
    (hBookLocal : base.params[7]? = some (.i64 oldBook))
    (hTradesLocal : base.params[9]? = some (.i64 oldTrades))
    (hRemainingLocal : base.params[10]? = some (.i64 remaining))
    (hIndexLocal : base.locals[14]? = some (.i64 (UInt64.ofNat i)))
    (hCapacityLocal : base.locals[60]? = some (.i64 capacity))
    (hNextLocal : base.locals[61]? = some (.i64 next))
    (hi : i < oldOrders.length)
    (hOrdersLength64 : oldOrders.length < UInt64.size)
    (hn : ts.length + 1 < UInt64.size)
    (hbytes : fixedArrayBytes (ts.length + 1) 4 + 7 < UInt64.size)
    (hTotalU : (UInt64.ofNat ts.length * 4).toNat = ts.length * 4)
    (hTotal64 : ts.length * 4 < UInt64.size)
    (hTop : (g0 + 48 + fixedArrayBytesU (ts.length + 1) 4).toNat =
      g0.toNat + 48 + (fixedArrayBytesU (ts.length + 1) 4).toNat)
    (hFit32 : g0.toNat + 48 +
      (fixedArrayBytesU (ts.length + 1) 4).toNat < 4294967296)
    (hFit : g0.toNat + 48 +
      (fixedArrayBytesU (ts.length + 1) 4).toNat ≤
        st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hOldBook48 : 48 ≤ oldBook.toNat)
    (hOldBook32 : oldBook.toNat +
      fixedArrayBytes oldOrders.length 5 < 4294967296)
    (hOldBookCapacity :
      fixedArrayBytes oldOrders.length 5 ≤ oldBookCapacity.toNat)
    (hOldBookBelow : oldBook.toNat + oldBookCapacity.toNat ≤ g0.toNat)
    (hOldBookOwned :
      OwnedOrderArrayAt st oldBook oldBookCapacity oldOrders)
    (hNewBook48 : 48 ≤ newBook.toNat)
    (hNewBook32 : newBook.toNat +
      fixedArrayBytes newOrders.length 5 < 4294967296)
    (hNewBookCapacity :
      fixedArrayBytes newOrders.length 5 ≤ newBookCapacity.toNat)
    (hNewBookBelow : newBook.toNat + newBookCapacity.toNat ≤ g0.toNat)
    (hNewBookOwned :
      OwnedOrderArrayAt st newBook newBookCapacity newOrders)
    (hOldTrades48 : 48 ≤ oldTrades.toNat)
    (hOldTrades32 : oldTrades.toNat +
      fixedArrayBytes ts.length 4 < 4294967296)
    (hOldTradesCapacity :
      fixedArrayBytes ts.length 4 ≤ oldTradesCapacity.toNat)
    (hOldTradesBelow :
      oldTrades.toNat + oldTradesCapacity.toNat ≤ g0.toNat)
    (hOldTradesOwned :
      OwnedTradeArrayAt st oldTrades oldTradesCapacity ts)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s,
      FullTradeResultAt s fuel taker newBook (g0 + 48)
        (remaining - oldOrders[i]!.oqty) →
      OwnedOrderArrayAt st1 oldBook oldBookCapacity oldOrders →
      OwnedOrderArrayAt st1 newBook newBookCapacity newOrders →
      OwnedTradeArrayAt st1 oldTrades oldTradesCapacity ts →
      OwnedTradeArrayAt st1 (g0 + 48)
        (fixedArrayBytesU (ts.length + 1) 4)
        (ts ++ [Project.ClobMatchFuel.Model.fillTradeL
          taker oldOrders[i]! oldOrders[i]!.oqty]) →
      MemEqOutsideFlatWords
        (partialTradeAllocStore st (ts.length + 1) g0) st1
        (g0 + 48) ((ts.length + 1) * 4) →
      st1.mem.pages = st.mem.pages →
      st1.globals.globals =
        (partialTradeAllocStore st (ts.length + 1) g0).globals.globals.set 2
          (.i64 (g2 + 1)) →
      wp «module» rest Q st1 s env) :
    wp «module» (fullTradeUpdateProg ++ rest) Q st base env := by
  let trade := Project.ClobMatchFuel.Model.fillTradeL
    taker oldOrders[i]! oldOrders[i]!.oqty
  have hFuelAt : base.params[0]? = some (.i64 fuel) := by
    simpa [Locals.get, hParams] using hFuel
  have hCarryOidAt : base.locals[15]? = some (.i64 taker.oid) := by
    simpa [Locals.get, hParams, hLocals] using hCarryOid
  have hCarryTraderAt : base.locals[16]? = some (.i64 taker.otrader) := by
    simpa [Locals.get, hParams, hLocals] using hCarryTrader
  have hCarrySideAt : base.locals[17]? = some (.i64 taker.oside) := by
    simpa [Locals.get, hParams, hLocals] using hCarrySide
  have hCarryPriceAt : base.locals[18]? = some (.i64 taker.oprice) := by
    simpa [Locals.get, hParams, hLocals] using hCarryPrice
  have hCarryQtyAt : base.locals[19]? = some (.i64 taker.oqty) := by
    simpa [Locals.get, hParams, hLocals] using hCarryQty
  have hFuelElem : base.params[0] = .i64 fuel :=
    (List.getElem?_eq_some_iff.mp hFuelAt).2
  have hCarryOidElem : base.locals[15] = .i64 taker.oid :=
    (List.getElem?_eq_some_iff.mp hCarryOidAt).2
  have hCarryTraderElem : base.locals[16] = .i64 taker.otrader :=
    (List.getElem?_eq_some_iff.mp hCarryTraderAt).2
  have hCarrySideElem : base.locals[17] = .i64 taker.oside :=
    (List.getElem?_eq_some_iff.mp hCarrySideAt).2
  have hCarryPriceElem : base.locals[18] = .i64 taker.oprice :=
    (List.getElem?_eq_some_iff.mp hCarryPriceAt).2
  have hCarryQtyElem : base.locals[19] = .i64 taker.oqty :=
    (List.getElem?_eq_some_iff.mp hCarryQtyAt).2
  unfold fullTradeUpdateProg
  rw [List.append_assoc, List.append_assoc]
  apply fullTradePrepareProg_spec env st base newBook oldBook oldTrades taker
    oldOrders ts i hParams hLocals hValues hTakerLocal hBookLocal
    hTradesLocal hIndexLocal hi hOrdersLength64 hOldBookOwned.2
    hOldTradesOwned.2 Q (partialTradeUpdateProg ++ fullTradeFinishProg ++ rest)
  apply partialTradeUpdateProg_spec env st
    (fullTradePrepareFrame base newBook oldBook oldTrades taker
      oldOrders[i]! i ts)
    oldBook oldBookCapacity newBook newBookCapacity oldTrades
    oldTradesCapacity g0 g2 capacity next oldOrders newOrders ts trade
  · simpa [fullTradePrepareFrame] using hParams
  · simpa [fullTradePrepareFrame, List.length_set] using hLocals
  · simp [fullTradePrepareFrame]
  · simp [fullTradePrepareFrame, hLocals]
  · simp [fullTradePrepareFrame, hLocals]
  · simp [fullTradePrepareFrame, hLocals]
  · simp [fullTradePrepareFrame, hLocals]
  · simp [fullTradePrepareFrame, trade,
      Project.ClobMatchFuel.Model.fillTradeL, hLocals]
  · simp [fullTradePrepareFrame, trade,
      Project.ClobMatchFuel.Model.fillTradeL, hLocals]
  · simp [fullTradePrepareFrame, trade,
      Project.ClobMatchFuel.Model.fillTradeL, hLocals]
  · change
      (fullTradePrepareFrame base newBook oldBook oldTrades taker
        oldOrders[i]! i ts).locals[54]? = some (.i64 oldOrders[i]!.oqty)
    simp [fullTradePrepareFrame, hLocals]
  · simpa [fullTradePrepareFrame, List.getElem?_set, hLocals] using
      hCapacityLocal
  · simpa [fullTradePrepareFrame, List.getElem?_set, hLocals] using
      hNextLocal
  · exact hn
  · exact hbytes
  · exact hTotalU
  · exact hTotal64
  · exact hTop
  · exact hFit32
  · exact hFit
  · exact hPages
  · exact hOldBook48
  · exact hOldBook32
  · exact hOldBookCapacity
  · exact hOldBookBelow
  · exact hOldBookOwned
  · exact hNewBook48
  · exact hNewBook32
  · exact hNewBookCapacity
  · exact hNewBookBelow
  · exact hNewBookOwned
  · exact hOldTrades48
  · exact hOldTrades32
  · exact hOldTradesCapacity
  · exact hOldTradesBelow
  · exact hOldTradesOwned
  · exact hg0
  · exact hg1
  · exact hg2
  · intro st1 hOldBookFinal hNewBookFinal hOldTradesFinal hNewTradesFinal
      hOutsideFinal hPagesFinal hGlobalsFinal
    let resultBase :=
      partialTradeResultFrame
        (partialTradeAllocFrame
          (fullTradePrepareFrame base newBook oldBook oldTrades taker
            oldOrders[i]! i ts) (ts.length + 1) g0)
        (g0 + 48) (ts.length * 4)
    apply fullTradeFinishProg_spec env st1 resultBase (g0 + 48) oldBook
      remaining oldOrders i
    · simpa [resultBase, partialTradeResultFrame, partialTradeCopyFrame,
        partialTradeAllocFrame, InternalTradeBump.allocFrame,
        fullTradePrepareFrame] using hParams
    · simpa [resultBase, partialTradeResultFrame, partialTradeCopyFrame,
        partialTradeAllocFrame, InternalTradeBump.allocFrame,
        fullTradePrepareFrame, List.length_set] using hLocals
    · simp [resultBase, partialTradeResultFrame]
    · simpa [resultBase, partialTradeResultFrame, partialTradeCopyFrame,
        partialTradeAllocFrame, InternalTradeBump.allocFrame,
        fullTradePrepareFrame] using hRemainingLocal
    · simpa [resultBase, partialTradeResultFrame, partialTradeCopyFrame,
        partialTradeAllocFrame, InternalTradeBump.allocFrame,
        fullTradePrepareFrame] using hBookLocal
    · simpa [resultBase, partialTradeResultFrame, partialTradeCopyFrame,
        partialTradeAllocFrame, InternalTradeBump.allocFrame,
        fullTradePrepareFrame, hLocals] using hIndexLocal
    · exact hi
    · exact hOrdersLength64
    · exact hOldBookFinal.2
    · apply hDone st1
        (fullTradeFinishFrame resultBase (g0 + 48) oldBook i remaining
          oldOrders[i]!.oqty)
      · simp [FullTradeResultAt, fullTradeFinishFrame, resultBase,
          partialTradeResultFrame, partialTradeCopyFrame,
          partialTradeAllocFrame, InternalTradeBump.allocFrame,
          fullTradePrepareFrame, Locals.get, hParams, hLocals, hFuelElem,
          hCarryOidElem, hCarryTraderElem, hCarrySideElem, hCarryPriceElem,
          hCarryQtyElem, InternalIteration.AllocScratchAt]
      · exact hOldBookFinal
      · exact hNewBookFinal
      · exact hOldTradesFinal
      · simpa [trade] using hNewTradesFinal
      · exact hOutsideFinal
      · exact hPagesFinal
      · exact hGlobalsFinal

end Project.ClobLimit.InternalFullTradeUpdate
