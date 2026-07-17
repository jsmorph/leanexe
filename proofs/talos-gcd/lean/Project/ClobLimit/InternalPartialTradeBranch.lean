import Project.ClobLimit.InternalPartialFinish

/-!
# Complete partial-fill trade branch

The trade continuation prepares one fill, allocates and copies its result
array, appends the fill, and records the completed recursive result.  Its
postcondition retains every live array and the exact allocator state.
-/

namespace Project.ClobLimit.InternalPartialTradeBranch

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalPartialTradePrepare
  Project.ClobLimit.InternalPartialTradeUpdate
  Project.ClobLimit.InternalPartialTradeCopy
  Project.ClobLimit.InternalPartialTradeFinish
  Project.ClobLimit.InternalPartialFinish
  Project.ClobMatchFuel.AllocatorFrame

def partialTradeBranchProg : Wasm.Program :=
  partialTradePrepareProg ++ partialTradeUpdateProg ++ partialFinishProg

def PartialResultAt (s : Locals) (book trades : UInt64) : Prop :=
  s.locals[0]? = some (.i64 book) ∧
  s.locals[1]? = some (.i64 book) ∧
  s.locals[2]? = some (.i64 trades) ∧
  s.locals[3]? = some (.i64 trades) ∧
  s.locals[4]? = some (.i64 0) ∧
  s.locals[5]? = some (.i64 1) ∧
  s.params.length = 11 ∧ s.locals.length = 64 ∧ s.values = []

set_option Elab.async false in
theorem partialTradeBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (newBook newBookCapacity oldBook oldBookCapacity : UInt64)
    (oldTrades oldTradesCapacity remaining g0 g2 capacity next : UInt64)
    (taker : OrderL) (oldOrders newOrders : List OrderL)
    (ts : List TradeL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [.i64 newBook])
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
      (fixedArrayBytesU (ts.length + 1) 4).toNat ≤ st.mem.pages * 65536)
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
      PartialResultAt s newBook (g0 + 48) →
      OwnedOrderArrayAt st1 oldBook oldBookCapacity oldOrders →
      OwnedOrderArrayAt st1 newBook newBookCapacity newOrders →
      OwnedTradeArrayAt st1 oldTrades oldTradesCapacity ts →
      OwnedTradeArrayAt st1 (g0 + 48)
        (fixedArrayBytesU (ts.length + 1) 4)
        (ts ++ [Project.ClobMatchFuel.Model.fillTradeL
          taker oldOrders[i]! remaining]) →
      MemEqOutsideFlatWords
        (partialTradeAllocStore st (ts.length + 1) g0) st1
        (g0 + 48) ((ts.length + 1) * 4) →
      st1.mem.pages = st.mem.pages →
      st1.globals.globals =
        (partialTradeAllocStore st (ts.length + 1) g0).globals.globals.set 2
          (.i64 (g2 + 1)) →
      wp «module» rest Q st1 s env) :
    wp «module» (partialTradeBranchProg ++ rest) Q st base env := by
  let trade := Project.ClobMatchFuel.Model.fillTradeL
    taker oldOrders[i]! remaining
  unfold partialTradeBranchProg
  rw [List.append_assoc, List.append_assoc]
  apply partialTradePrepareProg_spec env st base newBook oldBook oldTrades
    remaining taker oldOrders ts i hParams hLocals hValues hTakerLocal
    hBookLocal hTradesLocal hRemainingLocal hIndexLocal hi hOrdersLength64
    hOldBookOwned.2 hOldTradesOwned.2 Q
      (partialTradeUpdateProg ++ partialFinishProg ++ rest)
  apply partialTradeUpdateProg_spec env st
    (partialTradePrepareFrame base newBook oldBook oldTrades taker
      oldOrders[i]! remaining i ts)
    oldBook oldBookCapacity newBook newBookCapacity oldTrades
    oldTradesCapacity g0 g2 capacity next oldOrders newOrders ts trade
  · simpa [partialTradePrepareFrame] using hParams
  · simpa [partialTradePrepareFrame, List.length_set] using hLocals
  · simp [partialTradePrepareFrame]
  · simp [partialTradePrepareFrame, hLocals]
  · simp [partialTradePrepareFrame, hLocals]
  · simp [partialTradePrepareFrame, hLocals]
  · simp [partialTradePrepareFrame, hLocals]
  · simp [partialTradePrepareFrame, trade,
      Project.ClobMatchFuel.Model.fillTradeL, hLocals]
  · simp [partialTradePrepareFrame, trade,
      Project.ClobMatchFuel.Model.fillTradeL, hLocals]
  · simp [partialTradePrepareFrame, trade,
      Project.ClobMatchFuel.Model.fillTradeL, hLocals]
  · change
      (partialTradePrepareFrame base newBook oldBook oldTrades taker
        oldOrders[i]! remaining i ts).locals[54]? =
          some (.i64 remaining)
    simp [partialTradePrepareFrame, hLocals]
  · simpa [partialTradePrepareFrame, List.getElem?_set, hLocals] using
      hCapacityLocal
  · simpa [partialTradePrepareFrame, List.getElem?_set, hLocals] using
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
    apply partialFinishProg_spec env st1
      (partialTradeResultFrame
        (partialTradeAllocFrame
          (partialTradePrepareFrame base newBook oldBook oldTrades taker
            oldOrders[i]! remaining i ts) (ts.length + 1) g0)
        (g0 + 48) (ts.length * 4)) (g0 + 48)
    · simpa [partialTradeResultFrame, partialTradeCopyFrame,
        partialTradeAllocFrame, InternalTradeBump.allocFrame,
        partialTradePrepareFrame] using hParams
    · simpa [partialTradeResultFrame, partialTradeCopyFrame,
        partialTradeAllocFrame, InternalTradeBump.allocFrame,
        partialTradePrepareFrame, List.length_set] using hLocals
    · simp [partialTradeResultFrame]
    · apply hDone st1
      · simp [PartialResultAt, partialFinishFrame, partialTradeResultFrame,
          partialTradeCopyFrame, partialTradeAllocFrame,
          InternalTradeBump.allocFrame, partialTradePrepareFrame, hParams,
          hLocals]
      · exact hOldBookFinal
      · exact hNewBookFinal
      · exact hOldTradesFinal
      · simpa [trade] using hNewTradesFinal
      · exact hOutsideFinal
      · exact hPagesFinal
      · exact hGlobalsFinal

end Project.ClobLimit.InternalPartialTradeBranch
