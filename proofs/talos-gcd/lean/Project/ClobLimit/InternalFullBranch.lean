import Project.ClobLimit.InternalFullBookTrade
import Project.ClobLimit.InternalFullTransition

/-!
# Complete internal full-fill branch

The full-fill branch removes the selected maker, appends its complete trade,
and updates the recursive parameters.  This module composes the two allocation
updates with the separately proved local-state transition.
-/

namespace Project.ClobLimit.InternalFullBranch

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalFullBookTrade
  Project.ClobLimit.InternalFullTradeUpdate
  Project.ClobLimit.InternalFullTransition
  Project.ClobMatchFuel.AllocatorFrame

def fullBranchProg : Wasm.Program :=
  fullBookTradeProg ++ fullTransitionProg

def RecursiveResultAt (s : Locals) (fuel : UInt64) (taker : OrderL)
    (book trades remaining : UInt64) : Prop :=
  s.params.length = 11 ∧ s.locals.length = 64 ∧ s.values = [] ∧
  s.get 0 = some (.i64 (fuel - 1)) ∧
  s.get 1 = some (.i64 taker.oid) ∧
  s.get 2 = some (.i64 taker.otrader) ∧
  s.get 3 = some (.i64 taker.oside) ∧
  s.get 4 = some (.i64 taker.oprice) ∧
  s.get 5 = some (.i64 taker.oqty) ∧
  s.get 6 = some (.i64 book) ∧
  s.get 7 = some (.i64 book) ∧
  s.get 8 = some (.i64 trades) ∧
  s.get 9 = some (.i64 trades) ∧
  s.get 10 = some (.i64 remaining)

theorem recursiveResultAt_fullTransitionFrame
    (base : Locals) (fuel newBook newTrades remaining : UInt64)
    (taker : OrderL) (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64) :
    RecursiveResultAt
      (fullTransitionFrame base fuel taker newBook newTrades remaining)
      fuel taker newBook newTrades remaining := by
  simp [RecursiveResultAt, fullTransitionFrame, fullTransitionParams,
    fullTransitionLocals, Locals.get, hParams, hLocals]

set_option Elab.async false in
theorem fullBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book bookCapacity oldTrades oldTradesCapacity : UInt64)
    (fuel remaining g0 g2 capacity next tradeNext : UInt64)
    (taker : OrderL) (os : List OrderL) (ts : List TradeL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hOid : base.get 1 = some (.i64 taker.oid))
    (hTrader : base.get 2 = some (.i64 taker.otrader))
    (hSide : base.get 3 = some (.i64 taker.oside))
    (hPrice : base.get 4 = some (.i64 taker.oprice))
    (hQty : base.get 5 = some (.i64 taker.oqty))
    (hBookLocal : base.get 7 = some (.i64 book))
    (hTradesLocal : base.get 9 = some (.i64 oldTrades))
    (hRemainingLocal : base.get 10 = some (.i64 remaining))
    (hIndexLocal : base.get 25 = some (.i64 (UInt64.ofNat i)))
    (hCapacityLocal : base.locals[58]? = some (.i64 capacity))
    (hNextLocal : base.locals[59]? = some (.i64 next))
    (hTradeNextLocal : base.locals[61]? = some (.i64 tradeNext))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hErasedLength64 : os.length - 1 < UInt64.size)
    (hOrderWords64 : os.length * 5 < UInt64.size)
    (hBookBytes : fixedArrayBytes (os.length - 1) 5 + 7 < UInt64.size)
    (hBookTop :
      (g0 + 48 + fixedArrayBytesU (os.length - 1) 5).toNat =
        g0.toNat + 48 + (fixedArrayBytesU (os.length - 1) 5).toNat)
    (hBookFit32 : g0.toNat + 48 +
      (fixedArrayBytesU (os.length - 1) 5).toNat < 4294967296)
    (hBookFit : g0.toNat + 48 +
      (fixedArrayBytesU (os.length - 1) 5).toNat ≤ st.mem.pages * 65536)
    (hTradeLength64 : ts.length + 1 < UInt64.size)
    (hTradeBytes :
      fixedArrayBytes (ts.length + 1) 4 + 7 < UInt64.size)
    (hTradeTotalU : (UInt64.ofNat ts.length * 4).toNat = ts.length * 4)
    (hTradeTotal64 : ts.length * 4 < UInt64.size)
    (hTradeTop :
      (g0 + 48 + fixedArrayBytesU (os.length - 1) 5 + 48 +
          fixedArrayBytesU (ts.length + 1) 4).toNat =
        (g0 + 48 + fixedArrayBytesU (os.length - 1) 5).toNat + 48 +
          (fixedArrayBytesU (ts.length + 1) 4).toNat)
    (hTradeFit32 :
      (g0 + 48 + fixedArrayBytesU (os.length - 1) 5).toNat + 48 +
          (fixedArrayBytesU (ts.length + 1) 4).toNat < 4294967296)
    (hTradeFit :
      (g0 + 48 + fixedArrayBytesU (os.length - 1) 5).toNat + 48 +
          (fixedArrayBytesU (ts.length + 1) 4).toNat ≤
        st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hBook48 : 48 ≤ book.toNat)
    (hBook32 : book.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes os.length 5 ≤ bookCapacity.toNat)
    (hBookBelow : book.toNat + bookCapacity.toNat ≤ g0.toNat)
    (hBookOwned : OwnedOrderArrayAt st book bookCapacity os)
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
      RecursiveResultAt s fuel taker (g0 + 48)
        (g0 + 48 + fixedArrayBytesU (os.length - 1) 5 + 48)
        (remaining - os[i]!.oqty) →
      OwnedOrderArrayAt st1 book bookCapacity os →
      OwnedOrderArrayAt st1 (g0 + 48)
        (fixedArrayBytesU (os.length - 1) 5) (os.eraseIdx i) →
      OwnedTradeArrayAt st1 oldTrades oldTradesCapacity ts →
      OwnedTradeArrayAt st1
        (g0 + 48 + fixedArrayBytesU (os.length - 1) 5 + 48)
        (fixedArrayBytesU (ts.length + 1) 4)
        (ts ++ [Project.ClobMatchFuel.Model.fillTradeL
          taker os[i]! os[i]!.oqty]) →
      st1.mem.pages = st.mem.pages →
      st1.globals.globals[0]? = some (.i64
        (g0 + 48 + fixedArrayBytesU (os.length - 1) 5 + 48 +
          fixedArrayBytesU (ts.length + 1) 4)) →
      st1.globals.globals[1]? = some (.i64 0) →
      st1.globals.globals[2]? = some (.i64 (g2 + 2)) →
      (∀ a : Nat, a < g0.toNat → st1.mem.bytes a = st.mem.bytes a) →
      wp «module» rest Q st1 s env) :
    wp «module» (fullBranchProg ++ rest) Q st base env := by
  unfold fullBranchProg
  rw [List.append_assoc]
  apply fullBookTradeProg_spec env st base book bookCapacity oldTrades
    oldTradesCapacity fuel remaining g0 g2 capacity next tradeNext taker os ts i
    hParams hLocals hValues hFuel hOid hTrader hSide hPrice hQty hBookLocal
    hTradesLocal hRemainingLocal hIndexLocal hCapacityLocal hNextLocal
    hTradeNextLocal hi hOrdersLength64 hErasedLength64 hOrderWords64 hBookBytes
    hBookTop hBookFit32 hBookFit hTradeLength64 hTradeBytes hTradeTotalU
    hTradeTotal64 hTradeTop hTradeFit32 hTradeFit hPages hBook48 hBook32
    hBookCapacity hBookBelow hBookOwned hOldTrades48 hOldTrades32
    hOldTradesCapacity hOldTradesBelow hOldTradesOwned hg0 hg1 hg2 Q
    (fullTransitionProg ++ rest)
  intro st1 s hResult hBookFinal hNewBookFinal hOldTradesFinal hNewTradesFinal
    hFinalPages hFinalG0 hFinalG1 hFinalG2 hBelow
  rcases hResult with ⟨hResultParams, hResultLocals, hResultValues, hResultFuel,
    hResultOid, hResultTrader, hResultSide, hResultPrice, hResultQty,
    hResultBookOwner, hResultBookPointer, hResultTradesOwner,
    hResultTradesPointer, hResultRemaining⟩
  apply fullTransitionProg_spec env st1 s fuel (g0 + 48)
    (g0 + 48 + fixedArrayBytesU (os.length - 1) 5 + 48)
    (remaining - os[i]!.oqty) taker hResultParams hResultLocals hResultValues
    hResultFuel hResultOid hResultTrader hResultSide hResultPrice hResultQty
    hResultBookOwner hResultBookPointer hResultTradesOwner hResultTradesPointer
    hResultRemaining Q rest
  apply hDone st1
    (fullTransitionFrame s fuel taker (g0 + 48)
      (g0 + 48 + fixedArrayBytesU (os.length - 1) 5 + 48)
      (remaining - os[i]!.oqty))
  · exact recursiveResultAt_fullTransitionFrame s fuel (g0 + 48)
      (g0 + 48 + fixedArrayBytesU (os.length - 1) 5 + 48)
      (remaining - os[i]!.oqty) taker hResultParams hResultLocals
  · exact hBookFinal
  · exact hNewBookFinal
  · exact hOldTradesFinal
  · exact hNewTradesFinal
  · exact hFinalPages
  · exact hFinalG0
  · exact hFinalG1
  · exact hFinalG2
  · exact hBelow

end Project.ClobLimit.InternalFullBranch
