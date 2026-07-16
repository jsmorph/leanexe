import Project.ClobMatchFuel.FullBranch
import Project.ClobMatchFuel.FullTransition

/-!
# Full-fill release and transition

The full-fill result either has no tracked source allocation or tracks the
source trade array.  This module composes the corresponding release path with
the recursive local-state transition.
-/

namespace Project.ClobMatchFuel.FullReleaseTransition

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame
  Project.ClobMatchFuel.ReleaseFrame

def fullReleaseTransitionProg : Wasm.Program :=
  ReleaseOld.releaseOldValuesProg ++ FullTransition.fullTransitionProg

set_option Elab.async false in
theorem fullReleaseTransitionProg_none
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel newBook newTrades remaining : UInt64) (taker : OrderL)
    (hResult : FullTradeUpdate.FullResultAt base fuel taker 0 0 newBook
      newTrades remaining)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (FullTransition.fullTransitionFrame base fuel taker newBook newTrades
        remaining 0 0) env) :
    wp «module» (fullReleaseTransitionProg ++ rest) Q st base env := by
  rcases hResult with ⟨hParams, hLocals, hValues, hFuel, hOldBookTracker,
    hOldTradesTracker, hOid, hTrader, hSide, hPrice, hQty, hNewBookOwner,
    hNewBookPointer, hNewTradesOwner, hNewTradesPointer, hRemaining⟩
  unfold fullReleaseTransitionProg
  rw [List.append_assoc]
  apply ReleaseOld.releaseOldValuesProg_none env st base newBook newTrades
    hOldBookTracker hOldTradesTracker hNewBookOwner hNewTradesOwner hValues Q
    (FullTransition.fullTransitionProg ++ rest)
  exact FullTransition.fullTransitionProg_spec env st base fuel newBook newTrades
    remaining 0 0 taker hParams hLocals hValues hFuel hOid hTrader hSide hPrice
    hQty hNewBookOwner hNewBookPointer hNewTradesOwner hNewTradesPointer
    hRemaining hOldBookTracker hOldTradesTracker Q rest hDone

set_option Elab.async false in
theorem fullReleaseTransitionProg_trade
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel oldTrades oldTradesCapacity newBook newBookCapacity : UInt64)
    (newTrades newTradesCapacity remaining g4 g5 : UInt64)
    (taker : OrderL) (oldTradeValues newTradeValues : List TradeL)
    (newOrders : List OrderL) (nodes : List FreeNode)
    (hResult : FullTradeUpdate.FullResultAt base fuel taker 0 oldTrades newBook
      newTrades remaining)
    (hOldTrades48 : 48 ≤ oldTrades.toNat)
    (hOldTrades32 :
      oldTrades.toNat + oldTradesCapacity.toNat < 4294967296)
    (hOldTradesFit :
      oldTrades.toNat + oldTradesCapacity.toNat ≤ st.mem.pages * 65536)
    (hOldTradesCapacity :
      fixedArrayBytes oldTradeValues.length 4 ≤ oldTradesCapacity.toNat)
    (hNewBook48 : 48 ≤ newBook.toNat)
    (hNewBook32 :
      newBook.toNat + fixedArrayBytes newOrders.length 5 < 4294967296)
    (hNewBookCapacity :
      fixedArrayBytes newOrders.length 5 ≤ newBookCapacity.toNat)
    (hNewTrades48 : 48 ≤ newTrades.toNat)
    (hNewTrades32 : newTrades.toNat +
      fixedArrayBytes newTradeValues.length 4 < 4294967296)
    (hNewTradesCapacity :
      fixedArrayBytes newTradeValues.length 4 ≤ newTradesCapacity.toNat)
    (hOldTradesOwned :
      OwnedTradeArrayAt st oldTrades oldTradesCapacity oldTradeValues)
    (hNewBookOwned :
      OwnedOrderArrayAt st newBook newBookCapacity newOrders)
    (hNewTradesOwned :
      OwnedTradeArrayAt st newTrades newTradesCapacity newTradeValues)
    (hOldTradesNewBook : regionsDisjoint
      (fixedArrayRegion oldTrades oldTradesCapacity)
      (fixedArrayRegion newBook newBookCapacity))
    (hOldTradesNewTrades : regionsDisjoint
      (fixedArrayRegion oldTrades oldTradesCapacity)
      (fixedArrayRegion newTrades newTradesCapacity))
    (hOldTradesNodes : FreeListSeparatedFromFixedArray nodes oldTrades
      oldTradesCapacity)
    (hList : FreeListAt st.mem nodes)
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1,
      st1.mem = fixedArrayReleaseMem st oldTrades (freeHead nodes) →
      st1.globals.globals = fixedArrayReleaseGlobals st oldTrades g4 g5 →
      OwnedOrderArrayAt st1 newBook newBookCapacity newOrders →
      OwnedTradeArrayAt st1 newTrades newTradesCapacity newTradeValues →
      FreeListAt st1.mem (releasedNode oldTrades oldTradesCapacity :: nodes) →
      wp «module» rest Q st1
        (FullTransition.fullTransitionFrame base fuel taker newBook newTrades
          remaining 0 oldTrades) env) :
    wp «module» (fullReleaseTransitionProg ++ rest) Q st base env := by
  rcases hResult with ⟨hParams, hLocals, hValues, hFuel, hOldBookTracker,
    hOldTradesTracker, hOid, hTrader, hSide, hPrice, hQty, hNewBookOwner,
    hNewBookPointer, hNewTradesOwner, hNewTradesPointer, hRemaining⟩
  unfold fullReleaseTransitionProg
  rw [List.append_assoc]
  apply ReleaseOld.releaseTrackedTradeProg_spec env st base oldTrades
    oldTradesCapacity newBook newBookCapacity newTrades newTradesCapacity g4 g5
    oldTradeValues newTradeValues newOrders nodes hOldBookTracker
    hOldTradesTracker hNewBookOwner hNewTradesOwner hValues hOldTrades48
    hOldTrades32 hOldTradesFit hOldTradesCapacity hNewBook48 hNewBook32
    hNewBookCapacity hNewTrades48 hNewTrades32 hNewTradesCapacity
    hOldTradesOwned hNewBookOwned hNewTradesOwned hOldTradesNewBook
    hOldTradesNewTrades hOldTradesNodes hList hg1 hg4 hg5 Q
    (FullTransition.fullTransitionProg ++ rest)
  intro st1 hMem hGlobals hNewBookOwned1 hNewTradesOwned1 hList1
  apply FullTransition.fullTransitionProg_spec env st1 base fuel newBook newTrades
    remaining 0 oldTrades taker hParams hLocals hValues hFuel hOid hTrader hSide
    hPrice hQty hNewBookOwner hNewBookPointer hNewTradesOwner hNewTradesPointer
    hRemaining hOldBookTracker hOldTradesTracker Q rest
  exact hDone st1 hMem hGlobals hNewBookOwned1 hNewTradesOwned1 hList1

end Project.ClobMatchFuel.FullReleaseTransition
