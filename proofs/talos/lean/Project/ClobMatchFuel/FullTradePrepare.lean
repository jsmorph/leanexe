import Project.ClobMatchFuel.SelectedOrder
import Project.ClobMatchFuel.TradeAllocAppend

/-!
# Full-fill trade preparation

The full-fill branch moves its fresh book root into result locals, copies the
saved maker fields, and prepares the old trade array for allocation and
append.  This module proves that instruction bridge independently of both
allocators.
-/

namespace Project.ClobMatchFuel.FullTradePrepare

open Wasm Project.Common Project.Clob Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576


def fullTradePrepareProg : Wasm.Program :=
  [
  .localSet 44,
  .localGet 44,
  .localSet 45,
  .localGet 17,
  .localSet 42,
  .localGet 42,
  .localSet 76,
  .localGet 9,
  .localSet 82,
  .localGet 34,
  .localSet 83,
  .localGet 37,
  .localSet 84,
  .localGet 38,
  .localSet 85,
  .localGet 76,
  .wrapI64,
  .load64 0,
  .localSet 77,
  .localGet 77,
  .constI64 4,
  .mulI64,
  .localSet 78,
  .localGet 77,
  .constI64 1,
  .addI64,
  .localSet 79
  ]

def fullTradePrepareFrame (base : Locals) (newBook oldBook oldTrades : UInt64)
    (taker maker : OrderL) (i : Nat) (ts : List TradeL) : Locals :=
  { base with
    locals :=
      let locals := base.locals.set 35 (.i64 (newBook))
      let locals := locals.set 36 (.i64 (newBook))
      let locals := locals.set 33 (.i64 (oldTrades))
      let locals := locals.set 67 (.i64 (oldTrades))
      let locals := locals.set 73 (.i64 (taker.oid))
      let locals := locals.set 74 (.i64 (maker.oid))
      let locals := locals.set 75 (.i64 (maker.oprice))
      let locals := locals.set 76 (.i64 (maker.oqty))
      let locals := locals.set 68 (.i64 (UInt64.ofNat ts.length))
      let locals := locals.set 69 (.i64 (UInt64.ofNat ts.length * 4))
      locals.set 70 (.i64 (UInt64.ofNat ts.length + 1))
    values := [] }

set_option Elab.async false in
theorem fullTradePrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (newBook oldBook oldTrades : UInt64)
    (taker : OrderL) (os : List OrderL) (ts : List TradeL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [.i64 newBook])
    (hTakerLocal : base.locals[0]? = some (.i64 taker.oid))
    (hBookLocal : base.locals[6]? = some (.i64 oldBook))
    (hTradesLocal : base.locals[8]? = some (.i64 oldTrades))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hMaker : SelectedOrder.At base os[i]!)
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st oldBook os)
    (hTrades : TradesAt st oldTrades ts)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (fullTradePrepareFrame base newBook oldBook oldTrades taker os[i]! i ts)
      env) :
    wp «module» (fullTradePrepareProg ++ rest) Q st base env := by
  have hTakerGet : base.locals[0] = .i64 taker.oid := getElem_of_some hTakerLocal
  have hBookGet : base.locals[6] = .i64 oldBook := getElem_of_some hBookLocal
  have hTradesGet : base.locals[8] = .i64 oldTrades := getElem_of_some hTradesLocal
  have hIndexGet : base.locals[24] = .i64 (UInt64.ofNat i) := getElem_of_some hIndexLocal
  have hTradesLengthRead :
      st.mem.read64 (UInt32.ofNat (oldTrades.toNat % 4294967296)) =
        UInt64.ofNat ts.length := hTrades.1.1
  have hTradesLengthBound :
      oldTrades.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536 := hTrades.1.2
  rcases hMaker with ⟨hMakerOid, hMakerTrader, hMakerSide, hMakerPrice, hMakerQty⟩
  have hMakerOidGet := getElem_of_some hMakerOid
  have hMakerPriceGet := getElem_of_some hMakerPrice
  have hMakerQtyGet := getElem_of_some hMakerQty
  simp only [fullTradePrepareProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hTakerGet, hTradesGet,
    hMakerOidGet, hMakerPriceGet, hMakerQtyGet]
  rw [if_neg (Nat.not_lt.mpr hTradesLengthBound), hTradesLengthRead]
  simpa only [fullTradePrepareFrame, List.getElem!_eq_getElem?_getD] using
    hDone

end Project.ClobMatchFuel.FullTradePrepare
