import Project.ClobMatchFuel.SelectedOrder
import Project.ClobMatchFuel.PartialBookPrepare
import Project.ClobMatchFuel.TradeAllocAppend

/-!
# Partial-fill trade preparation

The partial-fill branch records its replacement book before allocating the
result trade array.  It copies the saved maker identifier and price, uses the
remaining taker quantity as the fill quantity, and prepares the trade allocator
locals.  This module proves that instruction bridge against the source arrays.
-/

namespace Project.ClobMatchFuel.PartialTradePrepare

open Wasm Project.Common Project.Clob Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576


def partialTradePrepareProg : Wasm.Program :=
  [
  .localSet 73,
  .localGet 73,
  .localSet 21,
  .localGet 17,
  .localSet 74,
  .localGet 74,
  .localSet 76,
  .localGet 9,
  .localSet 82,
  .localGet 34,
  .localSet 83,
  .localGet 37,
  .localSet 84,
  .localGet 18,
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

def partialTradePrepareFrame (base : Locals) (newBook oldBook oldTrades : UInt64)
    (taker maker : OrderL) (remaining : UInt64) (i : Nat)
    (ts : List TradeL) : Locals :=
  { base with
    locals :=
      let locals := base.locals.set 64 (.i64 (newBook))
      let locals := locals.set 12 (.i64 (newBook))
      let locals := locals.set 65 (.i64 (oldTrades))
      let locals := locals.set 67 (.i64 (oldTrades))
      let locals := locals.set 73 (.i64 (taker.oid))
      let locals := locals.set 74 (.i64 (maker.oid))
      let locals := locals.set 75 (.i64 (maker.oprice))
      let locals := locals.set 76 (.i64 (remaining))
      let locals := locals.set 68 (.i64 (UInt64.ofNat ts.length))
      let locals := locals.set 69 (.i64 (UInt64.ofNat ts.length * 4))
      locals.set 70 (.i64 (UInt64.ofNat ts.length + 1))
    values := [] }

set_option Elab.async false in
theorem partialTradePrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (newBook oldBook oldTrades remaining : UInt64)
    (taker : OrderL) (os : List OrderL) (ts : List TradeL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [.i64 newBook])
    (hTakerLocal : base.locals[0]? = some (.i64 taker.oid))
    (hBookLocal : base.locals[6]? = some (.i64 oldBook))
    (hTradesLocal : base.locals[8]? = some (.i64 oldTrades))
    (hRemainingLocal : base.locals[9]? = some (.i64 remaining))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hMaker : SelectedOrder.At base os[i]!)
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st oldBook os)
    (hTrades : TradesAt st oldTrades ts)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (partialTradePrepareFrame base newBook oldBook oldTrades taker os[i]!
        remaining i ts) env) :
    wp «module» (partialTradePrepareProg ++ rest) Q st base env := by
  have hTakerGet : base.locals[0] = .i64 taker.oid := getElem_of_some hTakerLocal
  have hBookGet : base.locals[6] = .i64 oldBook := getElem_of_some hBookLocal
  have hTradesGet : base.locals[8] = .i64 oldTrades := getElem_of_some hTradesLocal
  have hRemainingGet : base.locals[9] = .i64 remaining := getElem_of_some hRemainingLocal
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
  simp only [partialTradePrepareProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hTakerGet, hTradesGet,
    hMakerOidGet, hMakerPriceGet, hMakerQtyGet, hRemainingGet]
  rw [if_neg (Nat.not_lt.mpr hTradesLengthBound), hTradesLengthRead]
  simpa only [partialTradePrepareFrame,
    List.getElem!_eq_getElem?_getD] using hDone

end Project.ClobMatchFuel.PartialTradePrepare
