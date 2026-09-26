import Project.ClobMatchFuel.SelectedMaker
import Project.ClobMatchFuel.PartialBookPrepare
import Project.ClobMatchFuel.TradeAllocAppend

/-!
# Partial-fill trade preparation

The partial-fill branch records its replacement book before allocating the
result trade array.  It reads the matched maker identifier and price, uses the
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
    locals := (((((((((((base.locals.set 64 (.i64 (newBook))).set 12 (.i64 (newBook))).set 65 (.i64 (oldTrades))).set 67 (.i64 (oldTrades))).set 73 (.i64 (taker.oid))).set 74 (.i64 (maker.oid))).set 75 (.i64 (maker.oprice))).set 76 (.i64 (remaining))).set 68 (.i64 (UInt64.ofNat ts.length))).set 69 (.i64 (UInt64.ofNat ts.length * 4))).set 70 (.i64 (UInt64.ofNat ts.length + 1)))
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
    (hSelected : SelectedMaker.At base os[i]!)
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st oldBook os)
    (hTrades : TradesAt st oldTrades ts)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (partialTradePrepareFrame base newBook oldBook oldTrades taker os[i]!
        remaining i ts) env) :
    wp «module» (partialTradePrepareProg ++ rest) Q st base env := by
  obtain ⟨hMakerId, _, _, hMakerPrice, hMakerQty⟩ := hSelected
  have hMakerId' := getElem_of_some hMakerId
  have hMakerPrice' := getElem_of_some hMakerPrice
  have hMakerQty' := getElem_of_some hMakerQty
  have hTaker' := getElem_of_some hTakerLocal
  have hTrades' := getElem_of_some hTradesLocal
  have hRemaining' := getElem_of_some hRemainingLocal
  have hHead := hTrades.1.1
  have hSafe := Nat.not_lt.mpr hTrades.1.2
  simp only [partialTradePrepareProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hMakerId', hMakerPrice', hMakerQty',
    hTaker', hTrades', hHead, hSafe, hRemaining']
  simpa only [partialTradePrepareFrame, List.getElem!_eq_getElem?_getD] using hDone

#print axioms partialTradePrepareProg_spec
end Project.ClobMatchFuel.PartialTradePrepare
