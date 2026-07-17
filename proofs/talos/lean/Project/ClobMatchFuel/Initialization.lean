import Project.ClobMatchFuel.Iteration

/-!
# Match-state initialization

The exported function copies its public taker and array arguments into the
recursive local layout, clears both owner trackers, and clears the completion
flag before entering the outer loop.
-/

namespace Project.ClobMatchFuel.Initialization

open Wasm Project.Clob Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def initProg : Wasm.Program :=
  [
  .localGet 1,
  .localSet 9,
  .localGet 2,
  .localSet 10,
  .localGet 3,
  .localSet 11,
  .localGet 4,
  .localSet 12,
  .localGet 5,
  .localSet 13,
  .constI64 0,
  .localSet 14,
  .localGet 6,
  .localSet 15,
  .constI64 0,
  .localSet 16,
  .localGet 7,
  .localSet 17,
  .localGet 8,
  .localSet 18,
  .constI64 0,
  .localSet 19,
  .constI64 0,
  .localSet 20,
  .constI64 0,
  .localSet 24
  ]

def initLocals (base : Locals) (taker : OrderL)
    (book trades remaining : UInt64) : List Value :=
  let locals := base.locals.set 0 (.i64 taker.oid)
  let locals := locals.set 1 (.i64 taker.otrader)
  let locals := locals.set 2 (.i64 taker.oside)
  let locals := locals.set 3 (.i64 taker.oprice)
  let locals := locals.set 4 (.i64 taker.oqty)
  let locals := locals.set 5 (.i64 0)
  let locals := locals.set 6 (.i64 book)
  let locals := locals.set 7 (.i64 0)
  let locals := locals.set 8 (.i64 trades)
  let locals := locals.set 9 (.i64 remaining)
  let locals := locals.set 10 (.i64 0)
  let locals := locals.set 11 (.i64 0)
  locals.set 15 (.i64 0)

def initFrame (base : Locals) (taker : OrderL)
    (book trades remaining : UInt64) : Locals :=
  { base with locals := initLocals base taker book trades remaining, values := [] }

set_option Elab.async false in
theorem initProg_spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book trades remaining : UInt64) (taker : OrderL)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hOid : base.get 1 = some (.i64 taker.oid))
    (hTrader : base.get 2 = some (.i64 taker.otrader))
    (hSide : base.get 3 = some (.i64 taker.oside))
    (hPrice : base.get 4 = some (.i64 taker.oprice))
    (hQty : base.get 5 = some (.i64 taker.oqty))
    (hBook : base.get 6 = some (.i64 book))
    (hTrades : base.get 7 = some (.i64 trades))
    (hRemaining : base.get 8 = some (.i64 remaining))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (initFrame base taker book trades remaining) env) :
    wp «module» (initProg ++ rest) Q st base env := by
  simp only [Locals.get] at hOid hTrader hSide hPrice hQty hBook hTrades hRemaining
  have hOid' : base.params[1] = .i64 taker.oid := by
    simpa [hParams, hLocals] using hOid
  have hTrader' : base.params[2] = .i64 taker.otrader := by
    simpa [hParams, hLocals] using hTrader
  have hSide' : base.params[3] = .i64 taker.oside := by
    simpa [hParams, hLocals] using hSide
  have hPrice' : base.params[4] = .i64 taker.oprice := by
    simpa [hParams, hLocals] using hPrice
  have hQty' : base.params[5] = .i64 taker.oqty := by
    simpa [hParams, hLocals] using hQty
  have hBook' : base.params[6] = .i64 book := by
    simpa [hParams, hLocals] using hBook
  have hTrades' : base.params[7] = .i64 trades := by
    simpa [hParams, hLocals] using hTrades
  have hRemaining' : base.params[8] = .i64 remaining := by
    simpa [hParams, hLocals] using hRemaining
  simp only [initProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals,
    hValues, hOid', hTrader', hSide', hPrice', hQty', hBook', hTrades',
    hRemaining']
  simpa [initFrame, initLocals] using hDone

end Project.ClobMatchFuel.Initialization
