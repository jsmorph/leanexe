import Project.ClobLimit.InternalFullTradeUpdate

/-!
# Full-fill recursive transition

The full-fill branch copies the taker and the two replacement arrays into the
loop parameters.  It records the reduced remaining quantity and decrements the
fuel parameter.  This theorem covers the exact generated instruction slice.
-/

namespace Project.ClobLimit.InternalFullTransition

open Wasm Project.Clob Project.ClobLimit

def fullTransitionProg : Wasm.Program :=
  [
  .localGet 26,
  .localSet 41,
  .localGet 27,
  .localSet 42,
  .localGet 28,
  .localSet 43,
  .localGet 29,
  .localSet 44,
  .localGet 30,
  .localSet 45,
  .localGet 36,
  .localSet 46,
  .localGet 37,
  .localSet 47,
  .localGet 38,
  .localSet 48,
  .localGet 39,
  .localSet 49,
  .localGet 40,
  .localSet 50,
  .localGet 41,
  .localSet 1,
  .localGet 42,
  .localSet 2,
  .localGet 43,
  .localSet 3,
  .localGet 44,
  .localSet 4,
  .localGet 45,
  .localSet 5,
  .localGet 46,
  .localSet 6,
  .localGet 47,
  .localSet 7,
  .localGet 48,
  .localSet 8,
  .localGet 49,
  .localSet 9,
  .localGet 50,
  .localSet 10,
  .localGet 0,
  .constI64 1,
  .subI64,
  .localSet 0
  ]

def fullTransitionLocals (base : Locals) (taker : OrderL)
    (newBook newTrades remaining : UInt64) : List Value :=
  let locals := base.locals.set 30 (.i64 taker.oid)
  let locals := locals.set 31 (.i64 taker.otrader)
  let locals := locals.set 32 (.i64 taker.oside)
  let locals := locals.set 33 (.i64 taker.oprice)
  let locals := locals.set 34 (.i64 taker.oqty)
  let locals := locals.set 35 (.i64 newBook)
  let locals := locals.set 36 (.i64 newBook)
  let locals := locals.set 37 (.i64 newTrades)
  let locals := locals.set 38 (.i64 newTrades)
  locals.set 39 (.i64 remaining)

def fullTransitionParams (base : Locals) (fuel : UInt64) (taker : OrderL)
    (newBook newTrades remaining : UInt64) : List Value :=
  let params := base.params.set 1 (.i64 taker.oid)
  let params := params.set 2 (.i64 taker.otrader)
  let params := params.set 3 (.i64 taker.oside)
  let params := params.set 4 (.i64 taker.oprice)
  let params := params.set 5 (.i64 taker.oqty)
  let params := params.set 6 (.i64 newBook)
  let params := params.set 7 (.i64 newBook)
  let params := params.set 8 (.i64 newTrades)
  let params := params.set 9 (.i64 newTrades)
  let params := params.set 10 (.i64 remaining)
  params.set 0 (.i64 (fuel - 1))

def fullTransitionFrame (base : Locals) (fuel : UInt64) (taker : OrderL)
    (newBook newTrades remaining : UInt64) : Locals :=
  { params := fullTransitionParams base fuel taker newBook newTrades remaining
    locals := fullTransitionLocals base taker newBook newTrades remaining
    values := [] }

macro "wp_run_limit_transition" : tactic => `(tactic|
  simp_all (config := { maxSteps := 10000000 }) [wp_simp, Locals.get,
    Locals.set?, fullTransitionFrame, fullTransitionParams,
    fullTransitionLocals, List.length_set])

set_option Elab.async false in
theorem fullTransitionProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel newBook newTrades remaining : UInt64) (taker : OrderL)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hOid : base.get 26 = some (.i64 taker.oid))
    (hTrader : base.get 27 = some (.i64 taker.otrader))
    (hSide : base.get 28 = some (.i64 taker.oside))
    (hPrice : base.get 29 = some (.i64 taker.oprice))
    (hQty : base.get 30 = some (.i64 taker.oqty))
    (hNewBookOwner : base.get 36 = some (.i64 newBook))
    (hNewBookPointer : base.get 37 = some (.i64 newBook))
    (hNewTradesOwner : base.get 38 = some (.i64 newTrades))
    (hNewTradesPointer : base.get 39 = some (.i64 newTrades))
    (hRemaining : base.get 40 = some (.i64 remaining))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (fullTransitionFrame base fuel taker newBook newTrades remaining) env) :
    wp «module» (fullTransitionProg ++ rest) Q st base env := by
  rcases base with ⟨params, locals, values⟩
  dsimp only at hValues
  subst values
  simp only [fullTransitionProg, List.cons_append, List.nil_append]
  wp_run_limit_transition

end Project.ClobLimit.InternalFullTransition
