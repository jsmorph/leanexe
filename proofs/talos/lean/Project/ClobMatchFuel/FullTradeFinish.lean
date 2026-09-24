import Project.ClobMatchFuel.FullTradePrepare
import Project.ClobMatchFuel.ReleaseOld

/-!
# Full-fill trade finalization

The full-fill branch records its fresh trade root and computes the remaining
quantity before releasing prior loop-owned arrays.  This module proves the
generated local-state bridge to the release block.
-/

namespace Project.ClobMatchFuel.FullTradeFinish

open Wasm Project.Common Project.Clob Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576


def fullTradeFinishProg : Wasm.Program :=
  [
  .localSet 46,
  .localGet 46,
  .localSet 47,
  .localGet 18,
  .localGet 38,
  .subI64,
  .localSet 48,
  .localGet 9,
  .localSet 49,
  .localGet 10,
  .localSet 50,
  .localGet 11,
  .localSet 51,
  .localGet 12,
  .localSet 52,
  .localGet 13,
  .localSet 53,
  .localGet 44,
  .localSet 54,
  .localGet 45,
  .localSet 55,
  .localGet 46,
  .localSet 56,
  .localGet 47,
  .localSet 57,
  .localGet 48,
  .localSet 58
  ]

def fullTradeFinishFrame (base : Locals) (newTrades oldBook : UInt64)
    (i : Nat) (remaining makerQty : UInt64) : Locals :=
  { base with
    locals :=
      let locals := base.locals.set 37 (.i64 newTrades)
      let locals := locals.set 38 (.i64 newTrades)
      let locals := locals.set 39 (.i64 (remaining - makerQty))
      let locals := locals.set 40 (base.locals[0]!)
      let locals := locals.set 41 (base.locals[1]!)
      let locals := locals.set 42 (base.locals[2]!)
      let locals := locals.set 43 (base.locals[3]!)
      let locals := locals.set 44 (base.locals[4]!)
      let locals := locals.set 45 (base.locals[35]!)
      let locals := locals.set 46 (base.locals[36]!)
      let locals := locals.set 47 (.i64 newTrades)
      let locals := locals.set 48 (.i64 newTrades)
      locals.set 49 (.i64 (remaining - makerQty))
    values := [] }

set_option Elab.async false in
theorem fullTradeFinishProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (newTrades oldBook remaining : UInt64)
    (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [.i64 newTrades])
    (hRemainingLocal : base.locals[9]? = some (.i64 remaining))
    (hBookLocal : base.locals[6]? = some (.i64 oldBook))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hMaker : SelectedOrder.At base os[i]!)
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hOrders : OrdersAt st oldBook os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (fullTradeFinishFrame base newTrades oldBook i remaining os[i]!.oqty)
      env) :
    wp «module» (fullTradeFinishProg ++ rest) Q st base env := by
  have hRemainingGet : base.locals[9] = .i64 remaining := getElem_of_some hRemainingLocal
  have hQtyGet := getElem_of_some hMaker.2.2.2.2
  simp only [fullTradeFinishProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hRemainingGet, hQtyGet]
  simpa [fullTradeFinishFrame, List.getElem!_eq_getElem?_getD, hLocals] using hDone

end Project.ClobMatchFuel.FullTradeFinish
