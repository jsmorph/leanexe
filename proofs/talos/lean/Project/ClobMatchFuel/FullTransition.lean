import Project.ClobMatchFuel.FullTradeFinish

/-!
# Full-fill recursive transition

The full-fill branch copies its result into the loop-carried state after the
release guards finish.  It also computes the next owner trackers and decrements
the fuel parameter.  This module proves that local-state transition as one
continuation-parametric instruction slice.
-/

namespace Project.ClobMatchFuel.FullTransition

open Wasm Project.Clob Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def nextBookTracker (newBook oldBookTracker oldTradesTracker : UInt64) :
    UInt64 :=
  if newBook = oldBookTracker then newBook
  else if newBook = oldTradesTracker then newBook
  else 0

def fullTransitionProg : Wasm.Program :=
  [
  .localGet 49,
  .localSet 59,
  .localGet 50,
  .localSet 60,
  .localGet 51,
  .localSet 61,
  .localGet 52,
  .localSet 62,
  .localGet 53,
  .localSet 63,
  .localGet 54,
  .localSet 64,
  .localGet 55,
  .localSet 65,
  .localGet 56,
  .localSet 66,
  .localGet 57,
  .localSet 67,
  .localGet 58,
  .localSet 68,
  .localGet 54,
  .localGet 19,
  .eqI64,
  .iff 0 1 [
    .localGet 54
  ] [
    .localGet 54,
    .localGet 20,
    .eqI64,
    .iff 0 1 [
      .localGet 54
    ] [
      .constI64 0
    ] [] [.i64]
  ] [] [.i64],
  .localSet 69,
  .localGet 56,
  .localSet 70,
  .localGet 59,
  .localSet 9,
  .localGet 60,
  .localSet 10,
  .localGet 61,
  .localSet 11,
  .localGet 62,
  .localSet 12,
  .localGet 63,
  .localSet 13,
  .localGet 64,
  .localSet 14,
  .localGet 65,
  .localSet 15,
  .localGet 66,
  .localSet 16,
  .localGet 67,
  .localSet 17,
  .localGet 68,
  .localSet 18,
  .localGet 69,
  .localSet 19,
  .localGet 70,
  .localSet 20,
  .localGet 0,
  .constI64 1,
  .subI64,
  .localSet 0
  ]

def fullTransitionLocals (base : Locals) (taker : OrderL)
    (newBook newTrades remaining oldBookTracker oldTradesTracker : UInt64) :
    List Value :=
  let locals := base.locals.set 50 (.i64 taker.oid)
  let locals := locals.set 51 (.i64 taker.otrader)
  let locals := locals.set 52 (.i64 taker.oside)
  let locals := locals.set 53 (.i64 taker.oprice)
  let locals := locals.set 54 (.i64 taker.oqty)
  let locals := locals.set 55 (.i64 newBook)
  let locals := locals.set 56 (.i64 newBook)
  let locals := locals.set 57 (.i64 newTrades)
  let locals := locals.set 58 (.i64 newTrades)
  let locals := locals.set 59 (.i64 remaining)
  let locals := locals.set 60
    (.i64 (nextBookTracker newBook oldBookTracker oldTradesTracker))
  let locals := locals.set 61 (.i64 newTrades)
  let locals := locals.set 0 (.i64 taker.oid)
  let locals := locals.set 1 (.i64 taker.otrader)
  let locals := locals.set 2 (.i64 taker.oside)
  let locals := locals.set 3 (.i64 taker.oprice)
  let locals := locals.set 4 (.i64 taker.oqty)
  let locals := locals.set 5 (.i64 newBook)
  let locals := locals.set 6 (.i64 newBook)
  let locals := locals.set 7 (.i64 newTrades)
  let locals := locals.set 8 (.i64 newTrades)
  let locals := locals.set 9 (.i64 remaining)
  let locals := locals.set 10
    (.i64 (nextBookTracker newBook oldBookTracker oldTradesTracker))
  locals.set 11 (.i64 newTrades)

def fullTransitionFrame (base : Locals) (fuel : UInt64) (taker : OrderL)
    (newBook newTrades remaining oldBookTracker oldTradesTracker : UInt64) :
    Locals :=
  { params := base.params.set 0 (.i64 (fuel - 1))
    locals := fullTransitionLocals base taker newBook newTrades remaining
      oldBookTracker oldTradesTracker
    values := [] }

macro "wp_run_transition" : tactic => `(tactic|
  simp_all (config := { maxSteps := 10000000 }) [wp_simp, Locals.get,
    Locals.set?, fullTransitionFrame, fullTransitionLocals,
    nextBookTracker, List.length_set])

set_option Elab.async false in
theorem fullTransitionProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel newBook newTrades remaining oldBookTracker oldTradesTracker : UInt64)
    (taker : OrderL)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 86)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hOid : base.get 49 = some (.i64 taker.oid))
    (hTrader : base.get 50 = some (.i64 taker.otrader))
    (hSide : base.get 51 = some (.i64 taker.oside))
    (hPrice : base.get 52 = some (.i64 taker.oprice))
    (hQty : base.get 53 = some (.i64 taker.oqty))
    (hNewBookOwner : base.get 54 = some (.i64 newBook))
    (hNewBookPointer : base.get 55 = some (.i64 newBook))
    (hNewTradesOwner : base.get 56 = some (.i64 newTrades))
    (hNewTradesPointer : base.get 57 = some (.i64 newTrades))
    (hRemaining : base.get 58 = some (.i64 remaining))
    (hOldBookTracker : base.get 19 = some (.i64 oldBookTracker))
    (hOldTradesTracker : base.get 20 = some (.i64 oldTradesTracker))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st
      (fullTransitionFrame base fuel taker newBook newTrades remaining
        oldBookTracker oldTradesTracker) env) :
    wp «module» (fullTransitionProg ++ rest) Q st base env := by
  rcases base with ⟨params, locals, values⟩
  dsimp only at hValues
  subst values
  simp only [fullTransitionProg, List.cons_append, List.nil_append]
  by_cases hBook : newBook = oldBookTracker
  · wp_run_transition
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run_transition
  · wp_run_transition
    refine wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    by_cases hTrades : newBook = oldTradesTracker
    · wp_run_transition
      refine wp_iff_cons rfl ?_
      rw [if_pos (by decide)]
      wp_run_transition
    · wp_run_transition
      refine wp_iff_cons rfl ?_
      rw [if_neg (by decide)]
      wp_run_transition

end Project.ClobMatchFuel.FullTransition
