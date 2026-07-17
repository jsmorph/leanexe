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
  .localGet 34,
  .localSet 49,
  .localGet 35,
  .localSet 50,
  .localGet 36,
  .localSet 51,
  .localGet 37,
  .localSet 52,
  .localGet 38,
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
  .localSet 58,
  .localGet 44,
  .localGet 19,
  .eqI64,
  .iff 0 1 [
    .localGet 44
  ] [
    .localGet 44,
    .localGet 20,
    .eqI64,
    .iff 0 1 [
      .localGet 44
    ] [
      .constI64 0
    ]
  ],
  .localSet 59,
  .localGet 46,
  .localSet 60,
  .localGet 49,
  .localSet 9,
  .localGet 50,
  .localSet 10,
  .localGet 51,
  .localSet 11,
  .localGet 52,
  .localSet 12,
  .localGet 53,
  .localSet 13,
  .localGet 54,
  .localSet 14,
  .localGet 55,
  .localSet 15,
  .localGet 56,
  .localSet 16,
  .localGet 57,
  .localSet 17,
  .localGet 58,
  .localSet 18,
  .localGet 59,
  .localSet 19,
  .localGet 60,
  .localSet 20,
  .localGet 0,
  .constI64 1,
  .subI64,
  .localSet 0
  ]

def fullTransitionLocals (base : Locals) (taker : OrderL)
    (newBook newTrades remaining oldBookTracker oldTradesTracker : UInt64) :
    List Value :=
  let locals := base.locals.set 40 (.i64 taker.oid)
  let locals := locals.set 41 (.i64 taker.otrader)
  let locals := locals.set 42 (.i64 taker.oside)
  let locals := locals.set 43 (.i64 taker.oprice)
  let locals := locals.set 44 (.i64 taker.oqty)
  let locals := locals.set 45 (.i64 newBook)
  let locals := locals.set 46 (.i64 newBook)
  let locals := locals.set 47 (.i64 newTrades)
  let locals := locals.set 48 (.i64 newTrades)
  let locals := locals.set 49 (.i64 remaining)
  let locals := locals.set 50
    (.i64 (nextBookTracker newBook oldBookTracker oldTradesTracker))
  let locals := locals.set 51 (.i64 newTrades)
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
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hOid : base.get 34 = some (.i64 taker.oid))
    (hTrader : base.get 35 = some (.i64 taker.otrader))
    (hSide : base.get 36 = some (.i64 taker.oside))
    (hPrice : base.get 37 = some (.i64 taker.oprice))
    (hQty : base.get 38 = some (.i64 taker.oqty))
    (hNewBookOwner : base.get 44 = some (.i64 newBook))
    (hNewBookPointer : base.get 45 = some (.i64 newBook))
    (hNewTradesOwner : base.get 46 = some (.i64 newTrades))
    (hNewTradesPointer : base.get 47 = some (.i64 newTrades))
    (hRemaining : base.get 48 = some (.i64 remaining))
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
