import Project.ClobMarket.Call

/-!
# Valid market result

The valid branch stores function 18's book and trade pointers, calls the zero
status helper, and returns three public values.  This theorem records the exact
post-call frame and preserves the matcher's semantic output data.  No matcher
predicate is reduced while the generated local assignments execute.
-/

namespace Project.ClobMarket.ValidResult

open Wasm Project.Clob Project.ClobMarket
  Project.ClobLimit.InternalLoopInvariant

def outputFrame (book : UInt64) (order : OrderL)
    (ctx : Context) (data : Project.ClobLimit.InternalLoopResult.OutputData) :
    Locals :=
  let taker := Model.unlimitedTakerL order
  { params := [.i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty]
    locals := [.i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty, .i64 1,
      .i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
      .i64 taker.oprice, .i64 taker.oqty, .i64 0, .i64 book,
      .i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
      .i64 taker.oprice, .i64 taker.oqty, .i64 data.bookOwner,
      .i64 data.book, .i64 data.tradesOwner, .i64 data.trades,
      .i64 ctx.result.remaining, .i64 0, .i64 data.book, .i64 0,
      .i64 data.trades, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 data.book, .i64 data.trades] ++ List.replicate 13 (.i64 0)
    values := [.i64 data.trades, .i64 data.book, .i64 0] }

def resultFrame (book : UInt64) (order : OrderL)
    (ctx : Context) (data : Project.ClobLimit.InternalLoopResult.OutputData) :
    Locals :=
  { outputFrame book order ctx data with values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem validResultProg_spec (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : Project.ClobLimit.InternalLoopResult.OutputData)
    (values : List Value)
    (hValues : values =
      Project.ClobLimit.InternalLoopResult.outputValues ctx data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.ClobMarket.«module» rest Q st
      (resultFrame book order ctx data) env) :
    wp Project.ClobMarket.«module»
      (Entry.validResultProg ++ rest) Q st
      { Call.callFrame book order with values := values } env := by
  subst values
  simp only [Entry.validResultProg, List.cons_append, List.nil_append]
  simp [Project.ClobLimit.InternalLoopResult.outputValues,
    Call.callFrame]
  refine wp_call_tw (Helpers.func19_spec env st) ?_
  rintro st1 result ⟨rfl, rfl⟩
  wp_run
  simpa [resultFrame, outputFrame] using hNext

set_option Elab.async false in
theorem resultProg_spec (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : Project.ClobLimit.InternalLoopResult.OutputData)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.ClobMarket.«module» rest Q st
      (outputFrame book order ctx data) env) :
    wp Project.ClobMarket.«module» (Entry.resultProg ++ rest) Q st
      (resultFrame book order ctx data) env := by
  simp only [Entry.resultProg, List.cons_append, List.nil_append]
  wp_run
  simpa [resultFrame, outputFrame] using hNext

end Project.ClobMarket.ValidResult
