import Project.ClobLimit.LimitRunMatchCall

/-!
# Exported `limit` matcher result prefix

Function 21 stores function 18's five results, copies the book and trade
pointers into result locals, and normalizes the remaining-quantity test.  The
filled theorem ends before the generated filled-or-residual branch.
-/

namespace Project.ClobLimit.LimitRunMatchResult

open Wasm Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant

def resultFrame (book : UInt64) (order : OrderL)
    (ctx : Context) (data : InternalLoopResult.OutputData) : Locals :=
  { params := [.i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty]
    locals := [.i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty, .i64 1,
      .i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty,
      .i64 data.bookOwner, .i64 data.book, .i64 data.tradesOwner,
      .i64 data.trades, .i64 ctx.result.remaining, .i64 0,
      .i64 data.book, .i64 0, .i64 data.trades,
      .i64 ctx.result.remaining] ++ List.replicate 28 (.i64 0)
    values := [] }

def filledConditionFrame (book : UInt64) (order : OrderL)
    (ctx : Context) (data : InternalLoopResult.OutputData) : Locals :=
  { resultFrame book order ctx data with values := [.i32 1] }

def residualConditionFrame (book : UInt64) (order : OrderL)
    (ctx : Context) (data : InternalLoopResult.OutputData) : Locals :=
  { resultFrame book order ctx data with values := [.i32 0] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem validResultStoreProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (values : List Value)
    (hValues : values = InternalLoopResult.outputValues ctx data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (resultFrame book order ctx data) env) :
    wp «module» (LimitEntry.validResultStoreProg ++ rest) Q st
      { LimitRunMatchCall.callFrame book order with values := values } env := by
  simp only [LimitEntry.validResultStoreProg, List.cons_append,
    List.nil_append]
  simp only [hValues, InternalLoopResult.outputValues]
  wp_run
  simpa [LimitRunMatchCall.callFrame, resultFrame] using hNext

set_option Elab.async false in
theorem validConditionProg_filled_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hRemaining : ctx.result.remaining = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (filledConditionFrame book order ctx data) env) :
    wp «module» (LimitEntry.validConditionProg ++ rest) Q st
      (resultFrame book order ctx data) env := by
  simp only [LimitEntry.validConditionProg, List.cons_append, List.nil_append]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hRemaining])]
  wp_run
  simp
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run
  simpa [filledConditionFrame, resultFrame, hRemaining] using hNext

set_option Elab.async false in
theorem validConditionProg_residual_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hRemaining : ctx.result.remaining ≠ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (residualConditionFrame book order ctx data) env) :
    wp «module» (LimitEntry.validConditionProg ++ rest) Q st
      (resultFrame book order ctx data) env := by
  simp only [LimitEntry.validConditionProg, List.cons_append, List.nil_append]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hRemaining])]
  wp_run
  simp
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run
  simpa [residualConditionFrame, resultFrame, hRemaining] using hNext

set_option Elab.async false in
theorem validResultPrefixProg_filled_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (values : List Value)
    (hValues : values = InternalLoopResult.outputValues ctx data)
    (hRemaining : ctx.result.remaining = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (filledConditionFrame book order ctx data) env) :
    wp «module» (LimitEntry.validResultPrefixProg ++ rest) Q st
      { LimitRunMatchCall.callFrame book order with values := values } env := by
  simp only [LimitEntry.validResultPrefixProg, List.append_assoc]
  apply validResultStoreProg_spec env st book order ctx data values hValues
  exact validConditionProg_filled_spec env st book order ctx data hRemaining
    Q rest hNext

set_option Elab.async false in
theorem validResultPrefixProg_residual_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (values : List Value)
    (hValues : values = InternalLoopResult.outputValues ctx data)
    (hRemaining : ctx.result.remaining ≠ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (residualConditionFrame book order ctx data) env) :
    wp «module» (LimitEntry.validResultPrefixProg ++ rest) Q st
      { LimitRunMatchCall.callFrame book order with values := values } env := by
  simp only [LimitEntry.validResultPrefixProg, List.append_assoc]
  apply validResultStoreProg_spec env st book order ctx data values hValues
  exact validConditionProg_residual_spec env st book order ctx data hRemaining
    Q rest hNext

end Project.ClobLimit.LimitRunMatchResult
