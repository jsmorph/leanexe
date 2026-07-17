import Project.ClobLimit.LimitRunMatchResult
import Project.ClobLimit.Allocation

/-!
# Residual `limit` status prefix

The residual branch calls the status-zero helper and copies the matched book
pointer into its append locals.  The theorem ends before any source-array read
or allocation arithmetic.
-/

namespace Project.ClobLimit.LimitResidualStatus

open Wasm Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant

def statusFrame (book : UInt64) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) : Locals :=
  { params := [.i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty]
    locals := [.i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty, .i64 1,
      .i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty,
      .i64 data.bookOwner, .i64 data.book, .i64 data.tradesOwner,
      .i64 data.trades, .i64 ctx.result.remaining, .i64 0,
      .i64 data.book, .i64 0, .i64 data.trades,
      .i64 ctx.result.remaining, .i64 0, .i64 0, .i64 data.book,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 data.book] ++ List.replicate 18 (.i64 0)
    values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem residualStatusProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st (statusFrame book order ctx data) env) :
    wp «module» (LimitEntry.residualStatusProg ++ rest) Q st
      { LimitRunMatchResult.residualConditionFrame book order ctx data with
        values := [] } env := by
  simp only [LimitEntry.residualStatusProg]
  refine wp_call_tw (Allocation.func19_spec env st) ?_
  rintro st1 values ⟨rfl, rfl⟩
  wp_run
  simpa [statusFrame, LimitRunMatchResult.residualConditionFrame,
    LimitRunMatchResult.resultFrame] using hNext

end Project.ClobLimit.LimitResidualStatus
