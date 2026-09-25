import Project.ClobLimit.LimitResidualFinish
import Project.Common

/-!
# Exported `limit` result epilogue

The final three local reads return status, book, and trades in the artifact's
multi-result stack order.  This theorem keeps that local-frame reduction out
of the exported branch compositions.
-/

namespace Project.ClobLimit.LimitResult

open Wasm Project.Common Project.ClobLimit

def outputFrame (base : Locals)
    (data : MatchOutput.OutputData) (target : UInt64) : Locals :=
  { base with
    values := [.i64 data.trades, .i64 target, .i64 0] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem resultProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (ctx : MatchInvariant.Context)
    (data : MatchOutput.OutputData) (target : UInt64)
    (hResult : LimitResidualFinish.ResultLocalsAt base ctx data target)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st (outputFrame base data target) env) :
    wp «module» (LimitEntry.resultProg ++ rest) Q st base env := by
  rcases hResult with
    ⟨hParams, hLocals, hValues, hStatus, hBook, hTrades⟩
  have hStatusValue : base.locals[31] = .i64 0 := getElem_of_some hStatus
  have hBookValue : base.locals[33] = .i64 target := getElem_of_some hBook
  have hTradesValue : base.locals[35] = .i64 data.trades := getElem_of_some hTrades
  simp only [LimitEntry.resultProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, Locals.get, hParams, hLocals, hValues, hStatusValue,
      hBookValue, hTradesValue]
  simpa [outputFrame] using hNext

end Project.ClobLimit.LimitResult
