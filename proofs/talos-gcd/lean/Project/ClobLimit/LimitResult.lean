import Project.ClobLimit.LimitResidualFinish

/-!
# Exported `limit` result epilogue

The final three local reads return status, book, and trades in the artifact's
multi-result stack order.  This theorem keeps that local-frame reduction out
of the exported branch compositions.
-/

namespace Project.ClobLimit.LimitResult

open Wasm Project.ClobLimit

def outputFrame (base : Locals)
    (data : InternalLoopResult.OutputData) : Locals :=
  { base with
    values := [.i64 data.trades, .i64 (data.g0 + 48), .i64 0] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem resultProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (ctx : InternalLoopInvariant.Context)
    (data : InternalLoopResult.OutputData)
    (hResult : LimitResidualFinish.ResultLocalsAt base ctx data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st (outputFrame base data) env) :
    wp «module» (LimitEntry.resultProg ++ rest) Q st base env := by
  rcases hResult with
    ⟨hParams, hLocals, hValues, hStatus, hBook, hTrades⟩
  have hStatusValue : base.locals[31] = .i64 0 := by
    apply Option.some.inj
    calc
      some base.locals[31] = base.locals[31]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 0) := hStatus
  have hBookValue : base.locals[32] = .i64 (data.g0 + 48) := by
    apply Option.some.inj
    calc
      some base.locals[32] = base.locals[32]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (data.g0 + 48)) := hBook
  have hTradesValue : base.locals[33] = .i64 data.trades := by
    apply Option.some.inj
    calc
      some base.locals[33] = base.locals[33]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 data.trades) := hTrades
  simp only [LimitEntry.resultProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, Locals.get, hParams, hLocals, hValues, hStatusValue,
      hBookValue, hTradesValue]
  simpa [outputFrame] using hNext

end Project.ClobLimit.LimitResult
