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
  Project.ClobMatchFuel.LoopInvariant

def statusFrame (book : UInt64) (order : OrderL) (ctx : Context)
    (data : HeapRunMatch.OutputData) : Locals :=
  let frame := LimitRunMatchResult.resultFrame book order ctx data
  { frame with locals := (((frame.locals.set 26 (.i64 0)).set 31 (.i64 0)).set
      27 (.i64 data.book)).set 36 (.i64 data.book) }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem residualStatusProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : Context)
    (data : HeapRunMatch.OutputData)
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
