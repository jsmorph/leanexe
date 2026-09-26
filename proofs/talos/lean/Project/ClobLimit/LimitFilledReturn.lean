import Project.ClobLimit.LimitRunMatchResult
import Project.ClobLimit.Allocation

namespace Project.ClobLimit.LimitFilledReturn

open Wasm Project.Clob Project.ClobLimit

set_option maxRecDepth 1048576

structure ResultAt (frame : Locals) (data : MatchOutput.OutputData) : Prop where
  params : frame.params.length = 6
  locals : frame.locals.length = 55
  values : frame.values = []
  status : frame.locals[31]? = some (.i64 0)
  book : frame.locals[33]? = some (.i64 data.book)
  trades : frame.locals[35]? = some (.i64 data.trades)

theorem program_spec (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (ctx : MatchInvariant.Context)
    (data : MatchOutput.OutputData) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Locals, ResultAt final data → wp «module» rest Q st final env) :
    wp «module» (LimitEntry.filledProg ++ rest) Q st
      { LimitRunMatchResult.filledConditionFrame book order ctx data with values := [] }
      env := by
  simp only [LimitEntry.filledProg, List.cons_append, List.nil_append]
  refine wp_call_tw (Allocation.func19_spec env st) ?_
  rintro st1 values ⟨rfl, rfl⟩
  simp only [LimitRunMatchResult.filledConditionFrame, LimitRunMatchResult.resultFrame]
  wp_run
  apply hNext
  constructor <;> simp

theorem result_spec (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (data : MatchOutput.OutputData) (hFrame : ResultAt frame data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Locals,
      final.values = [.i64 data.trades, .i64 data.book, .i64 0] →
      wp «module» rest Q st final env) :
    wp «module» (LimitEntry.resultProg ++ rest) Q st frame env := by
  rcases hFrame with ⟨hParams, hLocals, hValues, hStatus, hBook, hTrades⟩
  simp only [LimitEntry.resultProg, List.cons_append, List.nil_append]
  simp [wp_simp, Locals.get, hParams, hLocals, hValues,
    Project.Common.getElem_of_some hStatus, Project.Common.getElem_of_some hBook,
    Project.Common.getElem_of_some hTrades]
  apply hNext
  rfl

end Project.ClobLimit.LimitFilledReturn
