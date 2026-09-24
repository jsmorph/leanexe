import Project.ClobLimit.HeapAppendFrames

namespace Project.ClobLimit.HeapAppendResult
open Wasm Project.Common Project.Clob Project.ClobLimit
open Project.ClobMatchFuel.LoopInvariant

structure LocalsAt (frame : Locals) (book trades : UInt64) : Prop where
  params : frame.params.length = 6
  locals : frame.locals.length = 55
  values : frame.values = []
  status : frame.locals[31]? = some (.i64 0)
  book : frame.locals[33]? = some (.i64 book)
  trades : frame.locals[35]? = some (.i64 trades)

def resultFrame (base : Locals) (book trades : UInt64) : Locals :=
  { base with
    locals := (((base.locals.set 32 (.i64 book)).set 33 (.i64 book)).set
      34 (base.locals[22]!)).set 35 (.i64 trades)
    values := [] }

set_option maxRecDepth 1048576
set_option Elab.async false in
theorem spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (root : UInt64) (order : OrderL) (ctx : Context) (data : HeapRunMatch.OutputData)
    (h : HeapAppendFrames.CopyLocalsAt base root order ctx data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, LocalsAt final root data.trades → wp «module» rest Q st final env) :
    wp «module» (LimitEntry.residualResultProg ++ rest) Q st base env := by
  have hp := h.stores.params
  have hl := h.stores.locals
  have hv := h.stores.values
  have hr := getElem_of_some h.stores.target
  have ht := getElem_of_some h.trades
  have hStatus := getElem_of_some h.status
  have hResult : LocalsAt (resultFrame base root data.trades) root data.trades := by
    constructor <;> simp [resultFrame, hp, hl, hv, hStatus]
  have hContinue := hNext (resultFrame base root data.trades) hResult
  simp only [LimitEntry.residualResultProg, List.cons_append, List.nil_append]
  wp_run_with [hp, hl, hv, hr, ht]
  simpa [resultFrame, hl, getElem!_pos] using hContinue

set_option Elab.async false in
theorem export_spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book trades : UInt64) (h : LocalsAt base book trades)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      {base with values := [.i64 trades, .i64 book, .i64 0]} env) :
    wp «module» (LimitEntry.resultProg ++ rest) Q st base env := by
  rcases h with ⟨hp, hl, hv, hs, hb, ht⟩
  have hs' := getElem_of_some hs
  have hb' := getElem_of_some hb
  have ht' := getElem_of_some ht
  simp only [LimitEntry.resultProg, List.cons_append, List.nil_append]
  wp_run_with [hp, hl, hv, hs', hb', ht']
  exact hNext

#print axioms spec
#print axioms export_spec
end Project.ClobLimit.HeapAppendResult
