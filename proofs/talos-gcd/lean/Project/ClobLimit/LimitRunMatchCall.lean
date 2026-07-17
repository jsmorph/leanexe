import Project.ClobLimit.LimitValidEntry

/-!
# Exported `limit` matcher call

The valid path passes a zero owner, the input book, and the five order fields
to function 18.  This theorem applies an arbitrary matching function 18
specification against an abstract continuation.
-/

namespace Project.ClobLimit.LimitRunMatchCall

open Wasm Project.Clob Project.ClobLimit

def callFrame (book : UInt64) (order : OrderL) : Locals :=
  { params := [.i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty]
    locals := [.i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty, .i64 1,
      .i64 0, .i64 book, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty] ++
        List.replicate 38 (.i64 0)
    values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem validCallProg_spec (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL)
    (P : Store Unit → List Value → Prop)
    (hCall : TerminatesWith (m := «module») (id := 18)
      (initial := st) (env := env)
      (RunMatchCorrect.runMatchArgs 0 book order) P)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (st' : Store Unit) (values : List Value), P st' values →
      wp «module» rest Q st' { callFrame book order with values := values }
        env) :
    wp «module» (LimitEntry.validCallProg ++ rest) Q st
      { LimitValidEntry.validFrame book order with values := [] } env := by
  simp only [LimitEntry.validCallProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, LimitValidEntry.validFrame]
  refine wp_call_tw hCall ?_
  intro st' values hPost
  simpa [callFrame] using hNext st' values hPost

end Project.ClobLimit.LimitRunMatchCall
