import Project.ClobLimit.InternalPartialTradeUpdate

/-!
# Partial-fill result finalization

The partial-fill branch records the new trade array in the recursive result
locals.  It sets the remaining quantity to zero and marks the result as
complete.  This module proves the exact assignments before loop re-entry.
-/

namespace Project.ClobLimit.InternalPartialFinish

open Wasm Project.ClobLimit

def partialFinishProg : Wasm.Program :=
  [
  .localSet 13,
  .localGet 13,
  .localSet 14,
  .constI64 0,
  .localSet 15,
  .constI64 1,
  .localSet 16
  ]

def partialFinishFrame (base : Locals) (newTrades : UInt64) : Locals :=
  { base with
    locals := (((base.locals.set 2 (.i64 newTrades)).set 3
      (.i64 newTrades)).set 4 (.i64 0)).set 5 (.i64 1)
    values := [] }

set_option Elab.async false in
theorem partialFinishProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (newTrades : UInt64)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [.i64 newTrades])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st (partialFinishFrame base newTrades) env) :
    wp «module» (partialFinishProg ++ rest) Q st base env := by
  simp (config := { maxSteps := 10000000 }) [partialFinishProg, wp_simp,
    Locals.get, Locals.set?, List.cons_append, List.nil_append,
    List.length_set, hParams, hLocals, hValues]
  simpa only [partialFinishFrame] using hDone

end Project.ClobLimit.InternalPartialFinish
