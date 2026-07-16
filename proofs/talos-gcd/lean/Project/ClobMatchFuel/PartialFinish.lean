import Project.ClobMatchFuel.PartialTradePrepare

/-!
# Partial-fill result finalization

The partial-fill branch exits after appending one trade.  It records the fresh
trade root, sets the remaining quantity to zero, and marks the loop result as
complete.  This module proves the final local assignments before loop re-entry.
-/

namespace Project.ClobMatchFuel.PartialFinish

open Wasm Project.ClobMatchFuel

def partialFinishProg : Wasm.Program :=
  [
  .localSet 65,
  .localGet 65,
  .localSet 22,
  .constI64 0,
  .localSet 23,
  .constI64 1,
  .localSet 24
  ]

def partialFinishFrame (base : Locals) (newTrades : UInt64) : Locals :=
  { base with
    locals := (((base.locals.set 56 (.i64 newTrades)).set 13
      (.i64 newTrades)).set 14 (.i64 0)).set 15 (.i64 1)
    values := [] }

set_option Elab.async false in
theorem partialFinishProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (newTrades : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [.i64 newTrades])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st (partialFinishFrame base newTrades) env) :
    wp «module» (partialFinishProg ++ rest) Q st base env := by
  simp (config := { maxSteps := 10000000 }) [partialFinishProg, wp_simp,
    Locals.get, Locals.set?, List.cons_append, List.nil_append,
    List.length_set,
    hParams, hLocals, hValues]
  simpa only [partialFinishFrame] using hDone

end Project.ClobMatchFuel.PartialFinish
