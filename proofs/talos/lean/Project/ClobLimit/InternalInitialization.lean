import Project.ClobLimit.InternalLoopResult

/-!
# Internal match-state initialization

The recursive matcher receives its complete state in eleven parameters.  Its
initialization clears the completion flag before entering the outer loop.  The
instruction leaves the store and all parameters unchanged.
-/

namespace Project.ClobLimit.InternalInitialization

open Wasm Project.ClobLimit

def initProg : Wasm.Program :=
  [
  .constI64 0,
  .localSet 16
  ]

def initFrame (base : Locals) : Locals :=
  { base with locals := base.locals.set 5 (.i64 0), values := [] }

set_option Elab.async false in
theorem initProg_spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q st (initFrame base) env) :
    wp «module» (initProg ++ rest) Q st base env := by
  simp only [initProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals,
    hValues]
  simpa [initFrame] using hDone

end Project.ClobLimit.InternalInitialization
