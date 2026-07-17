import Project.ClobLimit.RunMatchCall

/-!
# `runMatch` result epilogue

Function 18 copies the five values returned by function 17 through result
locals and returns them in the same order.  This module proves that exact
stack behavior for an arbitrary compatible caller frame.
-/

namespace Project.ClobLimit.RunMatchResult

open Wasm Project.ClobLimit

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem resultProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (values : List Value)
    (ctx : InternalLoopInvariant.Context)
    (data : InternalLoopResult.OutputData)
    (hParams : base.params.length = 7)
    (hLocals : base.locals.length = 35)
    (hValues : values = InternalLoopResult.outputValues ctx data)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Locals,
      final.values = InternalLoopResult.outputValues ctx data →
      wp «module» rest Q st final env) :
    wp «module» (RunMatchEntry.resultProg ++ rest) Q st
      { base with values := values } env := by
  simp only [RunMatchEntry.resultProg, List.cons_append, List.nil_append]
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals,
    hValues, InternalLoopResult.outputValues]
  apply hNext
  rfl

end Project.ClobLimit.RunMatchResult
