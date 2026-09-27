import Project.Core.Correctness

namespace Project.Core

/-- Pure source execution preserves the entire caller store. The theorem is
about the compiler's actual output module, including recursive functions. -/
theorem pure_correct (source : LeanExe.Core.Module)
    (executed : LeanExe.Core.Invokes source (fun _ _ (_ : Unit) _ _ => False)
      callee () args () value)
    (host : Wasm.HostEnv α) (store : Wasm.Store α)
    (exports : List Wasm.Export := []) :
    Wasm.TerminatesWith host (compile source (exports := exports)) callee store
      (args.map Wasm.Value.i64).reverse
      (fun final values => final = store ∧ values = [.i64 value]) := by
  let context : Context Unit α := {
    source := source
    effects := fun _ _ _ _ _ => False
    target := compile source (exports := exports)
    host := host
    effectCode := fun _ => []
    represents := fun _ next => next = store
    functions := by
      intro index function found
      simp [compile, List.getElem?_map, found]
    effectCorrect := by
      intro operation args initial value final impossible
      exact impossible.elim }
  simpa only [context, compile, List.length_nil, Nat.zero_add] using
    invocation_correct context executed store rfl

end Project.Core
