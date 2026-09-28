import LeanExe.Core.Examples
import LeanExe.Core.StateExamples
import Project.Core.Frontend

namespace Project.Core.FrontendExamples

run_elab Frontend.compile ``LeanExe.Core.Examples.gcd `Project.Core.FrontendExamples.gcdModule
run_elab Frontend.compileState ``LeanExe.Core.StateExamples.updateByte `Project.Core.FrontendExamples.updateModule

/-- The public compiler entry point produces the actual Talos Module. -/
example : Wasm.Module := gcdModule
example : Wasm.Encoding.Spec.Validity.Module gcdModule := gcdModule.valid
example : Wasm.Encoding.Ready gcdModule := gcdModule.ready

example (a b : UInt64) (host : Wasm.HostEnv α) (store : Wasm.Store α) :
    Wasm.TerminatesWith host gcdModule gcdModule.entry store [.i64 b, .i64 a]
      (fun final values => final = store ∧ values = [.i64 (LeanExe.Core.Examples.gcd a b)]) :=
  gcdModule.correct [a, b] rfl α host store

example : Wasm.Encoding.Spec.Validity.Module updateModule := updateModule.valid
example : Wasm.Encoding.Ready updateModule := updateModule.ready

#print axioms gcdModule.correct
#print axioms updateModule.correct

end Project.Core.FrontendExamples
