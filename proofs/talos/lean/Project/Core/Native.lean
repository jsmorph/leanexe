import LeanExe.Core.Native
import Project.Core.Module

namespace Project.Core

/-- The exported module for a certified ordinary Lean definition. -/
def nativeModule {arity : Nat} {function : LeanExe.Core.Native arity}
    (certificate : LeanExe.Core.NativeCertificate function)
    (name : String := "main") : Wasm.Module :=
  compile certificate.source (exports := [{ name, funcIdx := certificate.entry }])

/-- Correctness is stated using the original Lean function's value. -/
theorem native_correct {arity : Nat} {function : LeanExe.Core.Native arity}
    (certificate : LeanExe.Core.NativeCertificate function)
    (args : List UInt64) (length : args.length = arity)
    (host : Wasm.HostEnv α) (store : Wasm.Store α) (name : String := "main") :
    Wasm.TerminatesWith host (nativeModule certificate name) certificate.entry store
      (args.map Wasm.Value.i64).reverse
      (fun final values => final = store ∧
        values = [.i64 (LeanExe.Core.applyNative function args)]) :=
  pure_correct certificate.source (certificate.correct args length) host store _

end Project.Core
