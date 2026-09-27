import Project.Core.Native
import Project.Core.Check
import Project.Core.Ready

namespace Project.Core

/-- The compiler result includes its original Lean meaning and the premises
required by the existing Talos-module encoder. -/
structure Compiled {arity : Nat} (function : LeanExe.Core.Native arity) where
  target : Wasm.Module
  entry : Nat
  valid : Wasm.Encoding.Spec.Validity.Module target
  ready : Wasm.Encoding.Ready target
  correct : ∀ (args : List UInt64), args.length = arity →
    ∀ (α : Type) (host : Wasm.HostEnv α) (store : Wasm.Store α),
      Wasm.TerminatesWith host target entry store (args.map Wasm.Value.i64).reverse
        (fun final values => final = store ∧
          values = [.i64 (LeanExe.Core.applyNative function args)])

def SourceLimits (source : LeanExe.Core.Module) (entry : Nat) : Prop :=
  source.length < 2 ^ 32 ∧
  (∀ function ∈ source, function.params + function.locals +
    max (width function.body) function.result.scratchWidth < 2 ^ 32) ∧
  entry < source.length

instance (source : LeanExe.Core.Module) (entry : Nat) : Decidable (SourceLimits source entry) := by
  unfold SourceLimits
  infer_instance

theorem native_valid {arity : Nat} {function : LeanExe.Core.Native arity}
    (certificate : LeanExe.Core.NativeCertificate function)
    (checked : Validity.checkSource certificate.source (fun _ => none) = true)
    (limits : SourceLimits certificate.source certificate.entry) (name : String) :
    Wasm.Encoding.Spec.Validity.Module (nativeModule certificate name) := by
  apply Validity.compile_valid certificate.source (fun _ => []) []
    [{ name, funcIdx := certificate.entry }] none (fun _ => none)
  · exact Validity.checkSource_sound _ _ checked
  · intro operation arity impossible
    contradiction
  · simp
  · exact limits.2.1
  · simp
  · simpa using limits.1
  · simpa using limits.2.2
  · simp

/-- Check the finite structural and size conditions, then return the proved
module. No decoder, external validation tool or per-program typing proof is used. -/
def compileNative {arity : Nat} {function : LeanExe.Core.Native arity}
    (certificate : LeanExe.Core.NativeCertificate function) (name : String := "main") :
    Except String (Compiled function) :=
  if checked : Validity.checkSource certificate.source (fun _ => none) = true then
    if limits : SourceLimits certificate.source certificate.entry then
      if sizes : Validity.ReadyLimits (nativeModule certificate name) then
        .ok {
          target := nativeModule certificate name
          entry := certificate.entry
          valid := native_valid certificate checked limits name
          ready := Validity.module_ready (native_valid certificate checked limits name) sizes
          correct := fun args length _ host store => native_correct certificate args length host store name }
      else .error "module exceeds a WASM binary size limit"
    else .error "invalid entry or WASM function/local limit exceeded"
  else .error "invalid source variable index or call signature"

end Project.Core
