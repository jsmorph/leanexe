import LeanExe.Core.StateNative
import Project.Core.Compiler
import Project.Core.MemoryModuleValidity

namespace Project.Core

/-- The ordinary Lean state computation determines both the returned word and
all accessible bytes of the final Talos memory. -/
structure MemoryCompiled {arity : Nat} (function : LeanExe.Core.StateNative ByteArray arity) where
  target : Wasm.Module
  entry : Nat
  valid : Wasm.Encoding.Spec.Validity.Module target
  ready : Wasm.Encoding.Ready target
  correct : ∀ (args : List UInt64), args.length = arity →
    ∀ (initial : ByteArray) (α : Type) (host : Wasm.HostEnv α) (store : Wasm.Store α),
      MemoryGrow.MemoryAt initial store.mem → store.memoryCap target 0 = 65536 →
      Wasm.TerminatesWith host target entry store (args.map Wasm.Value.i64).reverse
        (fun final values =>
          (MemoryGrow.MemoryAt (LeanExe.Core.applyStateNative function args initial).2 final.mem ∧
            final.memoryCap target 0 = 65536) ∧
          values = [.i64 (LeanExe.Core.applyStateNative function args initial).1])

def nativeMemoryModule {arity : Nat} {function : LeanExe.Core.StateNative ByteArray arity}
    (certificate : LeanExe.Core.StateCertificate LeanExe.Core.Memory.effects function)
    (name : String := "main") : Wasm.Module :=
  MemoryRuntime.memoryModule certificate.source [{ name, funcIdx := certificate.entry }]

theorem native_memory_valid {arity : Nat} {function : LeanExe.Core.StateNative ByteArray arity}
    (certificate : LeanExe.Core.StateCertificate LeanExe.Core.Memory.effects function)
    (checked : Validity.checkSource certificate.source LeanExe.Core.Memory.effectArity = true)
    (limits : SourceLimits certificate.source certificate.entry)
    (functions : certificate.source.length + 4 < 2 ^ 32) (name : String) :
    Wasm.Encoding.Spec.Validity.Module (nativeMemoryModule certificate name) := by
  apply MemoryModuleValidity.module_valid_exports certificate.source _
    (Validity.checkSource_sound _ _ checked) limits.2.1 functions
  · intro entry member
    have same : entry = { name := name, funcIdx := certificate.entry } := by simpa using member
    subst entry
    have bound := limits.2.2
    dsimp
    omega
  · simp

theorem native_memory_correct {arity : Nat} {function : LeanExe.Core.StateNative ByteArray arity}
    (certificate : LeanExe.Core.StateCertificate LeanExe.Core.Memory.effects function)
    (args : List UInt64) (length : args.length = arity) (initial : ByteArray)
    (host : Wasm.HostEnv α) (store : Wasm.Store α)
    (represented : MemoryGrow.MemoryAt initial store.mem)
    (name : String := "main")
    (capacity : store.memoryCap (nativeMemoryModule certificate name) 0 = 65536) :
    Wasm.TerminatesWith host (nativeMemoryModule certificate name) certificate.entry store
      (args.map Wasm.Value.i64).reverse
      (fun final values =>
        (MemoryGrow.MemoryAt (LeanExe.Core.applyStateNative function args initial).2 final.mem ∧
          final.memoryCap (nativeMemoryModule certificate name) 0 = 65536) ∧
        values = [.i64 (LeanExe.Core.applyStateNative function args initial).1]) :=
  MemoryRuntime.correct certificate.source host (certificate.correct args length initial)
    store ⟨represented, capacity⟩ _

/-- Memory begins with sixteen zero-filled pages in the generated module. -/
theorem initial_memory_represents [Inhabited α] (source : LeanExe.Core.Module)
    (exports : List Wasm.Export := []) :
    MemoryRuntime.represents source (LeanExe.Core.Memory.zeroBytes (16 * 65536))
      ((MemoryRuntime.memoryModule source exports).initialStore : Wasm.Store α) := by
  constructor
  · change MemoryGrow.MemoryAt _ (Wasm.Mem.empty 16)
    exact MemoryGrow.MemoryAt.empty 16 (by decide)
  · rfl

def compileMemory {arity : Nat} {function : LeanExe.Core.StateNative ByteArray arity}
    (certificate : LeanExe.Core.StateCertificate LeanExe.Core.Memory.effects function)
    (name : String := "main") : Except String (MemoryCompiled function) :=
  if checked : Validity.checkSource certificate.source LeanExe.Core.Memory.effectArity = true then
    if limits : SourceLimits certificate.source certificate.entry then
      if functions : certificate.source.length + 4 < 2 ^ 32 then
        if sizes : Validity.ReadyLimits (nativeMemoryModule certificate name) then
          .ok {
            target := nativeMemoryModule certificate name
            entry := certificate.entry
            valid := native_memory_valid certificate checked limits functions name
            ready := Validity.module_ready
              (native_memory_valid certificate checked limits functions name) sizes
            correct := fun args length initial _ host store represented capacity =>
              native_memory_correct certificate args length initial host store represented name capacity }
        else .error "module exceeds a WASM binary size limit"
      else .error "source and memory runtime exceed the WASM function limit"
    else .error "invalid entry or WASM function/local limit exceeded"
  else .error "invalid source variable index or call signature"

end Project.Core
