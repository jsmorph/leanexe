import Verified.Wasi.ProcessCode
import Verified.Wasi.ModuleCompileInitial

namespace Verified.Wasi

open Wasm LeanExe.Pipeline

def ProcessEntry.startIndexWith (calls : List LeanExe.Wasi.Call) (source : Wasm.Module) (_entry : ProcessEntry effectSigs) : Nat :=
  Wrappers.effectIndexWith calls source effectSigs.length

def ProcessEntry.startIndex (source : Wasm.Module) (_entry : ProcessEntry effectSigs) : Nat :=
  ProcessEntry.startIndexWith [] source _entry

@[simp] theorem compileProcess_imports_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool) :
    (compileProcessWith calls source program entry pool).imports = ABI.importsWith calls := rfl

@[simp] theorem compileProcess_imports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool) :
    (compileProcess source program entry pool).imports = ABI.imports := by
  layout_instance compileProcess_imports_with

theorem compileProcess_effect_arity_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool) (callee : EffectVar effectSigs signature) :
    ∃ function,
      (compileProcessWith calls source program entry pool).funcs[
        Wrappers.effectIndexWith calls source callee.index - (ABI.importsWith calls).length]? = some function ∧
      function.numParams = 1 + widthSum signature.params := by
  have arity := (compileProcess_functionsIn_with (calls := calls) source program entry pool).arity callee
  simpa only [Wrappers.effectIndexWith, Module.extraIndexWith, ABI.importsWith_length,
    show 3 + calls.length + source.funcs.length + (3 + callee.index) - (3 + calls.length) =
      source.funcs.length + (3 + callee.index) by omega] using arity

theorem compileProcess_effect_arity (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool) (callee : EffectVar effectSigs signature) :
    ∃ function,
      (compileProcess source program entry pool).funcs[
        Wrappers.effectIndex source callee.index - ABI.imports.length]? = some function ∧
      function.numParams = 1 + widthSum signature.params := by
  layout_instance compileProcess_effect_arity_with

theorem compileProcess_start_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) :
    (compileProcessWith calls source program entry pool).funcs[
      source.funcs.length + (3 + effectSigs.length)]? =
      some (entry.functionWith calls source (effectTypeIndex source effectSigs.length)) := by
  change (Module.assembleWith calls source (Wrappers.extensionWith calls source
    (entry.extensionWith calls source program pool))).funcs[source.funcs.length + (3 + effectSigs.length)]? = _
  rw [Wrappers.next_function_with]
  change (program.functionsWith calls source pool ++ [_])[effectSigs.length]? = _
  rw [List.getElem?_append_right (by rw [program.functions_length_with source pool]),
    program.functions_length_with source pool, Nat.sub_self]
  rfl

theorem compileProcess_start (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) :
    (compileProcess source program entry pool).funcs[
      source.funcs.length + (3 + effectSigs.length)]? =
      some (entry.function source (effectTypeIndex source effectSigs.length)) := by
  layout_instance compileProcess_start_with

theorem compileProcess_export_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) :
    ({ name := "_start", funcIdx := Wrappers.effectIndexWith calls source effectSigs.length } : Wasm.Export) ∈
      (compileProcessWith calls source program entry pool).exports := List.mem_singleton_self _

theorem compileProcess_export (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) :
    ({ name := "_start", funcIdx := Wrappers.effectIndex source effectSigs.length } : Wasm.Export) ∈
      (compileProcess source program entry pool).exports := by
  layout_instance compileProcess_export_with

theorem compileProcess_initialStore (pure : Prog pureSigs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper pureSigs tables.length)) (pool : Bytes.LiteralPool)
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs) (world : World)
    (poolBase : pool.base = tablesEnd tables) (fits : pool.top ≤ 65535 * 65536) :
    let source := Verified.compileWith pure tables wrappers pool
    let target := compileProcess source program entry pool
    let store := PureTransport.erase (PureTransport.restore world (target.initialStore : Store Unit))
    (initialStaticHeap pool).At store ∧ store.memoryCap target 0 ≤ 65535 ∧
      pool.Static (initialStaticHeap pool) store := by
  have initialized := Module.compileWith_initialStaticStore pure tables wrappers pool
    (Wrappers.extension (Verified.compileWith pure tables wrappers pool)
      (entry.extension (Verified.compileWith pure tables wrappers pool) program pool)) world poolBase fits
  exact ⟨initialized.1, initialized.2.1, initialized.2.2.2⟩

end Verified.Wasi
