import Verified.Wasi.Program
import Verified.Wasi.ModuleTransport
import Verified.Wasi.CompilerFacts
import Verified.Correct

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

def EffectProg.FunctionsInWith (calls : List LeanExe.Wasi.Call) (source target : Wasm.Module) (pool : Bytes.LiteralPool)
    (program : EffectProg pureSigs effectSigs) : Prop :=
  ∀ index < effectSigs.length,
    target.funcs[source.funcs.length + (3 + index)]? = (program.functionsWith calls source pool)[index]?

def EffectProg.FunctionsIn (source target : Wasm.Module) (pool : Bytes.LiteralPool)
    (program : EffectProg pureSigs effectSigs) : Prop :=
  EffectProg.FunctionsInWith [] source target pool program

theorem compile_functionsIn_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) :
    program.FunctionsInWith calls source (compileCalls calls source program entries main pool) pool :=
  fun _ bound => compile_body_with source program entries main bound pool

theorem compile_functionsIn (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) :
    program.FunctionsIn source (compile source program entries main pool) pool := by
  layout_instance compile_functionsIn_with

theorem EffectProg.FunctionsInWith.tail {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module} {pool : Bytes.LiteralPool}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    (present : (EffectProg.cons function rest).FunctionsInWith calls source target pool) :
    rest.FunctionsInWith calls source target pool := by
  intro index bound
  have selected := present index (by simp only [List.length_cons]; omega)
  rw [EffectProg.functionsWith,
    List.getElem?_append_left (by rw [rest.functions_length_with source pool]; exact bound)] at selected
  exact selected

theorem EffectProg.FunctionsIn.tail {source target : Wasm.Module} {pool : Bytes.LiteralPool}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    (present : (EffectProg.cons function rest).FunctionsIn source target pool) :
    rest.FunctionsIn source target pool := by
  layout_instance EffectProg.FunctionsInWith.tail

theorem EffectProg.FunctionsInWith.head {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module} {pool : Bytes.LiteralPool}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    (present : (EffectProg.cons function rest).FunctionsInWith calls source target pool) :
    target.funcs[source.funcs.length + (3 + effectSigs.length)]? =
      some (function.functionWith calls source (effectTypeIndex source effectSigs.length) pool) := by
  have selected := present effectSigs.length (by simp only [List.length_cons]; omega)
  rw [EffectProg.functionsWith,
    List.getElem?_append_right (by rw [rest.functions_length_with source pool]),
    rest.functions_length_with source pool, Nat.sub_self] at selected
  exact selected

theorem EffectProg.FunctionsIn.head {source target : Wasm.Module} {pool : Bytes.LiteralPool}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    (present : (EffectProg.cons function rest).FunctionsIn source target pool) :
    target.funcs[source.funcs.length + (3 + effectSigs.length)]? =
      some (function.function source (effectTypeIndex source effectSigs.length) pool) := by
  layout_instance EffectProg.FunctionsInWith.head

theorem EffectProg.FunctionsInWith.arity {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module} {pool : Bytes.LiteralPool}
    {program : EffectProg pureSigs effectSigs}
    (present : program.FunctionsInWith calls source target pool) (callee : EffectVar effectSigs signature) :
    ∃ function, target.funcs[source.funcs.length + (3 + callee.index)]? = some function ∧
      function.numParams = 1 + widthSum signature.params := by
  have sameSignature := program.function_signature_with (calls := calls) source callee pool
  cases selected : (program.functionsWith calls source pool)[callee.index]? with
  | none =>
      rw [selected, Option.map_none] at sameSignature
      cases sameSignature
  | some function =>
      refine ⟨function, (present _ callee.index_lt).trans selected, ?_⟩
      rw [selected, Option.map_some] at sameSignature
      have same := congrArg FuncType.params (Option.some.inj sameSignature)
      change function.params = codeParams _ true at same
      change function.params.length = 1 + widthSum _
      rw [same]
      simp only [codeParams, ite_true, List.cons_append, List.nil_append,
        List.length_cons, flatMap_types_length]
      omega

theorem EffectProg.FunctionsIn.arity {source target : Wasm.Module} {pool : Bytes.LiteralPool}
    {program : EffectProg pureSigs effectSigs}
    (present : program.FunctionsIn source target pool) (callee : EffectVar effectSigs signature) :
    ∃ function, target.funcs[source.funcs.length + (3 + callee.index)]? = some function ∧
      function.numParams = 1 + widthSum signature.params := by
  layout_instance EffectProg.FunctionsInWith.arity

theorem compile_layout_with {calls : List LeanExe.Wasi.Call}
    {source : Wasm.Module} (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) (imports : source.imports = []) :
    Relocation.LayoutWith calls source (compileCalls calls source program entries main pool) := by
  refine ⟨imports, ?_, ?_, rfl, rfl⟩
  · rw [compile_imports_with, ABI.importsWith_length]
  · intro index function selected
    cases main with
    | none =>
      exact Module.pure_function_with
        (Wrappers.extensionWith calls source (program.callableExtensionWith calls source entries pool)) selected
    | some main =>
      exact Module.pure_function_with
        (Wrappers.extensionWith calls source (program.commandExtensionWith calls source main pool)) selected

theorem compile_layout {source : Wasm.Module} (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) (imports : source.imports = []) :
    Relocation.Layout source (compile source program entries main pool) := by
  layout_instance compile_layout_with

theorem compile_read_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).funcs[source.funcs.length]? =
      some (readFunctionWith calls (Module.extraTypeIndex source 0)) := by
  cases main with
  | none => exact Wrappers.read_function_with source (program.callableExtensionWith calls source entries pool)
  | some main => exact Wrappers.read_function_with source (program.commandExtensionWith calls source main pool)

theorem compile_read (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).funcs[source.funcs.length]? =
      some (readFunction (Module.extraTypeIndex source 0)) := by
  layout_instance compile_read_with

theorem compile_stdout_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).funcs[source.funcs.length + 1]? =
      some (writeFunction .stdout (Module.extraTypeIndex source 1)) := by
  cases main with
  | none => exact Wrappers.stdout_function_with source (program.callableExtensionWith calls source entries pool)
  | some main => exact Wrappers.stdout_function_with source (program.commandExtensionWith calls source main pool)

theorem compile_stdout (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).funcs[source.funcs.length + 1]? =
      some (writeFunction .stdout (Module.extraTypeIndex source 1)) := by
  layout_instance compile_stdout_with

theorem compile_stderr_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).funcs[source.funcs.length + 2]? =
      some (writeFunction .stderr (Module.extraTypeIndex source 1)) := by
  cases main with
  | none => exact Wrappers.stderr_function_with source (program.callableExtensionWith calls source entries pool)
  | some main => exact Wrappers.stderr_function_with source (program.commandExtensionWith calls source main pool)

theorem compile_stderr (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).funcs[source.funcs.length + 2]? =
      some (writeFunction .stderr (Module.extraTypeIndex source 1)) := by
  layout_instance compile_stderr_with

theorem compile_effect_arity_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) (callee : EffectVar effectSigs signature) :
    ∃ function,
      (compileCalls calls source program entries main pool).funcs[
        Wrappers.effectIndexWith calls source callee.index -
          (compileCalls calls source program entries main pool).imports.length]? = some function ∧
      function.numParams = 1 + widthSum signature.params := by
  have arity := (compile_functionsIn_with (calls := calls) source program entries main pool).arity
    callee
  simpa only [Wrappers.effectIndexWith, Module.extraIndexWith, compile_imports_with,
    ABI.importsWith_length,
    show 3 + calls.length + source.funcs.length + (3 + callee.index) - (3 + calls.length) =
      source.funcs.length + (3 + callee.index) by omega] using arity

theorem compile_effect_arity (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) (callee : EffectVar effectSigs signature) :
    ∃ function,
      (compile source program entries main pool).funcs[
        Wrappers.effectIndex source callee.index -
          (compile source program entries main pool).imports.length]? = some function ∧
      function.numParams = 1 + widthSum signature.params := by
  layout_instance compile_effect_arity_with

theorem compiled_pure_calls (program : Prog pureSigs) (funs : Funs pureSigs)
    (meaning : program.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper pureSigs tables.length)) (pool : Bytes.LiteralPool)
    (covered : program.Covered pool) :
    Calls (Verified.compileWith program tables wrappers pool)
      (Resource.PureContext.ofProg program funs).funs
      (Resource.PureContext.ofProg program funs).flags
      (Resource.PureContext.ofProg program funs).bounds
      (Resource.PureContext.ofProg program funs).fits pool :=
  program.correctStaticWith funs meaning tables wrappers pool covered

end Verified.Wasi
