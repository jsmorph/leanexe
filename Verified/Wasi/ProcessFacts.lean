import Verified.Wasi.ProcessCode
import Verified.Wasi.ModuleCompileInitial

namespace Verified.Wasi

open Wasm LeanExe.Pipeline

def ProcessEntry.startIndex (source : Wasm.Module) (_entry : ProcessEntry effectSigs) : Nat :=
  Wrappers.effectIndex source effectSigs.length

@[simp] theorem compileProcess_imports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool) :
    (compileProcess source program entry pool).imports = ABI.imports := rfl

theorem compileProcess_effect_arity (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool) (callee : EffectVar effectSigs signature) :
    ∃ function,
      (compileProcess source program entry pool).funcs[
        Wrappers.effectIndex source callee.index - ABI.imports.length]? = some function ∧
      function.numParams = 1 + widthSum signature.params := by
  have arity := (compileProcess_functionsIn source program entry pool).arity callee
  simpa only [Wrappers.effectIndex, Module.extraIndex, ABI.imports_length,
    show 3 + source.funcs.length + (3 + callee.index) - 3 =
      source.funcs.length + (3 + callee.index) by omega] using arity

theorem compileProcess_start (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) :
    (compileProcess source program entry pool).funcs[
      source.funcs.length + (3 + effectSigs.length)]? =
      some (entry.function source (effectTypeIndex source effectSigs.length)) := by
  change (Module.assemble source (Wrappers.extension source
    (entry.extension source program pool))).funcs[source.funcs.length + (3 + effectSigs.length)]? = _
  rw [Wrappers.next_function]
  change (program.functions source pool ++ [_])[effectSigs.length]? = _
  rw [List.getElem?_append_right (by rw [program.functions_length source pool]),
    program.functions_length source pool, Nat.sub_self]
  rfl

theorem compileProcess_export (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) :
    ({ name := "_start", funcIdx := Wrappers.effectIndex source effectSigs.length } : Wasm.Export) ∈
      (compileProcess source program entry pool).exports := List.mem_singleton_self _

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
