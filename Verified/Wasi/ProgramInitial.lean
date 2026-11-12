import Verified.Wasi.Program
import Verified.Wasi.ModuleCompileInitial

namespace Verified.Wasi

open Wasm LeanExe.Pipeline

def compileInitialStore (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) (world : World) : Store World :=
  PureTransport.restore world ((compile source program entries main pool).initialStore : Store Unit)

@[simp] theorem compileInitialStore_host (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) (world : World) :
    (compileInitialStore source program entries main pool world).host = world := rfl

/-- The initial store of the module that imports the flat calls `calls`. -/
def compileInitialStoreWith (calls : List LeanExe.Wasi.Call) (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) (world : World) :
    Store World :=
  PureTransport.restore world
    ((compileCalls calls source program entries main pool).initialStore : Store Unit)

@[simp] theorem compileInitialStoreWith_host (calls : List LeanExe.Wasi.Call)
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (pool : Bytes.LiteralPool) (world : World) :
    (compileInitialStoreWith calls source program entries main pool world).host = world := rfl

theorem compileWith_initialStore_with {calls : List LeanExe.Wasi.Call} {pureSigs : List Sig}
    (pure : Prog pureSigs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper pureSigs tables.length)) (pool : Bytes.LiteralPool)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (world : World)
    (poolBase : pool.base = tablesEnd tables) (poolFit : pool.top ≤ 65535 * 65536) :
    let source := Verified.compileWith pure tables wrappers pool
    let target := compileCalls calls source program entries main pool
    let store := PureTransport.erase
      (compileInitialStoreWith calls source program entries main pool world)
    (initialStaticHeap pool).At store ∧ store.memoryCap target 0 ≤ 65535 ∧
      (∀ index (bound : index < tables.length),
        (initialStaticHeap pool).Borrowed store (tableAddr tables index) tables[index]) ∧
      pool.Static (initialStaticHeap pool) store := by
  cases main with
  | none =>
      exact Module.compileWith_initialStaticStore_with (calls := calls) pure tables wrappers pool
        (Wrappers.extensionWith calls (Verified.compileWith pure tables wrappers pool)
          (program.callableExtensionWith calls (Verified.compileWith pure tables wrappers pool)
            entries pool))
        world poolBase poolFit
  | some entry =>
      exact Module.compileWith_initialStaticStore_with (calls := calls) pure tables wrappers pool
        (Wrappers.extensionWith calls (Verified.compileWith pure tables wrappers pool)
          (program.commandExtensionWith calls (Verified.compileWith pure tables wrappers pool)
            entry pool))
        world poolBase poolFit

theorem compileWith_initialStore {pureSigs : List Sig} (pure : Prog pureSigs)
    (tables : List (Array UInt64)) (wrappers : List (Wrapper pureSigs tables.length))
    (pool : Bytes.LiteralPool) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs)) (world : World)
    (poolBase : pool.base = tablesEnd tables) (poolFit : pool.top ≤ 65535 * 65536) :
    let source := Verified.compileWith pure tables wrappers pool
    let target := compile source program entries main pool
    let store := PureTransport.erase (compileInitialStore source program entries main pool world)
    (initialStaticHeap pool).At store ∧ store.memoryCap target 0 ≤ 65535 ∧
      (∀ index (bound : index < tables.length),
        (initialStaticHeap pool).Borrowed store (tableAddr tables index) tables[index]) ∧
      pool.Static (initialStaticHeap pool) store := by
  cases main with
  | none =>
      exact Module.compileWith_initialStaticStore pure tables wrappers pool
        (Wrappers.extension (Verified.compileWith pure tables wrappers pool)
          (program.callableExtension (Verified.compileWith pure tables wrappers pool) entries pool))
        world poolBase poolFit
  | some entry =>
      exact Module.compileWith_initialStaticStore pure tables wrappers pool
        (Wrappers.extension (Verified.compileWith pure tables wrappers pool)
          (program.commandExtension (Verified.compileWith pure tables wrappers pool) entry pool))
        world poolBase poolFit

end Verified.Wasi
