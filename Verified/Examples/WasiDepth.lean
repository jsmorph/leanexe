import Verified.Wasi.ReflectCommand

namespace Verified.Examples.WasiDepth

open LeanExe.Wasi

set_option verified.tailLoops false

def table : Array UInt64 := #[10]

def guarded (values : Array UInt64) (count : UInt64) : UInt64 :=
  if count = 0 then values[(0 : UInt64).toNat]! else guarded values (count - 1) + 1
termination_by count.toNat
decreasing_by
  rename_i nonzero
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at nonzero ⊢
  omega

def pureHelper (values : Array UInt64) (count : UInt64) : UInt64 := guarded values count + 1

def fromTable (count : UInt64) : UInt64 := pureHelper table count

def effectHelper (count : UInt64) : Action UInt64 := do
  let _ ← writeStdoutSome bytes![68, 10]
  pure (fromTable count)

def effectCaller (count : UInt64) : Action UInt64 := effectHelper count

verified_compile_wasi compiled := [guarded, pureHelper, fromTable, effectHelper, effectCaller]

#guard compiled.pure.tables = [table]
#guard compiled.pure.wrappers.map (·.depth) = [true]
#guard compiled.effectHelper.func.params = [.array .word, .word]
#guard compiled.effectHelper.func.modes = [.borrowed, .borrowed]
#guard compiled.effectCaller.func.params = [.array .word, .word]
#guard compiled.effectCaller.func.modes = [.borrowed, .borrowed]
#guard compiled.module.exports.map Wasm.Export.name = ["alloc", "release", "effectHelper", "effectCaller"]

end Verified.Examples.WasiDepth
