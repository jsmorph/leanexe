import Verified.Wasi.ProgramCorrect
import Verified.Wasi.CostCommandCorrect

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem EffectProg.correct_with {calls : List LeanExe.Wasi.Call}
    {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (effectCalls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (sourceHost : HostEnv Unit)
    (ready : program.Ready source pool) (covered : program.Covered pool) :
    CostEffectCallsWith calls source (compileCalls calls source program entries main pool) pure program pool :=
  program.correctCost_with entries main pool runtime profile effectCalls poolApart sourceHost
    (fun {_} _ facts effectCalls {_} {_} command =>
      Command.cost_code_spec_with facts effectCalls sourceHost command)
    ready covered

theorem EffectProg.correct {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (sourceHost : HostEnv Unit)
    (ready : program.Ready source pool) (covered : program.Covered pool) :
    CostEffectCalls source (compile source program entries main pool) pure program pool := by
  layout_instance EffectProg.correct_with

theorem EffectProg.correctWith_with {calls : List LeanExe.Wasi.Call}
    {pureSigs : List Sig} (pure : Prog pureSigs)
    (funs : Funs pureSigs) (meaning : pure.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper pureSigs tables.length)) (pool : Bytes.LiteralPool)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs))
    (profile : Relocation.Profile (Verified.compileWith pure tables wrappers pool))
    (pureCovered : pure.Covered pool) (covered : program.Covered pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (ready : program.Ready (Verified.compileWith pure tables wrappers pool) pool)
    (sourceHost : HostEnv Unit) :
    CostEffectCallsWith calls (Verified.compileWith pure tables wrappers pool)
      (compileCalls calls (Verified.compileWith pure tables wrappers pool) program entries main pool)
      (Resource.PureContext.ofProg pure funs) program pool :=
  correctCostWith_with (calls := calls) pure funs meaning tables wrappers pool program entries main profile pureCovered
    covered poolApart ready sourceHost
    (fun {_} _ facts effectCalls {_} {_} command =>
      Command.cost_code_spec_with facts effectCalls sourceHost command)

theorem EffectProg.correctWith {pureSigs : List Sig} (pure : Prog pureSigs)
    (funs : Funs pureSigs) (meaning : pure.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper pureSigs tables.length)) (pool : Bytes.LiteralPool)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs))
    (profile : Relocation.Profile (Verified.compileWith pure tables wrappers pool))
    (pureCovered : pure.Covered pool) (covered : program.Covered pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (ready : program.Ready (Verified.compileWith pure tables wrappers pool) pool)
    (sourceHost : HostEnv Unit) :
    CostEffectCalls (Verified.compileWith pure tables wrappers pool)
      (compile (Verified.compileWith pure tables wrappers pool) program entries main pool)
      (Resource.PureContext.ofProg pure funs) program pool := by
  layout_instance EffectProg.correctWith_with

end Verified.Wasi
