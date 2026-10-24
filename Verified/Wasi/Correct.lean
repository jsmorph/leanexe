import Verified.Wasi.ProgramCorrect
import Verified.Wasi.CostCommandCorrect

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem EffectProg.correct {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (sourceHost : HostEnv Unit)
    (ready : program.Ready source pool) (covered : program.Covered pool) :
    CostEffectCalls source (compile source program entries main pool) pure program pool :=
  program.correctCost entries main pool runtime profile calls poolApart sourceHost
    (fun {_} _ facts effectCalls {_} {_} command =>
      Command.cost_code_spec facts effectCalls sourceHost command)
    ready covered

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
      (Resource.PureContext.ofProg pure funs) program pool :=
  correctCostWith pure funs meaning tables wrappers pool program entries main profile pureCovered
    covered poolApart ready sourceHost
    (fun {_} _ facts effectCalls {_} {_} command =>
      Command.cost_code_spec facts effectCalls sourceHost command)

end Verified.Wasi
