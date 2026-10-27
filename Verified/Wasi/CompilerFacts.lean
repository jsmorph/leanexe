import Verified.Wasi.EffectSpec
import Verified.Wasi.ResourceCost
import Verified.ExprCorrect

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

structure CompilerFacts (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (effects : EffectFuns effectSigs) (pool : Bytes.LiteralPool) : Prop where
  runtime : Runtime source
  layout : Relocation.Layout source target
  profile : Relocation.Profile source
  calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool
  effectCalls : EffectCalls source target effects pool
  imports : target.imports = ABI.imports
  read : ∃ typeIndex, target.funcs[source.funcs.length]? = some (readFunction typeIndex)
  stdout : ∃ typeIndex, target.funcs[source.funcs.length + 1]? =
    some (writeFunction .stdout typeIndex)
  stderr : ∃ typeIndex, target.funcs[source.funcs.length + 2]? =
    some (writeFunction .stderr typeIndex)
  effectFunctions : ∀ {signature : EffectSig} (callee : EffectVar effectSigs signature),
    ∃ function, target.funcs[Wrappers.effectIndex source callee.index - target.imports.length]? =
        some function ∧ function.numParams = 1 + widthSum signature.params
  poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch

theorem CompilerFacts.write_function {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} (facts : CompilerFacts source target pure effects pool)
    (output : LeanExe.Wasi.Output) :
    ∃ typeIndex, target.funcs[match output with
      | .stdout => source.funcs.length + 1
      | .stderr => source.funcs.length + 2]? = some (writeFunction output typeIndex) := by
  cases output with
  | stdout => exact facts.stdout
  | stderr => exact facts.stderr

end Verified.Wasi
