import Verified.Wasi.EffectSpec
import Verified.Wasi.ResourceCost
import Verified.ExprCorrect

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- The facts about a module that imports the flat calls `imported` that the command rules use. -/
structure CompilerFactsWith (imported : List LeanExe.Wasi.Call) (source target : Wasm.Module)
    (pure : Resource.PureContext pureSigs) (effects : EffectFuns effectSigs)
    (pool : Bytes.LiteralPool) : Prop where
  runtime : Runtime source
  layout : Relocation.LayoutWith imported source target
  profile : Relocation.Profile source
  calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool
  effectCalls : EffectCallsWith imported source target effects pool
  imports : target.imports = ABI.importsWith imported
  read : ∃ typeIndex, target.funcs[source.funcs.length]? =
    some (readFunctionWith imported typeIndex)
  stdout : ∃ typeIndex, target.funcs[source.funcs.length + 1]? =
    some (writeFunction .stdout typeIndex)
  stderr : ∃ typeIndex, target.funcs[source.funcs.length + 2]? =
    some (writeFunction .stderr typeIndex)
  effectFunctions : ∀ {signature : EffectSig} (callee : EffectVar effectSigs signature),
    ∃ function, target.funcs[Wrappers.effectIndexWith imported source callee.index -
        target.imports.length]? =
        some function ∧ function.numParams = 1 + widthSum signature.params
  poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch

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

theorem CompilerFacts.toWith {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} (facts : CompilerFacts source target pure effects pool) :
    CompilerFactsWith [] source target pure effects pool :=
  ⟨facts.runtime, facts.layout.toWith, facts.profile, facts.calls, facts.effectCalls,
    facts.imports, facts.read, facts.stdout, facts.stderr, facts.effectFunctions, facts.poolApart⟩

theorem CompilerFactsWith.toFacts {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} (facts : CompilerFactsWith [] source target pure effects pool) :
    CompilerFacts source target pure effects pool :=
  ⟨facts.runtime, facts.layout.toLayout, facts.profile, facts.calls, facts.effectCalls,
    facts.imports, facts.read, facts.stdout, facts.stderr, facts.effectFunctions, facts.poolApart⟩

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

theorem CompilerFactsWith.write_function {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} (facts : CompilerFactsWith calls source target pure effects pool)
    (output : LeanExe.Wasi.Output) :
    ∃ typeIndex, target.funcs[match output with
      | .stdout => source.funcs.length + 1
      | .stderr => source.funcs.length + 2]? = some (writeFunction output typeIndex) := by
  cases output with
  | stdout => exact facts.stdout
  | stderr => exact facts.stderr

end Verified.Wasi

macro_rules
  | `(tactic| layout_convert) =>
    `(tactic| (apply Verified.Wasi.CompilerFacts.toWith; assumption))

macro_rules
  | `(tactic| layout_back) => `(tactic| apply Verified.Wasi.CompilerFactsWith.toFacts)
