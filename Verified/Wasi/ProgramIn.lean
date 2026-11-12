import Verified.Wasi.Correct

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

structure CompilerBaseWith (imported : List LeanExe.Wasi.Call) (source target : Wasm.Module)
    (pure : Resource.PureContext pureSigs) (pool : Bytes.LiteralPool) : Prop where
  runtime : Runtime source
  layout : Relocation.LayoutWith imported source target
  profile : Relocation.Profile source
  calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool
  imports : target.imports = ABI.importsWith imported
  read : ∃ typeIndex, target.funcs[source.funcs.length]? =
    some (readFunctionWith imported typeIndex)
  stdout : ∃ typeIndex, target.funcs[source.funcs.length + 1]? =
    some (writeFunction .stdout typeIndex)
  stderr : ∃ typeIndex, target.funcs[source.funcs.length + 2]? =
    some (writeFunction .stderr typeIndex)
  poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch

structure CompilerBase (source target : Wasm.Module) (pure : Resource.PureContext pureSigs)
    (pool : Bytes.LiteralPool) : Prop where
  runtime : Runtime source
  layout : Relocation.Layout source target
  profile : Relocation.Profile source
  calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool
  imports : target.imports = ABI.imports
  read : ∃ typeIndex, target.funcs[source.funcs.length]? = some (readFunction typeIndex)
  stdout : ∃ typeIndex, target.funcs[source.funcs.length + 1]? =
    some (writeFunction .stdout typeIndex)
  stderr : ∃ typeIndex, target.funcs[source.funcs.length + 2]? =
    some (writeFunction .stderr typeIndex)
  poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch

theorem CompilerBase.toWith {source target : Wasm.Module} {pure : Resource.PureContext pureSigs}
    {pool : Bytes.LiteralPool} (base : CompilerBase source target pure pool) :
    CompilerBaseWith [] source target pure pool :=
  ⟨base.runtime, base.layout.toWith, base.profile, base.calls, base.imports, base.read,
    base.stdout, base.stderr, base.poolApart⟩

theorem CompilerBaseWith.facts {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module} {pure : Resource.PureContext pureSigs}
    {pool : Bytes.LiteralPool} (base : CompilerBaseWith calls source target pure pool)
    (program : EffectProg pureSigs effectSigs)
    (present : program.FunctionsInWith calls source target pool)
    (effectCalls : EffectCallsWith calls source target (program.funs pure.funs) pool) :
    CompilerFactsWith calls source target pure (program.funs pure.funs) pool :=
  { runtime := base.runtime
    layout := base.layout
    profile := base.profile
    calls := base.calls
    effectCalls := effectCalls
    imports := base.imports
    read := base.read
    stdout := base.stdout
    stderr := base.stderr
    poolApart := base.poolApart
    effectFunctions := fun callee => by
      have arity := present.arity callee
      simpa only [Wrappers.effectIndexWith, Module.extraIndexWith, base.imports,
        ABI.importsWith_length,
        show 3 + calls.length + source.funcs.length + (3 + callee.index) - (3 + calls.length) =
          source.funcs.length + (3 + callee.index) by omega] using arity }

theorem CompilerBaseWith.toBase {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {pool : Bytes.LiteralPool}
    (base : CompilerBaseWith [] source target pure pool) : CompilerBase source target pure pool :=
  ⟨base.runtime, base.layout.toLayout, base.profile, base.calls, base.imports, base.read,
    base.stdout, base.stderr, base.poolApart⟩

end Verified.Wasi

macro_rules
  | `(tactic| layout_convert) =>
    `(tactic| (apply Verified.Wasi.CompilerBase.toWith; assumption))

macro_rules
  | `(tactic| layout_back) => `(tactic| apply Verified.Wasi.CompilerBaseWith.toBase)

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem CompilerBase.facts {source target : Wasm.Module} {pure : Resource.PureContext pureSigs}
    {pool : Bytes.LiteralPool} (base : CompilerBase source target pure pool)
    (program : EffectProg pureSigs effectSigs)
    (present : program.FunctionsIn source target pool)
    (calls : EffectCalls source target (program.funs pure.funs) pool) :
    CompilerFacts source target pure (program.funs pure.funs) pool := by
  layout_instance CompilerBaseWith.facts

theorem EffectProg.correctIn_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {pool : Bytes.LiteralPool}
    (base : CompilerBaseWith calls source target pure pool) (sourceHost : HostEnv Unit)
    (program : EffectProg pureSigs effectSigs)
    (present : program.FunctionsInWith calls source target pool)
    (ready : program.ReadyWith calls source pool) (covered : program.Covered pool) :
    CostEffectCallsWith calls source target pure program pool := by
  induction program with
  | nil =>
      intro signature callee
      cases callee
  | cons function rest ih =>
      rcases ready with ⟨⟨form, closed, bodyReady, place⟩, restReady⟩
      have restCovered : rest.Covered pool :=
        fun _ member => covered (List.mem_append_left _ member)
      have bodyCovered : function.body.Covered pool :=
        fun _ member => covered (List.mem_append_right _ member)
      have restCalls : CostEffectCallsWith calls source target pure rest pool :=
        ih present.tail restReady restCovered
      have facts := base.facts rest present.tail (CostEffectCallsWith.safety restCalls)
      have bodySpec := Command.cost_code_spec_with (calls := calls) facts restCalls sourceHost function.body
      intro signature callee
      cases callee with
      | here =>
          have head := CostEffectSpecWith.here facts sourceHost present.head form closed bodyReady
            bodyCovered place bodySpec
          simpa only [Wrappers.effectIndexWith, Module.extraIndexWith, EffectVar.index, Nat.add_assoc] using head
      | there callee => exact (restCalls callee).there

theorem EffectProg.correctIn {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {pool : Bytes.LiteralPool}
    (base : CompilerBase source target pure pool) (sourceHost : HostEnv Unit)
    (program : EffectProg pureSigs effectSigs)
    (present : program.FunctionsIn source target pool)
    (ready : program.Ready source pool) (covered : program.Covered pool) :
    CostEffectCalls source target pure program pool := by
  layout_instance EffectProg.correctIn_with

end Verified.Wasi
