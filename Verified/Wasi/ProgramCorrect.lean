import Verified.Wasi.ProgramFacts
import Verified.Wasi.CostFunctionSpec
import Verified.Wasi.CostFunctionLift

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def EffectFunc.Ready (source : Wasm.Module) (pool : Bytes.LiteralPool)
    (function : EffectFunc pureSigs effectSigs) : Prop :=
  Encoding.ProgramForm (releaseWhere function.params
      (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) ∧
    Relocation.programClosed source.funcs.length (releaseWhere function.params
      (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) = true ∧
    function.body.Ready source function.positions (paramSlots function.params function.modes 1)
      (1 + widthSum function.params) (fun _ => false) pool ∧
    function.body.placeArgs = true

def EffectProg.Ready (source : Wasm.Module) (pool : Bytes.LiteralPool) :
    {effectSigs : List EffectSig} → EffectProg pureSigs effectSigs → Prop
  | _, .nil => True
  | _, .cons function rest => function.Ready source pool ∧ rest.Ready source pool

theorem compile_prefix_facts_with {calls : List LeanExe.Wasi.Call}
    {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (full : EffectProg pureSigs fullSigs) (entries : List (EffectEntry fullSigs))
    (main : Option (EffectMain fullSigs)) (pool : Bytes.LiteralPool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (pureCalls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (program : EffectProg pureSigs effectSigs)
    (present : program.FunctionsInWith calls source (compileCalls calls source full entries main pool) pool)
    (effectCalls : EffectCallsWith calls source (compileCalls calls source full entries main pool)
      (program.funs pure.funs) pool) :
    CompilerFactsWith calls source (compileCalls calls source full entries main pool) pure (program.funs pure.funs) pool := by
  refine
    { runtime
      layout := compile_layout_with full entries main pool runtime.imports
      profile
      calls := pureCalls
      effectCalls
      imports := compile_imports_with source full entries main pool
      read := ⟨_, compile_read_with source full entries main pool⟩
      stdout := ⟨_, compile_stdout_with source full entries main pool⟩
      stderr := ⟨_, compile_stderr_with source full entries main pool⟩
      effectFunctions := ?_
      poolApart }
  intro signature callee
  have arity := present.arity callee
  simpa only [Wrappers.effectIndexWith, Module.extraIndexWith, compile_imports_with,
    ABI.importsWith_length,
    show 3 + calls.length + source.funcs.length + (3 + callee.index) - (3 + calls.length) =
      source.funcs.length + (3 + callee.index) by omega] using arity

theorem compile_prefix_facts {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (full : EffectProg pureSigs fullSigs) (entries : List (EffectEntry fullSigs))
    (main : Option (EffectMain fullSigs)) (pool : Bytes.LiteralPool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (program : EffectProg pureSigs effectSigs)
    (present : program.FunctionsIn source (compile source full entries main pool) pool)
    (effectCalls : EffectCalls source (compile source full entries main pool)
      (program.funs pure.funs) pool) :
    CompilerFacts source (compile source full entries main pool) pure (program.funs pure.funs) pool := by
  layout_instance compile_prefix_facts_with

theorem EffectProg.cost_calls_with {calls : List LeanExe.Wasi.Call}
    {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (full : EffectProg pureSigs fullSigs) (entries : List (EffectEntry fullSigs))
    (main : Option (EffectMain fullSigs)) (pool : Bytes.LiteralPool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (effectCalls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (sourceHost : HostEnv Unit)
    (commandRule : ∀ {signatures : List EffectSig} (program : EffectProg pureSigs signatures),
      CompilerFactsWith calls source (compileCalls calls source full entries main pool) pure (program.funs pure.funs) pool →
      CostEffectCallsWith calls source (compileCalls calls source full entries main pool) pure program pool →
      ∀ {context : List Ty} {result : ResultTy} (command : Command pureSigs signatures context result),
        CostCommandCodeSpecWith calls source (compileCalls calls source full entries main pool) pure program pool command) :
    ∀ {signatures : List EffectSig} (program : EffectProg pureSigs signatures),
      program.FunctionsInWith calls source (compileCalls calls source full entries main pool) pool →
      program.Ready source pool → program.Covered pool →
      CostEffectCallsWith calls source (compileCalls calls source full entries main pool) pure program pool := by
  intro signatures program
  induction program with
  | nil =>
      intro _ _ _ signature callee
      cases callee
  | cons function rest ih =>
      intro present ready covered
      rcases ready with ⟨functionReady, restReady⟩
      rcases functionReady with ⟨form, closed, bodyReady, place⟩
      have restCovered : rest.Covered pool :=
        fun _ member => covered (List.mem_append_left _ member)
      have bodyCovered : function.body.Covered pool :=
        fun _ member => covered (List.mem_append_right _ member)
      have restCalls : CostEffectCallsWith calls source (compileCalls calls source full entries main pool) pure rest pool :=
        ih present.tail restReady restCovered
      have facts : CompilerFactsWith calls source (compileCalls calls source full entries main pool) pure
          (rest.funs pure.funs) pool :=
        compile_prefix_facts_with (calls := calls) full entries main pool runtime profile effectCalls poolApart
          rest present.tail (CostEffectCallsWith.safety restCalls)
      have bodySpec : CostCommandCodeSpecWith calls source (compileCalls calls source full entries main pool)
          pure rest pool function.body :=
        commandRule rest facts restCalls function.body
      intro signature callee
      cases callee with
      | here =>
          have head := CostEffectSpecWith.here facts sourceHost present.head form closed bodyReady
            bodyCovered place bodySpec
          simpa only [Wrappers.effectIndexWith, Module.extraIndexWith, EffectVar.index, Nat.add_assoc] using head
      | there callee => exact (restCalls callee).there

theorem EffectProg.cost_calls {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (full : EffectProg pureSigs fullSigs) (entries : List (EffectEntry fullSigs))
    (main : Option (EffectMain fullSigs)) (pool : Bytes.LiteralPool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (sourceHost : HostEnv Unit)
    (commandRule : ∀ {signatures : List EffectSig} (program : EffectProg pureSigs signatures),
      CompilerFacts source (compile source full entries main pool) pure (program.funs pure.funs) pool →
      CostEffectCalls source (compile source full entries main pool) pure program pool →
      ∀ {context : List Ty} {result : ResultTy} (command : Command pureSigs signatures context result),
        CostCommandCodeSpec source (compile source full entries main pool) pure program pool command) :
    ∀ {signatures : List EffectSig} (program : EffectProg pureSigs signatures),
      program.FunctionsIn source (compile source full entries main pool) pool →
      program.Ready source pool → program.Covered pool →
      CostEffectCalls source (compile source full entries main pool) pure program pool :=
  fun program present ready covered =>
    EffectProg.cost_calls_with (calls := []) full entries main pool runtime profile calls poolApart
      sourceHost (fun part facts effects => commandRule part facts.toFacts effects)
      program present ready covered

theorem EffectProg.correctCost_with {calls : List LeanExe.Wasi.Call}
    {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (effectCalls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (sourceHost : HostEnv Unit)
    (commandRule : ∀ {signatures : List EffectSig} (part : EffectProg pureSigs signatures),
      CompilerFactsWith calls source (compileCalls calls source program entries main pool) pure (part.funs pure.funs) pool →
      CostEffectCallsWith calls source (compileCalls calls source program entries main pool) pure part pool →
      ∀ {context : List Ty} {result : ResultTy} (command : Command pureSigs signatures context result),
        CostCommandCodeSpecWith calls source (compileCalls calls source program entries main pool) pure part pool command)
    (ready : program.Ready source pool) (covered : program.Covered pool) :
    CostEffectCallsWith calls source (compileCalls calls source program entries main pool) pure program pool :=
  program.cost_calls_with entries main pool runtime profile effectCalls poolApart sourceHost commandRule program
    (compile_functionsIn_with source program entries main pool) ready covered

theorem EffectProg.correctCost {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (sourceHost : HostEnv Unit)
    (commandRule : ∀ {signatures : List EffectSig} (part : EffectProg pureSigs signatures),
      CompilerFacts source (compile source program entries main pool) pure (part.funs pure.funs) pool →
      CostEffectCalls source (compile source program entries main pool) pure part pool →
      ∀ {context : List Ty} {result : ResultTy} (command : Command pureSigs signatures context result),
        CostCommandCodeSpec source (compile source program entries main pool) pure part pool command)
    (ready : program.Ready source pool) (covered : program.Covered pool) :
    CostEffectCalls source (compile source program entries main pool) pure program pool :=
  EffectProg.correctCost_with (calls := []) program entries main pool runtime profile calls
    poolApart sourceHost
    (fun part facts effects => commandRule part facts.toFacts effects) ready covered

theorem EffectProg.correctCostWith_with {calls : List LeanExe.Wasi.Call}
    {pureSigs : List Sig} (pure : Prog pureSigs)
    (funs : Funs pureSigs) (meaning : pure.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper pureSigs tables.length)) (pool : Bytes.LiteralPool)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs))
    (profile : Relocation.Profile (Verified.compileWith pure tables wrappers pool))
    (pureCovered : pure.Covered pool) (covered : program.Covered pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (ready : program.Ready (Verified.compileWith pure tables wrappers pool) pool)
    (sourceHost : HostEnv Unit)
    (commandRule : ∀ {signatures : List EffectSig} (part : EffectProg pureSigs signatures),
      CompilerFactsWith calls (Verified.compileWith pure tables wrappers pool)
        (compileCalls calls (Verified.compileWith pure tables wrappers pool) program entries main pool)
        (Resource.PureContext.ofProg pure funs) (part.funs funs) pool →
      CostEffectCallsWith calls (Verified.compileWith pure tables wrappers pool)
        (compileCalls calls (Verified.compileWith pure tables wrappers pool) program entries main pool)
        (Resource.PureContext.ofProg pure funs) part pool →
      ∀ {context : List Ty} {result : ResultTy} (command : Command pureSigs signatures context result),
        CostCommandCodeSpecWith calls (Verified.compileWith pure tables wrappers pool)
          (compileCalls calls (Verified.compileWith pure tables wrappers pool) program entries main pool)
          (Resource.PureContext.ofProg pure funs) part pool command) :
    CostEffectCallsWith calls (Verified.compileWith pure tables wrappers pool)
      (compileCalls calls (Verified.compileWith pure tables wrappers pool) program entries main pool)
      (Resource.PureContext.ofProg pure funs) program pool :=
  program.correctCost_with entries main pool (compileWith_runtime pure tables wrappers pool) profile
    (compiled_pure_calls pure funs meaning tables wrappers pool pureCovered) poolApart sourceHost
    commandRule ready covered

theorem EffectProg.correctCostWith {pureSigs : List Sig} (pure : Prog pureSigs)
    (funs : Funs pureSigs) (meaning : pure.Meaning funs) (tables : List (Array UInt64))
    (wrappers : List (Wrapper pureSigs tables.length)) (pool : Bytes.LiteralPool)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs))
    (profile : Relocation.Profile (Verified.compileWith pure tables wrappers pool))
    (pureCovered : pure.Covered pool) (covered : program.Covered pool)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (ready : program.Ready (Verified.compileWith pure tables wrappers pool) pool)
    (sourceHost : HostEnv Unit)
    (commandRule : ∀ {signatures : List EffectSig} (part : EffectProg pureSigs signatures),
      CompilerFacts (Verified.compileWith pure tables wrappers pool)
        (compile (Verified.compileWith pure tables wrappers pool) program entries main pool)
        (Resource.PureContext.ofProg pure funs) (part.funs funs) pool →
      CostEffectCalls (Verified.compileWith pure tables wrappers pool)
        (compile (Verified.compileWith pure tables wrappers pool) program entries main pool)
        (Resource.PureContext.ofProg pure funs) part pool →
      ∀ {context : List Ty} {result : ResultTy} (command : Command pureSigs signatures context result),
        CostCommandCodeSpec (Verified.compileWith pure tables wrappers pool)
          (compile (Verified.compileWith pure tables wrappers pool) program entries main pool)
          (Resource.PureContext.ofProg pure funs) part pool command) :
    CostEffectCalls (Verified.compileWith pure tables wrappers pool)
      (compile (Verified.compileWith pure tables wrappers pool) program entries main pool)
      (Resource.PureContext.ofProg pure funs) program pool :=
  EffectProg.correctCostWith_with (calls := []) pure funs meaning tables wrappers pool program
    entries main profile pureCovered covered poolApart ready sourceHost
    (fun part facts effects => commandRule part facts.toFacts effects)

end Verified.Wasi
