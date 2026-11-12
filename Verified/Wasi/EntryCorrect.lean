import Verified.Wasi.ProgramCorrect
import Verified.Wasi.CostCallHelper
import Verified.Wasi.CostFunctionPost
import Verified.Wasi.WrapperStack

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_entry_body_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {entry : EffectEntry effectSigs} {pool : Bytes.LiteralPool} {typeIdx : Nat}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {visibleWords : List Value} {args : Env entry.signature.params} {budget : Nat} {aborts : Bool}
    {calleeFunction : Wasm.Function}
    (spec : CostEffectSpecWith calls source target pure program entry.callee
      (Wrappers.effectIndexWith calls source entry.callee.index) pool)
    (imports : target.imports = ABI.importsWith calls)
    (lookup : target.funcs[Wrappers.effectIndexWith calls source entry.callee.index - target.imports.length]? =
      some calleeFunction)
    (arity : calleeFunction.numParams = 1 + widthSum entry.signature.params)
    (length : visibleWords.length = widthSum entry.tables.visibleParams)
    (valid : targetHost.Satisfies target (hostSpecWith host calls))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep entry.signature.mode heap (PureTransport.erase initial)
      (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) entry.signature.mode
        (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
      (Env.reads (PureTransport.erase initial) entry.signature.mode
        (entry.tables.addresses.map Value.i64 ++ visibleWords) args))
    (input : @Bytes.LiteralPool.Input (Env entry.signature.params)
      (Env.represent entry.signature.params entry.signature.modes) pool heap
      (PureTransport.erase initial) (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) entry.signature.mode
      (entry.tables.addresses.map Value.i64 ++ visibleWords) args,
      regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program entry.callee 0 args initial.host budget) :
    wp target (entry.functionWith calls source typeIdx).body
      (CostFunctionPost host pure program entry.callee 0 args
        (entry.tables.addresses.map Value.i64 ++ visibleWords) heap initial aborts)
      initial ((entry.functionWith calls source typeIdx).toLocals visibleWords) targetHost := by
  let Q := CostFunctionPost host pure program entry.callee 0 args
    (entry.tables.addresses.map Value.i64 ++ visibleWords) heap initial aborts
  have noImport : target.imports[Wrappers.effectIndexWith calls source entry.callee.index]? = none :=
    List.getElem?_eq_none (by
      rw [imports, ABI.importsWith_length]
      simp only [Wrappers.effectIndexWith, Module.extraIndexWith]
      omega)
  change wp target ([.constI64 0] ++ entry.tables.addresses.map Instruction.constI64 ++
      (List.range (entry.tables.visibleParams.flatMap Ty.types).length).map Instruction.localGet ++
      [.call (Wrappers.effectIndexWith calls source entry.callee.index)]) Q initial
      ((entry.functionWith calls source typeIdx).toLocals visibleWords) targetHost
  rw [flatMap_types_length, ← length]
  refine wp_injected_arguments entry.tables.addresses visibleWords rfl ?_
  have execution := wp_cost_effect_helper_with (calls := calls) (locals := (entry.functionWith calls source typeIdx).toLocals visibleWords)
    (values := []) (depth := 0) (rest := []) (Q := Q) spec noImport lookup arity valid at_
    rep separate input scratch cap resources
    (fun value finalHeap final words trace spent fits resourceExecution step representation top => by
      rw [wp_nil]
      change CostFunctionResult host pure program entry.callee 0 args
        (entry.tables.addresses.map Value.i64 ++ visibleWords) heap initial aborts
        (.Success ((words.reverse ++ []).take entry.signature.result.width) final)
      rw [List.append_nil, List.take_of_length_le (by
        rw [List.length_reverse, representation.length])]
      exact CostFunctionResult.returned value finalHeap final words trace spent fits
        resourceExecution step representation top)
    (fun final message classification => by
      change CostFunctionResult host pure program entry.callee 0 args
        (entry.tables.addresses.map Value.i64 ++ visibleWords) heap initial aborts (.Trap final message)
      exact .trapped final message classification)
  simpa only [Function.toLocals] using execution

theorem wp_entry_body {World : Type} {source target : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {entry : EffectEntry effectSigs} {pool : Bytes.LiteralPool} {typeIdx : Nat}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {visibleWords : List Value} {args : Env entry.signature.params} {budget : Nat} {aborts : Bool}
    {calleeFunction : Wasm.Function}
    (spec : CostEffectSpec source target pure program entry.callee
      (Wrappers.effectIndex source entry.callee.index) pool)
    (imports : target.imports = ABI.imports)
    (lookup : target.funcs[Wrappers.effectIndex source entry.callee.index - target.imports.length]? =
      some calleeFunction)
    (arity : calleeFunction.numParams = 1 + widthSum entry.signature.params)
    (length : visibleWords.length = widthSum entry.tables.visibleParams)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep entry.signature.mode heap (PureTransport.erase initial)
      (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) entry.signature.mode
        (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
      (Env.reads (PureTransport.erase initial) entry.signature.mode
        (entry.tables.addresses.map Value.i64 ++ visibleWords) args))
    (input : @Bytes.LiteralPool.Input (Env entry.signature.params)
      (Env.represent entry.signature.params entry.signature.modes) pool heap
      (PureTransport.erase initial) (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) entry.signature.mode
      (entry.tables.addresses.map Value.i64 ++ visibleWords) args,
      regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program entry.callee 0 args initial.host budget) :
    wp target (entry.function source typeIdx).body
      (CostFunctionPost host pure program entry.callee 0 args
        (entry.tables.addresses.map Value.i64 ++ visibleWords) heap initial aborts)
      initial ((entry.function source typeIdx).toLocals visibleWords) targetHost := by
  layout_instance wp_entry_body_with

theorem compile_entry_export_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (pool : Bytes.LiteralPool)
    {index : Nat} {entry : EffectEntry effectSigs} (selected : entries[index]? = some entry) :
    ({ name := entry.signature.name,
       funcIdx := Wrappers.effectIndexWith calls source (effectSigs.length + index) } : Wasm.Export) ∈
      (compileCalls calls source program entries none pool).exports := by
  rw [compile_callable_exports_with source program entries pool]
  apply List.mem_append_right
  apply List.mem_of_getElem? (i := index)
  rw [List.getElem?_mapIdx, selected]
  rfl

theorem compile_entry_export (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (pool : Bytes.LiteralPool)
    {index : Nat} {entry : EffectEntry effectSigs} (selected : entries[index]? = some entry) :
    ({ name := entry.signature.name,
       funcIdx := Wrappers.effectIndex source (effectSigs.length + index) } : Wasm.Export) ∈
      (compile source program entries none pool).exports := by
  layout_instance compile_entry_export_with

theorem compiled_entry_run_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (pool : Bytes.LiteralPool)
    {index : Nat} {entry : EffectEntry effectSigs} (selected : entries[index]? = some entry)
    (effectCalls : CostEffectCallsWith calls source (compileCalls calls source program entries none pool) pure program pool)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {visibleWords : List Value} {args : Env entry.signature.params} {budget : Nat} {aborts : Bool}
    (length : visibleWords.length = widthSum entry.tables.visibleParams)
    (valid : targetHost.Satisfies (compileCalls calls source program entries none pool) (hostSpecWith host calls))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep entry.signature.mode heap (PureTransport.erase initial)
      (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) entry.signature.mode
        (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
      (Env.reads (PureTransport.erase initial) entry.signature.mode
        (entry.tables.addresses.map Value.i64 ++ visibleWords) args))
    (input : @Bytes.LiteralPool.Input (Env entry.signature.params)
      (Env.represent entry.signature.params entry.signature.modes) pool heap
      (PureTransport.erase initial) (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) entry.signature.mode
      (entry.tables.addresses.map Value.i64 ++ visibleWords) args,
      regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap (compileCalls calls source program entries none pool) 0 ≤ 65535)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program entry.callee 0 args initial.host budget) :
    ∃ bound, ∀ fuel ≥ bound,
      CostFunctionResult host pure program entry.callee 0 args
        (entry.tables.addresses.map Value.i64 ++ visibleWords) heap initial aborts
        (run fuel (compileCalls calls source program entries none pool)
          (Wrappers.effectIndexWith calls source (effectSigs.length + index)) initial visibleWords.reverse targetHost) := by
  have lookup : (compileCalls calls source program entries none pool).funcs[
      source.funcs.length + (3 + (effectSigs.length + index))]? =
      some (entry.functionWith calls source (effectTypeIndex source (effectSigs.length + index))) := by
    rw [compile_entry_with source program entries index pool, selected]
    rfl
  obtain ⟨calleeFunction, calleeLookup, arity⟩ := compile_effect_arity_with (calls := calls) source program entries none pool entry.callee
  have body := wp_entry_body_with (calls := calls) (typeIdx := effectTypeIndex source (effectSigs.length + index))
    (effectCalls entry.callee) (compile_imports_with source program entries none pool) calleeLookup arity
    length valid at_ rep separate input scratch cap resources
  have execution := defined_function_run_post_with (calls := calls) (compile_imports_with source program entries none pool) lookup
    (show visibleWords.length = (entry.functionWith calls source (effectTypeIndex source (effectSigs.length + index))).numParams
      from by
        change visibleWords.length = (entry.tables.visibleParams.flatMap Ty.types).length
        rw [flatMap_types_length]
        exact length)
    (show (entry.functionWith calls source (effectTypeIndex source (effectSigs.length + index))).results.length =
        entry.signature.result.width from entry.signature.result.types_length) body
  simpa only [Wrappers.effectIndexWith, Module.extraIndexWith, Nat.add_assoc] using execution

theorem compiled_entry_run {World : Type} {source : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (pool : Bytes.LiteralPool)
    {index : Nat} {entry : EffectEntry effectSigs} (selected : entries[index]? = some entry)
    (calls : CostEffectCalls source (compile source program entries none pool) pure program pool)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {visibleWords : List Value} {args : Env entry.signature.params} {budget : Nat} {aborts : Bool}
    (length : visibleWords.length = widthSum entry.tables.visibleParams)
    (valid : targetHost.Satisfies (compile source program entries none pool) (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep entry.signature.mode heap (PureTransport.erase initial)
      (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) entry.signature.mode
        (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
      (Env.reads (PureTransport.erase initial) entry.signature.mode
        (entry.tables.addresses.map Value.i64 ++ visibleWords) args))
    (input : @Bytes.LiteralPool.Input (Env entry.signature.params)
      (Env.represent entry.signature.params entry.signature.modes) pool heap
      (PureTransport.erase initial) (entry.tables.addresses.map Value.i64 ++ visibleWords) args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) entry.signature.mode
      (entry.tables.addresses.map Value.i64 ++ visibleWords) args,
      regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap (compile source program entries none pool) 0 ≤ 65535)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program entry.callee 0 args initial.host budget) :
    ∃ bound, ∀ fuel ≥ bound,
      CostFunctionResult host pure program entry.callee 0 args
        (entry.tables.addresses.map Value.i64 ++ visibleWords) heap initial aborts
        (run fuel (compile source program entries none pool)
          (Wrappers.effectIndex source (effectSigs.length + index)) initial visibleWords.reverse targetHost) := by
  layout_instance compiled_entry_run_with

end Verified.Wasi
