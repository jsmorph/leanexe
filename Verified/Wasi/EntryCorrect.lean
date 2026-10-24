import Verified.Wasi.ProgramCorrect
import Verified.Wasi.CostCallHelper
import Verified.Wasi.CostFunctionPost
import Verified.Wasi.WrapperStack

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

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
  let Q := CostFunctionPost host pure program entry.callee 0 args
    (entry.tables.addresses.map Value.i64 ++ visibleWords) heap initial aborts
  have noImport : target.imports[Wrappers.effectIndex source entry.callee.index]? = none :=
    List.getElem?_eq_none (by
      rw [imports, ABI.imports_length]
      simp only [Wrappers.effectIndex, Module.extraIndex]
      omega)
  change wp target ([.constI64 0] ++ entry.tables.addresses.map Instruction.constI64 ++
      (List.range (entry.tables.visibleParams.flatMap Ty.types).length).map Instruction.localGet ++
      [.call (Wrappers.effectIndex source entry.callee.index)]) Q initial
      ((entry.function source typeIdx).toLocals visibleWords) targetHost
  rw [flatMap_types_length, ← length]
  refine wp_injected_arguments entry.tables.addresses visibleWords rfl ?_
  have execution := wp_cost_effect_helper (locals := (entry.function source typeIdx).toLocals visibleWords)
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

theorem compile_entry_export (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (pool : Bytes.LiteralPool)
    {index : Nat} {entry : EffectEntry effectSigs} (selected : entries[index]? = some entry) :
    ({ name := entry.signature.name,
       funcIdx := Wrappers.effectIndex source (effectSigs.length + index) } : Wasm.Export) ∈
      (compile source program entries none pool).exports := by
  rw [compile_callable_exports source program entries pool]
  apply List.mem_append_right
  apply List.mem_of_getElem? (i := index)
  rw [List.getElem?_mapIdx, selected]
  rfl

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
  have lookup : (compile source program entries none pool).funcs[
      source.funcs.length + (3 + (effectSigs.length + index))]? =
      some (entry.function source (effectTypeIndex source (effectSigs.length + index))) := by
    rw [compile_entry source program entries index pool, selected]
    rfl
  obtain ⟨calleeFunction, calleeLookup, arity⟩ := compile_effect_arity source program entries none pool entry.callee
  have body := wp_entry_body (typeIdx := effectTypeIndex source (effectSigs.length + index))
    (calls entry.callee) (compile_imports source program entries none pool) calleeLookup arity
    length valid at_ rep separate input scratch cap resources
  have execution := defined_function_run_post (compile_imports source program entries none pool) lookup
    (show visibleWords.length = (entry.function source (effectTypeIndex source (effectSigs.length + index))).numParams
      from by
        change visibleWords.length = (entry.tables.visibleParams.flatMap Ty.types).length
        rw [flatMap_types_length]
        exact length)
    (show (entry.function source (effectTypeIndex source (effectSigs.length + index))).results.length =
        entry.signature.result.width from entry.signature.result.types_length) body
  simpa only [Wrappers.effectIndex, Module.extraIndex, Nat.add_assoc] using execution

end Verified.Wasi
