import Verified.Wasi.EntryCorrect
import Verified.Wasi.NativeResult

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem compiled_native_entry_run {World α : Type} {source : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (pool : Bytes.LiteralPool)
    {index : Nat} {entry : EffectEntry effectSigs} (selected : entries[index]? = some entry)
    (calls : CostEffectCalls source (compile source program entries none pool) pure program pool)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {visibleWords : List Value} {args : Env entry.signature.params} {budget : Nat} {aborts : Bool}
    (native : Action α) (flatten : α → entry.signature.result.denote)
    (related : Action.Rel (fun native flat => flat = flatten native) native
      ((program.funs pure.funs).get entry.callee args))
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
      NativeFunctionResult host entry.signature native flatten args
        (entry.tables.addresses.map Value.i64 ++ visibleWords) heap initial aborts
        (run fuel (compile source program entries none pool)
          (Wrappers.effectIndex source (effectSigs.length + index)) initial visibleWords.reverse targetHost) := by
  obtain ⟨bound, execution⟩ := compiled_entry_run (host := host) program entries pool selected calls
    length valid at_ rep separate input scratch cap resources
  exact ⟨bound, fun fuel enough => (execution fuel enough).erase.toNative related⟩

end Verified.Wasi
