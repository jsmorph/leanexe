import Verified.Wasi.CommandRun
import Verified.Wasi.NativeResult

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem EffectMain.related_action (main : EffectMain effectSigs) (pure : Funs pureSigs)
    (program : EffectProg pureSigs effectSigs) (args : Env main.signature.params)
    (native : Action UInt64)
    (related : Action.Rel (fun native flat : UInt64 => flat = native) native
      ((program.funs pure).get main.callee args)) :
    Action.Rel (fun native flat : Unit => flat = native)
      (Action.bind native fun status => Action.exit (α := Unit) status)
      (main.action pure program args) := by
  apply related.bind
  intro left right same
  subst right
  exact .exit left

theorem compiled_native_start_run {World : Type} {source : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : EffectMain effectSigs) (pool : Bytes.LiteralPool)
    (calls : CostEffectCalls source (compile source program entries (some main) pool) pure program pool)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {args : Env main.signature.params} {budget : Nat} {aborts : Bool}
    (native : Action UInt64)
    (related : Action.Rel (fun native flat : UInt64 => flat = native) native
      ((program.funs pure.funs).get main.callee args))
    (valid : targetHost.Satisfies (compile source program entries (some main) pool) (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep main.signature.mode heap (PureTransport.erase initial) (main.tables.map Value.i64) args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) main.signature.mode (main.tables.map Value.i64) args)
      (Env.reads (PureTransport.erase initial) main.signature.mode (main.tables.map Value.i64) args))
    (input : @Bytes.LiteralPool.Input (Env main.signature.params)
      (Env.represent main.signature.params main.signature.modes) pool heap (PureTransport.erase initial)
      (main.tables.map Value.i64) args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) main.signature.mode
      (main.tables.map Value.i64) args, regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap (compile source program entries (some main) pool) 0 ≤ 65535)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program main.callee 0 args initial.host budget) :
    ∃ bound, ∀ fuel ≥ bound,
      NativeFunctionResult host startSignature
        (Action.bind native fun status => Action.exit (α := Unit) status)
        (fun value : Unit => value) .nil [] heap initial aborts
        (run fuel (compile source program entries (some main) pool)
          (Wrappers.effectIndex source effectSigs.length) initial [] targetHost) := by
  obtain ⟨bound, execution⟩ := compiled_start_run (host := host) program entries main pool calls
    valid at_ rep separate input scratch cap resources
  have relation := main.related_action pure.funs program args native related
  exact ⟨bound, fun fuel enough => (execution fuel enough).toNative relation⟩

end Verified.Wasi
