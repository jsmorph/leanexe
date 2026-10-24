import Verified.Wasi.CommandSpec
import Verified.Bytes.StaticInput
import Verified.Wasi.CallWrappers

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

inductive FunctionResult {World : Type} (host : Host World) (signature : EffectSig)
    (action : Action signature.result.denote) (args : Env signature.params)
    (params : List Value) (heap : Heap) (initial : Store (Observed World)) (aborts : Bool) :
    Result (Observed World) → Prop where
  | returned (value : signature.result.denote) (finalHeap : Heap)
      (final : Store (Observed World)) (words : List Value) (trace : List Event)
      (execution : Exec (observedHost host) action initial.host trace (.returned value) final.host)
      (step : Step heap (PureTransport.erase initial)
        (fun region => Apart (PureTransport.erase initial)
            (Env.moves (PureTransport.erase initial) signature.mode params args) region ∧
          regionsDisjoint region ABI.scratch)
        finalHeap (PureTransport.erase final)
        (signature.result.fresh (PureTransport.erase final) words value))
      (rep : signature.result.Rep finalHeap (PureTransport.erase final) words value) :
      FunctionResult host signature action args params heap initial aborts
        (.Success words.reverse final)
  | terminal (final : Store (Observed World)) (trace : List Event)
      (outcome : Outcome signature.result.denote) (message : String)
      (execution : Exec (observedHost host) action initial.host trace outcome final.host)
      (terminal : TerminalMessage message outcome) :
      FunctionResult host signature action args params heap initial aborts (.Trap final message)
  | resource (final : Store (Observed World)) (trace : List Event)
      (residual : Action signature.result.denote) (allowed : aborts = true)
      (progress : Prefix (observedHost host) action initial.host trace residual final.host) :
      FunctionResult host signature action args params heap initial aborts (.Trap final "unreachable")

def EffectSpec (target : Wasm.Module) (signature : EffectSig) (index : Nat)
    (meaning : Env signature.params → Action signature.result.denote)
    (pool : Bytes.LiteralPool) : Prop :=
  ∀ (World : Type) (host : Host World) (targetHost : HostEnv (Observed World))
    (depth : UInt64) (heap : Heap) (initial : Store (Observed World))
    (params : List Value) (args : Env signature.params),
    targetHost.Satisfies target (hostSpec host) →
    heap.At (PureTransport.erase initial) →
    Env.Rep signature.mode heap (PureTransport.erase initial) params args →
    Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) signature.mode params args)
      (Env.reads (PureTransport.erase initial) signature.mode params args) →
    @Bytes.LiteralPool.Input (Env signature.params)
      (Env.represent signature.params signature.modes) pool heap (PureTransport.erase initial)
      params args →
    (∀ region ∈ Env.reads (PureTransport.erase initial) signature.mode params args,
      regionsDisjoint ABI.scratch region) →
    (PureTransport.erase initial).memoryCap target 0 ≤ 65535 →
    ∃ bound, ∀ fuel ≥ bound,
      FunctionResult host signature (meaning args) args params heap initial true
        (run fuel target index initial ((.i64 depth :: params).reverse) targetHost)

def EffectCalls (source target : Wasm.Module) (functions : EffectFuns signatures)
    (pool : Bytes.LiteralPool) : Prop :=
  ∀ {signature : EffectSig} (callee : EffectVar signatures signature),
    EffectSpec target signature (Wrappers.effectIndex source callee.index)
      (functions.get callee) pool

def CallContinuation (locals : Locals) : Result World → Continuation World
  | .Success values final => .Fallthrough final { locals with values }
  | .Trap final message => .Trap final message
  | .Invalid message => .Invalid message
  | .OutOfFuel => .OutOfFuel
  | .Thrown tag values final => .Throwing tag values final locals

theorem wp_call_refinement {World : Type} {target : Wasm.Module}
    {targetHost : HostEnv World} {initial : Store World} {locals : Locals} {index : Nat}
    {P : Assertion World}
    (execution : ∃ bound, ∀ fuel ≥ bound,
      P (CallContinuation locals (run fuel target index initial locals.values targetHost))) :
    wp target [.call index] P initial locals targetHost := by
  obtain ⟨bound, boundProof⟩ := execution
  unfold wp
  refine ⟨bound + 1, fun fuel enough => ?_⟩
  obtain ⟨fuel, rfl⟩ : ∃ previous, fuel = previous + 1 := ⟨fuel - 1, by omega⟩
  have post := boundProof fuel (by omega)
  rw [exec_call_cons]
  cases result : run fuel target index initial locals.values targetHost <;>
    simpa only [result, CallContinuation, exec] using post

end Verified.Wasi
