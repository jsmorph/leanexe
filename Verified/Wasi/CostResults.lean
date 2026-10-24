import Verified.Wasi.BudgetSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

inductive CostCommandResult {World : Type} (host : Host World)
    (pure : Resource.PureContext pureSigs) (program : EffectProg pureSigs effectSigs)
    (command : Command pureSigs effectSigs context result) (depth : UInt64)
    (env : Env context) (slots : List Slot) (liveIn live : Nat → Bool) (base : Nat)
    (heap : Heap) (initial : Store (Observed World)) (locals : Locals) (aborts : Bool) :
    Continuation (Observed World) → Prop where
  | returned (value : result.denote) (finalHeap : Heap) (final : Store (Observed World))
      (finalLocals : Locals) (words : List Value) (trace : List Event) (spent : Nat) (fits : Bool)
      (execution : Resource.ResourceExec (observedHost host) pure program depth
        (slots.map Slot.mode) live command env initial.host trace (.returned value) final.host
        spent fits)
      (after : After env slots liveIn live base heap initial locals result value
        finalHeap final finalLocals words)
      (top : fits = true → finalHeap.top.toNat ≤ heap.top.toNat + spent) :
      CostCommandResult host pure program command depth env slots liveIn live base heap initial
        locals aborts (.Fallthrough final { finalLocals with values := words.reverse ++ locals.values })
  | trapped (final : Store (Observed World)) (message : String)
      (classification : CommandResult host env slots liveIn live base result
        (command.denote pure.funs (program.funs pure.funs) env) heap initial locals aborts
        (.Trap final message)) :
      CostCommandResult host pure program command depth env slots liveIn live base heap initial
        locals aborts (.Trap final message)

theorem CostCommandResult.erase {World : Type} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {command : Command pureSigs effectSigs context result} {depth : UInt64}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {continuation : Continuation (Observed World)}
    (classification : CostCommandResult host pure program command depth env slots liveIn live
      base heap initial locals aborts continuation) :
    CommandResult host env slots liveIn live base result
      (command.denote pure.funs (program.funs pure.funs) env) heap initial locals aborts
      continuation := by
  cases classification with
  | returned value finalHeap final finalLocals words trace _ _ execution after _ =>
      exact .returned value finalHeap final finalLocals words trace execution.erase after
  | trapped _ _ classification => exact classification

inductive CostFunctionResult {World : Type} (host : Host World)
    (pure : Resource.PureContext pureSigs) (program : EffectProg pureSigs effectSigs)
    (callee : EffectVar effectSigs signature) (depth : UInt64) (args : Env signature.params)
    (params : List Value) (heap : Heap) (initial : Store (Observed World)) (aborts : Bool) :
    Result (Observed World) → Prop where
  | returned (value : signature.result.denote) (finalHeap : Heap)
      (final : Store (Observed World)) (words : List Value) (trace : List Event)
      (spent : Nat) (fits : Bool)
      (execution : Resource.ResourceCall (observedHost host) pure program callee depth args
        initial.host trace (.returned value) final.host spent fits)
      (step : Step heap (PureTransport.erase initial)
        (fun region => Apart (PureTransport.erase initial)
            (Env.moves (PureTransport.erase initial) signature.mode params args) region ∧
          regionsDisjoint region ABI.scratch)
        finalHeap (PureTransport.erase final)
        (signature.result.fresh (PureTransport.erase final) words value))
      (rep : signature.result.Rep finalHeap (PureTransport.erase final) words value)
      (top : fits = true → finalHeap.top.toNat ≤ heap.top.toNat + spent) :
      CostFunctionResult host pure program callee depth args params heap initial aborts
        (.Success words.reverse final)
  | trapped (final : Store (Observed World)) (message : String)
      (classification : FunctionResult host signature ((program.funs pure.funs).get callee args)
        args params heap initial aborts (.Trap final message)) :
      CostFunctionResult host pure program callee depth args params heap initial aborts
        (.Trap final message)

theorem CostFunctionResult.erase {World : Type} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {args : Env signature.params}
    {params : List Value} {heap : Heap} {initial : Store (Observed World)} {aborts : Bool}
    {outcome : Result (Observed World)}
    (classification : CostFunctionResult host pure program callee depth args params heap
      initial aborts outcome) :
    FunctionResult host signature ((program.funs pure.funs).get callee args) args params heap
      initial aborts outcome := by
  cases classification with
  | returned value finalHeap final words trace _ _ execution step rep _ =>
      exact .returned value finalHeap final words trace execution.erase step rep
  | trapped _ _ classification => exact classification

end Verified.Wasi
