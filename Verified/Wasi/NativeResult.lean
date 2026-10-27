import Verified.Wasi.CostTotal
import LeanExe.Wasi.RelatedExec
import LeanExe.Wasi.RelatedPrefix

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

inductive NativeFunctionResult {World α : Type} (host : Host World) (signature : EffectSig)
    (action : Action α) (flatten : α → signature.result.denote) (args : Env signature.params)
    (params : List Value) (heap : Heap) (initial : Store (Observed World)) (aborts : Bool) :
    Result (Observed World) → Prop where
  | returned (value : α) (finalHeap : Heap) (final : Store (Observed World))
      (words : List Value) (trace : List Event)
      (execution : Exec (observedHost host) action initial.host trace (.returned value) final.host)
      (step : Step heap (PureTransport.erase initial)
        (fun region => Apart (PureTransport.erase initial)
            (Env.moves (PureTransport.erase initial) signature.mode params args) region ∧
          regionsDisjoint region ABI.scratch)
        finalHeap (PureTransport.erase final)
        (signature.result.fresh (PureTransport.erase final) words (flatten value)))
      (rep : signature.result.Rep finalHeap (PureTransport.erase final) words (flatten value)) :
      NativeFunctionResult host signature action flatten args params heap initial aborts
        (.Success words.reverse final)
  | terminal (final : Store (Observed World)) (trace : List Event)
      (outcome : Outcome α) (message : String)
      (execution : Exec (observedHost host) action initial.host trace outcome final.host)
      (terminal : TerminalMessage message outcome) :
      NativeFunctionResult host signature action flatten args params heap initial aborts (.Trap final message)
  | resource (final : Store (Observed World)) (trace : List Event)
      (residual : Action α) (allowed : aborts = true)
      (progress : Prefix (observedHost host) action initial.host trace residual final.host) :
      NativeFunctionResult host signature action flatten args params heap initial aborts (.Trap final "unreachable")

theorem FunctionResult.toNative {World α : Type} {host : Host World} {signature : EffectSig}
    {native : Action α} {flat : Action signature.result.denote}
    {flatten : α → signature.result.denote} {args : Env signature.params} {params : List Value}
    {heap : Heap} {initial : Store (Observed World)} {aborts : Bool} {result : Result (Observed World)}
    (classification : FunctionResult host signature flat args params heap initial aborts result)
    (related : Action.Rel (fun native flat => flat = flatten native) native flat) :
    NativeFunctionResult host signature native flatten args params heap initial aborts result := by
  cases classification with
  | returned flatValue finalHeap final words trace execution step rep =>
      obtain ⟨value, nativeExecution, same⟩ :=
        (related.exec_returned_iff (host := observedHost host)).mp execution
      exact NativeFunctionResult.returned value finalHeap final words trace nativeExecution
        (by simpa only [same] using step) (by simpa only [same] using rep)
  | terminal final trace outcome message execution terminal =>
      obtain ⟨nativeOutcome, nativeExecution, values⟩ :=
        related.exec_back (host := observedHost host) execution
      cases values with
      | returned same => exact terminal.elim
      | exited code =>
          exact NativeFunctionResult.terminal final trace (.exited code) message nativeExecution terminal
      | trapped cause =>
          exact NativeFunctionResult.terminal final trace (.trapped cause) message nativeExecution terminal
  | resource final trace residual allowed progress =>
      obtain ⟨nativeResidual, nativeProgress, _⟩ :=
        related.transportPrefixBack (host := observedHost host) progress
      exact NativeFunctionResult.resource final trace nativeResidual allowed nativeProgress

theorem NativeFunctionResult.return_or_accepted_exit {World α : Type} {host : Host World}
    {signature : EffectSig} {action : Action α} {flatten : α → signature.result.denote}
    {args : Env signature.params} {params : List Value} {heap : Heap}
    {initial : Store (Observed World)} {outcome : Result (Observed World)}
    (classification : NativeFunctionResult host signature action flatten args params heap initial false outcome)
    (safe : host.NoTrapsAlong action initial.host.world) :
    ReturnOrAcceptedExit host action initial.host outcome := by
  cases classification with
  | returned value finalHeap final words trace execution step rep =>
      obtain ⟨native, events⟩ := exec_observed execution
      exact ⟨value, trace, native, events,
        by simpa only [Outcome.exitMarker] using native.exited_marker⟩
  | terminal final trace outcome message execution terminal =>
      obtain ⟨native, events⟩ := exec_observed execution
      cases outcome with
      | returned value => exact terminal.elim
      | exited code =>
          exact ⟨code, trace, terminal, native, events,
            by simpa only [Outcome.exitMarker] using native.exited_marker⟩
      | trapped cause => exact False.elim (native.not_trapped_of_prefix safe cause rfl)
  | resource final trace residual allowed progress => exact False.elim (Bool.noConfusion allowed)

end Verified.Wasi
