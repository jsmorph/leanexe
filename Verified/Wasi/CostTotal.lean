import Verified.Wasi.CostEffectSpec
import LeanExe.Wasi.NoTrapPrefix

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def ReturnOrAcceptedExit {World : Type} (host : Host World) (action : Action α)
    (initial : Observed World) : Result (Observed World) → Prop
  | .Success _ final =>
      ∃ value trace, Exec host action initial.world trace (.returned value) final.host.world ∧
        final.host.events = initial.events ++ trace ∧
        host.exited final.host.world = host.exited initial.world
  | .Trap final message =>
      ∃ code trace, message = exitTrap ∧
        Exec host action initial.world trace (.exited code) final.host.world ∧
        final.host.events = initial.events ++ trace ∧ host.exited final.host.world = some code
  | _ => False

theorem CostFunctionResult.return_or_accepted_exit {World : Type} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {args : Env signature.params}
    {params : List Value} {heap : Heap} {initial : Store (Observed World)}
    {outcome : Result (Observed World)}
    (classification : CostFunctionResult host pure program callee depth args params heap initial false outcome)
    (safe : host.NoTrapsAlong ((program.funs pure.funs).get callee args) initial.host.world) :
    ReturnOrAcceptedExit host ((program.funs pure.funs).get callee args) initial.host outcome := by
  cases classification with
  | returned value finalHeap final words trace spent fits execution step rep top =>
    obtain ⟨native, events⟩ := exec_observed execution.erase
    exact ⟨value, trace, native, events, by simpa only [Outcome.exitMarker] using native.exited_marker⟩
  | trapped final message classification =>
    cases classification with
    | terminal final trace outcome message execution terminal =>
      obtain ⟨native, events⟩ := exec_observed execution
      cases outcome with
      | returned value => exact terminal.elim
      | exited code =>
        exact ⟨code, trace, terminal, native, events,
          by simpa only [Outcome.exitMarker] using native.exited_marker⟩
      | trapped cause => exact False.elim (native.not_trapped_of_prefix safe cause rfl)
    | resource final trace residual allowed progress => exact False.elim (Bool.noConfusion allowed)

theorem CostEffectSpec.return_or_accepted_exit {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {index : Nat} {pool : Bytes.LiteralPool}
    (spec : CostEffectSpec source target pure program callee index pool)
    {World : Type} (host : Host World) (targetHost : HostEnv (Observed World))
    (depth : UInt64) (heap : Heap) (initial : Store (Observed World))
    (params : List Value) (args : Env signature.params) (budget : Nat)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep signature.mode heap (PureTransport.erase initial) params args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) signature.mode params args)
      (Env.reads (PureTransport.erase initial) signature.mode params args))
    (input : @Bytes.LiteralPool.Input (Env signature.params)
      (Env.represent signature.params signature.modes) pool heap (PureTransport.erase initial) params args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) signature.mode params args,
      regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (within : heap.Within (PureTransport.erase initial) source budget)
    (bounded : Resource.CallPrefixBound (observedHost host) pure program callee depth args initial.host budget)
    (safe : host.NoTrapsAlong ((program.funs pure.funs).get callee args) initial.host.world) :
    ∃ bound, ∀ fuel ≥ bound,
      CostFunctionResult host pure program callee depth args params heap initial false
        (run fuel target index initial ((.i64 depth :: params).reverse) targetHost) ∧
      ReturnOrAcceptedExit host ((program.funs pure.funs).get callee args) initial.host
        (run fuel target index initial ((.i64 depth :: params).reverse) targetHost) := by
  obtain ⟨bound, proof⟩ := spec World host targetHost depth heap initial params args budget false
    valid at_ rep separate input scratch cap (fun _ => ⟨within, bounded⟩)
  exact ⟨bound, fun fuel enough =>
    ⟨proof fuel enough, (proof fuel enough).return_or_accepted_exit safe⟩⟩

end Verified.Wasi
