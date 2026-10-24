import Verified.Wasi.After
import Verified.Wasi.Code
import Verified.Wasi.HostSpec
import LeanExe.Wasi.RelatedExec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def TerminalMessage (message : String) : Outcome α → Prop
  | .returned _ => False
  | .exited _ => message = exitTrap
  | .trapped cause => message = cause

inductive CommandResult {World : Type} {context : List Ty}
    (host : Host World) (env : Env context) (slots : List Slot)
    (liveIn live : Nat → Bool) (base : Nat) (result : ResultTy)
    (action : Action result.denote) (heap : Heap) (initial : Store (Observed World))
    (locals : Locals) (aborts : Bool) : Continuation (Observed World) → Prop where
  | returned (value : result.denote) (finalHeap : Heap) (final : Store (Observed World))
      (finalLocals : Locals) (words : List Value) (trace : List Event)
      (execution : Exec (observedHost host) action initial.host trace (.returned value) final.host)
      (after : After env slots liveIn live base heap initial locals result value
        finalHeap final finalLocals words) :
      CommandResult host env slots liveIn live base result action heap initial locals aborts
        (.Fallthrough final { finalLocals with values := words.reverse ++ locals.values })
  | terminal (final : Store (Observed World)) (trace : List Event)
      (outcome : Outcome result.denote) (message : String)
      (execution : Exec (observedHost host) action initial.host trace outcome final.host)
      (terminal : TerminalMessage message outcome) :
      CommandResult host env slots liveIn live base result action heap initial locals aborts
        (.Trap final message)
  | resource (final : Store (Observed World)) (trace : List Event)
      (residual : Action result.denote) (allowed : aborts = true)
      (progress : Prefix (observedHost host) action initial.host trace residual final.host) :
      CommandResult host env slots liveIn live base result action heap initial locals aborts
        (.Trap final "unreachable")

theorem CommandResult.resource_refl {World : Type} {context : List Ty}
    {host : Host World} {env : Env context} {slots : List Slot}
    {liveIn live : Nat → Bool} {base : Nat} {result : ResultTy}
    {action : Action result.denote} {heap : Heap} {initial final : Store (Observed World)}
    {locals : Locals} {aborts : Bool} (allowed : aborts = true)
    (sameWorld : final.host = initial.host) :
    CommandResult host env slots liveIn live base result action heap initial locals aborts
      (.Trap final "unreachable") :=
  .resource final [] action allowed (sameWorld.symm ▸ Prefix.refl action initial.host)

theorem wp_command_unit {World : Type} {host : Host World} {context : List Ty}
    {pureSigs : List Sig} {effectSigs : List EffectSig} {env : Env context}
    {slots : List Slot} {live : Nat → Bool} {base h : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {source target : Wasm.Module}
    {targetHost : HostEnv (Observed World)} {aborts : Bool} {pool : Bytes.LiteralPool}
    (at_ : heap.At (PureTransport.erase initial))
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals) :
    wp target ((Command.unit (pureSigs := pureSigs) (effectSigs := effectSigs)
        (context := context)).code
        (pool := pool) source h slots base live)
      (CommandResult host env slots live live base .unit (.pure ()) heap initial locals aborts)
      initial locals targetHost := by
  change wp target [] _ initial locals targetHost
  rw [wp_nil]
  have result : CommandResult host env slots live live base .unit (.pure ()) heap initial
      locals aborts (.Fallthrough initial { locals with values := ([] : List Value).reverse ++
        locals.values }) :=
    CommandResult.returned (result := .unit) () heap initial locals [] [] (Exec.pure initial.host ())
      (After.unit at_ vars)
  cases locals
  simpa only [List.reverse_nil, List.nil_append] using result

end Verified.Wasi
