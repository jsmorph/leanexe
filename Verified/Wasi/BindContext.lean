import Verified.Wasi.CommandValue
import Verified.Wasi.LoopAfter
import Verified.Wasi.OwnedScratch
import Verified.Wasi.CostResults

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem CommandResult.lower {World : Type} {host : Host World} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base upper : Nat}
    {result : ResultTy} {action : Action result.denote} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {continuation : Continuation (Observed World)}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (selected : ∀ i, live i = true → liveIn i = true) (below : base ≤ upper)
    (classification : CommandResult host env slots liveIn live upper result action
      heap initial locals aborts continuation) :
    CommandResult host env slots liveIn live base result action heap initial locals aborts
      continuation := by
  cases classification with
  | returned value finalHeap final finalLocals words trace execution after =>
      exact .returned value finalHeap final finalLocals words trace execution
        (after.lower vars selected below)
  | terminal final trace outcome message execution ending =>
      exact .terminal final trace outcome message execution ending
  | resource final trace residual allowed progress =>
      exact .resource final trace residual allowed progress

theorem CostCommandResult.lower {World : Type} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {command : Command pureSigs effectSigs context result} {depth : UInt64}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base upper : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {continuation : Continuation (Observed World)}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (selected : ∀ i, live i = true → liveIn i = true) (below : base ≤ upper)
    (classification : CostCommandResult host pure program command depth env slots liveIn live
      upper heap initial locals aborts continuation) :
    CostCommandResult host pure program command depth env slots liveIn live base heap initial
      locals aborts continuation := by
  cases classification with
  | returned value finalHeap final finalLocals words trace spent fits execution after top =>
      exact .returned value finalHeap final finalLocals words trace spent fits execution
        (after.lower vars selected below) top
  | trapped final message classification =>
      exact .trapped final message (classification.lower vars selected below)

theorem bind_context_holds {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live bodyIn : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {initial final : Store World} {locals finalLocals boundLocals : Locals}
    {type : Ty} {value : type.denote} {words : List Value}
    (after : After env slots liveIn live base heap initial locals (.value type) value
      finalHeap final finalLocals words)
    (frame : Frame base finalLocals boundLocals)
    (held : LocalsHold boundLocals base type.types words)
    (selected : ∀ i, bodyIn (i + 1) = true → live i = true) :
    Holds (.cons value env) (⟨base, .owned⟩ :: slots) bodyIn (base + type.width)
      finalHeap (PureTransport.erase final) boundLocals := by
  have adjusted := after.reframe frame
  exact (adjusted.holds.live_mono selected).push held adjusted.rep
    (adjusted.apart.live_mono selected)

theorem bind_context_scratch {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live bodyIn : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {initial final : Store World} {locals finalLocals boundLocals : Locals}
    {type : Ty} {value : type.denote} {words : List Value}
    (after : After env slots liveIn live base heap initial locals (.value type) value
      finalHeap final finalLocals words)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (frame : Frame base finalLocals boundLocals)
    (held : LocalsHold boundLocals base type.types words)
    (liveSelected : ∀ i, live i = true → liveIn i = true)
    (selected : ∀ i, bodyIn (i + 1) = true → live i = true) :
    Holds.ApartFrom (.cons value env) (⟨base, .owned⟩ :: slots) bodyIn
      (PureTransport.erase final) boundLocals ABI.scratch := by
  have adjusted := after.reframe frame
  exact ((adjusted.scratch vars scratch liveSelected).mono selected).push held adjusted.rep.length
    (fun _ => owned_scratch adjusted.rep)

theorem bind_context_safe {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live bodyIn : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {initial final : Store World} {locals finalLocals boundLocals : Locals}
    {type : Ty} {value : type.denote} {words : List Value} {pool : Bytes.LiteralPool}
    (after : After env slots liveIn live base heap initial locals (.value type) value
      finalHeap final finalLocals words)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (safe : pool.Safe env slots liveIn heap (PureTransport.erase initial) locals)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (frame : Frame base finalLocals boundLocals)
    (held : LocalsHold boundLocals base type.types words)
    (liveSelected : ∀ i, live i = true → liveIn i = true)
    (selected : ∀ i, bodyIn (i + 1) = true → live i = true) :
    pool.Safe (.cons value env) (⟨base, .owned⟩ :: slots) bodyIn
      finalHeap (PureTransport.erase final) boundLocals := by
  have adjusted := after.reframe frame
  obtain ⟨preserved, fresh⟩ := adjusted.pool_safe safe vars scratch liveSelected poolApart
  exact (preserved.mono selected).push held adjusted.rep fresh

end Verified.Wasi
