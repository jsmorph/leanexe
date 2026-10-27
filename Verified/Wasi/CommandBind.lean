import Verified.Wasi.CommandSpec
import Verified.Wasi.AfterScratch
import LeanExe.ProofKit.Sequencing

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem CommandResult.bind_trap {World : Type} {host : Host World}
    {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn liveMid live : Nat → Bool} {base : Nat} {intermediate result : ResultTy}
    {first : Action intermediate.denote} {next : intermediate.denote → Action result.denote}
    {heap : Heap} {initial final : Store (Observed World)} {locals : Locals}
    {innerAborts aborts : Bool} {message : String}
    (execution : CommandResult host env slots liveIn liveMid base intermediate first
      heap initial locals innerAborts (.Trap final message))
    (allowed : innerAborts = true → aborts = true) :
    CommandResult host env slots liveIn live base result (Action.bind first next)
      heap initial locals aborts (.Trap final message) := by
  cases execution with
  | terminal final trace outcome message execution terminal =>
      cases outcome with
      | returned value => exact terminal.elim
      | exited code =>
          refine .terminal final trace (.exited code) message ?_ terminal
          simpa only [List.append_nil] using execution.bind
            (next := next) (rest := []) ⟨rfl, rfl, rfl⟩
      | trapped cause =>
          refine .terminal final trace (.trapped cause) message ?_ terminal
          simpa only [List.append_nil] using execution.bind
            (next := next) (rest := []) ⟨rfl, rfl, rfl⟩
  | resource final trace residual hAllowed progress =>
      exact .resource final trace (Action.bind residual next) (allowed hAllowed) progress.bind

theorem CommandResult.bind_after_trap {World : Type} {host : Host World}
    {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn liveMid live : Nat → Bool} {base : Nat} {intermediate result : ResultTy}
    {first : Action intermediate.denote} {next : intermediate.denote → Action result.denote}
    {value : intermediate.denote} {heap middleHeap : Heap}
    {initial middle final : Store (Observed World)} {locals middleLocals : Locals}
    {firstTrace : List Event} {aborts : Bool} {message : String}
    (firstExecution : Exec (observedHost host) first initial.host firstTrace (.returned value)
      middle.host)
    (execution : CommandResult host env slots liveMid live base result (next value)
      middleHeap middle middleLocals aborts (.Trap final message)) :
    CommandResult host env slots liveIn live base result (Action.bind first next)
      heap initial locals aborts (.Trap final message) := by
  cases execution with
  | terminal final trace outcome message execution terminal =>
      exact .terminal final (firstTrace ++ trace) outcome message
        (firstExecution.bind execution) terminal
  | resource final trace residual allowed progress =>
      exact .resource final (firstTrace ++ trace) residual allowed
        (Prefix.bind_after firstExecution progress)

theorem CommandResult.bind_unit {World : Type} {host : Host World}
    {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn liveMid live : Nat → Bool} {base : Nat} {result : ResultTy}
    {first : Action Unit} {next : Unit → Action result.denote}
    {heap middleHeap : Heap} {initial middle : Store (Observed World)}
    {locals middleLocals : Locals} {firstTrace : List Event} {aborts : Bool}
    {continuation : Continuation (Observed World)}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (firstExecution : Exec (observedHost host) first initial.host firstTrace (.returned ())
      middle.host)
    (firstAfter : After env slots liveIn liveMid base heap initial locals .unit ()
      middleHeap middle middleLocals [])
    (sameStack : middleLocals.values = locals.values)
    (execution : CommandResult host env slots liveMid live base result (next ())
      middleHeap middle middleLocals aborts continuation)
    (midSelected : ∀ i, liveMid i = true → liveIn i = true)
    (selected : ∀ i, live i = true → liveMid i = true) :
    CommandResult host env slots liveIn live base result (Action.bind first next)
      heap initial locals aborts continuation := by
  cases execution with
  | returned value finalHeap final finalLocals words trace execution after =>
      rw [sameStack]
      exact .returned value finalHeap final finalLocals words (firstTrace ++ trace)
        (firstExecution.bind execution)
        (After.thenUnit vars apart firstAfter after midSelected selected)
  | terminal final trace outcome message execution terminal =>
      exact .terminal final (firstTrace ++ trace) outcome message
        (firstExecution.bind execution) terminal
  | resource final trace residual allowed progress =>
      exact .resource final (firstTrace ++ trace) residual allowed
        (Prefix.bind_after firstExecution progress)

theorem wp_sequence_unit {World : Type} {host : Host World}
    {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn liveMid live : Nat → Bool} {base : Nat} {result : ResultTy}
    {first : Action Unit} {next : Unit → Action result.denote}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {aborts : Bool} {target : Wasm.Module} {targetHost : HostEnv (Observed World)}
    {firstCode nextCode : Program}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (midSelected : ∀ i, liveMid i = true → liveIn i = true)
    (selected : ∀ i, live i = true → liveMid i = true)
    (firstRun : wp target firstCode
      (CommandResult host env slots liveIn liveMid base .unit first heap initial locals aborts)
      initial locals targetHost)
    (nextRun : ∀ middleHeap middle middleLocals trace,
      Exec (observedHost host) first initial.host trace (.returned ()) middle.host →
      After env slots liveIn liveMid base heap initial locals .unit ()
        middleHeap middle middleLocals [] →
      middleLocals.values = locals.values →
      wp target nextCode
        (CommandResult host env slots liveMid live base result (next ())
          middleHeap middle middleLocals aborts) middle middleLocals targetHost) :
    wp target (firstCode ++ nextCode)
      (CommandResult host env slots liveIn live base result (Action.bind first next)
        heap initial locals aborts) initial locals targetHost := by
  apply wp_append
  refine wp.conseq (fun continuation execution => ?_) firstRun
  cases execution with
  | returned value middleHeap middle middleLocals words trace execution after =>
      cases value
      have empty : words = [] := after.rep
      subst words
      simp only [List.reverse_nil, List.nil_append, Then]
      have adjusted : After env slots liveIn liveMid base heap initial locals .unit ()
          middleHeap middle { middleLocals with values := locals.values } [] :=
        ⟨after.step,
          ⟨after.frame.params, after.frame.length, after.frame.below, after.frame.below32⟩,
          after.holds, after.rep, after.apart⟩
      refine wp.conseq (fun continuation second => ?_)
        (nextRun middleHeap middle _ trace execution adjusted rfl)
      exact CommandResult.bind_unit vars apart execution adjusted rfl second midSelected selected
  | terminal final trace outcome message execution terminal =>
      exact CommandResult.bind_trap (intermediate := .unit) (result := result)
        (liveMid := liveMid) (next := next)
        (CommandResult.terminal (result := .unit) final trace outcome message execution terminal) id
  | resource final trace residual allowed progress =>
      exact CommandResult.resource final trace (Action.bind residual next) allowed progress.bind

theorem CommandResult.bind_value {World : Type} {host : Host World}
    {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn liveMid bodyIn live : Nat → Bool} {base : Nat} {type : Ty} {result : ResultTy}
    {first : Action type.denote} {next : type.denote → Action result.denote}
    {intermediate : type.denote} {heap middleHeap : Heap}
    {initial middle : Store (Observed World)} {locals middleLocals boundLocals : Locals}
    {firstWords : List Value} {firstTrace : List Event} {aborts : Bool}
    {continuation : Continuation (Observed World)}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (firstExecution : Exec (observedHost host) first initial.host firstTrace
      (.returned intermediate) middle.host)
    (firstAfter : After env slots liveIn liveMid base heap initial locals (.value type)
      intermediate middleHeap middle middleLocals firstWords)
    (frame : Frame base middleLocals boundLocals)
    (held : LocalsHold boundLocals base type.types firstWords)
    (sameStack : boundLocals.values = locals.values)
    (execution : CommandResult host (.cons intermediate env) (⟨base, .owned⟩ :: slots)
      bodyIn (shift 1 live) (base + type.width) result (next intermediate)
      middleHeap middle boundLocals aborts continuation)
    (bodySelected : ∀ i, bodyIn (i + 1) = true → liveMid i = true)
    (midSelected : ∀ i, liveMid i = true → liveIn i = true)
    (selected : ∀ i, live i = true → liveMid i = true) :
    CommandResult host env slots liveIn live base result (Action.bind first next)
      heap initial locals aborts continuation := by
  cases execution with
  | returned value finalHeap final finalLocals words trace execution after =>
      rw [sameStack]
      exact .returned value finalHeap final finalLocals words (firstTrace ++ trace)
        (firstExecution.bind execution)
        (After.bind_value vars apart firstAfter frame held after bodySelected midSelected selected)
  | terminal final trace outcome message execution terminal =>
      exact .terminal final (firstTrace ++ trace) outcome message
        (firstExecution.bind execution) terminal
  | resource final trace residual allowed progress =>
      exact .resource final (firstTrace ++ trace) residual allowed
        (Prefix.bind_after firstExecution progress)

end Verified.Wasi
