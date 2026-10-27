import Verified.Wasi.LoopAfter
import Verified.Wasi.LoopSemantics
import Verified.Wasi.CommandSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem loop_context_keep {context : List Ty} {env : Env context} {slots : List Slot}
    {type : Ty} {value : type.denote} {index : UInt64} {stateSlot indexSlot : Nat}
    {liveIn liveOut : Nat → Bool} {store : Store Unit} {locals : Locals} {words : List Value}
    {region : Nat × Nat} (held : LocalsHold locals stateSlot type.types words)
    (width : words.length = type.width)
    (apart : ∀ block ∈ type.blocks store words value, regionsDisjoint region block) :
    Holds.KeepDying (.cons value (.cons (t := .word) index env))
      (⟨stateSlot, .owned⟩ :: ⟨indexSlot, .borrowed⟩ :: loopCaptured slots)
      liveIn liveOut store locals region := by
  intro other x selected discarded owned values actual actualWidth block member
  cases x with
  | here =>
      change LocalsHold locals stateSlot type.types values at actual
      obtain rfl := LocalsHold.unique actual held (actualWidth.trans width.symm)
      exact apart block member
  | there x =>
      cases x with
      | here => exact nomatch owned
      | there x =>
          simp only [Var.index, List.getD_cons_succ, loopCaptured_getD] at owned
          exact nomatch owned

theorem loop_context_no_dying {context : List Ty} {env : Env context} {slots : List Slot}
    {type : Ty} {value : type.denote} {index : UInt64} {stateSlot indexSlot : Nat}
    {liveIn liveOut : Nat → Bool} {store : Store Unit} {locals : Locals} {region : Nat × Nat}
    (kept : liveOut 0 = true) :
    Holds.KeepDying (.cons value (.cons (t := .word) index env))
      (⟨stateSlot, .owned⟩ :: ⟨indexSlot, .borrowed⟩ :: loopCaptured slots)
      liveIn liveOut store locals region := by
  intro other x selected discarded owned
  cases x with
  | here =>
      change liveOut 0 = false at discarded
      rw [kept] at discarded
      exact nomatch discarded
  | there x =>
      cases x with
      | here => exact nomatch owned
      | there x =>
          simp only [Var.index, List.getD_cons_succ, loopCaptured_getD] at owned
          exact nomatch owned

theorem loop_body_step {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {type : Ty} {state value : type.denote} {index : UInt64}
    {stateSlot indexSlot scratch : Nat} {releaseIn bodyIn live : Nat → Bool}
    {heap middleHeap finalHeap : Heap} {initial middle final : Store World} {locals finalLocals : Locals}
    {stateWords words : List Value}
    (held : LocalsHold locals stateSlot type.types stateWords)
    (rep : type.Rep .owned heap (PureTransport.erase initial) stateWords state)
    (cleanup : Evolves (.cons state (.cons (t := .word) index env))
      (⟨stateSlot, .owned⟩ :: ⟨indexSlot, .borrowed⟩ :: loopCaptured slots)
      releaseIn bodyIn scratch heap (PureTransport.erase initial) locals
      middleHeap (PureTransport.erase middle) locals)
    (body : After (.cons state (.cons (t := .word) index env))
      (⟨stateSlot, .owned⟩ :: ⟨indexSlot, .borrowed⟩ :: loopCaptured slots)
      bodyIn live scratch middleHeap middle locals (.value type) value
      finalHeap final finalLocals words) :
    Step heap (PureTransport.erase initial)
      (LoopStateKeep type (PureTransport.erase initial) stateWords state)
      finalHeap (PureTransport.erase final) (type.blocks (PureTransport.erase final) words value) := by
  refine cleanup.step.trans body.step (fun region kept => ⟨?_, fun _ => ⟨?_, kept.2⟩⟩)
  · exact loop_context_keep held rep.length kept.1
  · by_cases used : bodyIn 0 = true
    · have unchanged : Step heap (PureTransport.erase initial) (fun _ => True)
          middleHeap (PureTransport.erase middle) [] :=
        cleanup.step.mono (fun _ _ => loop_context_no_dying used) (fun _ member => nomatch member)
      have same : type.blocks (PureTransport.erase middle) stateWords state =
          type.blocks (PureTransport.erase initial) stateWords state :=
        (rep.step unchanged (fun _ _ => trivial)).2.1
      apply loop_context_keep held rep.length
      rw [same]
      exact kept.1
    · intro other x selected discarded owned values actual width block member
      cases x with
      | here => exact False.elim (used selected)
      | there x =>
          cases x with
          | here => exact nomatch owned
          | there x =>
              simp only [Var.index, List.getD_cons_succ, loopCaptured_getD] at owned
              exact nomatch owned

theorem CommandResult.loop_body_trap {World : Type} {host : Host World}
    {outerContext bodyContext : List Ty} {outerEnv : Env outerContext} {bodyEnv : Env bodyContext}
    {outerSlots bodySlots : List Slot} {outerIn outerLive bodyIn bodyLive : Nat → Bool}
    {outerBase bodyBase : Nat} {type : Ty} {count index : UInt64} {initialState state : type.denote}
    {test : UInt64 → type.denote → Bool} {step : UInt64 → type.denote → Action type.denote}
    {initialHeap bodyHeap : Heap} {initial bodyInitial final : Store (Observed World)}
    {outerLocals bodyLocals : Locals} {trace : List Event} {bodyAborts aborts : Bool} {message : String}
    (history : LoopProgress (observedHost host) count initialState test step Action.pure
      initial.host index state trace bodyInitial.host)
    (bound : index < count) (runs : test index state = true)
    (body : CommandResult host bodyEnv bodySlots bodyIn bodyLive bodyBase (.value type)
      (step index state) bodyHeap bodyInitial bodyLocals bodyAborts (.Trap final message))
    (allowed : bodyAborts = true → aborts = true) :
    CommandResult host outerEnv outerSlots outerIn outerLive outerBase (.value type)
      (.loop count initialState test step Action.pure) initialHeap initial outerLocals aborts
      (.Trap final message) := by
  cases body with
  | terminal final first outcome message execution terminal =>
      cases outcome with
      | returned value => exact terminal.elim
      | exited code =>
          exact .terminal final (trace ++ first) (.exited code) message
            (history.exited bound runs execution) terminal
      | trapped cause =>
          exact .terminal final (trace ++ first) (.trapped cause) message
            (history.trapped bound runs execution) terminal
  | resource final first residual permitted progress =>
      exact .resource final (trace ++ first)
        (Action.bind residual (loopResidual count (index + 1) test step Action.pure))
        (allowed permitted) (history.resource bound runs progress)

end Verified.Wasi
