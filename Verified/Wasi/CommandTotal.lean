import Verified.Wasi.NativeCommand
import Verified.Wasi.NativeTotal

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline

def AcceptedExit {World : Type} (host : Host World) (action : Action Unit)
    (initial : Observed World) : Result (Observed World) → Prop
  | .Trap final message =>
      ∃ code trace, message = exitTrap ∧
        Exec host action initial.world trace (.exited code) final.host.world ∧
        final.host.events = initial.events ++ trace ∧ host.exited final.host.world = some code
  | _ => False

theorem bind_exit_not_returned {World : Type} {host : Host World} {native : Action UInt64}
    {world : World} {trace : List Event} {value : Unit} {final : World}
    (execution : Exec host (Action.bind native fun status => Action.exit (α := Unit) status)
      world trace (.returned value) final) : False := by
  obtain ⟨after, first, middle, rest, mainRun, nextRun, sameTrace⟩ := Exec.unbind native execution
  cases middle with
  | returned status =>
      change Exec host (Action.exit (α := Unit) status) after rest (.returned value) final at nextRun
      cases nextRun
  | exited code =>
      change rest = [] ∧ (.returned value : Outcome Unit) = .exited code ∧ final = after at nextRun
      cases nextRun.2.1
  | trapped cause =>
      change rest = [] ∧ (.returned value : Outcome Unit) = .trapped cause ∧ final = after at nextRun
      cases nextRun.2.1

theorem ReturnOrAcceptedExit.command_exit {World : Type} {host : Host World} {native : Action UInt64}
    {initial : Observed World} {outcome : Result (Observed World)}
    (total : ReturnOrAcceptedExit host
      (Action.bind native fun status => Action.exit (α := Unit) status) initial outcome) :
    AcceptedExit host (Action.bind native fun status => Action.exit (α := Unit) status) initial outcome := by
  cases outcome with
  | Success values final =>
      obtain ⟨value, trace, execution, events, marker⟩ := total
      exact False.elim (bind_exit_not_returned execution)
  | Trap final message => exact total
  | Invalid message => exact False.elim total
  | OutOfFuel => exact False.elim total
  | Thrown tag values final => exact False.elim total

theorem command_run_total {World : Type} {host : Host World}
    {heap : Heap} {initial : Store (Observed World)} {runner : Nat → Result (Observed World)}
    (native : Action UInt64)
    (execution : ∃ bound, ∀ fuel ≥ bound,
      NativeFunctionResult host startSignature
        (Action.bind native fun status => Action.exit (α := Unit) status)
        (fun value : Unit => value) .nil [] heap initial false (runner fuel))
    (safe : host.NoTrapsAlong (Action.bind native fun status => Action.exit (α := Unit) status)
      initial.host.world) :
    ∃ bound, ∀ fuel ≥ bound,
      AcceptedExit host (Action.bind native fun status => Action.exit (α := Unit) status)
        initial.host (runner fuel) := by
  obtain ⟨bound, total⟩ := native_run_total execution safe
  exact ⟨bound, fun fuel enough => (total fuel enough).command_exit⟩

end Verified.Wasi
