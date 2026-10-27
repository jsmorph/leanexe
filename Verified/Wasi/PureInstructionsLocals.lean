import Verified.Wasi.PureInstructionsBasic

namespace Verified.Wasi.PureTransport

open Wasm

theorem local_transport {World : Type} (source target : Module)
    {inst : Instruction} (hForm : Encoding.InstructionForm inst) (hLocal : localAtomic inst = true)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals inst targetHost =
        liftContinuation world (execOne fuel source initial locals inst sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals inst sourceHost) := by
  cases fuel with
  | zero => simp only [execOne.eq_def, liftContinuation, NoReturnCall, and_self]
  | succ fuel =>
    cases hForm <;> simp_all only [localAtomic, Bool.false_eq_true]
    all_goals
      constructor
      · simp only [execOne.eq_def, restore_globals]
        repeat' first
          | rfl
          | split <;> simp_all only [liftContinuation, restore_globals, restore_update_globals]
      · apply (noReturnCall_iff_flag _).2
        simp only [execOne.eq_def]
        repeat' first | rfl | split

end Verified.Wasi.PureTransport
